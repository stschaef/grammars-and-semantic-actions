const http = require('http'), fs = require('fs'), path = require('path');
const root = __dirname, port = process.argv[2] ? +process.argv[2] : 8317;
http.createServer((req, res) => {
  let p = decodeURIComponent(req.url.split('?')[0]);
  if (p === '/' ) p = '/combinators.html';
  const f = path.join(root, path.normalize(p).replace(/^(\.\.[/\\])+/, ''));
  fs.readFile(f, (err, buf) => {
    if (err) { res.writeHead(404, {'Content-Type':'text/plain'}); return res.end('not found'); }
    const ext = path.extname(f);
    const ct = ext === '.html' ? 'text/html; charset=utf-8'
             : ext === '.js' ? 'text/javascript; charset=utf-8'
             : 'text/plain; charset=utf-8';
    res.writeHead(200, {'Content-Type': ct});
    res.end(buf);
  });
}).listen(port, '127.0.0.1', () => console.log('serving ' + root + ' on http://127.0.0.1:' + port + '/'));
