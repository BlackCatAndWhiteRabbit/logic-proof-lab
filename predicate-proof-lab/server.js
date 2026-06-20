const http = require("http");
const fs = require("fs");
const path = require("path");

const root = __dirname;
const port = Number(process.env.PORT) || 5600;
const host = "127.0.0.1";
const theoremDataPath = path.join(root, "data", "theorems.json");

const types = {
  ".html": "text/html; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".md": "text/plain; charset=utf-8",
};

const server = http.createServer((req, res) => {
  const url = new URL(req.url, `http://${host}:${port}`);

  if (url.pathname === "/api/theorems") {
    handleTheoremApi(req, res);
    return;
  }

  let filePath = decodeURIComponent(url.pathname);
  if (filePath === "/") filePath = "/index.html";

  const fullPath = path.normalize(path.join(root, filePath));
  if (!fullPath.startsWith(root)) {
    res.writeHead(403);
    res.end("Forbidden");
    return;
  }

  fs.readFile(fullPath, (error, data) => {
    if (error) {
      res.writeHead(404);
      res.end("Not found");
      return;
    }
    res.writeHead(200, {
      "Content-Type": types[path.extname(fullPath)] || "application/octet-stream",
    });
    res.end(data);
  });
});

function handleTheoremApi(req, res) {
  if (req.method === "GET") {
    fs.readFile(theoremDataPath, "utf8", (error, data) => {
      if (error && error.code !== "ENOENT") {
        sendJson(res, 500, { error: "Failed to read theorem library file." });
        return;
      }
      if (error && error.code === "ENOENT") {
        sendJson(res, 200, []);
        return;
      }
      try {
        const parsed = JSON.parse(data || "[]");
        sendJson(res, 200, Array.isArray(parsed) ? parsed : []);
      } catch {
        sendJson(res, 500, { error: "The theorem library file is not valid JSON." });
      }
    });
    return;
  }

  if (req.method === "POST") {
    let body = "";
    req.on("data", (chunk) => {
      body += chunk;
      if (body.length > 10 * 1024 * 1024) {
        req.destroy();
      }
    });
    req.on("end", () => {
      try {
        const parsed = JSON.parse(body || "[]");
        if (!Array.isArray(parsed)) {
          sendJson(res, 400, { error: "The theorem library payload must be an array." });
          return;
        }
        fs.mkdir(path.dirname(theoremDataPath), { recursive: true }, (mkdirError) => {
          if (mkdirError) {
            sendJson(res, 500, { error: "Failed to create data directory." });
            return;
          }
          fs.writeFile(theoremDataPath, `${JSON.stringify(parsed, null, 2)}\n`, "utf8", (writeError) => {
            if (writeError) {
              sendJson(res, 500, { error: "Failed to write theorem library file." });
              return;
            }
            sendJson(res, 200, { ok: true });
          });
        });
      } catch {
        sendJson(res, 400, { error: "Invalid JSON payload." });
      }
    });
    return;
  }

  sendJson(res, 405, { error: "Method not allowed." });
}

function sendJson(res, status, payload) {
  res.writeHead(status, {
    "Content-Type": "application/json; charset=utf-8",
  });
  res.end(JSON.stringify(payload));
}

server.listen(port, host, () => {
  console.log(`Predicate Proof Lab running at http://${host}:${port}/`);
});
