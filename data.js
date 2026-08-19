import { createClient } from "redis";

const KEY = "pipeline-review";

let client;

async function getClient() {
  if (!client) {
    client = createClient({ url: process.env.REDIS_URL });
    client.on("error", () => {});
  }
  if (!client.isOpen) await client.connect();
  return client;
}

export default async function handler(req, res) {
  try {
    const c = await getClient();

    if (req.method === "GET") {
      const value = await c.get(KEY);
      res.setHeader("Cache-Control", "no-store");
      return res.status(200).json({ value: value === null ? null : value });
    }

    if (req.method === "POST") {
      const body = typeof req.body === "string" ? JSON.parse(req.body) : req.body;
      if (!body || typeof body.value !== "string") {
        return res.status(400).json({ error: "Expected a JSON body of the form {value: \"...\"}" });
      }
      await c.set(KEY, body.value);
      return res.status(200).json({ ok: true });
    }

    res.setHeader("Allow", "GET, POST");
    return res.status(405).json({ error: "Method not allowed" });
  } catch (err) {
    return res.status(500).json({ error: String((err && err.message) || err) });
  }
}
