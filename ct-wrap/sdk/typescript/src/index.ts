export type WrapOptions = {
  generateProof?: boolean;
  contentType?: string;
  circuit?: string;
};

export class CTWrapClient {
  constructor(private readonly baseUrl: string) {}

  async wrap(data: Uint8Array, recipients: string[], opts: WrapOptions = {}) {
    const res = await fetch(`${this.baseUrl}/api/v1/wrap`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({
        data: Buffer.from(data).toString("base64"),
        recipients,
        content_type: opts.contentType ?? null,
        generate_proof: opts.generateProof ?? false,
        circuit: opts.circuit ?? null,
      }),
    });
    if (!res.ok) throw new Error(`wrap failed: ${res.status}`);
    return await res.json();
  }
}
