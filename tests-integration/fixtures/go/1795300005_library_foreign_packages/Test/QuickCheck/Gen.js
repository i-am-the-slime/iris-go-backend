export const float32ToInt32 = (n) => new Int32Array(new Float32Array([n]).buffer)[0];
