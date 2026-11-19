// A seeded, deterministic random source (mulberry32), so that a seed names a program.

export class Random {
  private state: number;

  constructor(seed: number) {
    this.state = seed >>> 0;
  }

  next(): number {
    this.state = (this.state + 0x6d2b79f5) >>> 0;
    let t = this.state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  }

  int(low: number, high: number): number {
    return low + Math.floor(this.next() * (high - low + 1));
  }

  chance(probability: number): boolean {
    return this.next() < probability;
  }

  pick<T>(items: readonly T[]): T {
    return items[Math.floor(this.next() * items.length)];
  }

  weighted<T>(items: readonly [number, T][]): T {
    const total = items.reduce((sum, [weight]) => sum + weight, 0);
    let roll = this.next() * total;
    for (const [weight, item] of items) {
      roll -= weight;
      if (roll < 0) return item;
    }
    return items[items.length - 1][1];
  }

  shuffle<T>(items: T[]): T[] {
    const copy = [...items];
    for (let i = copy.length - 1; i > 0; i--) {
      const j = this.int(0, i);
      [copy[i], copy[j]] = [copy[j], copy[i]];
    }
    return copy;
  }
}
