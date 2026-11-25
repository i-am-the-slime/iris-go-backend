export const joinEntriesImpl = (first, second, entries) =>
  entries.map((entry) => first(entry) + "=" + second(entry)).join(",");
