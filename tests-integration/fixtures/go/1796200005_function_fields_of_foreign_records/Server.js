export const serve = (routes) => () => {
  routes.handle("alice", "hi", (reply) => () => console.log(reply));
  console.log(routes.add(1)(2));
  routes.each.forEach((each) => each("a")("b")());
  console.log(routes.settings.greeting("hello")("alice"));
};

export const installHooks = () => ({
  route: (name) => (body, reply) => reply(name + " " + body)(),
  fold: (step) => step(1)(2),
});

export const log = (line) => () => console.log(line);
