# Effect, Aff and IO; Ref, IORef and MVar

On Go you get three ways to do things and three places to keep state. Here's which one to grab.

- **`Effect`**: one thing after another. Printing, reading a file, bumping a `Ref`. `main` is one,
  and it's where you start.
- **`Aff`**: waiting without holding everything else up. A `delay`, an HTTP request, a child
  process, Go code that calls you back later. Fibers take turns, as they do in JavaScript.
- **`IO`**: work for every core. It's Haskell's `IO`, from `Go.IO` in
  [purescript-go](https://github.com/i-am-the-slime/purescript-go)'s `go-io` package, and its
  threads really run at the same time.

And for state:

| | Use it from | Safe to share between |
| --- | --- | --- |
| `Effect.Ref` | `Effect`, `Aff` | fibers, but not threads that run at the same time |
| `IORef` | `IO` | threads, if you update it with `atomicModifyIORef'` |
| `MVar` | `IO` | threads, and it makes them wait until there's a value |

To see the Go each of these turns into, read [Int64, Aff, JSON and foreign code](libraries.md).

## Fibers take turns

```purescript
main :: Effect Unit
main = launchAff_ do
  visits <- Ref.new 0 # liftEffect
  fibers <- for (1 .. 1000) \_ -> forkAff do
    delay (Milliseconds 10.0)
    Ref.modify_ (_ + 1) visits # liftEffect
  traverse_ joinFiber fibers
  total <- Ref.read visits # liftEffect
  log ("1000 fibers, " <> show total <> " visits")
```

```
1000 fibers, 1000 visits
```

Only one fiber runs at a time, and it only hands over when it waits. So between two waits a fiber
has every `Ref` to itself, and no visit gets lost. Across a wait it doesn't: read a `Ref`, `delay`,
write it back, and another fiber may have written in between. Same as in JavaScript.

## Threads run at the same time

```purescript
main :: Effect Unit
main = launchIO_ do
  hits <- newIORef 0
  forConcurrently_ (1 .. 1000) \_ ->
    atomicModifyIORef' hits \n -> (n + 1) /\ unit
  total <- readIORef hits
  log ("1000 threads, " <> show total <> " hits")
```

```
1000 threads, 1000 hits
```

`forConcurrently_` runs each element on its own thread and waits for all of them. Every thread
always sees a whole value in an `IORef`, and `atomicModifyIORef'` tries again when another thread
wrote in between, so each hit counts. Keep the function you hand it cheap, it may run more than
once. `modifyIORef` reads and then writes, so two threads can lose an update.

### `Effect.Ref` from a thread

`liftEffect` runs an `Effect` from inside `IO`. What that means for a `Ref` depends on the rest of
your program:

- **No `Aff` anywhere**: no `launchAff_`, no `AVar`, no `Promise`, also not in a library you use.
  Then there are no fibers to protect, so `liftEffect` runs the `Effect` right there on the thread,
  and your threads run side by side, `log` included. An `Effect.Ref` isn't built for that: two
  threads modifying one lose updates, and reading a record while another thread writes it can crash
  the program. Use an `IORef` or an `MVar`.
- **`Aff` somewhere**: now `liftEffect` waits until it's the thread's turn on the event loop, where
  the fibers live, and runs the `Effect` there. A `Ref` is safe again:

```purescript
main :: Effect Unit
main = launchAff_ do
  hits <- Ref.new 0 # liftEffect
  forConcurrently_ (1 .. 1000) (\_ -> Ref.modify_ (_ + 1) hits # liftEffect) # toAff
  total <- Ref.read hits # liftEffect
  log ("1000 threads, " <> show total <> " hits")
```

```
1000 threads, 1000 hits
```

`toAff` runs the `IO` from `Aff`, and the fiber waits for it without holding up the others. Each
trip to the event loop and back costs about 80 ns, though, and no fiber runs while one is under
way. Keep a hot loop's state in an `IORef`.

## `MVar`s hand things over

```purescript
main :: Effect Unit
main = launchIO_ do
  answer <- newEmptyMVar
  _ <- forkIO do
    threadDelay (Milliseconds 50.0)
    putMVar answer 42
  log "waiting for the worker"
  result <- takeMVar answer
  log ("the worker says " <> show result)
```

```
waiting for the worker
the worker says 42
```

`takeMVar` waits until there's something to take. Your program doesn't wait for the threads it
`forkIO`s, so this is how you wait for one.

An `MVar` is also a lock. `modifyMVar_` takes the value out, so every other thread waits until the
new one is back in. Reach for it instead of an `IORef` when an update has to do `IO` along the
way, like asking another server before writing down the answer. [No `Aff`, no
waiting](libraries.md#no-aff-no-waiting) counts hits that way.

## Getting `go-io`

`Go.IO` isn't in the registry yet. The
[purescript-go README](https://github.com/i-am-the-slime/purescript-go#installing) shows the lines
to add to your `spago.yaml`.
