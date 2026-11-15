# foldable-traversable's test defines `deferEff :: forall a. (Unit -> a) -> Effect a` as
# `unsafeCoerce`, which holds only where an Effect is a JS thunk. The replacement defers the
# evaluation the same way (the function runs when the effect runs) without the coercion.
sed -i '' 's/^deferEff = unsafeCoerce$/deferEff f = pure unit >>= \\_ -> pure (f unit)/' Main.purs
grep -q '^deferEff f = pure unit' Main.purs
