# Private query dispatch adapter

`dispatch.rs` is the concrete, scoped API query dispatcher. The compiler loads
it as `framework2::tools` through the explicit path in `framework2/mod.rs`, so
engine assembly remains private while its physical source is covered by the
API-directory version/documentation gate. The public facade exposes only the
read-only query traits and DTOs, not the authority bundle or mutable engine
handles. All six operation authorization, scope, cancellation and resource
checks remain at this boundary.
