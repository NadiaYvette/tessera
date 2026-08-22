default Order dec

$include <prelude.sail>

// Tessera — the timer device (SSG-5): per-hart mtimecmp, monotonic
// mtime counter, timer interrupt pending bits.  The Sail file
// typechecks only — the generated timer_types.v provides the record
// types; timer.v is hand-written with Iris-free Rocq definitions.

struct HartTimer = {
  mtimecmp : bits(64),
  pending  : bool
}

struct TimerDevice = {
  mtime : bits(64),
  harts : list(HartTimer)
}
