#pragma once

#ifdef C2PULSE

// Dummy declaration for C assert() translation
static inline void __c2pulse_c_assert(int x) { (void)x; }
// Opaque function used to guard assert — Pulse verifies both branches
__attribute__((annotate("c2pulse-pure"))) _Bool c2pulse_c_assert_enabled(void);

#define __c2pulse_concat_ind(x, y) x ## y
#define __c2pulse_concat(x, y) __c2pulse_concat_ind(x, y)
#define _include_pulse(...) [[clang::annotate("c2pulse-includes", __COUNTER__)]] \
    void __c2pulse_concat(__c2pulse_include_anchor_, __COUNTER__) (void) {}

#define __capture_args(args) __COUNTER__

#define _requires(p) __attribute__((annotate("c2pulse-requires", __capture_args(p))))
#define _ensures(p) __attribute__((annotate("c2pulse-ensures", __capture_args(p))))
#define _refine(p) __attribute__((annotate("c2pulse-refine", __capture_args(p))))
#define _refine_always(p) __attribute__((annotate("c2pulse-refine-always", __capture_args(p))))
#define _invariant(p) __attribute__((annotate("c2pulse-invariant", __capture_args(p))))
#define _do_while_first(name) __attribute__((annotate("c2pulse-do-while-first", #name)))

#define _assert(p) ({ __attribute__((annotate("c2pulse-assert", __capture_args(p)))) {} })
#define _ghost_stmt(args) ({ __attribute__((annotate("c2pulse-ghost-stmt", __capture_args(args)))) {} })

#define _plain __attribute__((annotate("c2pulse-plain")))
#define _consumes __attribute__((annotate("c2pulse-consumes")))
#define _out __attribute__((annotate("c2pulse-out")))
#define _array __attribute((annotate("c2pulse-array")))
#define _arrayptr __attribute((annotate("c2pulse-arrayptr")))
#define _pure __attribute((annotate("c2pulse-pure")))

#define _inline_pulse(args) _inline_pulse(__capture_args(args))

#else

#define _include_pulse(...)
#define _requires(p)
#define _ensures(p)
#define _refine(p)
#define _refine_always(p)
#define _invariant(p)
#define _do_while_first(name)

#define _assert(p)
#define _ghost_stmt(args)

#define _plain
#define _consumes
#define _out
#define _array
#define _arrayptr
#define _pure

#endif

#define _preserves(p) _requires(p) _ensures(p)
#define _allocated _refine((_slprop) _inline_pulse(freeable $(this)))

#define _same_as_old(x) ((x) == _old(x))
#define _preserves_value(x) _ensures(_same_as_old(x))

// Override C assert to translate to Pulse assertion
#ifdef C2PULSE
#undef assert
#define assert(x) __c2pulse_c_assert(x)
#endif