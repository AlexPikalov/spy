//! Spy crate is inspired by such famous Javascript testing tools
//! as Jasmine and Sinon.js. It provides easy configurable spies
//! with predefined behaviour.
//!
//! # Spy without arguments
//!
//! `spy!()` creates a pair of a spy function that receives no arguments
//! and does nothing and corresponded `Spy` object.
//!
//! ```rust
//! #[macro_use]
//! extern crate spy;
//!
//! use spy::*;
//!
//! fn main() {
//!     let (spy_fn, spy) = spy!();
//!
//!     assert_eq!(spy_fn(), ());
//!     assert_eq!(spy_fn(), ());
//!
//!     // take a snapshot
//!     let snapshot = spy.snapshot();
//!
//!     // make assertions
//!     assert!(
//!         snapshot.called_with(()),
//!         "should be called with () at least once"
//!     );
//!     assert!(
//!         snapshot.each_called_with(()),
//!         "should be called with () each time"
//!     );
//!     assert_eq!(snapshot.num_of_calls(), 2, "should be called 2 times");
//!     assert_eq!(snapshot.all_calls(), &vec![(), ()]);
//!     assert_eq!(snapshot.first_call().expect("should be Some"), &());
//!     assert_eq!(snapshot.last_call().expect("should be Some"), &());
//!     assert_eq!(snapshot.nth_call(1).expect("should be Some"), &());
//! }
//!
//! ```
//!
//! # Spy with arguments
//!
//! If a spy function should receive arguments it can be created in one
//! of following ways:
//!
//! * `spy!(|n, m|)` creates a spy function that can receive two arguments.
//! Any number of arguments could be passed inside `||`.
//! Types of these arguments will be inferred from a spy function usage.
//! This function does nothing and returns `()`.
//!
//! * `spy!(|n, m| a + b)` creates a spy function that can receive two
//! arguments followed by a function body but any number of arguments could be requested.
//! This syntax is pretty much the same as Rust closures. Types of arguments
//! and an output will be inferred from a spy function usage.
//!
//! * `spy!(|n: u8, m: u8| -> u8 { return n + m; })` creates spy function
//! with type annotations both for arguments and for an output.
//!

use std::sync::mpsc::Receiver;

/// Spy object that tracks calls of associated spy function.
pub struct Spy<Args> {
    pub calls_recv: Receiver<Args>,
}

impl<Args: PartialEq> Spy<Args> {
    /// It takes a snapshot of a spy object. Taken snapshot
    /// contains all the calls starting from previous snapshot.
    pub fn snapshot(&self) -> SpySnapshot<Args> {
        let mut calls: Vec<Args> = vec![];
        loop {
            match self
                .calls_recv
                .recv_timeout(::std::time::Duration::from_millis(0))
            {
                Ok(args) => calls.push(args),
                Err(_) => {
                    break;
                }
            }
        }
        SpySnapshot { calls }
    }
}

/// The structure represents a snapshot of a spy object. Taken snapshot
/// contains all the calls starting from the moment when `Spy` object was created
/// or previous snapshot if there was taken one.
///
/// Generic type `Args` is in fact a tuple that describes argument values for each
/// call.
pub struct SpySnapshot<Args: PartialEq> {
    calls: Vec<Args>,
}

impl<Args: PartialEq> SpySnapshot<Args> {
    /// It returns `true` if spy function was called at least once and `false` otherwise.
    pub fn called(&self) -> bool {
        !self.calls.is_empty()
    }

    /// It returns `true` if spy function was called at least once
    /// with provided arguments and `false` otherwise.
    pub fn called_with(&self, args: Args) -> bool {
        for call in &self.calls {
            if &args == call {
                return true;
            }
        }
        false
    }

    /// It returns `true` if spy function was called with provided arguments each time
    /// it was called.
    pub fn each_called_with(&self, args: Args) -> bool {
        for call in &self.calls {
            if &args != call {
                return false;
            }
        }
        true
    }

    /// It returns how many times spy function was called.
    pub fn num_of_calls(&self) -> usize {
        self.calls.len()
    }

    /// It returns a vector that contains all calls arguments.
    pub fn all_calls(&self) -> &Vec<Args> {
        &self.calls
    }

    /// It returns first call arguments. `None` will be returned if spy function was not
    /// called till the moment when a snapshot was taken.
    pub fn first_call(&self) -> Option<&Args> {
        self.calls.first()
    }

    /// It returns last call arguments. `None` will be returned if spy function was not
    /// called till the moment when a snapshot was taken.
    pub fn last_call(&self) -> Option<&Args> {
        self.calls.last()
    }

    /// It returns n-th call arguments. `None` will be returned if spy function was not
    /// called enough times till the moment when a snapshot was taken.
    pub fn nth_call(&self, n: usize) -> Option<&Args> {
        self.calls.get(n)
    }
}

/// The macro that creates a pair of a `Spy` object and a spy function tracked by returned
/// spy.
///
/// ```rust
/// use spy::{spy, Spy};
///
/// /// spy function that takes no argument and returns no value
/// let (spy_fn, spy) = spy!();
///
/// spy_fn();
///
/// /// spy function that takes one argument argument and returns no value.
/// let (spy_fn, spy) = spy!(|n|);
///
/// spy_fn(42);
///
/// /// spy function that takes one argument argument and returns some value
/// /// evaluated basing on taken argument.
/// let (spy_fn, spy) = spy!(|n| n % 2 == 0);
///
/// spy_fn(42);
/// ```
#[macro_export]
macro_rules! spy {
    () => {
        {
            let (s, recv) = ::std::sync::mpsc::channel();
            let spy_fn = move || {
                s.send(())
                    .expect("Problem with call agregation: cannot send call arguments to channel");
            };
            (spy_fn, Spy{ calls_recv: recv })
        }
    };
    (|$arg:ident|) => {
        {
            let (s, recv) = ::std::sync::mpsc::channel();
            let spy_fn = move |$arg| {
                s.send($arg)
                    .expect("Problem with call agregation: cannot send call arguments to channel");
            };
            (spy_fn, Spy{ calls_recv: recv })
        }
    };
    (|$($arg:ident),*|) => {
        {
            let (s, recv) = ::std::sync::mpsc::channel();
            let spy_fn = move |$($arg),*| {
                let args_tuple = ($($arg,) *);
                s.send(args_tuple)
                    .expect("Problem with call agregation: cannot send call arguments to channel");
            };
            (spy_fn, Spy{ calls_recv: recv })
        }
    };
    (|$arg:ident| $expression:expr) => {
        {
            let (s, recv) = ::std::sync::mpsc::channel();

            let spy_fn = move |$arg| {
                s.send($arg)
                    .expect("Problem with call agregation: cannot send call arguments to channel");
                $expression
            };
            (spy_fn, Spy{ calls_recv: recv })
        }
    };
    (|$($arg:ident),*| $expression:expr) => {
        {
            let (s, recv) = ::std::sync::mpsc::channel();

            let spy_fn = move |$($arg),*| {
                let args_tuple = ($($arg,) *);
                s.send(args_tuple)
                    .expect("Problem with call agregation: cannot send call arguments to channel");
                $expression
            };
            (spy_fn, Spy{ calls_recv: recv })
        }
    };
    (|$($arg:ident : $arg_type:ty),*| $(-> $return_type:ty)* $expression:block) => {
        {
            let (s, recv) = ::std::sync::mpsc::channel();

            let spy_fn = move |$($arg : $arg_type),*| $(-> $return_type)* {
                let args_tuple = ($($arg,) *);
                s.send(args_tuple)
                    .expect("Problem with call agregation: cannot send call arguments to channel");
                $expression
            };
            (spy_fn, Spy{ calls_recv: recv })
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    fn no_args_cb<F>(cb: F)
    where
        F: Fn() + Sized,
    {
        // 3 times call
        cb();
        cb();
        cb();
    }

    #[test]
    fn create_spy_test() {
        let (spy_fn, spy) = spy!();

        no_args_cb(spy_fn);
        let snapshot = spy.snapshot();

        assert!(snapshot.called(), "should be called");
        assert!(
            snapshot.called_with(()),
            "should be called with () at least once"
        );
        assert!(
            snapshot.each_called_with(()),
            "should be called with () each time"
        );
        assert_eq!(snapshot.num_of_calls(), 3, "should be called 3 times");
        assert_eq!(snapshot.all_calls(), &vec![(), (), ()]);
        assert_eq!(snapshot.first_call().expect("should be Some"), &());
        assert_eq!(snapshot.last_call().expect("should be Some"), &());
        assert_eq!(snapshot.nth_call(1).expect("should be Some"), &());
    }

    #[test]
    fn create_spy_with_args_test() {
        let (spy_fn, spy) = spy!(|n|);

        spy_fn(1u8);
        spy_fn(2u8);

        let snapshot = spy.snapshot();

        assert!(snapshot.called(), "should be called");

        assert!(
            snapshot.called_with(1u8),
            "should be called with &1u8 at least once"
        );
        assert!(
            !snapshot.each_called_with(1u8),
            "should be called with different arguments"
        );
        assert_eq!(snapshot.num_of_calls(), 2, "should be called 3 times");
        assert_eq!(snapshot.all_calls(), &vec![1u8, 2u8]);
        assert_eq!(snapshot.first_call().expect("should be Some"), &1u8);
        assert_eq!(snapshot.last_call().expect("should be Some"), &2u8);
        assert_eq!(snapshot.nth_call(1).expect("should be Some"), &2u8);
    }

    #[test]
    fn create_spy_with_many_args_test() {
        let (spy_fn, spy) = spy!(|n, s|);

        spy_fn(1u8, "first");
        spy_fn(2u8, "second");

        let snapshot = spy.snapshot();

        assert!(snapshot.called(), "should be called");

        assert!(
            snapshot.called_with((1u8, "first")),
            "should be called with &1u8 at least once"
        );
        assert!(
            !snapshot.each_called_with((1u8, "first")),
            "should be called with different arguments"
        );
        assert_eq!(snapshot.num_of_calls(), 2, "should be called 3 times");
        assert_eq!(snapshot.all_calls(), &vec![(1u8, "first"), (2u8, "second")]);
        assert_eq!(
            snapshot.first_call().expect("should be Some"),
            &(1u8, "first")
        );
        assert_eq!(
            snapshot.last_call().expect("should be Some"),
            &(2u8, "second")
        );
        assert_eq!(
            snapshot.nth_call(1).expect("should be Some"),
            &(2u8, "second")
        );
    }

    #[test]
    fn create_spy_with_args_and_return_test() {
        let (spy_fn, spy) = spy!(|n| n % 2 == 0);

        assert!(spy_fn(2), "should return true for an even number");
        assert!(!spy_fn(3), "should return false for an odd number");

        let snapshot = spy.snapshot();

        assert!(snapshot.called(), "should be called");
        assert!(
            snapshot.called_with(2),
            "should be called with 2 at least once"
        );
        assert!(
            !snapshot.each_called_with(2),
            "should be called with different arguments"
        );
        assert_eq!(snapshot.all_calls(), &vec![2, 3]);
        assert_eq!(snapshot.first_call().expect("should be Some"), &2);
        assert_eq!(snapshot.last_call().expect("should be Some"), &3);
        assert_eq!(snapshot.nth_call(1).expect("should be Some"), &3);
    }

    #[test]
    fn create_spy_with_many_args_and_return_test() {
        let (spy_fn, spy) = spy!(|n, m| n + m);

        assert_eq!(spy_fn(2u8, 1u8), 3u8, "should return 3");
        assert_eq!(spy_fn(3u8, 1u8), 4u8, "should return 4");

        let snapshot = spy.snapshot();

        assert!(snapshot.called(), "should be called");
        assert!(
            snapshot.called_with((2u8, 1u8)),
            "should be called with 2 at least once"
        );
        assert!(
            !snapshot.each_called_with((2u8, 1u8)),
            "should be called with different arguments"
        );
        assert_eq!(snapshot.all_calls(), &vec![(2, 1), (3, 1)]);
        assert_eq!(snapshot.first_call().expect("should be Some"), &(2, 1));
        assert_eq!(snapshot.last_call().expect("should be Some"), &(3, 1));
        assert_eq!(snapshot.nth_call(1).expect("should be Some"), &(3, 1));
    }

    #[test]
    fn create_spy_type_annotations() {
        let (spy_fn, spy) = spy!(|n: u8, m: u8| -> u8 { n + m });

        assert_eq!(spy_fn(2, 1), 3, "should return 3");
        assert_eq!(spy_fn(3, 1), 4, "should return 4");

        let snapshot = spy.snapshot();

        assert!(snapshot.called(), "should be called");
        assert!(
            snapshot.called_with((2, 1)),
            "should be called with 2 at least once"
        );
        assert!(
            !snapshot.each_called_with((2, 1)),
            "should be called with different arguments"
        );
        assert_eq!(snapshot.all_calls(), &vec![(2, 1), (3, 1)]);
        assert_eq!(snapshot.first_call().expect("should be Some"), &(2, 1));
        assert_eq!(snapshot.last_call().expect("should be Some"), &(3, 1));
        assert_eq!(snapshot.nth_call(1).expect("should be Some"), &(3, 1));
    }
}
