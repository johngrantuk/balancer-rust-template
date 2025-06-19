use std::future::{join, Future};

pub trait AwaitableTuple {
    type Output;
    fn awaitable(self) -> Self::Output;
}

macro_rules! impl_awaitable_tuple {
    ($($name:ident),*) => {
        impl<$($name),*> AwaitableTuple for ($($name),*)
        where
            $($name: Future),*
        {
            type Output = impl Future<Output = ($($name::Output),*)>;

            fn awaitable(self) -> Self::Output {
                #![allow(non_snake_case)]
                let ($($name),*) = self;
                join!($($name),*)
            }
        }
    }
}

macro_rules! impl_awaitable_array {
    ($($name:ident),*) => {

        impl<T> AwaitableTuple for [T; ${count($name)}]
        where
            T: Future,
        {
            type Output = impl Future<Output = [T::Output; ${count($name)}]>;

            fn awaitable(self) -> Self::Output {
                #![allow(non_snake_case)]
                let [$($name),*] = self;
                let tuple = ($($name),*).awaitable();
                async move {
                    let ($($name),*) = tuple.await;
                    [$($name),*]
                }
            }
        }
    }
}

macro_rules! impl_tuple_array {
    ($($name:ident),*) => {
        impl_awaitable_tuple!($($name),*);
        impl_awaitable_array!($($name),*);
    }
}

impl<A>AwaitableTuple for (A,) where A: Future {
    type Output = impl Future<Output = (A::Output, )>;
    fn awaitable(self) -> Self::Output {
        async move {
            (self.0.await, )
        }
    }
}
impl<T> AwaitableTuple for [T;1] where T:Future {
    type Output = impl Future<Output = [T::Output; 1]>;
    fn awaitable(self) -> Self::Output {
        let tuple: (T,) = self.into();
        async move {
            let (a,) = tuple.awaitable().await;
            [a]
        }
    }
}

impl_tuple_array!(A, B);
impl_tuple_array!(A, B, C);
impl_tuple_array!(A, B, C, D);
impl_tuple_array!(A, B, C, D, E);
impl_tuple_array!(A, B, C, D, E, F);
impl_tuple_array!(A, B, C, D, E, F, G);
impl_tuple_array!(A, B, C, D, E, F, G, H);
impl_tuple_array!(A, B, C, D, E, F, G, H, I);
impl_tuple_array!(A, B, C, D, E, F, G, H, I, J);
impl_tuple_array!(A, B, C, D, E, F, G, H, I, J, K);
impl_tuple_array!(A, B, C, D, E, F, G, H, I, J, K, L);
impl_tuple_array!(A, B, C, D, E, F, G, H, I, J, K, L, M);
