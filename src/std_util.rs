use alloc::string::String;

use std::sync::{Arc, Mutex};

use crate::real_time::*;
use crate::runtime::*;
use crate::*;

struct ClockCache {
    value: Mutex<OffsetDateTime>,
    precision: Precision,
}

/// A clock with optional coarse granularity.
pub struct Clock {
    utc_offset: UtcOffset,
    cache: Option<ClockCache>,
}
impl Clock {
    /// Creates a new [`Clock`] with the specified [`UtcOffset`] and (optional) cache [`Precision`] (see [`Clock::read`]).
    pub fn new(utc_offset: UtcOffset, cache_precision: Option<Precision>) -> Self {
        let mut res = Self { utc_offset, cache: None };
        if let Some(precision) = cache_precision {
            res.cache = Some(ClockCache { value: Mutex::new(res.update()), precision });
        }
        res
    }
    /// Reads the current time with the specified level of precision.
    /// If caching was enabled by [`Clock::new`], requests at or below the cache precision level will use the cached timestamp.
    /// In any other case, the real current time is fetched by [`Clock::update`] and the result is stored in the cache if caching is enabled.
    pub fn read(&self, precision: Precision) -> OffsetDateTime {
        match &self.cache {
            Some(cache) if precision <= cache.precision => *cache.value.lock().unwrap(),
            _ => self.update(),
        }
    }
    /// Reads the real world time and stores the result in the cache if caching was enabled by [`Clock::new`].
    pub fn update(&self) -> OffsetDateTime {
        let t = OffsetDateTime::now_utc().to_offset(self.utc_offset);
        if let Some(cache) = &self.cache {
            *cache.value.lock().unwrap() = t;
        }
        t
    }
}

/// A shared [`Key`] type for an asynchronous request.
#[derive(Educe)]
#[educe(Clone)]
pub struct RequestKey<C: CustomTypes<S>, S: System<C>>(Arc<Mutex<AsyncResult<Result<C::Intermediate, String>>>>);
impl<C: CustomTypes<S>, S: System<C>> RequestKey<C, S> {
    pub fn new() -> Self {
        Self(Arc::new(Mutex::new(AsyncResult::new())))
    }
    pub fn poll(&self) -> AsyncResult<Result<C::Intermediate, String>> {
        self.0.lock().unwrap().poll()
    }
}
impl<C: CustomTypes<S>, S: System<C>> Key<Result<C::Intermediate, String>> for RequestKey<C, S> {
    /// Completes the request with the given result.
    /// A value of [`Ok`] denotes a successful request, whose value will be returned to the system
    /// after conversion under [`CustomTypes::from_intermediate`].
    /// A value of [`Err`] denotes a failed request, which will be returned as an error to the runtime,
    /// subject to the caller's [`ErrorScheme`] setting.
    fn complete(self, value: Result<C::Intermediate, String>) {
        assert!(self.0.lock().unwrap().complete(value).is_ok())
    }
}

/// A shared [`Key`] type for an asynchronous command.
#[derive(Clone)]
pub struct CommandKey(Arc<Mutex<AsyncResult<Result<(), String>>>>);
impl CommandKey {
    pub fn new() -> Self {
        Self(Arc::new(Mutex::new(AsyncResult::new())))
    }
    pub fn poll(&self) -> AsyncResult<Result<(), String>> {
        self.0.lock().unwrap().poll()
    }
}
impl Key<Result<(), String>> for CommandKey {
    /// Completes the command.
    /// A value of [`Ok`] denotes a successful command.
    /// A value of [`Err`] denotes a failed command, which will be returned as an error to the runtime,
    /// subject to the caller's [`ErrorScheme`] setting.
    fn complete(self, value: Result<(), String>) {
        assert!(self.0.lock().unwrap().complete(value).is_ok())
    }
}