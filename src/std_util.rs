//! A collection of helper types which depend on the standard library.
//! 
//! Note that this module is only available with the [`std`](crate) feature flag.

use std::sync::{Arc, Mutex};

use crate::real_time::*;
use crate::runtime::*;
use crate::json::*;
use crate::vecmap::VecMap;
use crate::*;

use compact_str::CompactString;

pub struct NetsBloxContext {
    pub base_url: CompactString,
    pub client_id: CompactString,
    pub services_url: CompactString,

    pub project_name: CompactString,
    pub project_id: CompactString,
    pub role_name: CompactString,
    pub role_id: CompactString,
}
pub struct RpcRequest<C: CustomTypes<S>, S: System<C>> {
    pub service: CompactString,
    pub rpc: CompactString,
    pub args: VecMap<CompactString, Json, false>,
    pub key: AsyncKey<Result<C::Intermediate, CompactString>>,
}
pub struct ReplyEntry {
    pub expiry: OffsetDateTime,
    pub value: Option<Json>,
}

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

/// A [`Key`] type which wraps a shared [`AsyncResult`].
#[derive(Educe)]
#[educe(Clone)]
pub struct AsyncKey<T>(Arc<Mutex<AsyncResult<T>>>);
impl<T> AsyncKey<T> {
    /// Equivalent to [`AsyncResult::new`] to create a new shared [`AsyncResult`].
    pub fn new() -> Self {
        Self(Arc::new(Mutex::new(AsyncResult::new())))
    }
    /// Equivalent to [`AsyncResult::poll`] on the shared [`AsyncResult`].
    pub fn poll(&self) -> AsyncResult<T> {
        self.0.lock().unwrap().poll()
    }
}
impl<T> Key<T> for AsyncKey<T> {
    /// Equivalent to [`AsyncResult::complete`] on the shared [`AsyncResult`]
    fn complete(self, value: T) {
        assert!(self.0.lock().unwrap().complete(value).is_ok())
    }
}
