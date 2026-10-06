
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_double_observe_0(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])).double().0.0[0].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_double_observe_1(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])).double().0.0[1].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_double_observe_2(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])).double().0.0[2].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_double_observe_3(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])).double().0.0[3].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_double_observe_4(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])).double().0.0[4].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_cached_add_observe_0(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])) + &CachedPoint(FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()]))).0.0[0].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_cached_add_observe_1(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])) + &CachedPoint(FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()]))).0.0[1].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_cached_add_observe_2(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])) + &CachedPoint(FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()]))).0.0[2].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_cached_add_observe_3(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])) + &CachedPoint(FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()]))).0.0[3].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_cached_add_observe_4(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])) + &CachedPoint(FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()]))).0.0[4].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_cached_sub_observe_0(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])) - &CachedPoint(FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()]))).0.0[0].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_cached_sub_observe_1(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])) - &CachedPoint(FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()]))).0.0[1].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_cached_sub_observe_2(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])) - &CachedPoint(FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()]))).0.0[2].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_cached_sub_observe_3(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])) - &CachedPoint(FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()]))).0.0[3].into() }

#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_point_cached_sub_observe_4(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&ExtendedPoint(FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()])) - &CachedPoint(FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()]))).0.0[4].into() }
