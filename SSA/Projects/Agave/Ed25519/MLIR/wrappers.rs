
// Appended observation wrappers; preceding pinned crate source is unmodified.
#[unsafe(no_mangle)]
pub fn agave_ed25519_verify(pk: &[u8;32], sig: &[u8;64], msg: &[u8]) -> bool {
    let Ok(vk) = ed_sigs::VerificationKey::try_from(*pk) else { return false; };
    vk.verify_dalek(&ed_sigs::Signature::from_bytes(sig), msg).is_ok()
}
#[unsafe(no_mangle)]
pub fn agave_serial_double_base(a: &Scalar, p: &EdwardsPoint, b: &Scalar) -> EdwardsPoint {
    backend::serial::scalar_mul::vartime_double_base::mul(a,p,b)
}
#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe fn agave_avx2_double_base(a: &Scalar, p: &EdwardsPoint, b: &Scalar) -> EdwardsPoint {
    backend::vector::scalar_mul::vartime_double_base::spec_avx2::mul(a,p,b)
}
#[unsafe(no_mangle)]
pub fn agave_serial_field_mul(a: &backend::serial::u64::field::FieldElement51, b: &backend::serial::u64::field::FieldElement51) -> backend::serial::u64::field::FieldElement51 { a*b }
#[unsafe(no_mangle)]
pub fn agave_serial_field_square(a: &backend::serial::u64::field::FieldElement51) -> backend::serial::u64::field::FieldElement51 { a.square() }
#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe fn agave_avx2_field_mul(a: &backend::vector::avx2::field::FieldElement2625x4, b: &backend::vector::avx2::field::FieldElement2625x4) -> backend::vector::avx2::field::FieldElement2625x4 { a*b }
#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe fn agave_avx2_field_square_negate_d(a: &backend::vector::avx2::field::FieldElement2625x4) -> backend::vector::avx2::field::FieldElement2625x4 { a.square_and_negate_D() }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe fn agave_avx2_field_reduce(a: &backend::vector::avx2::field::FieldElement2625x4) -> backend::vector::avx2::field::FieldElement2625x4 { a.reduce() }
#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe fn agave_avx2_field_new(a: &backend::serial::u64::field::FieldElement51,b: &backend::serial::u64::field::FieldElement51,c: &backend::serial::u64::field::FieldElement51,d: &backend::serial::u64::field::FieldElement51) -> backend::vector::avx2::field::FieldElement2625x4 { backend::vector::avx2::field::FieldElement2625x4::new(a,b,c,d) }
#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe fn agave_avx2_field_split(a: &backend::vector::avx2::field::FieldElement2625x4) -> [backend::serial::u64::field::FieldElement51;4] { a.split() }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_reduce_observe_0(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i {
    backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).reduce().0[0].into()
}

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_reduce_observe_1(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i {
    backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).reduce().0[1].into()
}

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_reduce_observe_2(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i {
    backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).reduce().0[2].into()
}

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_reduce_observe_3(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i {
    backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).reduce().0[3].into()
}

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_reduce_observe_4(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i {
    backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).reduce().0[4].into()
}

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_square_negate_d_observe_0(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).square_and_negate_D().0[0].into() }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_square_negate_d_observe_1(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).square_and_negate_D().0[1].into() }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_square_negate_d_observe_2(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).square_and_negate_D().0[2].into() }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_square_negate_d_observe_3(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).square_and_negate_D().0[3].into() }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_square_negate_d_observe_4(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).square_and_negate_D().0[4].into() }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_mul_observe_0(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]) * &backend::vector::avx2::field::FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()])).0[0].into() }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_mul_observe_1(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]) * &backend::vector::avx2::field::FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()])).0[1].into() }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_mul_observe_2(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]) * &backend::vector::avx2::field::FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()])).0[2].into() }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_mul_observe_3(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]) * &backend::vector::avx2::field::FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()])).0[3].into() }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_mul_observe_4(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i,v5: core::arch::x86_64::__m256i,v6: core::arch::x86_64::__m256i,v7: core::arch::x86_64::__m256i,v8: core::arch::x86_64::__m256i,v9: core::arch::x86_64::__m256i) -> core::arch::x86_64::__m256i { (&backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]) * &backend::vector::avx2::field::FieldElement2625x4([v5.into(),v6.into(),v7.into(),v8.into(),v9.into()])).0[4].into() }

#[unsafe(no_mangle)]
pub fn agave_serial_point_double(p: &backend::serial::curve_models::ProjectivePoint) -> backend::serial::curve_models::CompletedPoint { p.double() }
#[unsafe(no_mangle)]
pub fn agave_serial_point_cached_add(p: &EdwardsPoint, q: &backend::serial::curve_models::ProjectiveNielsPoint) -> backend::serial::curve_models::CompletedPoint { p+q }
#[unsafe(no_mangle)]
pub fn agave_serial_point_cached_sub(p: &EdwardsPoint, q: &backend::serial::curve_models::ProjectiveNielsPoint) -> backend::serial::curve_models::CompletedPoint { p-q }
#[unsafe(no_mangle)]
pub fn agave_serial_point_affine_add(p: &EdwardsPoint, q: &backend::serial::curve_models::AffineNielsPoint) -> backend::serial::curve_models::CompletedPoint { p+q }
#[unsafe(no_mangle)]
pub fn agave_serial_point_affine_sub(p: &EdwardsPoint, q: &backend::serial::curve_models::AffineNielsPoint) -> backend::serial::curve_models::CompletedPoint { p-q }
#[unsafe(no_mangle)]
pub fn agave_point_compress(p: &EdwardsPoint) -> [u8;32] { p.compress().0 }
#[unsafe(no_mangle)]
pub fn agave_scalar_naf5(a: &Scalar) -> [i8;256] { a.non_adjacent_form(5) }
#[unsafe(no_mangle)]
pub fn agave_scalar_naf8(a: &Scalar) -> [i8;256] { a.non_adjacent_form(8) }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_mul_observe_0(v0: u64,v1: u64,v2: u64,v3: u64,v4: u64,v5: u64,v6: u64,v7: u64,v8: u64,v9: u64) -> u64 { (&backend::serial::u64::field::FieldElement51([v0,v1,v2,v3,v4]) * &backend::serial::u64::field::FieldElement51([v5,v6,v7,v8,v9])).0[0] }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_mul_observe_1(v0: u64,v1: u64,v2: u64,v3: u64,v4: u64,v5: u64,v6: u64,v7: u64,v8: u64,v9: u64) -> u64 { (&backend::serial::u64::field::FieldElement51([v0,v1,v2,v3,v4]) * &backend::serial::u64::field::FieldElement51([v5,v6,v7,v8,v9])).0[1] }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_mul_observe_2(v0: u64,v1: u64,v2: u64,v3: u64,v4: u64,v5: u64,v6: u64,v7: u64,v8: u64,v9: u64) -> u64 { (&backend::serial::u64::field::FieldElement51([v0,v1,v2,v3,v4]) * &backend::serial::u64::field::FieldElement51([v5,v6,v7,v8,v9])).0[2] }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_mul_observe_3(v0: u64,v1: u64,v2: u64,v3: u64,v4: u64,v5: u64,v6: u64,v7: u64,v8: u64,v9: u64) -> u64 { (&backend::serial::u64::field::FieldElement51([v0,v1,v2,v3,v4]) * &backend::serial::u64::field::FieldElement51([v5,v6,v7,v8,v9])).0[3] }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_mul_observe_4(v0: u64,v1: u64,v2: u64,v3: u64,v4: u64,v5: u64,v6: u64,v7: u64,v8: u64,v9: u64) -> u64 { (&backend::serial::u64::field::FieldElement51([v0,v1,v2,v3,v4]) * &backend::serial::u64::field::FieldElement51([v5,v6,v7,v8,v9])).0[4] }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_from_bytes_observe_0(w0: u64,w1: u64,w2: u64,w3: u64) -> u64 { let mut bytes = [0u8;32]; bytes[0..8].copy_from_slice(&w0.to_le_bytes());bytes[8..16].copy_from_slice(&w1.to_le_bytes());bytes[16..24].copy_from_slice(&w2.to_le_bytes());bytes[24..32].copy_from_slice(&w3.to_le_bytes()); backend::serial::u64::field::FieldElement51::from_bytes(&bytes).0[0] }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_from_bytes_observe_1(w0: u64,w1: u64,w2: u64,w3: u64) -> u64 { let mut bytes = [0u8;32]; bytes[0..8].copy_from_slice(&w0.to_le_bytes());bytes[8..16].copy_from_slice(&w1.to_le_bytes());bytes[16..24].copy_from_slice(&w2.to_le_bytes());bytes[24..32].copy_from_slice(&w3.to_le_bytes()); backend::serial::u64::field::FieldElement51::from_bytes(&bytes).0[1] }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_from_bytes_observe_2(w0: u64,w1: u64,w2: u64,w3: u64) -> u64 { let mut bytes = [0u8;32]; bytes[0..8].copy_from_slice(&w0.to_le_bytes());bytes[8..16].copy_from_slice(&w1.to_le_bytes());bytes[16..24].copy_from_slice(&w2.to_le_bytes());bytes[24..32].copy_from_slice(&w3.to_le_bytes()); backend::serial::u64::field::FieldElement51::from_bytes(&bytes).0[2] }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_from_bytes_observe_3(w0: u64,w1: u64,w2: u64,w3: u64) -> u64 { let mut bytes = [0u8;32]; bytes[0..8].copy_from_slice(&w0.to_le_bytes());bytes[8..16].copy_from_slice(&w1.to_le_bytes());bytes[16..24].copy_from_slice(&w2.to_le_bytes());bytes[24..32].copy_from_slice(&w3.to_le_bytes()); backend::serial::u64::field::FieldElement51::from_bytes(&bytes).0[3] }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_from_bytes_observe_4(w0: u64,w1: u64,w2: u64,w3: u64) -> u64 { let mut bytes = [0u8;32]; bytes[0..8].copy_from_slice(&w0.to_le_bytes());bytes[8..16].copy_from_slice(&w1.to_le_bytes());bytes[16..24].copy_from_slice(&w2.to_le_bytes());bytes[24..32].copy_from_slice(&w3.to_le_bytes()); backend::serial::u64::field::FieldElement51::from_bytes(&bytes).0[4] }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_to_bytes_observe_0(v0: u64,v1: u64,v2: u64,v3: u64,v4: u64) -> u64 { let bytes = backend::serial::u64::field::FieldElement51([v0,v1,v2,v3,v4]).to_bytes(); u64::from_le_bytes([bytes[0],bytes[1],bytes[2],bytes[3],bytes[4],bytes[5],bytes[6],bytes[7]]) }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_to_bytes_observe_1(v0: u64,v1: u64,v2: u64,v3: u64,v4: u64) -> u64 { let bytes = backend::serial::u64::field::FieldElement51([v0,v1,v2,v3,v4]).to_bytes(); u64::from_le_bytes([bytes[8],bytes[9],bytes[10],bytes[11],bytes[12],bytes[13],bytes[14],bytes[15]]) }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_to_bytes_observe_2(v0: u64,v1: u64,v2: u64,v3: u64,v4: u64) -> u64 { let bytes = backend::serial::u64::field::FieldElement51([v0,v1,v2,v3,v4]).to_bytes(); u64::from_le_bytes([bytes[16],bytes[17],bytes[18],bytes[19],bytes[20],bytes[21],bytes[22],bytes[23]]) }

#[unsafe(no_mangle)]
pub extern "C" fn agave_serial_field_to_bytes_observe_3(v0: u64,v1: u64,v2: u64,v3: u64,v4: u64) -> u64 { let bytes = backend::serial::u64::field::FieldElement51([v0,v1,v2,v3,v4]).to_bytes(); u64::from_le_bytes([bytes[24],bytes[25],bytes[26],bytes[27],bytes[28],bytes[29],bytes[30],bytes[31]]) }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_0(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[0].0[0] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_1(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[0].0[1] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_2(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[0].0[2] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_3(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[0].0[3] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_4(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[0].0[4] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_5(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[1].0[0] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_6(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[1].0[1] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_7(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[1].0[2] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_8(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[1].0[3] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_9(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[1].0[4] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_10(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[2].0[0] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_11(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[2].0[1] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_12(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[2].0[2] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_13(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[2].0[3] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_14(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[2].0[4] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_15(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[3].0[0] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_16(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[3].0[1] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_17(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[3].0[2] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_18(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[3].0[3] }

#[cfg(curve25519_backend = "simd")]
#[unsafe(no_mangle)]
#[target_feature(enable="avx2")]
pub unsafe extern "C" fn agave_avx2_field_split_observe_19(v0: core::arch::x86_64::__m256i,v1: core::arch::x86_64::__m256i,v2: core::arch::x86_64::__m256i,v3: core::arch::x86_64::__m256i,v4: core::arch::x86_64::__m256i) -> u64 { backend::vector::avx2::field::FieldElement2625x4([v0.into(),v1.into(),v2.into(),v3.into(),v4.into()]).split()[3].0[4] }
