// Lean compiler output
// Module: Init.Data.String.Search
// Imports: public import Init.Data.String.Slice import Init.Data.Iterators.Consumers.Collect
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
lean_object* l_String_Slice_pos_x3f(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_revFind_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_revPositions(lean_object*);
uint8_t l_String_Slice_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toInt_x3f(lean_object*);
uint8_t l_String_Slice_isInt(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
lean_object* l_String_Slice_lines(lean_object*);
extern lean_object* l_Int_instInhabited;
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_splitInclusive___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_replace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_Pos_find_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pos_find_x3f___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_Pos_find_x3f___redArg___closed__0 = (const lean_object*)&l_String_Slice_Pos_find_x3f___redArg___closed__0_value;
static const lean_closure_object l_String_Slice_Pos_find_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pos_find_x3f___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_String_Slice_Pos_find_x3f___redArg___closed__1 = (const lean_object*)&l_String_Slice_Pos_find_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_find___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revFind_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revFind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revFind_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_posof(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Internal_posOfImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_findAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posOfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posOf(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_posOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revPosOfAux(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_revPosOfAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revPosOf(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_revPosOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revFindAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revFind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_findLineStart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitInclusive___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitInclusive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitInclusive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldrAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldrAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldrAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldrAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00String_anyAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00String_anyAux_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(lean_object*, uint32_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_string_contains(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Internal_containsImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_any___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_any___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_string_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_anyImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_isNat(lean_object*);
LEAN_EXPORT lean_object* l_String_isNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_toNat_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_toInt_x3f(lean_object*);
LEAN_EXPORT uint8_t l_String_isInt(lean_object*);
LEAN_EXPORT lean_object* l_String_isInt___boxed(lean_object*);
static const lean_string_object l_String_toInt_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Int expected"};
static const lean_object* l_String_toInt_x21___closed__0 = (const lean_object*)&l_String_toInt_x21___closed__0_value;
LEAN_EXPORT lean_object* l_String_toInt_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_front_x3f(lean_object*);
LEAN_EXPORT uint32_t l_String_front(lean_object*);
LEAN_EXPORT lean_object* l_String_front___boxed(lean_object*);
LEAN_EXPORT uint32_t lean_string_front(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_frontImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_back_x3f(lean_object*);
LEAN_EXPORT uint32_t l_String_back(lean_object*);
LEAN_EXPORT lean_object* l_String_back___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_lines(lean_object*);
LEAN_EXPORT lean_object* l_String_replace___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_s_3_, lean_object* v_inst_4_, lean_object* v_replacement_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_string_utf8_byte_size(v_s_3_);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v_s_3_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_7_);
v___x_9_ = l_String_Slice_replace___redArg(v_inst_1_, v_inst_2_, v___x_8_, v_inst_4_, v_replacement_5_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_String_replace(lean_object* v_00_u03c1_10_, lean_object* v_00_u03c3_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_00_u03b1_14_, lean_object* v_inst_15_, lean_object* v_s_16_, lean_object* v_pattern_17_, lean_object* v_inst_18_, lean_object* v_replacement_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_string_utf8_byte_size(v_s_16_);
v___x_22_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_22_, 0, v_s_16_);
lean_ctor_set(v___x_22_, 1, v___x_20_);
lean_ctor_set(v___x_22_, 2, v___x_21_);
v___x_23_ = l_String_Slice_replace___redArg(v_inst_13_, v_inst_15_, v___x_22_, v_inst_18_, v_replacement_19_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_String_replace___boxed(lean_object* v_00_u03c1_24_, lean_object* v_00_u03c3_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_00_u03b1_28_, lean_object* v_inst_29_, lean_object* v_s_30_, lean_object* v_pattern_31_, lean_object* v_inst_32_, lean_object* v_replacement_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_String_replace(v_00_u03c1_24_, v_00_u03c3_25_, v_inst_26_, v_inst_27_, v_00_u03b1_28_, v_inst_29_, v_s_30_, v_pattern_31_, v_inst_32_, v_replacement_33_);
lean_dec(v_pattern_31_);
lean_dec(v_inst_26_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___lam__0(lean_object* v_x_35_, lean_object* v_x_36_, lean_object* v_f_37_, lean_object* v_c_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_apply_1(v_f_37_, v_c_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___lam__1(lean_object* v___x_40_, lean_object* v_x1_41_, lean_object* v_x2_42_, lean_object* v_x3_43_){
_start:
{
if (lean_obj_tag(v_x1_41_) == 0)
{
lean_object* v___x_44_; 
v___x_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_40_);
return v___x_44_;
}
else
{
lean_object* v_startPos_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v___x_40_);
v_startPos_45_ = lean_ctor_get(v_x1_41_, 0);
lean_inc(v_startPos_45_);
v___x_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_46_, 0, v_startPos_45_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___lam__1___boxed(lean_object* v___x_48_, lean_object* v_x1_49_, lean_object* v_x2_50_, lean_object* v_x3_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_String_Slice_Pos_find_x3f___redArg___lam__1(v___x_48_, v_x1_49_, v_x2_50_, v_x3_51_);
lean_dec(v_x3_51_);
lean_dec_ref(v_x1_49_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg(lean_object* v_inst_56_, lean_object* v_s_57_, lean_object* v_pos_58_, lean_object* v_inst_59_){
_start:
{
lean_object* v_str_60_; lean_object* v_startInclusive_61_; lean_object* v_endExclusive_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_84_; 
v_str_60_ = lean_ctor_get(v_s_57_, 0);
v_startInclusive_61_ = lean_ctor_get(v_s_57_, 1);
v_endExclusive_62_ = lean_ctor_get(v_s_57_, 2);
v_isSharedCheck_84_ = !lean_is_exclusive(v_s_57_);
if (v_isSharedCheck_84_ == 0)
{
v___x_64_ = v_s_57_;
v_isShared_65_ = v_isSharedCheck_84_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_endExclusive_62_);
lean_inc(v_startInclusive_61_);
lean_inc(v_str_60_);
lean_dec(v_s_57_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_84_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___f_66_; lean_object* v___x_67_; lean_object* v___x_69_; 
v___f_66_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_67_ = lean_nat_add(v_startInclusive_61_, v_pos_58_);
lean_dec(v_startInclusive_61_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v___x_67_);
v___x_69_ = v___x_64_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_str_60_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_67_);
lean_ctor_set(v_reuseFailAlloc_83_, 2, v_endExclusive_62_);
v___x_69_ = v_reuseFailAlloc_83_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v_searcher_70_; lean_object* v___x_71_; lean_object* v___f_72_; lean_object* v___x_73_; 
lean_inc_ref(v___x_69_);
v_searcher_70_ = lean_apply_1(v_inst_59_, v___x_69_);
v___x_71_ = lean_box(0);
v___f_72_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_73_ = lean_apply_7(v_inst_56_, v___x_69_, v___f_66_, lean_box(0), lean_box(0), v_searcher_70_, v___x_71_, v___f_72_);
if (lean_obj_tag(v___x_73_) == 0)
{
return v___x_73_;
}
else
{
lean_object* v_val_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_82_; 
v_val_74_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_82_ == 0)
{
v___x_76_ = v___x_73_;
v_isShared_77_ = v_isSharedCheck_82_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_val_74_);
lean_dec(v___x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_82_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = lean_nat_add(v_pos_58_, v_val_74_);
lean_dec(v_val_74_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v___x_78_);
v___x_80_ = v___x_76_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___redArg___boxed(lean_object* v_inst_85_, lean_object* v_s_86_, lean_object* v_pos_87_, lean_object* v_inst_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_String_Slice_Pos_find_x3f___redArg(v_inst_85_, v_s_86_, v_pos_87_, v_inst_88_);
lean_dec(v_pos_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f(lean_object* v_00_u03c1_90_, lean_object* v_00_u03c3_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_s_94_, lean_object* v_pos_95_, lean_object* v_pattern_96_, lean_object* v_inst_97_){
_start:
{
lean_object* v_str_98_; lean_object* v_startInclusive_99_; lean_object* v_endExclusive_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_122_; 
v_str_98_ = lean_ctor_get(v_s_94_, 0);
v_startInclusive_99_ = lean_ctor_get(v_s_94_, 1);
v_endExclusive_100_ = lean_ctor_get(v_s_94_, 2);
v_isSharedCheck_122_ = !lean_is_exclusive(v_s_94_);
if (v_isSharedCheck_122_ == 0)
{
v___x_102_ = v_s_94_;
v_isShared_103_ = v_isSharedCheck_122_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_endExclusive_100_);
lean_inc(v_startInclusive_99_);
lean_inc(v_str_98_);
lean_dec(v_s_94_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_122_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v___f_104_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_105_ = lean_nat_add(v_startInclusive_99_, v_pos_95_);
lean_dec(v_startInclusive_99_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_105_);
v___x_107_ = v___x_102_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_str_98_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_121_, 2, v_endExclusive_100_);
v___x_107_ = v_reuseFailAlloc_121_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v_searcher_108_; lean_object* v___x_109_; lean_object* v___f_110_; lean_object* v___x_111_; 
lean_inc_ref(v___x_107_);
v_searcher_108_ = lean_apply_1(v_inst_97_, v___x_107_);
v___x_109_ = lean_box(0);
v___f_110_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_111_ = lean_apply_7(v_inst_93_, v___x_107_, v___f_104_, lean_box(0), lean_box(0), v_searcher_108_, v___x_109_, v___f_110_);
if (lean_obj_tag(v___x_111_) == 0)
{
return v___x_111_;
}
else
{
lean_object* v_val_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_120_; 
v_val_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_120_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_val_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_116_ = lean_nat_add(v_pos_95_, v_val_112_);
lean_dec(v_val_112_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_116_);
v___x_118_ = v___x_114_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find_x3f___boxed(lean_object* v_00_u03c1_123_, lean_object* v_00_u03c3_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_s_127_, lean_object* v_pos_128_, lean_object* v_pattern_129_, lean_object* v_inst_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_String_Slice_Pos_find_x3f(v_00_u03c1_123_, v_00_u03c3_124_, v_inst_125_, v_inst_126_, v_s_127_, v_pos_128_, v_pattern_129_, v_inst_130_);
lean_dec(v_pattern_129_);
lean_dec(v_pos_128_);
lean_dec(v_inst_125_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find___redArg(lean_object* v_inst_132_, lean_object* v_s_133_, lean_object* v_pos_134_, lean_object* v_inst_135_){
_start:
{
lean_object* v_str_136_; lean_object* v_startInclusive_137_; lean_object* v_endExclusive_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_155_; 
v_str_136_ = lean_ctor_get(v_s_133_, 0);
v_startInclusive_137_ = lean_ctor_get(v_s_133_, 1);
v_endExclusive_138_ = lean_ctor_get(v_s_133_, 2);
v_isSharedCheck_155_ = !lean_is_exclusive(v_s_133_);
if (v_isSharedCheck_155_ == 0)
{
v___x_140_ = v_s_133_;
v_isShared_141_ = v_isSharedCheck_155_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_endExclusive_138_);
lean_inc(v_startInclusive_137_);
lean_inc(v_str_136_);
lean_dec(v_s_133_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_155_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___f_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___f_142_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_143_ = lean_nat_add(v_startInclusive_137_, v_pos_134_);
lean_dec(v_startInclusive_137_);
lean_inc(v_endExclusive_138_);
lean_inc(v___x_143_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_143_);
v___x_145_ = v___x_140_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_str_136_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_endExclusive_138_);
v___x_145_ = v_reuseFailAlloc_154_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v_searcher_146_; lean_object* v___x_147_; lean_object* v___f_148_; lean_object* v___x_149_; 
lean_inc_ref(v___x_145_);
v_searcher_146_ = lean_apply_1(v_inst_135_, v___x_145_);
v___x_147_ = lean_box(0);
v___f_148_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_149_ = lean_apply_7(v_inst_132_, v___x_145_, v___f_142_, lean_box(0), lean_box(0), v_searcher_146_, v___x_147_, v___f_148_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_nat_sub(v_endExclusive_138_, v___x_143_);
lean_dec(v___x_143_);
lean_dec(v_endExclusive_138_);
v___x_151_ = lean_nat_add(v_pos_134_, v___x_150_);
lean_dec(v___x_150_);
return v___x_151_;
}
else
{
lean_object* v_val_152_; lean_object* v___x_153_; 
lean_dec(v___x_143_);
lean_dec(v_endExclusive_138_);
v_val_152_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_val_152_);
lean_dec_ref(v___x_149_);
v___x_153_ = lean_nat_add(v_pos_134_, v_val_152_);
lean_dec(v_val_152_);
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find___redArg___boxed(lean_object* v_inst_156_, lean_object* v_s_157_, lean_object* v_pos_158_, lean_object* v_inst_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_String_Slice_Pos_find___redArg(v_inst_156_, v_s_157_, v_pos_158_, v_inst_159_);
lean_dec(v_pos_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find(lean_object* v_00_u03c1_161_, lean_object* v_00_u03c3_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_s_165_, lean_object* v_pos_166_, lean_object* v_pattern_167_, lean_object* v_inst_168_){
_start:
{
lean_object* v_str_169_; lean_object* v_startInclusive_170_; lean_object* v_endExclusive_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_188_; 
v_str_169_ = lean_ctor_get(v_s_165_, 0);
v_startInclusive_170_ = lean_ctor_get(v_s_165_, 1);
v_endExclusive_171_ = lean_ctor_get(v_s_165_, 2);
v_isSharedCheck_188_ = !lean_is_exclusive(v_s_165_);
if (v_isSharedCheck_188_ == 0)
{
v___x_173_ = v_s_165_;
v_isShared_174_ = v_isSharedCheck_188_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_endExclusive_171_);
lean_inc(v_startInclusive_170_);
lean_inc(v_str_169_);
lean_dec(v_s_165_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_188_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___f_175_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_176_ = lean_nat_add(v_startInclusive_170_, v_pos_166_);
lean_dec(v_startInclusive_170_);
lean_inc(v_endExclusive_171_);
lean_inc(v___x_176_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 1, v___x_176_);
v___x_178_ = v___x_173_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_str_169_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_endExclusive_171_);
v___x_178_ = v_reuseFailAlloc_187_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v_searcher_179_; lean_object* v___x_180_; lean_object* v___f_181_; lean_object* v___x_182_; 
lean_inc_ref(v___x_178_);
v_searcher_179_ = lean_apply_1(v_inst_168_, v___x_178_);
v___x_180_ = lean_box(0);
v___f_181_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_182_ = lean_apply_7(v_inst_164_, v___x_178_, v___f_175_, lean_box(0), lean_box(0), v_searcher_179_, v___x_180_, v___f_181_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_nat_sub(v_endExclusive_171_, v___x_176_);
lean_dec(v___x_176_);
lean_dec(v_endExclusive_171_);
v___x_184_ = lean_nat_add(v_pos_166_, v___x_183_);
lean_dec(v___x_183_);
return v___x_184_;
}
else
{
lean_object* v_val_185_; lean_object* v___x_186_; 
lean_dec(v___x_176_);
lean_dec(v_endExclusive_171_);
v_val_185_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_val_185_);
lean_dec_ref(v___x_182_);
v___x_186_ = lean_nat_add(v_pos_166_, v_val_185_);
lean_dec(v_val_185_);
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_find___boxed(lean_object* v_00_u03c1_189_, lean_object* v_00_u03c3_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_s_193_, lean_object* v_pos_194_, lean_object* v_pattern_195_, lean_object* v_inst_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_String_Slice_Pos_find(v_00_u03c1_189_, v_00_u03c3_190_, v_inst_191_, v_inst_192_, v_s_193_, v_pos_194_, v_pattern_195_, v_inst_196_);
lean_dec(v_pattern_195_);
lean_dec(v_pos_194_);
lean_dec(v_inst_191_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_find_x3f___redArg(lean_object* v_inst_198_, lean_object* v_s_199_, lean_object* v_pos_200_, lean_object* v_inst_201_){
_start:
{
lean_object* v___f_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_searcher_205_; lean_object* v___x_206_; lean_object* v___f_207_; lean_object* v___x_208_; 
v___f_202_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_203_ = lean_string_utf8_byte_size(v_s_199_);
lean_inc(v_pos_200_);
v___x_204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_204_, 0, v_s_199_);
lean_ctor_set(v___x_204_, 1, v_pos_200_);
lean_ctor_set(v___x_204_, 2, v___x_203_);
lean_inc_ref(v___x_204_);
v_searcher_205_ = lean_apply_1(v_inst_201_, v___x_204_);
v___x_206_ = lean_box(0);
v___f_207_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_208_ = lean_apply_7(v_inst_198_, v___x_204_, v___f_202_, lean_box(0), lean_box(0), v_searcher_205_, v___x_206_, v___f_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_dec(v_pos_200_);
return v___x_206_;
}
else
{
lean_object* v_val_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_217_; 
v_val_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_217_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_val_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_nat_add(v_pos_200_, v_val_209_);
lean_dec(v_val_209_);
lean_dec(v_pos_200_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_213_);
v___x_215_ = v___x_211_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_find_x3f(lean_object* v_00_u03c1_218_, lean_object* v_00_u03c3_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_s_222_, lean_object* v_pos_223_, lean_object* v_pattern_224_, lean_object* v_inst_225_){
_start:
{
lean_object* v___f_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v_searcher_229_; lean_object* v___x_230_; lean_object* v___f_231_; lean_object* v___x_232_; 
v___f_226_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_227_ = lean_string_utf8_byte_size(v_s_222_);
lean_inc(v_pos_223_);
v___x_228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_228_, 0, v_s_222_);
lean_ctor_set(v___x_228_, 1, v_pos_223_);
lean_ctor_set(v___x_228_, 2, v___x_227_);
lean_inc_ref(v___x_228_);
v_searcher_229_ = lean_apply_1(v_inst_225_, v___x_228_);
v___x_230_ = lean_box(0);
v___f_231_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_232_ = lean_apply_7(v_inst_221_, v___x_228_, v___f_226_, lean_box(0), lean_box(0), v_searcher_229_, v___x_230_, v___f_231_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_dec(v_pos_223_);
return v___x_230_;
}
else
{
lean_object* v_val_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
v_val_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_241_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_val_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = lean_nat_add(v_pos_223_, v_val_233_);
lean_dec(v_val_233_);
lean_dec(v_pos_223_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_237_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_find_x3f___boxed(lean_object* v_00_u03c1_242_, lean_object* v_00_u03c3_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_s_246_, lean_object* v_pos_247_, lean_object* v_pattern_248_, lean_object* v_inst_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_String_Pos_find_x3f(v_00_u03c1_242_, v_00_u03c3_243_, v_inst_244_, v_inst_245_, v_s_246_, v_pos_247_, v_pattern_248_, v_inst_249_);
lean_dec(v_pattern_248_);
lean_dec(v_inst_244_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_find___redArg(lean_object* v_inst_251_, lean_object* v_s_252_, lean_object* v_pos_253_, lean_object* v_inst_254_){
_start:
{
lean_object* v___f_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v_searcher_258_; lean_object* v___x_259_; lean_object* v___f_260_; lean_object* v___x_261_; 
v___f_255_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_256_ = lean_string_utf8_byte_size(v_s_252_);
lean_inc(v_pos_253_);
v___x_257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_257_, 0, v_s_252_);
lean_ctor_set(v___x_257_, 1, v_pos_253_);
lean_ctor_set(v___x_257_, 2, v___x_256_);
lean_inc_ref(v___x_257_);
v_searcher_258_ = lean_apply_1(v_inst_254_, v___x_257_);
v___x_259_ = lean_box(0);
v___f_260_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_261_ = lean_apply_7(v_inst_251_, v___x_257_, v___f_255_, lean_box(0), lean_box(0), v_searcher_258_, v___x_259_, v___f_260_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_nat_sub(v___x_256_, v_pos_253_);
v___x_263_ = lean_nat_add(v_pos_253_, v___x_262_);
lean_dec(v___x_262_);
lean_dec(v_pos_253_);
return v___x_263_;
}
else
{
lean_object* v_val_264_; lean_object* v___x_265_; 
v_val_264_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_val_264_);
lean_dec_ref(v___x_261_);
v___x_265_ = lean_nat_add(v_pos_253_, v_val_264_);
lean_dec(v_val_264_);
lean_dec(v_pos_253_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_find(lean_object* v_00_u03c1_266_, lean_object* v_00_u03c3_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_s_270_, lean_object* v_pos_271_, lean_object* v_pattern_272_, lean_object* v_inst_273_){
_start:
{
lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_searcher_277_; lean_object* v___x_278_; lean_object* v___f_279_; lean_object* v___x_280_; 
v___f_274_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_275_ = lean_string_utf8_byte_size(v_s_270_);
lean_inc(v_pos_271_);
v___x_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_276_, 0, v_s_270_);
lean_ctor_set(v___x_276_, 1, v_pos_271_);
lean_ctor_set(v___x_276_, 2, v___x_275_);
lean_inc_ref(v___x_276_);
v_searcher_277_ = lean_apply_1(v_inst_273_, v___x_276_);
v___x_278_ = lean_box(0);
v___f_279_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_280_ = lean_apply_7(v_inst_269_, v___x_276_, v___f_274_, lean_box(0), lean_box(0), v_searcher_277_, v___x_278_, v___f_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_nat_sub(v___x_275_, v_pos_271_);
v___x_282_ = lean_nat_add(v_pos_271_, v___x_281_);
lean_dec(v___x_281_);
lean_dec(v_pos_271_);
return v___x_282_;
}
else
{
lean_object* v_val_283_; lean_object* v___x_284_; 
v_val_283_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_283_);
lean_dec_ref(v___x_280_);
v___x_284_ = lean_nat_add(v_pos_271_, v_val_283_);
lean_dec(v_val_283_);
lean_dec(v_pos_271_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_find___boxed(lean_object* v_00_u03c1_285_, lean_object* v_00_u03c3_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_s_289_, lean_object* v_pos_290_, lean_object* v_pattern_291_, lean_object* v_inst_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_String_Pos_find(v_00_u03c1_285_, v_00_u03c3_286_, v_inst_287_, v_inst_288_, v_s_289_, v_pos_290_, v_pattern_291_, v_inst_292_);
lean_dec(v_pattern_291_);
lean_dec(v_inst_287_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_String_find_x3f___redArg(lean_object* v_inst_294_, lean_object* v_s_295_, lean_object* v_inst_296_){
_start:
{
lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_searcher_301_; lean_object* v___x_302_; lean_object* v___f_303_; lean_object* v___x_304_; 
v___f_297_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_string_utf8_byte_size(v_s_295_);
v___x_300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_300_, 0, v_s_295_);
lean_ctor_set(v___x_300_, 1, v___x_298_);
lean_ctor_set(v___x_300_, 2, v___x_299_);
lean_inc_ref(v___x_300_);
v_searcher_301_ = lean_apply_1(v_inst_296_, v___x_300_);
v___x_302_ = lean_box(0);
v___f_303_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_304_ = lean_apply_7(v_inst_294_, v___x_300_, v___f_297_, lean_box(0), lean_box(0), v_searcher_301_, v___x_302_, v___f_303_);
if (lean_obj_tag(v___x_304_) == 0)
{
return v___x_302_;
}
else
{
lean_object* v_val_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v_val_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_val_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_val_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_find_x3f(lean_object* v_00_u03c1_313_, lean_object* v_00_u03c3_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_s_317_, lean_object* v_pattern_318_, lean_object* v_inst_319_){
_start:
{
lean_object* v___f_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_searcher_324_; lean_object* v___x_325_; lean_object* v___f_326_; lean_object* v___x_327_; 
v___f_320_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_string_utf8_byte_size(v_s_317_);
v___x_323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_323_, 0, v_s_317_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_322_);
lean_inc_ref(v___x_323_);
v_searcher_324_ = lean_apply_1(v_inst_319_, v___x_323_);
v___x_325_ = lean_box(0);
v___f_326_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_327_ = lean_apply_7(v_inst_316_, v___x_323_, v___f_320_, lean_box(0), lean_box(0), v_searcher_324_, v___x_325_, v___f_326_);
if (lean_obj_tag(v___x_327_) == 0)
{
return v___x_325_;
}
else
{
lean_object* v_val_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
v_val_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_val_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_val_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_find_x3f___boxed(lean_object* v_00_u03c1_336_, lean_object* v_00_u03c3_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_s_340_, lean_object* v_pattern_341_, lean_object* v_inst_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_String_find_x3f(v_00_u03c1_336_, v_00_u03c3_337_, v_inst_338_, v_inst_339_, v_s_340_, v_pattern_341_, v_inst_342_);
lean_dec(v_pattern_341_);
lean_dec(v_inst_338_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_String_find___redArg(lean_object* v_inst_344_, lean_object* v_s_345_, lean_object* v_inst_346_){
_start:
{
lean_object* v___f_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_searcher_351_; lean_object* v___x_352_; lean_object* v___f_353_; lean_object* v___x_354_; 
v___f_347_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_string_utf8_byte_size(v_s_345_);
v___x_350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_350_, 0, v_s_345_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
lean_ctor_set(v___x_350_, 2, v___x_349_);
lean_inc_ref(v___x_350_);
v_searcher_351_ = lean_apply_1(v_inst_346_, v___x_350_);
v___x_352_ = lean_box(0);
v___f_353_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_354_ = lean_apply_7(v_inst_344_, v___x_350_, v___f_347_, lean_box(0), lean_box(0), v_searcher_351_, v___x_352_, v___f_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
return v___x_349_;
}
else
{
lean_object* v_val_355_; 
v_val_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_val_355_);
lean_dec_ref(v___x_354_);
return v_val_355_;
}
}
}
LEAN_EXPORT lean_object* l_String_find(lean_object* v_00_u03c1_356_, lean_object* v_00_u03c3_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_s_360_, lean_object* v_pattern_361_, lean_object* v_inst_362_){
_start:
{
lean_object* v___f_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_searcher_367_; lean_object* v___x_368_; lean_object* v___f_369_; lean_object* v___x_370_; 
v___f_363_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__0));
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_string_utf8_byte_size(v_s_360_);
v___x_366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_366_, 0, v_s_360_);
lean_ctor_set(v___x_366_, 1, v___x_364_);
lean_ctor_set(v___x_366_, 2, v___x_365_);
lean_inc_ref(v___x_366_);
v_searcher_367_ = lean_apply_1(v_inst_362_, v___x_366_);
v___x_368_ = lean_box(0);
v___f_369_ = ((lean_object*)(l_String_Slice_Pos_find_x3f___redArg___closed__1));
v___x_370_ = lean_apply_7(v_inst_359_, v___x_366_, v___f_363_, lean_box(0), lean_box(0), v_searcher_367_, v___x_368_, v___f_369_);
if (lean_obj_tag(v___x_370_) == 0)
{
return v___x_365_;
}
else
{
lean_object* v_val_371_; 
v_val_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_val_371_);
lean_dec_ref(v___x_370_);
return v_val_371_;
}
}
}
LEAN_EXPORT lean_object* l_String_find___boxed(lean_object* v_00_u03c1_372_, lean_object* v_00_u03c3_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_s_376_, lean_object* v_pattern_377_, lean_object* v_inst_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_String_find(v_00_u03c1_372_, v_00_u03c3_373_, v_inst_374_, v_inst_375_, v_s_376_, v_pattern_377_, v_inst_378_);
lean_dec(v_pattern_377_);
lean_dec(v_inst_374_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f___redArg(lean_object* v_inst_380_, lean_object* v_s_381_, lean_object* v_pos_382_, lean_object* v_inst_383_){
_start:
{
lean_object* v_str_384_; lean_object* v_startInclusive_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_402_; 
v_str_384_ = lean_ctor_get(v_s_381_, 0);
v_startInclusive_385_ = lean_ctor_get(v_s_381_, 1);
v_isSharedCheck_402_ = !lean_is_exclusive(v_s_381_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; 
v_unused_403_ = lean_ctor_get(v_s_381_, 2);
lean_dec(v_unused_403_);
v___x_387_ = v_s_381_;
v_isShared_388_ = v_isSharedCheck_402_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_startInclusive_385_);
lean_inc(v_str_384_);
lean_dec(v_s_381_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_402_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = lean_nat_add(v_startInclusive_385_, v_pos_382_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 2, v___x_389_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_str_384_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_startInclusive_385_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v___x_389_);
v___x_391_ = v_reuseFailAlloc_401_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; 
v___x_392_ = l_String_Slice_revFind_x3f___redArg(v_inst_380_, v___x_391_, v_inst_383_);
if (lean_obj_tag(v___x_392_) == 0)
{
return v___x_392_;
}
else
{
lean_object* v_val_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
v_val_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_val_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_val_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f___redArg___boxed(lean_object* v_inst_404_, lean_object* v_s_405_, lean_object* v_pos_406_, lean_object* v_inst_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_String_Slice_Pos_revFind_x3f___redArg(v_inst_404_, v_s_405_, v_pos_406_, v_inst_407_);
lean_dec(v_pos_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f(lean_object* v_00_u03c1_409_, lean_object* v_00_u03c3_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_s_413_, lean_object* v_pos_414_, lean_object* v_pattern_415_, lean_object* v_inst_416_){
_start:
{
lean_object* v_str_417_; lean_object* v_startInclusive_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_435_; 
v_str_417_ = lean_ctor_get(v_s_413_, 0);
v_startInclusive_418_ = lean_ctor_get(v_s_413_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v_s_413_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; 
v_unused_436_ = lean_ctor_get(v_s_413_, 2);
lean_dec(v_unused_436_);
v___x_420_ = v_s_413_;
v_isShared_421_ = v_isSharedCheck_435_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_startInclusive_418_);
lean_inc(v_str_417_);
lean_dec(v_s_413_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_435_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = lean_nat_add(v_startInclusive_418_, v_pos_414_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 2, v___x_422_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_str_417_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_startInclusive_418_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v___x_422_);
v___x_424_ = v_reuseFailAlloc_434_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; 
v___x_425_ = l_String_Slice_revFind_x3f___redArg(v_inst_412_, v___x_424_, v_inst_416_);
if (lean_obj_tag(v___x_425_) == 0)
{
return v___x_425_;
}
else
{
lean_object* v_val_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v_val_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_val_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_val_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revFind_x3f___boxed(lean_object* v_00_u03c1_437_, lean_object* v_00_u03c3_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_s_441_, lean_object* v_pos_442_, lean_object* v_pattern_443_, lean_object* v_inst_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_String_Slice_Pos_revFind_x3f(v_00_u03c1_437_, v_00_u03c3_438_, v_inst_439_, v_inst_440_, v_s_441_, v_pos_442_, v_pattern_443_, v_inst_444_);
lean_dec(v_pattern_443_);
lean_dec(v_pos_442_);
lean_dec(v_inst_439_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f___redArg(lean_object* v_inst_446_, lean_object* v_s_447_, lean_object* v_pos_448_, lean_object* v_inst_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_451_, 0, v_s_447_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
lean_ctor_set(v___x_451_, 2, v_pos_448_);
v___x_452_ = l_String_Slice_revFind_x3f___redArg(v_inst_446_, v___x_451_, v_inst_449_);
if (lean_obj_tag(v___x_452_) == 0)
{
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v___x_453_; 
v___x_453_ = lean_box(0);
return v___x_453_;
}
else
{
lean_object* v_val_454_; lean_object* v___x_455_; 
v_val_454_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_val_454_);
lean_dec_ref(v___x_452_);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v_val_454_);
return v___x_455_;
}
}
else
{
lean_object* v_val_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_val_456_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_452_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_val_456_);
lean_dec(v___x_452_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_val_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f(lean_object* v_00_u03c1_464_, lean_object* v_00_u03c3_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_s_468_, lean_object* v_pos_469_, lean_object* v_pattern_470_, lean_object* v_inst_471_){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_473_, 0, v_s_468_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
lean_ctor_set(v___x_473_, 2, v_pos_469_);
v___x_474_ = l_String_Slice_revFind_x3f___redArg(v_inst_467_, v___x_473_, v_inst_471_);
if (lean_obj_tag(v___x_474_) == 0)
{
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v___x_475_; 
v___x_475_ = lean_box(0);
return v___x_475_;
}
else
{
lean_object* v_val_476_; lean_object* v___x_477_; 
v_val_476_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_476_);
lean_dec_ref(v___x_474_);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_val_476_);
return v___x_477_;
}
}
else
{
lean_object* v_val_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
v_val_478_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_474_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_val_478_);
lean_dec(v___x_474_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_val_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revFind_x3f___boxed(lean_object* v_00_u03c1_486_, lean_object* v_00_u03c3_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_s_490_, lean_object* v_pos_491_, lean_object* v_pattern_492_, lean_object* v_inst_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_String_Pos_revFind_x3f(v_00_u03c1_486_, v_00_u03c3_487_, v_inst_488_, v_inst_489_, v_s_490_, v_pos_491_, v_pattern_492_, v_inst_493_);
lean_dec(v_pattern_492_);
lean_dec(v_inst_488_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_String_revFind_x3f___redArg(lean_object* v_inst_495_, lean_object* v_s_496_, lean_object* v_inst_497_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_string_utf8_byte_size(v_s_496_);
v___x_500_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_500_, 0, v_s_496_);
lean_ctor_set(v___x_500_, 1, v___x_498_);
lean_ctor_set(v___x_500_, 2, v___x_499_);
v___x_501_ = l_String_Slice_revFind_x3f___redArg(v_inst_495_, v___x_500_, v_inst_497_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_box(0);
return v___x_502_;
}
else
{
lean_object* v_val_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
v_val_503_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_501_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_val_503_);
lean_dec(v___x_501_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_val_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_revFind_x3f(lean_object* v_00_u03c1_511_, lean_object* v_00_u03c3_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_s_515_, lean_object* v_pattern_516_, lean_object* v_inst_517_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_string_utf8_byte_size(v_s_515_);
v___x_520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_520_, 0, v_s_515_);
lean_ctor_set(v___x_520_, 1, v___x_518_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
v___x_521_ = l_String_Slice_revFind_x3f___redArg(v_inst_514_, v___x_520_, v_inst_517_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v___x_522_; 
v___x_522_ = lean_box(0);
return v___x_522_;
}
else
{
lean_object* v_val_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_val_523_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_521_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_val_523_);
lean_dec(v___x_521_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_val_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_revFind_x3f___boxed(lean_object* v_00_u03c1_531_, lean_object* v_00_u03c3_532_, lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_s_535_, lean_object* v_pattern_536_, lean_object* v_inst_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_String_revFind_x3f(v_00_u03c1_531_, v_00_u03c3_532_, v_inst_533_, v_inst_534_, v_s_535_, v_pattern_536_, v_inst_537_);
lean_dec(v_pattern_536_);
lean_dec(v_inst_533_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(lean_object* v___x_539_, lean_object* v_s_540_, uint32_t v_c_541_, lean_object* v_a_542_, lean_object* v_b_543_){
_start:
{
lean_object* v_startInclusive_544_; lean_object* v_endExclusive_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_startInclusive_544_ = lean_ctor_get(v___x_539_, 1);
v_endExclusive_545_ = lean_ctor_get(v___x_539_, 2);
v___x_546_ = lean_nat_sub(v_endExclusive_545_, v_startInclusive_544_);
v___x_547_ = lean_nat_dec_eq(v_a_542_, v___x_546_);
lean_dec(v___x_546_);
if (v___x_547_ == 0)
{
uint32_t v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_string_utf8_get_fast(v_s_540_, v_a_542_);
v___x_549_ = lean_uint32_dec_eq(v___x_548_, v_c_541_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_box(0);
v___x_551_ = lean_string_utf8_next_fast(v_s_540_, v_a_542_);
lean_dec(v_a_542_);
v_a_542_ = v___x_551_;
v_b_543_ = v___x_550_;
goto _start;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v_a_542_);
return v___x_553_;
}
}
else
{
lean_dec(v_a_542_);
lean_inc(v_b_543_);
return v_b_543_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg___boxed(lean_object* v___x_554_, lean_object* v_s_555_, lean_object* v_c_556_, lean_object* v_a_557_, lean_object* v_b_558_){
_start:
{
uint32_t v_c_boxed_559_; lean_object* v_res_560_; 
v_c_boxed_559_ = lean_unbox_uint32(v_c_556_);
lean_dec(v_c_556_);
v_res_560_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(v___x_554_, v_s_555_, v_c_boxed_559_, v_a_557_, v_b_558_);
lean_dec(v_b_558_);
lean_dec_ref(v_s_555_);
lean_dec_ref(v___x_554_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* lean_string_posof(lean_object* v_s_561_, uint32_t v_c_562_){
_start:
{
lean_object* v_searcher_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_searcher_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_string_utf8_byte_size(v_s_561_);
lean_inc_ref(v_s_561_);
v___x_565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_565_, 0, v_s_561_);
lean_ctor_set(v___x_565_, 1, v_searcher_563_);
lean_ctor_set(v___x_565_, 2, v___x_564_);
v___x_566_ = lean_box(0);
v___x_567_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(v___x_565_, v_s_561_, v_c_562_, v_searcher_563_, v___x_566_);
lean_dec_ref(v_s_561_);
lean_dec_ref(v___x_565_);
if (lean_obj_tag(v___x_567_) == 0)
{
return v___x_564_;
}
else
{
lean_object* v_val_568_; 
v_val_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_val_568_);
lean_dec_ref(v___x_567_);
return v_val_568_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_posOfImpl___boxed(lean_object* v_s_569_, lean_object* v_c_570_){
_start:
{
uint32_t v_c_boxed_571_; lean_object* v_res_572_; 
v_c_boxed_571_ = lean_unbox_uint32(v_c_570_);
lean_dec(v_c_570_);
v_res_572_ = lean_string_posof(v_s_569_, v_c_boxed_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0(lean_object* v___x_573_, lean_object* v_s_574_, uint32_t v_c_575_, lean_object* v_inst_576_, lean_object* v_R_577_, lean_object* v_a_578_, lean_object* v_b_579_, lean_object* v_c_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(v___x_573_, v_s_574_, v_c_575_, v_a_578_, v_b_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___boxed(lean_object* v___x_582_, lean_object* v_s_583_, lean_object* v_c_584_, lean_object* v_inst_585_, lean_object* v_R_586_, lean_object* v_a_587_, lean_object* v_b_588_, lean_object* v_c_589_){
_start:
{
uint32_t v_c_boxed_590_; lean_object* v_res_591_; 
v_c_boxed_590_ = lean_unbox_uint32(v_c_584_);
lean_dec(v_c_584_);
v_res_591_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0(v___x_582_, v_s_583_, v_c_boxed_590_, v_inst_585_, v_R_586_, v_a_587_, v_b_588_, v_c_589_);
lean_dec(v_b_588_);
lean_dec_ref(v_s_583_);
lean_dec_ref(v___x_582_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg(lean_object* v___x_592_, lean_object* v_pos_593_, lean_object* v_s_594_, lean_object* v_p_595_, lean_object* v_a_596_, lean_object* v_b_597_){
_start:
{
lean_object* v_startInclusive_598_; lean_object* v_endExclusive_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_startInclusive_598_ = lean_ctor_get(v___x_592_, 1);
v_endExclusive_599_ = lean_ctor_get(v___x_592_, 2);
v___x_600_ = lean_nat_sub(v_endExclusive_599_, v_startInclusive_598_);
v___x_601_ = lean_nat_dec_eq(v_a_596_, v___x_600_);
lean_dec(v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; uint32_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_602_ = lean_nat_add(v_pos_593_, v_a_596_);
v___x_603_ = lean_string_utf8_get_fast(v_s_594_, v___x_602_);
v___x_604_ = lean_box_uint32(v___x_603_);
lean_inc_ref(v_p_595_);
v___x_605_ = lean_apply_1(v_p_595_, v___x_604_);
v___x_606_ = lean_unbox(v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v_a_596_);
v___x_607_ = lean_box(0);
v___x_608_ = lean_string_utf8_next_fast(v_s_594_, v___x_602_);
lean_dec(v___x_602_);
v___x_609_ = lean_nat_sub(v___x_608_, v_pos_593_);
v_a_596_ = v___x_609_;
v_b_597_ = v___x_607_;
goto _start;
}
else
{
lean_object* v___x_611_; 
lean_dec(v___x_602_);
lean_dec_ref(v_p_595_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v_a_596_);
return v___x_611_;
}
}
else
{
lean_dec(v_a_596_);
lean_dec_ref(v_p_595_);
lean_inc(v_b_597_);
return v_b_597_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg___boxed(lean_object* v___x_612_, lean_object* v_pos_613_, lean_object* v_s_614_, lean_object* v_p_615_, lean_object* v_a_616_, lean_object* v_b_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg(v___x_612_, v_pos_613_, v_s_614_, v_p_615_, v_a_616_, v_b_617_);
lean_dec(v_b_617_);
lean_dec_ref(v_s_614_);
lean_dec(v_pos_613_);
lean_dec_ref(v___x_612_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_String_findAux(lean_object* v_s_619_, lean_object* v_p_620_, lean_object* v_stopPos_621_, lean_object* v_pos_622_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_nat_dec_le(v_pos_622_, v_stopPos_621_);
if (v___x_623_ == 0)
{
lean_dec(v_pos_622_);
lean_dec_ref(v_p_620_);
lean_dec_ref(v_s_619_);
return v_stopPos_621_;
}
else
{
uint8_t v___x_624_; 
v___x_624_ = lean_string_is_valid_pos(v_s_619_, v_pos_622_);
if (v___x_624_ == 0)
{
lean_dec(v_pos_622_);
lean_dec_ref(v_p_620_);
lean_dec_ref(v_s_619_);
return v_stopPos_621_;
}
else
{
uint8_t v___x_625_; 
v___x_625_ = lean_string_is_valid_pos(v_s_619_, v_stopPos_621_);
if (v___x_625_ == 0)
{
lean_dec(v_pos_622_);
lean_dec_ref(v_p_620_);
lean_dec_ref(v_s_619_);
return v_stopPos_621_;
}
else
{
lean_object* v___x_626_; lean_object* v_searcher_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_inc(v_stopPos_621_);
lean_inc(v_pos_622_);
lean_inc_ref(v_s_619_);
v___x_626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_626_, 0, v_s_619_);
lean_ctor_set(v___x_626_, 1, v_pos_622_);
lean_ctor_set(v___x_626_, 2, v_stopPos_621_);
v_searcher_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_box(0);
v___x_629_ = l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg(v___x_626_, v_pos_622_, v_s_619_, v_p_620_, v_searcher_627_, v___x_628_);
lean_dec_ref(v_s_619_);
lean_dec_ref(v___x_626_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_nat_sub(v_stopPos_621_, v_pos_622_);
lean_dec(v_stopPos_621_);
v___x_631_ = lean_nat_add(v_pos_622_, v___x_630_);
lean_dec(v___x_630_);
lean_dec(v_pos_622_);
return v___x_631_;
}
else
{
lean_object* v_val_632_; lean_object* v___x_633_; 
lean_dec(v_stopPos_621_);
v_val_632_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_val_632_);
lean_dec_ref(v___x_629_);
v___x_633_ = lean_nat_add(v_pos_622_, v_val_632_);
lean_dec(v_val_632_);
lean_dec(v_pos_622_);
return v___x_633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0(lean_object* v___x_634_, lean_object* v_pos_635_, lean_object* v_s_636_, lean_object* v_p_637_, lean_object* v_inst_638_, lean_object* v_R_639_, lean_object* v_a_640_, lean_object* v_b_641_, lean_object* v_c_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg(v___x_634_, v_pos_635_, v_s_636_, v_p_637_, v_a_640_, v_b_641_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___boxed(lean_object* v___x_644_, lean_object* v_pos_645_, lean_object* v_s_646_, lean_object* v_p_647_, lean_object* v_inst_648_, lean_object* v_R_649_, lean_object* v_a_650_, lean_object* v_b_651_, lean_object* v_c_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0(v___x_644_, v_pos_645_, v_s_646_, v_p_647_, v_inst_648_, v_R_649_, v_a_650_, v_b_651_, v_c_652_);
lean_dec(v_b_651_);
lean_dec_ref(v_s_646_);
lean_dec(v_pos_645_);
lean_dec_ref(v___x_644_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg(lean_object* v___x_654_, lean_object* v_pos_655_, lean_object* v_s_656_, uint32_t v_c_657_, lean_object* v_a_658_, lean_object* v_b_659_){
_start:
{
lean_object* v_startInclusive_660_; lean_object* v_endExclusive_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_startInclusive_660_ = lean_ctor_get(v___x_654_, 1);
v_endExclusive_661_ = lean_ctor_get(v___x_654_, 2);
v___x_662_ = lean_nat_sub(v_endExclusive_661_, v_startInclusive_660_);
v___x_663_ = lean_nat_dec_eq(v_a_658_, v___x_662_);
lean_dec(v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; uint32_t v___x_665_; uint8_t v___x_666_; 
v___x_664_ = lean_nat_add(v_pos_655_, v_a_658_);
v___x_665_ = lean_string_utf8_get_fast(v_s_656_, v___x_664_);
v___x_666_ = lean_uint32_dec_eq(v___x_665_, v_c_657_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
lean_dec(v_a_658_);
v___x_667_ = lean_box(0);
v___x_668_ = lean_string_utf8_next_fast(v_s_656_, v___x_664_);
lean_dec(v___x_664_);
v___x_669_ = lean_nat_sub(v___x_668_, v_pos_655_);
v_a_658_ = v___x_669_;
v_b_659_ = v___x_667_;
goto _start;
}
else
{
lean_object* v___x_671_; 
lean_dec(v___x_664_);
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v_a_658_);
return v___x_671_;
}
}
else
{
lean_dec(v_a_658_);
lean_inc(v_b_659_);
return v_b_659_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg___boxed(lean_object* v___x_672_, lean_object* v_pos_673_, lean_object* v_s_674_, lean_object* v_c_675_, lean_object* v_a_676_, lean_object* v_b_677_){
_start:
{
uint32_t v_c_boxed_678_; lean_object* v_res_679_; 
v_c_boxed_678_ = lean_unbox_uint32(v_c_675_);
lean_dec(v_c_675_);
v_res_679_ = l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg(v___x_672_, v_pos_673_, v_s_674_, v_c_boxed_678_, v_a_676_, v_b_677_);
lean_dec(v_b_677_);
lean_dec_ref(v_s_674_);
lean_dec(v_pos_673_);
lean_dec_ref(v___x_672_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_String_posOfAux(lean_object* v_s_680_, uint32_t v_c_681_, lean_object* v_stopPos_682_, lean_object* v_pos_683_){
_start:
{
uint8_t v___x_684_; 
v___x_684_ = lean_nat_dec_le(v_pos_683_, v_stopPos_682_);
if (v___x_684_ == 0)
{
lean_dec(v_pos_683_);
lean_dec_ref(v_s_680_);
return v_stopPos_682_;
}
else
{
uint8_t v___x_685_; 
v___x_685_ = lean_string_is_valid_pos(v_s_680_, v_pos_683_);
if (v___x_685_ == 0)
{
lean_dec(v_pos_683_);
lean_dec_ref(v_s_680_);
return v_stopPos_682_;
}
else
{
uint8_t v___x_686_; 
v___x_686_ = lean_string_is_valid_pos(v_s_680_, v_stopPos_682_);
if (v___x_686_ == 0)
{
lean_dec(v_pos_683_);
lean_dec_ref(v_s_680_);
return v_stopPos_682_;
}
else
{
lean_object* v___x_687_; lean_object* v_searcher_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
lean_inc(v_stopPos_682_);
lean_inc(v_pos_683_);
lean_inc_ref(v_s_680_);
v___x_687_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_687_, 0, v_s_680_);
lean_ctor_set(v___x_687_, 1, v_pos_683_);
lean_ctor_set(v___x_687_, 2, v_stopPos_682_);
v_searcher_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_box(0);
v___x_690_ = l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg(v___x_687_, v_pos_683_, v_s_680_, v_c_681_, v_searcher_688_, v___x_689_);
lean_dec_ref(v_s_680_);
lean_dec_ref(v___x_687_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_nat_sub(v_stopPos_682_, v_pos_683_);
lean_dec(v_stopPos_682_);
v___x_692_ = lean_nat_add(v_pos_683_, v___x_691_);
lean_dec(v___x_691_);
lean_dec(v_pos_683_);
return v___x_692_;
}
else
{
lean_object* v_val_693_; lean_object* v___x_694_; 
lean_dec(v_stopPos_682_);
v_val_693_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_val_693_);
lean_dec_ref(v___x_690_);
v___x_694_ = lean_nat_add(v_pos_683_, v_val_693_);
lean_dec(v_val_693_);
lean_dec(v_pos_683_);
return v___x_694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_posOfAux___boxed(lean_object* v_s_695_, lean_object* v_c_696_, lean_object* v_stopPos_697_, lean_object* v_pos_698_){
_start:
{
uint32_t v_c_boxed_699_; lean_object* v_res_700_; 
v_c_boxed_699_ = lean_unbox_uint32(v_c_696_);
lean_dec(v_c_696_);
v_res_700_ = l_String_posOfAux(v_s_695_, v_c_boxed_699_, v_stopPos_697_, v_pos_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0(lean_object* v___x_701_, lean_object* v_pos_702_, lean_object* v_s_703_, uint32_t v_c_704_, lean_object* v_inst_705_, lean_object* v_R_706_, lean_object* v_a_707_, lean_object* v_b_708_, lean_object* v_c_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg(v___x_701_, v_pos_702_, v_s_703_, v_c_704_, v_a_707_, v_b_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___boxed(lean_object* v___x_711_, lean_object* v_pos_712_, lean_object* v_s_713_, lean_object* v_c_714_, lean_object* v_inst_715_, lean_object* v_R_716_, lean_object* v_a_717_, lean_object* v_b_718_, lean_object* v_c_719_){
_start:
{
uint32_t v_c_boxed_720_; lean_object* v_res_721_; 
v_c_boxed_720_ = lean_unbox_uint32(v_c_714_);
lean_dec(v_c_714_);
v_res_721_ = l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0(v___x_711_, v_pos_712_, v_s_713_, v_c_boxed_720_, v_inst_715_, v_R_716_, v_a_717_, v_b_718_, v_c_719_);
lean_dec(v_b_718_);
lean_dec_ref(v_s_713_);
lean_dec(v_pos_712_);
lean_dec_ref(v___x_711_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_String_posOf(lean_object* v_s_722_, uint32_t v_c_723_){
_start:
{
lean_object* v_searcher_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_searcher_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_string_utf8_byte_size(v_s_722_);
lean_inc_ref(v_s_722_);
v___x_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_726_, 0, v_s_722_);
lean_ctor_set(v___x_726_, 1, v_searcher_724_);
lean_ctor_set(v___x_726_, 2, v___x_725_);
v___x_727_ = lean_box(0);
v___x_728_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(v___x_726_, v_s_722_, v_c_723_, v_searcher_724_, v___x_727_);
lean_dec_ref(v_s_722_);
lean_dec_ref(v___x_726_);
if (lean_obj_tag(v___x_728_) == 0)
{
return v___x_725_;
}
else
{
lean_object* v_val_729_; 
v_val_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_val_729_);
lean_dec_ref(v___x_728_);
return v_val_729_;
}
}
}
LEAN_EXPORT lean_object* l_String_posOf___boxed(lean_object* v_s_730_, lean_object* v_c_731_){
_start:
{
uint32_t v_c_boxed_732_; lean_object* v_res_733_; 
v_c_boxed_732_ = lean_unbox_uint32(v_c_731_);
lean_dec(v_c_731_);
v_res_733_ = l_String_posOf(v_s_730_, v_c_boxed_732_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg(lean_object* v_s_734_, uint32_t v_c_735_, lean_object* v_a_736_, lean_object* v_b_737_){
_start:
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_nat_dec_eq(v_a_736_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v_str_740_; lean_object* v_startInclusive_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint32_t v___x_749_; uint8_t v___x_750_; 
v_str_740_ = lean_ctor_get(v_s_734_, 0);
v_startInclusive_741_ = lean_ctor_get(v_s_734_, 1);
v___x_742_ = lean_nat_add(v_startInclusive_741_, v_a_736_);
lean_inc(v___x_742_);
lean_inc(v_startInclusive_741_);
lean_inc_ref(v_str_740_);
v___x_743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_743_, 0, v_str_740_);
lean_ctor_set(v___x_743_, 1, v_startInclusive_741_);
lean_ctor_set(v___x_743_, 2, v___x_742_);
v___x_744_ = lean_nat_sub(v___x_742_, v_startInclusive_741_);
lean_dec(v___x_742_);
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_nat_sub(v___x_744_, v___x_745_);
lean_dec(v___x_744_);
v___x_747_ = l_String_Slice_posLE(v___x_743_, v___x_746_);
lean_dec_ref(v___x_743_);
v___x_748_ = lean_nat_add(v_startInclusive_741_, v___x_747_);
v___x_749_ = lean_string_utf8_get_fast(v_str_740_, v___x_748_);
lean_dec(v___x_748_);
v___x_750_ = lean_uint32_dec_eq(v___x_749_, v_c_735_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec(v___x_747_);
v___x_751_ = lean_box(0);
v___x_752_ = lean_nat_sub(v_a_736_, v___x_745_);
lean_dec(v_a_736_);
v___x_753_ = l_String_Slice_posLE(v_s_734_, v___x_752_);
v_a_736_ = v___x_753_;
v_b_737_ = v___x_751_;
goto _start;
}
else
{
lean_object* v___x_755_; 
lean_dec(v_a_736_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_747_);
return v___x_755_;
}
}
else
{
lean_dec(v_a_736_);
lean_inc(v_b_737_);
return v_b_737_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg___boxed(lean_object* v_s_756_, lean_object* v_c_757_, lean_object* v_a_758_, lean_object* v_b_759_){
_start:
{
uint32_t v_c_boxed_760_; lean_object* v_res_761_; 
v_c_boxed_760_ = lean_unbox_uint32(v_c_757_);
lean_dec(v_c_757_);
v_res_761_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg(v_s_756_, v_c_boxed_760_, v_a_758_, v_b_759_);
lean_dec(v_b_759_);
lean_dec_ref(v_s_756_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0(uint32_t v_c_762_, lean_object* v_s_763_){
_start:
{
lean_object* v_startInclusive_764_; lean_object* v_endExclusive_765_; lean_object* v_searcher_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_startInclusive_764_ = lean_ctor_get(v_s_763_, 1);
v_endExclusive_765_ = lean_ctor_get(v_s_763_, 2);
v_searcher_766_ = lean_nat_sub(v_endExclusive_765_, v_startInclusive_764_);
v___x_767_ = lean_box(0);
v___x_768_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg(v_s_763_, v_c_762_, v_searcher_766_, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0___boxed(lean_object* v_c_769_, lean_object* v_s_770_){
_start:
{
uint32_t v_c_boxed_771_; lean_object* v_res_772_; 
v_c_boxed_771_ = lean_unbox_uint32(v_c_769_);
lean_dec(v_c_769_);
v_res_772_ = l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0(v_c_boxed_771_, v_s_770_);
lean_dec_ref(v_s_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_String_revPosOfAux(lean_object* v_s_773_, uint32_t v_c_774_, lean_object* v_pos_775_){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_string_utf8_byte_size(v_s_773_);
lean_inc_ref(v_s_773_);
v___x_778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_778_, 0, v_s_773_);
lean_ctor_set(v___x_778_, 1, v___x_776_);
lean_ctor_set(v___x_778_, 2, v___x_777_);
v___x_779_ = l_String_Slice_pos_x3f(v___x_778_, v_pos_775_);
lean_dec_ref(v___x_778_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; 
lean_dec_ref(v_s_773_);
v___x_780_ = lean_box(0);
return v___x_780_;
}
else
{
lean_object* v_val_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_800_; 
v_val_781_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_800_ == 0)
{
v___x_783_ = v___x_779_;
v_isShared_784_ = v_isSharedCheck_800_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_val_781_);
lean_dec(v___x_779_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_800_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_785_, 0, v_s_773_);
lean_ctor_set(v___x_785_, 1, v___x_776_);
lean_ctor_set(v___x_785_, 2, v_val_781_);
v___x_786_ = l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0(v_c_774_, v___x_785_);
lean_dec_ref(v___x_785_);
if (lean_obj_tag(v___x_786_) == 0)
{
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v___x_787_; 
lean_del_object(v___x_783_);
v___x_787_ = lean_box(0);
return v___x_787_;
}
else
{
lean_object* v_val_788_; lean_object* v___x_790_; 
v_val_788_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_val_788_);
lean_dec_ref(v___x_786_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v_val_788_);
v___x_790_ = v___x_783_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_val_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
else
{
lean_object* v_val_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_del_object(v___x_783_);
v_val_792_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_786_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_val_792_);
lean_dec(v___x_786_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_val_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_revPosOfAux___boxed(lean_object* v_s_801_, lean_object* v_c_802_, lean_object* v_pos_803_){
_start:
{
uint32_t v_c_boxed_804_; lean_object* v_res_805_; 
v_c_boxed_804_ = lean_unbox_uint32(v_c_802_);
lean_dec(v_c_802_);
v_res_805_ = l_String_revPosOfAux(v_s_801_, v_c_boxed_804_, v_pos_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0(lean_object* v_s_806_, uint32_t v_c_807_, lean_object* v_inst_808_, lean_object* v_R_809_, lean_object* v_a_810_, lean_object* v_b_811_, lean_object* v_c_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg(v_s_806_, v_c_807_, v_a_810_, v_b_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___boxed(lean_object* v_s_814_, lean_object* v_c_815_, lean_object* v_inst_816_, lean_object* v_R_817_, lean_object* v_a_818_, lean_object* v_b_819_, lean_object* v_c_820_){
_start:
{
uint32_t v_c_boxed_821_; lean_object* v_res_822_; 
v_c_boxed_821_ = lean_unbox_uint32(v_c_815_);
lean_dec(v_c_815_);
v_res_822_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0(v_s_814_, v_c_boxed_821_, v_inst_816_, v_R_817_, v_a_818_, v_b_819_, v_c_820_);
lean_dec(v_b_819_);
lean_dec_ref(v_s_814_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_String_revPosOf(lean_object* v_s_823_, uint32_t v_c_824_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_string_utf8_byte_size(v_s_823_);
v___x_827_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_827_, 0, v_s_823_);
lean_ctor_set(v___x_827_, 1, v___x_825_);
lean_ctor_set(v___x_827_, 2, v___x_826_);
v___x_828_ = l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0(v_c_824_, v___x_827_);
lean_dec_ref(v___x_827_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_829_; 
v___x_829_ = lean_box(0);
return v___x_829_;
}
else
{
lean_object* v_val_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v_val_830_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_828_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_val_830_);
lean_dec(v___x_828_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_val_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_revPosOf___boxed(lean_object* v_s_838_, lean_object* v_c_839_){
_start:
{
uint32_t v_c_boxed_840_; lean_object* v_res_841_; 
v_c_boxed_840_ = lean_unbox_uint32(v_c_839_);
lean_dec(v_c_839_);
v_res_841_ = l_String_revPosOf(v_s_838_, v_c_boxed_840_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg(lean_object* v_s_842_, lean_object* v_p_843_, lean_object* v_a_844_, lean_object* v_b_845_){
_start:
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = lean_nat_dec_eq(v_a_844_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v_str_848_; lean_object* v_startInclusive_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint32_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_str_848_ = lean_ctor_get(v_s_842_, 0);
v_startInclusive_849_ = lean_ctor_get(v_s_842_, 1);
v___x_850_ = lean_nat_add(v_startInclusive_849_, v_a_844_);
lean_inc(v___x_850_);
lean_inc(v_startInclusive_849_);
lean_inc_ref(v_str_848_);
v___x_851_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_851_, 0, v_str_848_);
lean_ctor_set(v___x_851_, 1, v_startInclusive_849_);
lean_ctor_set(v___x_851_, 2, v___x_850_);
v___x_852_ = lean_nat_sub(v___x_850_, v_startInclusive_849_);
lean_dec(v___x_850_);
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_nat_sub(v___x_852_, v___x_853_);
lean_dec(v___x_852_);
v___x_855_ = l_String_Slice_posLE(v___x_851_, v___x_854_);
lean_dec_ref(v___x_851_);
v___x_856_ = lean_nat_add(v_startInclusive_849_, v___x_855_);
v___x_857_ = lean_string_utf8_get_fast(v_str_848_, v___x_856_);
lean_dec(v___x_856_);
v___x_858_ = lean_box_uint32(v___x_857_);
lean_inc_ref(v_p_843_);
v___x_859_ = lean_apply_1(v_p_843_, v___x_858_);
v___x_860_ = lean_unbox(v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v___x_855_);
v___x_861_ = lean_box(0);
v___x_862_ = lean_nat_sub(v_a_844_, v___x_853_);
lean_dec(v_a_844_);
v___x_863_ = l_String_Slice_posLE(v_s_842_, v___x_862_);
v_a_844_ = v___x_863_;
v_b_845_ = v___x_861_;
goto _start;
}
else
{
lean_object* v___x_865_; 
lean_dec(v_a_844_);
lean_dec_ref(v_p_843_);
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_855_);
return v___x_865_;
}
}
else
{
lean_dec(v_a_844_);
lean_dec_ref(v_p_843_);
lean_inc(v_b_845_);
return v_b_845_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg___boxed(lean_object* v_s_866_, lean_object* v_p_867_, lean_object* v_a_868_, lean_object* v_b_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg(v_s_866_, v_p_867_, v_a_868_, v_b_869_);
lean_dec(v_b_869_);
lean_dec_ref(v_s_866_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0(lean_object* v_p_871_, lean_object* v_s_872_){
_start:
{
lean_object* v_startInclusive_873_; lean_object* v_endExclusive_874_; lean_object* v_searcher_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_startInclusive_873_ = lean_ctor_get(v_s_872_, 1);
v_endExclusive_874_ = lean_ctor_get(v_s_872_, 2);
v_searcher_875_ = lean_nat_sub(v_endExclusive_874_, v_startInclusive_873_);
v___x_876_ = lean_box(0);
v___x_877_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg(v_s_872_, v_p_871_, v_searcher_875_, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0___boxed(lean_object* v_p_878_, lean_object* v_s_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0(v_p_878_, v_s_879_);
lean_dec_ref(v_s_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_String_revFindAux(lean_object* v_s_881_, lean_object* v_p_882_, lean_object* v_pos_883_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_string_utf8_byte_size(v_s_881_);
lean_inc_ref(v_s_881_);
v___x_886_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_886_, 0, v_s_881_);
lean_ctor_set(v___x_886_, 1, v___x_884_);
lean_ctor_set(v___x_886_, 2, v___x_885_);
v___x_887_ = l_String_Slice_pos_x3f(v___x_886_, v_pos_883_);
lean_dec_ref(v___x_886_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v___x_888_; 
lean_dec_ref(v_p_882_);
lean_dec_ref(v_s_881_);
v___x_888_ = lean_box(0);
return v___x_888_;
}
else
{
lean_object* v_val_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_908_; 
v_val_889_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_908_ == 0)
{
v___x_891_ = v___x_887_;
v_isShared_892_ = v_isSharedCheck_908_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_val_889_);
lean_dec(v___x_887_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_908_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_893_, 0, v_s_881_);
lean_ctor_set(v___x_893_, 1, v___x_884_);
lean_ctor_set(v___x_893_, 2, v_val_889_);
v___x_894_ = l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0(v_p_882_, v___x_893_);
lean_dec_ref(v___x_893_);
if (lean_obj_tag(v___x_894_) == 0)
{
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v___x_895_; 
lean_del_object(v___x_891_);
v___x_895_ = lean_box(0);
return v___x_895_;
}
else
{
lean_object* v_val_896_; lean_object* v___x_898_; 
v_val_896_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_val_896_);
lean_dec_ref(v___x_894_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_val_896_);
v___x_898_ = v___x_891_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_val_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
else
{
lean_object* v_val_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_del_object(v___x_891_);
v_val_900_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_894_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_val_900_);
lean_dec(v___x_894_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_val_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0(lean_object* v_s_909_, lean_object* v_p_910_, lean_object* v_inst_911_, lean_object* v_R_912_, lean_object* v_a_913_, lean_object* v_b_914_, lean_object* v_c_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg(v_s_909_, v_p_910_, v_a_913_, v_b_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___boxed(lean_object* v_s_917_, lean_object* v_p_918_, lean_object* v_inst_919_, lean_object* v_R_920_, lean_object* v_a_921_, lean_object* v_b_922_, lean_object* v_c_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0(v_s_917_, v_p_918_, v_inst_919_, v_R_920_, v_a_921_, v_b_922_, v_c_923_);
lean_dec(v_b_922_);
lean_dec_ref(v_s_917_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_String_revFind(lean_object* v_s_925_, lean_object* v_p_926_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_string_utf8_byte_size(v_s_925_);
v___x_929_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_929_, 0, v_s_925_);
lean_ctor_set(v___x_929_, 1, v___x_927_);
lean_ctor_set(v___x_929_, 2, v___x_928_);
v___x_930_ = l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0(v_p_926_, v___x_929_);
lean_dec_ref(v___x_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v___x_931_; 
v___x_931_ = lean_box(0);
return v___x_931_;
}
else
{
lean_object* v_val_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
v_val_932_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_930_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_val_932_);
lean_dec(v___x_930_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_val_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg(lean_object* v_s_940_, lean_object* v_a_941_, lean_object* v_b_942_){
_start:
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = lean_nat_dec_eq(v_a_941_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v_str_945_; lean_object* v_startInclusive_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; uint32_t v___x_954_; uint32_t v___x_955_; uint8_t v___x_956_; 
v_str_945_ = lean_ctor_get(v_s_940_, 0);
v_startInclusive_946_ = lean_ctor_get(v_s_940_, 1);
v___x_947_ = lean_nat_add(v_startInclusive_946_, v_a_941_);
lean_inc(v___x_947_);
lean_inc(v_startInclusive_946_);
lean_inc_ref(v_str_945_);
v___x_948_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_948_, 0, v_str_945_);
lean_ctor_set(v___x_948_, 1, v_startInclusive_946_);
lean_ctor_set(v___x_948_, 2, v___x_947_);
v___x_949_ = lean_nat_sub(v___x_947_, v_startInclusive_946_);
lean_dec(v___x_947_);
v___x_950_ = lean_unsigned_to_nat(1u);
v___x_951_ = lean_nat_sub(v___x_949_, v___x_950_);
lean_dec(v___x_949_);
v___x_952_ = l_String_Slice_posLE(v___x_948_, v___x_951_);
lean_dec_ref(v___x_948_);
v___x_953_ = lean_nat_add(v_startInclusive_946_, v___x_952_);
v___x_954_ = lean_string_utf8_get_fast(v_str_945_, v___x_953_);
lean_dec(v___x_953_);
v___x_955_ = 10;
v___x_956_ = lean_uint32_dec_eq(v___x_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v___x_952_);
v___x_957_ = lean_box(0);
v___x_958_ = lean_nat_sub(v_a_941_, v___x_950_);
lean_dec(v_a_941_);
v___x_959_ = l_String_Slice_posLE(v_s_940_, v___x_958_);
v_a_941_ = v___x_959_;
v_b_942_ = v___x_957_;
goto _start;
}
else
{
lean_object* v___x_961_; 
lean_dec(v_a_941_);
v___x_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_952_);
return v___x_961_;
}
}
else
{
lean_dec(v_a_941_);
lean_inc(v_b_942_);
return v_b_942_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg___boxed(lean_object* v_s_962_, lean_object* v_a_963_, lean_object* v_b_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg(v_s_962_, v_a_963_, v_b_964_);
lean_dec(v_b_964_);
lean_dec_ref(v_s_962_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0(lean_object* v_s_966_){
_start:
{
lean_object* v_startInclusive_967_; lean_object* v_endExclusive_968_; lean_object* v_searcher_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_startInclusive_967_ = lean_ctor_get(v_s_966_, 1);
v_endExclusive_968_ = lean_ctor_get(v_s_966_, 2);
v_searcher_969_ = lean_nat_sub(v_endExclusive_968_, v_startInclusive_967_);
v___x_970_ = lean_box(0);
v___x_971_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg(v_s_966_, v_searcher_969_, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0___boxed(lean_object* v_s_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0(v_s_972_);
lean_dec_ref(v_s_972_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_String_findLineStart(lean_object* v_s_974_, lean_object* v_pos_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_976_ = lean_unsigned_to_nat(0u);
v___x_977_ = lean_string_utf8_byte_size(v_s_974_);
lean_inc_ref(v_s_974_);
v___x_978_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_978_, 0, v_s_974_);
lean_ctor_set(v___x_978_, 1, v___x_976_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
v___x_979_ = l_String_Slice_pos_x3f(v___x_978_, v_pos_975_);
lean_dec_ref(v___x_978_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_dec_ref(v_s_974_);
return v___x_976_;
}
else
{
lean_object* v_val_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_val_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_val_980_);
lean_dec_ref(v___x_979_);
v___x_981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_981_, 0, v_s_974_);
lean_ctor_set(v___x_981_, 1, v___x_976_);
lean_ctor_set(v___x_981_, 2, v_val_980_);
v___x_982_ = l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0(v___x_981_);
lean_dec_ref(v___x_981_);
if (lean_obj_tag(v___x_982_) == 0)
{
if (lean_obj_tag(v___x_982_) == 0)
{
return v___x_976_;
}
else
{
lean_object* v_val_983_; 
v_val_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_val_983_);
lean_dec_ref(v___x_982_);
return v_val_983_;
}
}
else
{
lean_object* v_val_984_; 
v_val_984_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_val_984_);
lean_dec_ref(v___x_982_);
return v_val_984_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0(lean_object* v_s_985_, lean_object* v_inst_986_, lean_object* v_R_987_, lean_object* v_a_988_, lean_object* v_b_989_, lean_object* v_c_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg(v_s_985_, v_a_988_, v_b_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___boxed(lean_object* v_s_992_, lean_object* v_inst_993_, lean_object* v_R_994_, lean_object* v_a_995_, lean_object* v_b_996_, lean_object* v_c_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0(v_s_992_, v_inst_993_, v_R_994_, v_a_995_, v_b_996_, v_c_997_);
lean_dec(v_b_996_);
lean_dec_ref(v_s_992_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_String_split___redArg(lean_object* v_s_999_, lean_object* v_inst_1000_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1001_ = lean_unsigned_to_nat(0u);
v___x_1002_ = lean_string_utf8_byte_size(v_s_999_);
v___x_1003_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1003_, 0, v_s_999_);
lean_ctor_set(v___x_1003_, 1, v___x_1001_);
lean_ctor_set(v___x_1003_, 2, v___x_1002_);
v___x_1004_ = l_String_Slice_splitToSubslice___redArg(v___x_1003_, v_inst_1000_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_String_split(lean_object* v_00_u03c1_1005_, lean_object* v_00_u03c3_1006_, lean_object* v_inst_1007_, lean_object* v_s_1008_, lean_object* v_pat_1009_, lean_object* v_inst_1010_){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = lean_string_utf8_byte_size(v_s_1008_);
v___x_1013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1013_, 0, v_s_1008_);
lean_ctor_set(v___x_1013_, 1, v___x_1011_);
lean_ctor_set(v___x_1013_, 2, v___x_1012_);
v___x_1014_ = l_String_Slice_splitToSubslice___redArg(v___x_1013_, v_inst_1010_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_String_split___boxed(lean_object* v_00_u03c1_1015_, lean_object* v_00_u03c3_1016_, lean_object* v_inst_1017_, lean_object* v_s_1018_, lean_object* v_pat_1019_, lean_object* v_inst_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_String_split(v_00_u03c1_1015_, v_00_u03c3_1016_, v_inst_1017_, v_s_1018_, v_pat_1019_, v_inst_1020_);
lean_dec(v_pat_1019_);
lean_dec(v_inst_1017_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_String_splitInclusive___redArg(lean_object* v_s_1022_, lean_object* v_inst_1023_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_string_utf8_byte_size(v_s_1022_);
v___x_1026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1026_, 0, v_s_1022_);
lean_ctor_set(v___x_1026_, 1, v___x_1024_);
lean_ctor_set(v___x_1026_, 2, v___x_1025_);
v___x_1027_ = l_String_Slice_splitInclusive___redArg(v___x_1026_, v_inst_1023_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_String_splitInclusive(lean_object* v_00_u03c1_1028_, lean_object* v_00_u03c3_1029_, lean_object* v_s_1030_, lean_object* v_pat_1031_, lean_object* v_inst_1032_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_string_utf8_byte_size(v_s_1030_);
v___x_1035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1035_, 0, v_s_1030_);
lean_ctor_set(v___x_1035_, 1, v___x_1033_);
lean_ctor_set(v___x_1035_, 2, v___x_1034_);
v___x_1036_ = l_String_Slice_splitInclusive___redArg(v___x_1035_, v_inst_1032_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_String_splitInclusive___boxed(lean_object* v_00_u03c1_1037_, lean_object* v_00_u03c3_1038_, lean_object* v_s_1039_, lean_object* v_pat_1040_, lean_object* v_inst_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_String_splitInclusive(v_00_u03c1_1037_, v_00_u03c3_1038_, v_s_1039_, v_pat_1040_, v_inst_1041_);
lean_dec(v_pat_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg(lean_object* v_f_1043_, lean_object* v___x_1044_, lean_object* v_a_1045_, lean_object* v_b_1046_){
_start:
{
lean_object* v_str_1047_; lean_object* v_startInclusive_1048_; lean_object* v_endExclusive_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v_str_1047_ = lean_ctor_get(v___x_1044_, 0);
v_startInclusive_1048_ = lean_ctor_get(v___x_1044_, 1);
v_endExclusive_1049_ = lean_ctor_get(v___x_1044_, 2);
v___x_1050_ = lean_nat_sub(v_endExclusive_1049_, v_startInclusive_1048_);
v___x_1051_ = lean_nat_dec_eq(v_a_1045_, v___x_1050_);
lean_dec(v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint32_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1052_ = lean_nat_add(v_startInclusive_1048_, v_a_1045_);
lean_dec(v_a_1045_);
v___x_1053_ = lean_string_utf8_next_fast(v_str_1047_, v___x_1052_);
v___x_1054_ = lean_nat_sub(v___x_1053_, v_startInclusive_1048_);
v___x_1055_ = lean_string_utf8_get_fast(v_str_1047_, v___x_1052_);
lean_dec(v___x_1052_);
v___x_1056_ = lean_box_uint32(v___x_1055_);
lean_inc(v_f_1043_);
v___x_1057_ = lean_apply_2(v_f_1043_, v_b_1046_, v___x_1056_);
v_a_1045_ = v___x_1054_;
v_b_1046_ = v___x_1057_;
goto _start;
}
else
{
lean_dec(v_a_1045_);
lean_dec(v_f_1043_);
return v_b_1046_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg___boxed(lean_object* v_f_1059_, lean_object* v___x_1060_, lean_object* v_a_1061_, lean_object* v_b_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg(v_f_1059_, v___x_1060_, v_a_1061_, v_b_1062_);
lean_dec_ref(v___x_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___redArg(lean_object* v_f_1064_, lean_object* v_s_1065_, lean_object* v_stopPos_1066_, lean_object* v_i_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = lean_string_utf8_byte_size(v_s_1065_);
lean_inc_ref(v_s_1065_);
v___x_1071_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1071_, 0, v_s_1065_);
lean_ctor_set(v___x_1071_, 1, v___x_1069_);
lean_ctor_set(v___x_1071_, 2, v___x_1070_);
v___x_1072_ = l_String_Slice_pos_x21(v___x_1071_, v_i_1067_);
v___x_1073_ = l_String_Slice_pos_x21(v___x_1071_, v_stopPos_1066_);
lean_dec_ref(v___x_1071_);
v___x_1074_ = l_String_slice_x21(v_s_1065_, v___x_1072_, v___x_1073_);
lean_dec(v___x_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = l_String_Slice_positions(v___x_1074_);
v___x_1076_ = l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg(v_f_1064_, v___x_1074_, v___x_1075_, v_a_1068_);
lean_dec_ref(v___x_1074_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___redArg___boxed(lean_object* v_f_1077_, lean_object* v_s_1078_, lean_object* v_stopPos_1079_, lean_object* v_i_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_String_foldlAux___redArg(v_f_1077_, v_s_1078_, v_stopPos_1079_, v_i_1080_, v_a_1081_);
lean_dec(v_i_1080_);
lean_dec(v_stopPos_1079_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux(lean_object* v_00_u03b1_1083_, lean_object* v_f_1084_, lean_object* v_s_1085_, lean_object* v_stopPos_1086_, lean_object* v_i_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_String_foldlAux___redArg(v_f_1084_, v_s_1085_, v_stopPos_1086_, v_i_1087_, v_a_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___boxed(lean_object* v_00_u03b1_1090_, lean_object* v_f_1091_, lean_object* v_s_1092_, lean_object* v_stopPos_1093_, lean_object* v_i_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_String_foldlAux(v_00_u03b1_1090_, v_f_1091_, v_s_1092_, v_stopPos_1093_, v_i_1094_, v_a_1095_);
lean_dec(v_i_1094_);
lean_dec(v_stopPos_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0(lean_object* v_00_u03b1_1097_, lean_object* v_f_1098_, lean_object* v___x_1099_, lean_object* v_inst_1100_, lean_object* v_R_1101_, lean_object* v_a_1102_, lean_object* v_b_1103_, lean_object* v_c_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg(v_f_1098_, v___x_1099_, v_a_1102_, v_b_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___boxed(lean_object* v_00_u03b1_1106_, lean_object* v_f_1107_, lean_object* v___x_1108_, lean_object* v_inst_1109_, lean_object* v_R_1110_, lean_object* v_a_1111_, lean_object* v_b_1112_, lean_object* v_c_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0(v_00_u03b1_1106_, v_f_1107_, v___x_1108_, v_inst_1109_, v_R_1110_, v_a_1111_, v_b_1112_, v_c_1113_);
lean_dec_ref(v___x_1108_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg(lean_object* v_f_1115_, lean_object* v___x_1116_, lean_object* v_a_1117_, lean_object* v_b_1118_){
_start:
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = lean_nat_dec_eq(v_a_1117_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v_str_1121_; lean_object* v_startInclusive_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v_prevPos_1125_; lean_object* v___x_1126_; uint32_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_str_1121_ = lean_ctor_get(v___x_1116_, 0);
v_startInclusive_1122_ = lean_ctor_get(v___x_1116_, 1);
v___x_1123_ = lean_unsigned_to_nat(1u);
v___x_1124_ = lean_nat_sub(v_a_1117_, v___x_1123_);
lean_dec(v_a_1117_);
v_prevPos_1125_ = l_String_Slice_posLE(v___x_1116_, v___x_1124_);
v___x_1126_ = lean_nat_add(v_startInclusive_1122_, v_prevPos_1125_);
v___x_1127_ = lean_string_utf8_get_fast(v_str_1121_, v___x_1126_);
lean_dec(v___x_1126_);
v___x_1128_ = lean_box_uint32(v___x_1127_);
lean_inc(v_f_1115_);
v___x_1129_ = lean_apply_2(v_f_1115_, v___x_1128_, v_b_1118_);
v_a_1117_ = v_prevPos_1125_;
v_b_1118_ = v___x_1129_;
goto _start;
}
else
{
lean_dec(v_a_1117_);
lean_dec(v_f_1115_);
return v_b_1118_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg___boxed(lean_object* v_f_1131_, lean_object* v___x_1132_, lean_object* v_a_1133_, lean_object* v_b_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg(v_f_1131_, v___x_1132_, v_a_1133_, v_b_1134_);
lean_dec_ref(v___x_1132_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_String_foldrAux___redArg(lean_object* v_f_1136_, lean_object* v_a_1137_, lean_object* v_s_1138_, lean_object* v_i_1139_, lean_object* v_begPos_1140_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = lean_string_utf8_byte_size(v_s_1138_);
lean_inc_ref(v_s_1138_);
v___x_1143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1143_, 0, v_s_1138_);
lean_ctor_set(v___x_1143_, 1, v___x_1141_);
lean_ctor_set(v___x_1143_, 2, v___x_1142_);
v___x_1144_ = l_String_Slice_pos_x21(v___x_1143_, v_begPos_1140_);
v___x_1145_ = l_String_Slice_pos_x21(v___x_1143_, v_i_1139_);
lean_dec_ref(v___x_1143_);
v___x_1146_ = l_String_slice_x21(v_s_1138_, v___x_1144_, v___x_1145_);
lean_dec(v___x_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = l_String_Slice_revPositions(v___x_1146_);
v___x_1148_ = l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg(v_f_1136_, v___x_1146_, v___x_1147_, v_a_1137_);
lean_dec_ref(v___x_1146_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_String_foldrAux___redArg___boxed(lean_object* v_f_1149_, lean_object* v_a_1150_, lean_object* v_s_1151_, lean_object* v_i_1152_, lean_object* v_begPos_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_String_foldrAux___redArg(v_f_1149_, v_a_1150_, v_s_1151_, v_i_1152_, v_begPos_1153_);
lean_dec(v_begPos_1153_);
lean_dec(v_i_1152_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_String_foldrAux(lean_object* v_00_u03b1_1155_, lean_object* v_f_1156_, lean_object* v_a_1157_, lean_object* v_s_1158_, lean_object* v_i_1159_, lean_object* v_begPos_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_String_foldrAux___redArg(v_f_1156_, v_a_1157_, v_s_1158_, v_i_1159_, v_begPos_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_String_foldrAux___boxed(lean_object* v_00_u03b1_1162_, lean_object* v_f_1163_, lean_object* v_a_1164_, lean_object* v_s_1165_, lean_object* v_i_1166_, lean_object* v_begPos_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_String_foldrAux(v_00_u03b1_1162_, v_f_1163_, v_a_1164_, v_s_1165_, v_i_1166_, v_begPos_1167_);
lean_dec(v_begPos_1167_);
lean_dec(v_i_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0(lean_object* v_00_u03b1_1169_, lean_object* v_f_1170_, lean_object* v___x_1171_, lean_object* v_inst_1172_, lean_object* v_R_1173_, lean_object* v_a_1174_, lean_object* v_b_1175_, lean_object* v_c_1176_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg(v_f_1170_, v___x_1171_, v_a_1174_, v_b_1175_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___boxed(lean_object* v_00_u03b1_1178_, lean_object* v_f_1179_, lean_object* v___x_1180_, lean_object* v_inst_1181_, lean_object* v_R_1182_, lean_object* v_a_1183_, lean_object* v_b_1184_, lean_object* v_c_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0(v_00_u03b1_1178_, v_f_1179_, v___x_1180_, v_inst_1181_, v_R_1182_, v_a_1183_, v_b_1184_, v_c_1185_);
lean_dec_ref(v___x_1180_);
return v_res_1186_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg(lean_object* v_s_1187_, lean_object* v_p_1188_, lean_object* v_a_1189_, uint8_t v_b_1190_){
_start:
{
lean_object* v_str_1191_; lean_object* v_startInclusive_1192_; lean_object* v_endExclusive_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v_str_1191_ = lean_ctor_get(v_s_1187_, 0);
v_startInclusive_1192_ = lean_ctor_get(v_s_1187_, 1);
v_endExclusive_1193_ = lean_ctor_get(v_s_1187_, 2);
v___x_1194_ = lean_nat_sub(v_endExclusive_1193_, v_startInclusive_1192_);
v___x_1195_ = lean_nat_dec_eq(v_a_1189_, v___x_1194_);
lean_dec(v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; uint32_t v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1196_ = lean_nat_add(v_startInclusive_1192_, v_a_1189_);
lean_dec(v_a_1189_);
v___x_1197_ = lean_string_utf8_get_fast(v_str_1191_, v___x_1196_);
v___x_1198_ = lean_box_uint32(v___x_1197_);
lean_inc_ref(v_p_1188_);
v___x_1199_ = lean_apply_1(v_p_1188_, v___x_1198_);
v___x_1200_ = lean_unbox(v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1201_ = lean_string_utf8_next_fast(v_str_1191_, v___x_1196_);
lean_dec(v___x_1196_);
v___x_1202_ = lean_nat_sub(v___x_1201_, v_startInclusive_1192_);
v___x_1203_ = lean_unbox(v___x_1199_);
v_a_1189_ = v___x_1202_;
v_b_1190_ = v___x_1203_;
goto _start;
}
else
{
uint8_t v___x_1205_; 
lean_dec(v___x_1196_);
lean_dec_ref(v_p_1188_);
v___x_1205_ = lean_unbox(v___x_1199_);
return v___x_1205_;
}
}
else
{
lean_dec(v_a_1189_);
lean_dec_ref(v_p_1188_);
return v_b_1190_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg___boxed(lean_object* v_s_1206_, lean_object* v_p_1207_, lean_object* v_a_1208_, lean_object* v_b_1209_){
_start:
{
uint8_t v_b_boxed_1210_; uint8_t v_res_1211_; lean_object* v_r_1212_; 
v_b_boxed_1210_ = lean_unbox(v_b_1209_);
v_res_1211_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg(v_s_1206_, v_p_1207_, v_a_1208_, v_b_boxed_1210_);
lean_dec_ref(v_s_1206_);
v_r_1212_ = lean_box(v_res_1211_);
return v_r_1212_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00String_anyAux_spec__0(lean_object* v_p_1213_, lean_object* v_s_1214_){
_start:
{
lean_object* v_searcher_1215_; uint8_t v___x_1216_; uint8_t v___x_1217_; 
v_searcher_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = 0;
v___x_1217_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg(v_s_1214_, v_p_1213_, v_searcher_1215_, v___x_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00String_anyAux_spec__0___boxed(lean_object* v_p_1218_, lean_object* v_s_1219_){
_start:
{
uint8_t v_res_1220_; lean_object* v_r_1221_; 
v_res_1220_ = l_String_Slice_contains___at___00String_anyAux_spec__0(v_p_1218_, v_s_1219_);
lean_dec_ref(v_s_1219_);
v_r_1221_ = lean_box(v_res_1220_);
return v_r_1221_;
}
}
LEAN_EXPORT uint8_t l_String_anyAux(lean_object* v_s_1222_, lean_object* v_stopPos_1223_, lean_object* v_p_1224_, lean_object* v_i_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = lean_string_utf8_byte_size(v_s_1222_);
lean_inc_ref(v_s_1222_);
v___x_1228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1228_, 0, v_s_1222_);
lean_ctor_set(v___x_1228_, 1, v___x_1226_);
lean_ctor_set(v___x_1228_, 2, v___x_1227_);
v___x_1229_ = l_String_Slice_pos_x21(v___x_1228_, v_i_1225_);
v___x_1230_ = l_String_Slice_pos_x21(v___x_1228_, v_stopPos_1223_);
lean_dec_ref(v___x_1228_);
v___x_1231_ = l_String_slice_x21(v_s_1222_, v___x_1229_, v___x_1230_);
lean_dec(v___x_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = l_String_Slice_contains___at___00String_anyAux_spec__0(v_p_1224_, v___x_1231_);
lean_dec_ref(v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_String_anyAux___boxed(lean_object* v_s_1233_, lean_object* v_stopPos_1234_, lean_object* v_p_1235_, lean_object* v_i_1236_){
_start:
{
uint8_t v_res_1237_; lean_object* v_r_1238_; 
v_res_1237_ = l_String_anyAux(v_s_1233_, v_stopPos_1234_, v_p_1235_, v_i_1236_);
lean_dec(v_i_1236_);
lean_dec(v_stopPos_1234_);
v_r_1238_ = lean_box(v_res_1237_);
return v_r_1238_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0(lean_object* v_s_1239_, lean_object* v_p_1240_, lean_object* v_inst_1241_, lean_object* v_R_1242_, lean_object* v_a_1243_, uint8_t v_b_1244_, lean_object* v_c_1245_){
_start:
{
uint8_t v___x_1246_; 
v___x_1246_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg(v_s_1239_, v_p_1240_, v_a_1243_, v_b_1244_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___boxed(lean_object* v_s_1247_, lean_object* v_p_1248_, lean_object* v_inst_1249_, lean_object* v_R_1250_, lean_object* v_a_1251_, lean_object* v_b_1252_, lean_object* v_c_1253_){
_start:
{
uint8_t v_b_boxed_1254_; uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_b_boxed_1254_ = lean_unbox(v_b_1252_);
v_res_1255_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0(v_s_1247_, v_p_1248_, v_inst_1249_, v_R_1250_, v_a_1251_, v_b_boxed_1254_, v_c_1253_);
lean_dec_ref(v_s_1247_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT uint8_t l_String_contains___redArg(lean_object* v_inst_1257_, lean_object* v_s_1258_, lean_object* v_inst_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = lean_string_utf8_byte_size(v_s_1258_);
v___x_1262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1262_, 0, v_s_1258_);
lean_ctor_set(v___x_1262_, 1, v___x_1260_);
lean_ctor_set(v___x_1262_, 2, v___x_1261_);
v___x_1263_ = l_String_Slice_contains___redArg(v_inst_1257_, v___x_1262_, v_inst_1259_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_String_contains___redArg___boxed(lean_object* v_inst_1264_, lean_object* v_s_1265_, lean_object* v_inst_1266_){
_start:
{
uint8_t v_res_1267_; lean_object* v_r_1268_; 
v_res_1267_ = l_String_contains___redArg(v_inst_1264_, v_s_1265_, v_inst_1266_);
v_r_1268_ = lean_box(v_res_1267_);
return v_r_1268_;
}
}
LEAN_EXPORT uint8_t l_String_contains(lean_object* v_00_u03c1_1269_, lean_object* v_00_u03c3_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_s_1273_, lean_object* v_pat_1274_, lean_object* v_inst_1275_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1276_ = lean_unsigned_to_nat(0u);
v___x_1277_ = lean_string_utf8_byte_size(v_s_1273_);
v___x_1278_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1278_, 0, v_s_1273_);
lean_ctor_set(v___x_1278_, 1, v___x_1276_);
lean_ctor_set(v___x_1278_, 2, v___x_1277_);
v___x_1279_ = l_String_Slice_contains___redArg(v_inst_1272_, v___x_1278_, v_inst_1275_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_String_contains___boxed(lean_object* v_00_u03c1_1280_, lean_object* v_00_u03c3_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_s_1284_, lean_object* v_pat_1285_, lean_object* v_inst_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l_String_contains(v_00_u03c1_1280_, v_00_u03c3_1281_, v_inst_1282_, v_inst_1283_, v_s_1284_, v_pat_1285_, v_inst_1286_);
lean_dec(v_pat_1285_);
lean_dec(v_inst_1282_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(lean_object* v_s_1289_, uint32_t v_c_1290_, lean_object* v_a_1291_, uint8_t v_b_1292_){
_start:
{
lean_object* v_str_1293_; lean_object* v_startInclusive_1294_; lean_object* v_endExclusive_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v_str_1293_ = lean_ctor_get(v_s_1289_, 0);
v_startInclusive_1294_ = lean_ctor_get(v_s_1289_, 1);
v_endExclusive_1295_ = lean_ctor_get(v_s_1289_, 2);
v___x_1296_ = lean_nat_sub(v_endExclusive_1295_, v_startInclusive_1294_);
v___x_1297_ = lean_nat_dec_eq(v_a_1291_, v___x_1296_);
lean_dec(v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; uint32_t v___x_1299_; uint8_t v___x_1300_; 
v___x_1298_ = lean_nat_add(v_startInclusive_1294_, v_a_1291_);
lean_dec(v_a_1291_);
v___x_1299_ = lean_string_utf8_get_fast(v_str_1293_, v___x_1298_);
v___x_1300_ = lean_uint32_dec_eq(v___x_1299_, v_c_1290_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_string_utf8_next_fast(v_str_1293_, v___x_1298_);
lean_dec(v___x_1298_);
v___x_1302_ = lean_nat_sub(v___x_1301_, v_startInclusive_1294_);
v_a_1291_ = v___x_1302_;
v_b_1292_ = v___x_1300_;
goto _start;
}
else
{
lean_dec(v___x_1298_);
return v___x_1300_;
}
}
else
{
lean_dec(v_a_1291_);
return v_b_1292_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg___boxed(lean_object* v_s_1304_, lean_object* v_c_1305_, lean_object* v_a_1306_, lean_object* v_b_1307_){
_start:
{
uint32_t v_c_boxed_1308_; uint8_t v_b_boxed_1309_; uint8_t v_res_1310_; lean_object* v_r_1311_; 
v_c_boxed_1308_ = lean_unbox_uint32(v_c_1305_);
lean_dec(v_c_1305_);
v_b_boxed_1309_ = lean_unbox(v_b_1307_);
v_res_1310_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_1304_, v_c_boxed_1308_, v_a_1306_, v_b_boxed_1309_);
lean_dec_ref(v_s_1304_);
v_r_1311_ = lean_box(v_res_1310_);
return v_r_1311_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(uint32_t v_c_1312_, lean_object* v_s_1313_){
_start:
{
lean_object* v_searcher_1314_; uint8_t v___x_1315_; uint8_t v___x_1316_; 
v_searcher_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = 0;
v___x_1316_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_1313_, v_c_1312_, v_searcher_1314_, v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0___boxed(lean_object* v_c_1317_, lean_object* v_s_1318_){
_start:
{
uint32_t v_c_boxed_1319_; uint8_t v_res_1320_; lean_object* v_r_1321_; 
v_c_boxed_1319_ = lean_unbox_uint32(v_c_1317_);
lean_dec(v_c_1317_);
v_res_1320_ = l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(v_c_boxed_1319_, v_s_1318_);
lean_dec_ref(v_s_1318_);
v_r_1321_ = lean_box(v_res_1320_);
return v_r_1321_;
}
}
LEAN_EXPORT uint8_t lean_string_contains(lean_object* v_s_1322_, uint32_t v_c_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = lean_string_utf8_byte_size(v_s_1322_);
v___x_1326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1326_, 0, v_s_1322_);
lean_ctor_set(v___x_1326_, 1, v___x_1324_);
lean_ctor_set(v___x_1326_, 2, v___x_1325_);
v___x_1327_ = l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(v_c_1323_, v___x_1326_);
lean_dec_ref(v___x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_containsImpl___boxed(lean_object* v_s_1328_, lean_object* v_c_1329_){
_start:
{
uint32_t v_c_boxed_1330_; uint8_t v_res_1331_; lean_object* v_r_1332_; 
v_c_boxed_1330_ = lean_unbox_uint32(v_c_1329_);
lean_dec(v_c_1329_);
v_res_1331_ = lean_string_contains(v_s_1328_, v_c_boxed_1330_);
v_r_1332_ = lean_box(v_res_1331_);
return v_r_1332_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0(lean_object* v_s_1333_, uint32_t v_c_1334_, lean_object* v_inst_1335_, lean_object* v_R_1336_, lean_object* v_a_1337_, uint8_t v_b_1338_, lean_object* v_c_1339_){
_start:
{
uint8_t v___x_1340_; 
v___x_1340_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_1333_, v_c_1334_, v_a_1337_, v_b_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___boxed(lean_object* v_s_1341_, lean_object* v_c_1342_, lean_object* v_inst_1343_, lean_object* v_R_1344_, lean_object* v_a_1345_, lean_object* v_b_1346_, lean_object* v_c_1347_){
_start:
{
uint32_t v_c_boxed_1348_; uint8_t v_b_boxed_1349_; uint8_t v_res_1350_; lean_object* v_r_1351_; 
v_c_boxed_1348_ = lean_unbox_uint32(v_c_1342_);
lean_dec(v_c_1342_);
v_b_boxed_1349_ = lean_unbox(v_b_1346_);
v_res_1350_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0(v_s_1341_, v_c_boxed_1348_, v_inst_1343_, v_R_1344_, v_a_1345_, v_b_boxed_1349_, v_c_1347_);
lean_dec_ref(v_s_1341_);
v_r_1351_ = lean_box(v_res_1350_);
return v_r_1351_;
}
}
LEAN_EXPORT uint8_t l_String_any___redArg(lean_object* v_inst_1352_, lean_object* v_s_1353_, lean_object* v_inst_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = lean_string_utf8_byte_size(v_s_1353_);
v___x_1357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1357_, 0, v_s_1353_);
lean_ctor_set(v___x_1357_, 1, v___x_1355_);
lean_ctor_set(v___x_1357_, 2, v___x_1356_);
v___x_1358_ = l_String_Slice_contains___redArg(v_inst_1352_, v___x_1357_, v_inst_1354_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_String_any___redArg___boxed(lean_object* v_inst_1359_, lean_object* v_s_1360_, lean_object* v_inst_1361_){
_start:
{
uint8_t v_res_1362_; lean_object* v_r_1363_; 
v_res_1362_ = l_String_any___redArg(v_inst_1359_, v_s_1360_, v_inst_1361_);
v_r_1363_ = lean_box(v_res_1362_);
return v_r_1363_;
}
}
LEAN_EXPORT uint8_t l_String_any(lean_object* v_00_u03c1_1364_, lean_object* v_00_u03c3_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_s_1368_, lean_object* v_pat_1369_, lean_object* v_inst_1370_){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1371_ = lean_unsigned_to_nat(0u);
v___x_1372_ = lean_string_utf8_byte_size(v_s_1368_);
v___x_1373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1373_, 0, v_s_1368_);
lean_ctor_set(v___x_1373_, 1, v___x_1371_);
lean_ctor_set(v___x_1373_, 2, v___x_1372_);
v___x_1374_ = l_String_Slice_contains___redArg(v_inst_1367_, v___x_1373_, v_inst_1370_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_String_any___boxed(lean_object* v_00_u03c1_1375_, lean_object* v_00_u03c3_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_s_1379_, lean_object* v_pat_1380_, lean_object* v_inst_1381_){
_start:
{
uint8_t v_res_1382_; lean_object* v_r_1383_; 
v_res_1382_ = l_String_any(v_00_u03c1_1375_, v_00_u03c3_1376_, v_inst_1377_, v_inst_1378_, v_s_1379_, v_pat_1380_, v_inst_1381_);
lean_dec(v_pat_1380_);
lean_dec(v_inst_1377_);
v_r_1383_ = lean_box(v_res_1382_);
return v_r_1383_;
}
}
LEAN_EXPORT uint8_t lean_string_any(lean_object* v_s_1384_, lean_object* v_p_1385_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = lean_string_utf8_byte_size(v_s_1384_);
v___x_1388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1388_, 0, v_s_1384_);
lean_ctor_set(v___x_1388_, 1, v___x_1386_);
lean_ctor_set(v___x_1388_, 2, v___x_1387_);
v___x_1389_ = l_String_Slice_contains___at___00String_anyAux_spec__0(v_p_1385_, v___x_1388_);
lean_dec_ref(v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_anyImpl___boxed(lean_object* v_s_1390_, lean_object* v_p_1391_){
_start:
{
uint8_t v_res_1392_; lean_object* v_r_1393_; 
v_res_1392_ = lean_string_any(v_s_1390_, v_p_1391_);
v_r_1393_ = lean_box(v_res_1392_);
return v_r_1393_;
}
}
LEAN_EXPORT uint8_t l_String_isNat(lean_object* v_s_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = lean_string_utf8_byte_size(v_s_1394_);
v___x_1397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1397_, 0, v_s_1394_);
lean_ctor_set(v___x_1397_, 1, v___x_1395_);
lean_ctor_set(v___x_1397_, 2, v___x_1396_);
v___x_1398_ = l_String_Slice_isNat(v___x_1397_);
lean_dec_ref(v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_String_isNat___boxed(lean_object* v_s_1399_){
_start:
{
uint8_t v_res_1400_; lean_object* v_r_1401_; 
v_res_1400_ = l_String_isNat(v_s_1399_);
v_r_1401_ = lean_box(v_res_1400_);
return v_r_1401_;
}
}
LEAN_EXPORT lean_object* l_String_toNat_x3f(lean_object* v_s_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = lean_string_utf8_byte_size(v_s_1402_);
v___x_1405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1405_, 0, v_s_1402_);
lean_ctor_set(v___x_1405_, 1, v___x_1403_);
lean_ctor_set(v___x_1405_, 2, v___x_1404_);
v___x_1406_ = l_String_Slice_toNat_x3f(v___x_1405_);
lean_dec_ref(v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_String_toNat_x21(lean_object* v_s_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = lean_string_utf8_byte_size(v_s_1407_);
v___x_1410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1410_, 0, v_s_1407_);
lean_ctor_set(v___x_1410_, 1, v___x_1408_);
lean_ctor_set(v___x_1410_, 2, v___x_1409_);
v___x_1411_ = l_String_Slice_toNat_x21(v___x_1410_);
lean_dec_ref(v___x_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_String_toInt_x3f(lean_object* v_s_1412_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1414_ = lean_string_utf8_byte_size(v_s_1412_);
v___x_1415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1415_, 0, v_s_1412_);
lean_ctor_set(v___x_1415_, 1, v___x_1413_);
lean_ctor_set(v___x_1415_, 2, v___x_1414_);
v___x_1416_ = l_String_Slice_toInt_x3f(v___x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT uint8_t l_String_isInt(lean_object* v_s_1417_){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1418_ = lean_unsigned_to_nat(0u);
v___x_1419_ = lean_string_utf8_byte_size(v_s_1417_);
v___x_1420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1420_, 0, v_s_1417_);
lean_ctor_set(v___x_1420_, 1, v___x_1418_);
lean_ctor_set(v___x_1420_, 2, v___x_1419_);
v___x_1421_ = l_String_Slice_isInt(v___x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_String_isInt___boxed(lean_object* v_s_1422_){
_start:
{
uint8_t v_res_1423_; lean_object* v_r_1424_; 
v_res_1423_ = l_String_isInt(v_s_1422_);
v_r_1424_ = lean_box(v_res_1423_);
return v_r_1424_;
}
}
LEAN_EXPORT lean_object* l_String_toInt_x21(lean_object* v_s_1426_){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_string_utf8_byte_size(v_s_1426_);
v___x_1429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1429_, 0, v_s_1426_);
lean_ctor_set(v___x_1429_, 1, v___x_1427_);
lean_ctor_set(v___x_1429_, 2, v___x_1428_);
v___x_1430_ = l_String_Slice_toInt_x3f(v___x_1429_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = l_Int_instInhabited;
v___x_1432_ = ((lean_object*)(l_String_toInt_x21___closed__0));
v___x_1433_ = l_panic___redArg(v___x_1431_, v___x_1432_);
return v___x_1433_;
}
else
{
lean_object* v_val_1434_; 
v_val_1434_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_val_1434_);
lean_dec_ref(v___x_1430_);
return v_val_1434_;
}
}
}
LEAN_EXPORT lean_object* l_String_front_x3f(lean_object* v_s_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = lean_string_utf8_byte_size(v_s_1435_);
v___x_1438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1438_, 0, v_s_1435_);
lean_ctor_set(v___x_1438_, 1, v___x_1436_);
lean_ctor_set(v___x_1438_, 2, v___x_1437_);
v___x_1439_ = l_String_Slice_Pos_get_x3f(v___x_1438_, v___x_1436_);
lean_dec_ref(v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT uint32_t l_String_front(lean_object* v_s_1440_){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = lean_string_utf8_byte_size(v_s_1440_);
v___x_1443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1443_, 0, v_s_1440_);
lean_ctor_set(v___x_1443_, 1, v___x_1441_);
lean_ctor_set(v___x_1443_, 2, v___x_1442_);
v___x_1444_ = l_String_Slice_Pos_get_x3f(v___x_1443_, v___x_1441_);
lean_dec_ref(v___x_1443_);
if (lean_obj_tag(v___x_1444_) == 0)
{
uint32_t v___x_1445_; 
v___x_1445_ = 65;
return v___x_1445_;
}
else
{
lean_object* v_val_1446_; uint32_t v___x_1447_; 
v_val_1446_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_val_1446_);
lean_dec_ref(v___x_1444_);
v___x_1447_ = lean_unbox_uint32(v_val_1446_);
lean_dec(v_val_1446_);
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l_String_front___boxed(lean_object* v_s_1448_){
_start:
{
uint32_t v_res_1449_; lean_object* v_r_1450_; 
v_res_1449_ = l_String_front(v_s_1448_);
v_r_1450_ = lean_box_uint32(v_res_1449_);
return v_r_1450_;
}
}
LEAN_EXPORT uint32_t lean_string_front(lean_object* v_s_1451_){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = lean_string_utf8_byte_size(v_s_1451_);
v___x_1454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1454_, 0, v_s_1451_);
lean_ctor_set(v___x_1454_, 1, v___x_1452_);
lean_ctor_set(v___x_1454_, 2, v___x_1453_);
v___x_1455_ = l_String_Slice_Pos_get_x3f(v___x_1454_, v___x_1452_);
lean_dec_ref(v___x_1454_);
if (lean_obj_tag(v___x_1455_) == 0)
{
uint32_t v___x_1456_; 
v___x_1456_ = 65;
return v___x_1456_;
}
else
{
lean_object* v_val_1457_; uint32_t v___x_1458_; 
v_val_1457_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_val_1457_);
lean_dec_ref(v___x_1455_);
v___x_1458_ = lean_unbox_uint32(v_val_1457_);
lean_dec(v_val_1457_);
return v___x_1458_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_frontImpl___boxed(lean_object* v_s_1459_){
_start:
{
uint32_t v_res_1460_; lean_object* v_r_1461_; 
v_res_1460_ = lean_string_front(v_s_1459_);
v_r_1461_ = lean_box_uint32(v_res_1460_);
return v_r_1461_;
}
}
LEAN_EXPORT lean_object* l_String_back_x3f(lean_object* v_s_1462_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = lean_string_utf8_byte_size(v_s_1462_);
v___x_1465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1465_, 0, v_s_1462_);
lean_ctor_set(v___x_1465_, 1, v___x_1463_);
lean_ctor_set(v___x_1465_, 2, v___x_1464_);
v___x_1466_ = l_String_Slice_Pos_prev_x3f(v___x_1465_, v___x_1464_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v___x_1467_; 
lean_dec_ref(v___x_1465_);
v___x_1467_ = lean_box(0);
return v___x_1467_;
}
else
{
lean_object* v_val_1468_; lean_object* v___x_1469_; 
v_val_1468_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_val_1468_);
lean_dec_ref(v___x_1466_);
v___x_1469_ = l_String_Slice_Pos_get_x3f(v___x_1465_, v_val_1468_);
lean_dec(v_val_1468_);
lean_dec_ref(v___x_1465_);
return v___x_1469_;
}
}
}
LEAN_EXPORT uint32_t l_String_back(lean_object* v_s_1470_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = lean_string_utf8_byte_size(v_s_1470_);
v___x_1473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1473_, 0, v_s_1470_);
lean_ctor_set(v___x_1473_, 1, v___x_1471_);
lean_ctor_set(v___x_1473_, 2, v___x_1472_);
v___x_1474_ = l_String_Slice_Pos_prev_x3f(v___x_1473_, v___x_1472_);
if (lean_obj_tag(v___x_1474_) == 0)
{
uint32_t v___x_1475_; 
lean_dec_ref(v___x_1473_);
v___x_1475_ = 65;
return v___x_1475_;
}
else
{
lean_object* v_val_1476_; lean_object* v___x_1477_; 
v_val_1476_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_val_1476_);
lean_dec_ref(v___x_1474_);
v___x_1477_ = l_String_Slice_Pos_get_x3f(v___x_1473_, v_val_1476_);
lean_dec(v_val_1476_);
lean_dec_ref(v___x_1473_);
if (lean_obj_tag(v___x_1477_) == 0)
{
uint32_t v___x_1478_; 
v___x_1478_ = 65;
return v___x_1478_;
}
else
{
lean_object* v_val_1479_; uint32_t v___x_1480_; 
v_val_1479_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_val_1479_);
lean_dec_ref(v___x_1477_);
v___x_1480_ = lean_unbox_uint32(v_val_1479_);
lean_dec(v_val_1479_);
return v___x_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_back___boxed(lean_object* v_s_1481_){
_start:
{
uint32_t v_res_1482_; lean_object* v_r_1483_; 
v_res_1482_ = l_String_back(v_s_1481_);
v_r_1483_ = lean_box_uint32(v_res_1482_);
return v_r_1483_;
}
}
LEAN_EXPORT lean_object* l_String_lines(lean_object* v_s_1484_){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1485_ = lean_unsigned_to_nat(0u);
v___x_1486_ = lean_string_utf8_byte_size(v_s_1484_);
v___x_1487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1487_, 0, v_s_1484_);
lean_ctor_set(v___x_1487_, 1, v___x_1485_);
lean_ctor_set(v___x_1487_, 2, v___x_1486_);
v___x_1488_ = l_String_Slice_lines(v___x_1487_);
lean_dec_ref(v___x_1487_);
return v___x_1488_;
}
}
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Search(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Search(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Search(builtin);
}
#ifdef __cplusplus
}
#endif
