// Lean compiler output
// Module: Std.Data.DHashMap.Internal.Defs
// Imports: public import Init.Data.Array.Lemmas public import Std.Data.DHashMap.RawDef public import Std.Data.Internal.List.Defs public import Std.Data.DHashMap.Internal.Index public import Init.Data.Nat.Power2.Basic import Init.ByCases import Init.Data.Nat.Power2.Lemmas import Init.Data.List.Impl import Init.Omega
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_noption_none();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_length___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Raw_setValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_toList___redArg(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_numCellsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_numCellsForCapacity___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Std_DHashMap_Internal_toListModel___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DHashMap_Internal_toListModel___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_toListModel___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_toListModel___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_toListModel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__1_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__2_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__3 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__3_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__4 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__4_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__5 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__5_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__6 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__6_value;
static const lean_ctor_object l_Std_DHashMap_Internal_computeSize___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__0_value),((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__1_value)}};
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__7 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__7_value;
static const lean_ctor_object l_Std_DHashMap_Internal_computeSize___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__7_value),((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__2_value),((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__3_value),((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__4_value),((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__5_value)}};
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__8 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__8_value;
static const lean_ctor_object l_Std_DHashMap_Internal_computeSize___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__8_value),((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__6_value)}};
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__9 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__9_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Internal_computeSize___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__10 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_found_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_found_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_found_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_absent_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_absent_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_absent_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scanFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scanFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_scanFrom_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_scanFrom_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scanSpec___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scanSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_found_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_found_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_found_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_empty_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_empty_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_empty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_full_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_full_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_full_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_nextIndex___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_nextIndex___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_nextIndex(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_nextIndex___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_nextIndexNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_nextIndexNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeStart(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeStart___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFrom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_empty_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_empty_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_empty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_full_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_full_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_full_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_findEmptyFrom_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_findEmptyFrom_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmpty___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCellCount___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCellCount(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertNoExpand___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertNoExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertNewAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertNewAt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertNewAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertNewAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_scan_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_scan_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_scan_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_insertNoExpand_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_insertNoExpand_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_insertNoExpand_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Data.DHashMap.Internal.Defs"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 31, .m_data = "Std.DHashMap.Internal.Raw₀.get!"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modifyImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modifyImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alterImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alterImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertIfNewImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertIfNewImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNewImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNewImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getThenInsertIfNewImpl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getThenInsertIfNewImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapStep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapTarget___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapTarget(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__9_value)} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 37, .m_data = "Std.DHashMap.Internal.Raw₀.Const.get!"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___closed__0_value;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modifyImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modifyImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alterImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alterImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getThenInsertIfNewImpl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getThenInsertIfNewImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 34, .m_data = "Std.DHashMap.Internal.Raw₀.getKey!"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___closed__0_value;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_numCellsForCapacity(lean_object* v_capacity_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_2_ = lean_unsigned_to_nat(4u);
v___x_3_ = lean_nat_mul(v_capacity_1_, v___x_2_);
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lean_nat_add(v___x_3_, v___x_4_);
lean_dec(v___x_3_);
v___x_6_ = lean_unsigned_to_nat(3u);
v___x_7_ = lean_nat_div(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_numCellsForCapacity___boxed(lean_object* v_capacity_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_numCellsForCapacity(v_capacity_8_);
lean_dec(v_capacity_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
if (lean_obj_tag(v_a_10_) == 0)
{
lean_object* v___x_12_; 
v___x_12_ = lean_array_to_list(v_a_11_);
return v___x_12_;
}
else
{
lean_object* v_head_13_; lean_object* v_tail_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_head_13_ = lean_ctor_get(v_a_10_, 0);
v_tail_14_ = lean_ctor_get(v_a_10_, 1);
v___x_15_ = l_Std_DHashMap_Internal_AssocList_toList___redArg(v_head_13_);
v___x_16_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_11_, v___x_15_);
v_a_10_ = v_tail_14_;
v_a_11_ = v___x_16_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg___boxed(lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(v_a_18_, v_a_19_);
lean_dec(v_a_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_toListModel___redArg(lean_object* v_buckets_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_array_to_list(v_buckets_23_);
v___x_25_ = ((lean_object*)(l_Std_DHashMap_Internal_toListModel___redArg___closed__0));
v___x_26_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(v___x_24_, v___x_25_);
lean_dec(v___x_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_toListModel(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_buckets_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(v_a_33_, v_a_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___boxed(lean_object* v_00_u03b1_36_, lean_object* v_00_u03b2_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0(v_00_u03b1_36_, v_00_u03b2_37_, v_a_38_, v_a_39_);
lean_dec(v_a_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize___redArg___lam__0(lean_object* v_x1_41_, lean_object* v_x2_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v_x2_42_);
v___x_44_ = lean_nat_add(v_x1_41_, v___x_43_);
lean_dec(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize___redArg___lam__0___boxed(lean_object* v_x1_45_, lean_object* v_x2_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Std_DHashMap_Internal_computeSize___redArg___lam__0(v_x1_45_, v_x2_46_);
lean_dec(v_x2_46_);
lean_dec(v_x1_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize___redArg(lean_object* v_buckets_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_array_get_size(v_buckets_68_);
v___x_71_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_72_ = lean_nat_dec_lt(v___x_69_, v___x_70_);
if (v___x_72_ == 0)
{
lean_dec_ref(v_buckets_68_);
return v___x_69_;
}
else
{
lean_object* v___f_73_; uint8_t v___x_74_; 
v___f_73_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__10));
v___x_74_ = lean_nat_dec_le(v___x_70_, v___x_70_);
if (v___x_74_ == 0)
{
if (v___x_72_ == 0)
{
lean_dec_ref(v_buckets_68_);
return v___x_69_;
}
else
{
size_t v___x_75_; size_t v___x_76_; lean_object* v___x_77_; 
v___x_75_ = ((size_t)0ULL);
v___x_76_ = lean_usize_of_nat(v___x_70_);
v___x_77_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_71_, v___f_73_, v_buckets_68_, v___x_75_, v___x_76_, v___x_69_);
return v___x_77_;
}
}
else
{
size_t v___x_78_; size_t v___x_79_; lean_object* v___x_80_; 
v___x_78_ = ((size_t)0ULL);
v___x_79_ = lean_usize_of_nat(v___x_70_);
v___x_80_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_71_, v___f_73_, v_buckets_68_, v___x_78_, v___x_79_, v___x_69_);
return v___x_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize(lean_object* v_00_u03b1_81_, lean_object* v_00_u03b2_82_, lean_object* v_buckets_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_array_get_size(v_buckets_83_);
v___x_86_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_87_ = lean_nat_dec_lt(v___x_84_, v___x_85_);
if (v___x_87_ == 0)
{
lean_dec_ref(v_buckets_83_);
return v___x_84_;
}
else
{
lean_object* v___f_88_; uint8_t v___x_89_; 
v___f_88_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__10));
v___x_89_ = lean_nat_dec_le(v___x_85_, v___x_85_);
if (v___x_89_ == 0)
{
if (v___x_87_ == 0)
{
lean_dec_ref(v_buckets_83_);
return v___x_84_;
}
else
{
size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; 
v___x_90_ = ((size_t)0ULL);
v___x_91_ = lean_usize_of_nat(v___x_85_);
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_86_, v___f_88_, v_buckets_83_, v___x_90_, v___x_91_, v___x_84_);
return v___x_92_;
}
}
else
{
size_t v___x_93_; size_t v___x_94_; lean_object* v___x_95_; 
v___x_93_ = ((size_t)0ULL);
v___x_94_ = lean_usize_of_nat(v___x_85_);
v___x_95_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_86_, v___f_88_, v_buckets_83_, v___x_93_, v___x_94_, v___x_84_);
return v___x_95_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorIdx___redArg(lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_97_; 
v___x_97_ = lean_unsigned_to_nat(0u);
return v___x_97_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = lean_unsigned_to_nat(1u);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorIdx___redArg___boxed(lean_object* v_x_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorIdx___redArg(v_x_99_);
lean_dec(v_x_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorIdx(lean_object* v_00_u03b1_101_, lean_object* v_inst_102_, lean_object* v_00_u03b2_103_, lean_object* v_query_104_, lean_object* v_n_105_, lean_object* v_x_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorIdx___redArg(v_x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorIdx___boxed(lean_object* v_00_u03b1_108_, lean_object* v_inst_109_, lean_object* v_00_u03b2_110_, lean_object* v_query_111_, lean_object* v_n_112_, lean_object* v_x_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorIdx(v_00_u03b1_108_, v_inst_109_, v_00_u03b2_110_, v_query_111_, v_n_112_, v_x_113_);
lean_dec(v_x_113_);
lean_dec(v_n_112_);
lean_dec(v_query_111_);
lean_dec_ref(v_inst_109_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorElim___redArg(lean_object* v_t_115_, lean_object* v_k_116_){
_start:
{
if (lean_obj_tag(v_t_115_) == 0)
{
lean_object* v_index_117_; lean_object* v_key_118_; lean_object* v_value_119_; lean_object* v___x_120_; 
v_index_117_ = lean_ctor_get(v_t_115_, 0);
lean_inc(v_index_117_);
v_key_118_ = lean_ctor_get(v_t_115_, 1);
lean_inc(v_key_118_);
v_value_119_ = lean_ctor_get(v_t_115_, 2);
lean_inc(v_value_119_);
lean_dec_ref_known(v_t_115_, 3);
v___x_120_ = lean_apply_4(v_k_116_, v_index_117_, v_key_118_, v_value_119_, lean_box(0));
return v___x_120_;
}
else
{
return v_k_116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorElim(lean_object* v_00_u03b1_121_, lean_object* v_inst_122_, lean_object* v_00_u03b2_123_, lean_object* v_query_124_, lean_object* v_n_125_, lean_object* v_motive_126_, lean_object* v_ctorIdx_127_, lean_object* v_t_128_, lean_object* v_h_129_, lean_object* v_k_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorElim___redArg(v_t_128_, v_k_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorElim___boxed(lean_object* v_00_u03b1_132_, lean_object* v_inst_133_, lean_object* v_00_u03b2_134_, lean_object* v_query_135_, lean_object* v_n_136_, lean_object* v_motive_137_, lean_object* v_ctorIdx_138_, lean_object* v_t_139_, lean_object* v_h_140_, lean_object* v_k_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorElim(v_00_u03b1_132_, v_inst_133_, v_00_u03b2_134_, v_query_135_, v_n_136_, v_motive_137_, v_ctorIdx_138_, v_t_139_, v_h_140_, v_k_141_);
lean_dec(v_ctorIdx_138_);
lean_dec(v_n_136_);
lean_dec(v_query_135_);
lean_dec_ref(v_inst_133_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_found_elim___redArg(lean_object* v_t_143_, lean_object* v_found_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorElim___redArg(v_t_143_, v_found_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_found_elim(lean_object* v_00_u03b1_146_, lean_object* v_inst_147_, lean_object* v_00_u03b2_148_, lean_object* v_query_149_, lean_object* v_n_150_, lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_found_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorElim___redArg(v_t_152_, v_found_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_found_elim___boxed(lean_object* v_00_u03b1_156_, lean_object* v_inst_157_, lean_object* v_00_u03b2_158_, lean_object* v_query_159_, lean_object* v_n_160_, lean_object* v_motive_161_, lean_object* v_t_162_, lean_object* v_h_163_, lean_object* v_found_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Std_DHashMap_Internal_Raw_u2080_ScanResult_found_elim(v_00_u03b1_156_, v_inst_157_, v_00_u03b2_158_, v_query_159_, v_n_160_, v_motive_161_, v_t_162_, v_h_163_, v_found_164_);
lean_dec(v_n_160_);
lean_dec(v_query_159_);
lean_dec_ref(v_inst_157_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_absent_elim___redArg(lean_object* v_t_166_, lean_object* v_absent_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorElim___redArg(v_t_166_, v_absent_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_absent_elim(lean_object* v_00_u03b1_169_, lean_object* v_inst_170_, lean_object* v_00_u03b2_171_, lean_object* v_query_172_, lean_object* v_n_173_, lean_object* v_motive_174_, lean_object* v_t_175_, lean_object* v_h_176_, lean_object* v_absent_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Std_DHashMap_Internal_Raw_u2080_ScanResult_ctorElim___redArg(v_t_175_, v_absent_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ScanResult_absent_elim___boxed(lean_object* v_00_u03b1_179_, lean_object* v_inst_180_, lean_object* v_00_u03b2_181_, lean_object* v_query_182_, lean_object* v_n_183_, lean_object* v_motive_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_absent_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_DHashMap_Internal_Raw_u2080_ScanResult_absent_elim(v_00_u03b1_179_, v_inst_180_, v_00_u03b2_181_, v_query_182_, v_n_183_, v_motive_184_, v_t_185_, v_h_186_, v_absent_187_);
lean_dec(v_n_183_);
lean_dec(v_query_182_);
lean_dec_ref(v_inst_180_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scanFrom___redArg(lean_object* v_inst_189_, lean_object* v_m_190_, lean_object* v_query_191_, lean_object* v_i_192_){
_start:
{
lean_object* v_keyArray_197_; lean_object* v_valueArray_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_keyArray_197_ = lean_ctor_get(v_m_190_, 1);
v_valueArray_198_ = lean_ctor_get(v_m_190_, 2);
v___x_199_ = lean_array_get_size(v_keyArray_197_);
v___x_200_ = lean_nat_dec_lt(v_i_192_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_dec(v_i_192_);
lean_dec(v_query_191_);
lean_dec_ref(v_m_190_);
lean_dec_ref(v_inst_189_);
v___x_201_ = lean_box(1);
return v___x_201_;
}
else
{
lean_object* v___x_202_; uint8_t v_isSome_203_; 
v___x_202_ = lean_array_fget_borrowed(v_keyArray_197_, v_i_192_);
v_isSome_203_ = lean_noption_is_some(v___x_202_);
if (v_isSome_203_ == 0)
{
goto v___jp_193_;
}
else
{
lean_object* v___x_204_; uint8_t v_isSome_205_; 
v___x_204_ = lean_array_fget_borrowed(v_valueArray_198_, v_i_192_);
v_isSome_205_ = lean_noption_is_some(v___x_204_);
if (v_isSome_205_ == 0)
{
goto v___jp_193_;
}
else
{
lean_object* v_val_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
lean_inc(v___x_202_);
v_val_206_ = lean_noption_get(v___x_202_);
lean_inc_ref(v_inst_189_);
lean_inc(v_query_191_);
lean_inc(v_val_206_);
v___x_207_ = lean_apply_2(v_inst_189_, v_val_206_, v_query_191_);
v___x_208_ = lean_unbox(v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v_val_206_);
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_add(v_i_192_, v___x_209_);
lean_dec(v_i_192_);
v_i_192_ = v___x_210_;
goto _start;
}
else
{
lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_219_; 
lean_inc(v___x_204_);
lean_dec(v_query_191_);
lean_dec_ref(v_inst_189_);
v_isSharedCheck_219_ = !lean_is_exclusive(v_m_190_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; lean_object* v_unused_221_; lean_object* v_unused_222_; 
v_unused_220_ = lean_ctor_get(v_m_190_, 2);
lean_dec(v_unused_220_);
v_unused_221_ = lean_ctor_get(v_m_190_, 1);
lean_dec(v_unused_221_);
v_unused_222_ = lean_ctor_get(v_m_190_, 0);
lean_dec(v_unused_222_);
v___x_213_ = v_m_190_;
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
else
{
lean_dec(v_m_190_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v_val_215_; lean_object* v___x_217_; 
v_val_215_ = lean_noption_get(v___x_204_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 2, v_val_215_);
lean_ctor_set(v___x_213_, 1, v_val_206_);
lean_ctor_set(v___x_213_, 0, v_i_192_);
v___x_217_ = v___x_213_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_i_192_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_val_206_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v_val_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
}
v___jp_193_:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_nat_add(v_i_192_, v___x_194_);
lean_dec(v_i_192_);
v_i_192_ = v___x_195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scanFrom(lean_object* v_00_u03b1_223_, lean_object* v_00_u03b2_224_, lean_object* v_inst_225_, lean_object* v_m_226_, lean_object* v_query_227_, lean_object* v_i_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Std_DHashMap_Internal_Raw_u2080_scanFrom___redArg(v_inst_225_, v_m_226_, v_query_227_, v_i_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_scanFrom_match__1_splitter___redArg(lean_object* v_x_230_, lean_object* v_h__1_231_, lean_object* v_h__2_232_){
_start:
{
if (lean_obj_tag(v_x_230_) == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v_h__2_232_);
v___x_233_ = lean_box(0);
v___x_234_ = lean_apply_1(v_h__1_231_, v___x_233_);
return v___x_234_;
}
else
{
lean_object* v_val_235_; lean_object* v_fst_236_; lean_object* v_snd_237_; lean_object* v___x_238_; 
lean_dec(v_h__1_231_);
v_val_235_ = lean_ctor_get(v_x_230_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v_x_230_, 1);
v_fst_236_ = lean_ctor_get(v_val_235_, 0);
lean_inc(v_fst_236_);
v_snd_237_ = lean_ctor_get(v_val_235_, 1);
lean_inc(v_snd_237_);
lean_dec(v_val_235_);
v___x_238_ = lean_apply_2(v_h__2_232_, v_fst_236_, v_snd_237_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_scanFrom_match__1_splitter(lean_object* v_00_u03b1_239_, lean_object* v_00_u03b2_240_, lean_object* v_motive_241_, lean_object* v_x_242_, lean_object* v_h__1_243_, lean_object* v_h__2_244_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec(v_h__2_244_);
v___x_245_ = lean_box(0);
v___x_246_ = lean_apply_1(v_h__1_243_, v___x_245_);
return v___x_246_;
}
else
{
lean_object* v_val_247_; lean_object* v_fst_248_; lean_object* v_snd_249_; lean_object* v___x_250_; 
lean_dec(v_h__1_243_);
v_val_247_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_val_247_);
lean_dec_ref_known(v_x_242_, 1);
v_fst_248_ = lean_ctor_get(v_val_247_, 0);
lean_inc(v_fst_248_);
v_snd_249_ = lean_ctor_get(v_val_247_, 1);
lean_inc(v_snd_249_);
lean_dec(v_val_247_);
v___x_250_ = lean_apply_2(v_h__2_244_, v_fst_248_, v_snd_249_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scanSpec___redArg(lean_object* v_inst_251_, lean_object* v_m_252_, lean_object* v_query_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_scanFrom___redArg(v_inst_251_, v_m_252_, v_query_253_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scanSpec(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b2_257_, lean_object* v_inst_258_, lean_object* v_m_259_, lean_object* v_query_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_scanFrom___redArg(v_inst_258_, v_m_259_, v_query_260_, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorIdx___redArg(lean_object* v_x_263_){
_start:
{
switch(lean_obj_tag(v_x_263_))
{
case 0:
{
lean_object* v___x_264_; 
v___x_264_ = lean_unsigned_to_nat(0u);
return v___x_264_;
}
case 1:
{
lean_object* v___x_265_; 
v___x_265_ = lean_unsigned_to_nat(1u);
return v___x_265_;
}
default: 
{
lean_object* v___x_266_; 
v___x_266_ = lean_unsigned_to_nat(2u);
return v___x_266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorIdx___redArg___boxed(lean_object* v_x_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorIdx___redArg(v_x_267_);
lean_dec(v_x_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorIdx(lean_object* v_00_u03b1_269_, lean_object* v_inst_270_, lean_object* v_00_u03b2_271_, lean_object* v_query_272_, lean_object* v_n_273_, lean_object* v_x_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorIdx___redArg(v_x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorIdx___boxed(lean_object* v_00_u03b1_276_, lean_object* v_inst_277_, lean_object* v_00_u03b2_278_, lean_object* v_query_279_, lean_object* v_n_280_, lean_object* v_x_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorIdx(v_00_u03b1_276_, v_inst_277_, v_00_u03b2_278_, v_query_279_, v_n_280_, v_x_281_);
lean_dec(v_x_281_);
lean_dec(v_n_280_);
lean_dec(v_query_279_);
lean_dec_ref(v_inst_277_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim___redArg(lean_object* v_t_283_, lean_object* v_k_284_){
_start:
{
switch(lean_obj_tag(v_t_283_))
{
case 0:
{
lean_object* v_index_285_; lean_object* v_key_286_; lean_object* v_value_287_; lean_object* v___x_288_; 
v_index_285_ = lean_ctor_get(v_t_283_, 0);
lean_inc(v_index_285_);
v_key_286_ = lean_ctor_get(v_t_283_, 1);
lean_inc(v_key_286_);
v_value_287_ = lean_ctor_get(v_t_283_, 2);
lean_inc(v_value_287_);
lean_dec_ref_known(v_t_283_, 3);
v___x_288_ = lean_apply_4(v_k_284_, v_index_285_, v_key_286_, v_value_287_, lean_box(0));
return v___x_288_;
}
case 1:
{
lean_object* v_index_289_; lean_object* v___x_290_; 
v_index_289_ = lean_ctor_get(v_t_283_, 0);
lean_inc(v_index_289_);
lean_dec_ref_known(v_t_283_, 1);
v___x_290_ = lean_apply_1(v_k_284_, v_index_289_);
return v___x_290_;
}
default: 
{
return v_k_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim(lean_object* v_00_u03b1_291_, lean_object* v_inst_292_, lean_object* v_00_u03b2_293_, lean_object* v_query_294_, lean_object* v_n_295_, lean_object* v_motive_296_, lean_object* v_ctorIdx_297_, lean_object* v_t_298_, lean_object* v_h_299_, lean_object* v_k_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim___redArg(v_t_298_, v_k_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim___boxed(lean_object* v_00_u03b1_302_, lean_object* v_inst_303_, lean_object* v_00_u03b2_304_, lean_object* v_query_305_, lean_object* v_n_306_, lean_object* v_motive_307_, lean_object* v_ctorIdx_308_, lean_object* v_t_309_, lean_object* v_h_310_, lean_object* v_k_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim(v_00_u03b1_302_, v_inst_303_, v_00_u03b2_304_, v_query_305_, v_n_306_, v_motive_307_, v_ctorIdx_308_, v_t_309_, v_h_310_, v_k_311_);
lean_dec(v_ctorIdx_308_);
lean_dec(v_n_306_);
lean_dec(v_query_305_);
lean_dec_ref(v_inst_303_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_found_elim___redArg(lean_object* v_t_313_, lean_object* v_found_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim___redArg(v_t_313_, v_found_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_found_elim(lean_object* v_00_u03b1_316_, lean_object* v_inst_317_, lean_object* v_00_u03b2_318_, lean_object* v_query_319_, lean_object* v_n_320_, lean_object* v_motive_321_, lean_object* v_t_322_, lean_object* v_h_323_, lean_object* v_found_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim___redArg(v_t_322_, v_found_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_found_elim___boxed(lean_object* v_00_u03b1_326_, lean_object* v_inst_327_, lean_object* v_00_u03b2_328_, lean_object* v_query_329_, lean_object* v_n_330_, lean_object* v_motive_331_, lean_object* v_t_332_, lean_object* v_h_333_, lean_object* v_found_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_found_elim(v_00_u03b1_326_, v_inst_327_, v_00_u03b2_328_, v_query_329_, v_n_330_, v_motive_331_, v_t_332_, v_h_333_, v_found_334_);
lean_dec(v_n_330_);
lean_dec(v_query_329_);
lean_dec_ref(v_inst_327_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_empty_elim___redArg(lean_object* v_t_336_, lean_object* v_empty_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim___redArg(v_t_336_, v_empty_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_empty_elim(lean_object* v_00_u03b1_339_, lean_object* v_inst_340_, lean_object* v_00_u03b2_341_, lean_object* v_query_342_, lean_object* v_n_343_, lean_object* v_motive_344_, lean_object* v_t_345_, lean_object* v_h_346_, lean_object* v_empty_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim___redArg(v_t_345_, v_empty_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_empty_elim___boxed(lean_object* v_00_u03b1_349_, lean_object* v_inst_350_, lean_object* v_00_u03b2_351_, lean_object* v_query_352_, lean_object* v_n_353_, lean_object* v_motive_354_, lean_object* v_t_355_, lean_object* v_h_356_, lean_object* v_empty_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_empty_elim(v_00_u03b1_349_, v_inst_350_, v_00_u03b2_351_, v_query_352_, v_n_353_, v_motive_354_, v_t_355_, v_h_356_, v_empty_357_);
lean_dec(v_n_353_);
lean_dec(v_query_352_);
lean_dec_ref(v_inst_350_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_full_elim___redArg(lean_object* v_t_359_, lean_object* v_full_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim___redArg(v_t_359_, v_full_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_full_elim(lean_object* v_00_u03b1_362_, lean_object* v_inst_363_, lean_object* v_00_u03b2_364_, lean_object* v_query_365_, lean_object* v_n_366_, lean_object* v_motive_367_, lean_object* v_t_368_, lean_object* v_h_369_, lean_object* v_full_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_ctorElim___redArg(v_t_368_, v_full_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_full_elim___boxed(lean_object* v_00_u03b1_372_, lean_object* v_inst_373_, lean_object* v_00_u03b2_374_, lean_object* v_query_375_, lean_object* v_n_376_, lean_object* v_motive_377_, lean_object* v_t_378_, lean_object* v_h_379_, lean_object* v_full_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_DHashMap_Internal_Raw_u2080_ProbeResult_full_elim(v_00_u03b1_372_, v_inst_373_, v_00_u03b2_374_, v_query_375_, v_n_376_, v_motive_377_, v_t_378_, v_h_379_, v_full_380_);
lean_dec(v_n_376_);
lean_dec(v_query_375_);
lean_dec_ref(v_inst_373_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_nextIndex___redArg(lean_object* v_n_382_, lean_object* v_i_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = lean_nat_add(v_i_383_, v___x_384_);
v___x_386_ = lean_nat_dec_lt(v___x_385_, v_n_382_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
lean_dec(v___x_385_);
v___x_387_ = lean_unsigned_to_nat(0u);
return v___x_387_;
}
else
{
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_nextIndex___redArg___boxed(lean_object* v_n_388_, lean_object* v_i_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_DHashMap_Internal_Raw_u2080_nextIndex___redArg(v_n_388_, v_i_389_);
lean_dec(v_i_389_);
lean_dec(v_n_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_nextIndex(lean_object* v_n_391_, lean_object* v_hn_392_, lean_object* v_i_393_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_add(v_i_393_, v___x_394_);
v___x_396_ = lean_nat_dec_lt(v___x_395_, v_n_391_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
lean_dec(v___x_395_);
v___x_397_ = lean_unsigned_to_nat(0u);
return v___x_397_;
}
else
{
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_nextIndex___boxed(lean_object* v_n_398_, lean_object* v_hn_399_, lean_object* v_i_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_DHashMap_Internal_Raw_u2080_nextIndex(v_n_398_, v_hn_399_, v_i_400_);
lean_dec(v_i_400_);
lean_dec(v_n_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_nextIndexNat(lean_object* v_n_402_, lean_object* v_i_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = lean_nat_add(v_i_403_, v___x_404_);
v___x_406_ = lean_nat_dec_lt(v___x_405_, v_n_402_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
lean_dec(v___x_405_);
v___x_407_ = lean_unsigned_to_nat(0u);
return v___x_407_;
}
else
{
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_nextIndexNat___boxed(lean_object* v_n_408_, lean_object* v_i_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_DHashMap_Internal_Raw_u2080_nextIndexNat(v_n_408_, v_i_409_);
lean_dec(v_i_409_);
lean_dec(v_n_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeStart(lean_object* v_n_411_, uint64_t v_hash_412_){
_start:
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_nat_dec_lt(v___x_413_, v_n_411_);
if (v___x_414_ == 0)
{
return v___x_413_;
}
else
{
uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v_fold_417_; uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; size_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v___x_425_; lean_object* v___x_426_; 
v___x_415_ = 32ULL;
v___x_416_ = lean_uint64_shift_right(v_hash_412_, v___x_415_);
v_fold_417_ = lean_uint64_xor(v_hash_412_, v___x_416_);
v___x_418_ = 16ULL;
v___x_419_ = lean_uint64_shift_right(v_fold_417_, v___x_418_);
v___x_420_ = lean_uint64_xor(v_fold_417_, v___x_419_);
v___x_421_ = lean_uint64_to_usize(v___x_420_);
v___x_422_ = lean_usize_of_nat(v_n_411_);
v___x_423_ = ((size_t)1ULL);
v___x_424_ = lean_usize_sub(v___x_422_, v___x_423_);
v___x_425_ = lean_usize_land(v___x_421_, v___x_424_);
v___x_426_ = lean_usize_to_nat(v___x_425_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeStart___boxed(lean_object* v_n_427_, lean_object* v_hash_428_){
_start:
{
uint64_t v_hash_boxed_429_; lean_object* v_res_430_; 
v_hash_boxed_429_ = lean_unbox_uint64(v_hash_428_);
lean_dec_ref(v_hash_428_);
v_res_430_ = l_Std_DHashMap_Internal_Raw_u2080_probeStart(v_n_427_, v_hash_boxed_429_);
lean_dec(v_n_427_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___redArg(lean_object* v_inst_431_, lean_object* v_m_432_, lean_object* v_query_433_, lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v_zero_437_; uint8_t v_isZero_438_; 
v_zero_437_ = lean_unsigned_to_nat(0u);
v_isZero_438_ = lean_nat_dec_eq(v_x_435_, v_zero_437_);
if (v_isZero_438_ == 1)
{
lean_dec(v_x_436_);
lean_dec(v_x_435_);
lean_dec(v_query_433_);
lean_dec_ref(v_inst_431_);
if (lean_obj_tag(v_x_434_) == 0)
{
lean_object* v___x_439_; 
v___x_439_ = lean_box(2);
return v___x_439_;
}
else
{
lean_object* v_val_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
v_val_440_ = lean_ctor_get(v_x_434_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v_x_434_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_val_440_);
lean_dec(v_x_434_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_val_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
else
{
lean_object* v_keyArray_448_; lean_object* v_valueArray_449_; lean_object* v___x_450_; uint8_t v_isSome_451_; 
v_keyArray_448_ = lean_ctor_get(v_m_432_, 1);
v_valueArray_449_ = lean_ctor_get(v_m_432_, 2);
v___x_450_ = lean_array_fget_borrowed(v_keyArray_448_, v_x_436_);
v_isSome_451_ = lean_noption_is_some(v___x_450_);
if (v_isSome_451_ == 0)
{
lean_dec(v_x_435_);
lean_dec(v_query_433_);
lean_dec_ref(v_inst_431_);
if (lean_obj_tag(v_x_434_) == 0)
{
lean_object* v___x_452_; 
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v_x_436_);
return v___x_452_;
}
else
{
lean_object* v_val_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec(v_x_436_);
v_val_453_ = lean_ctor_get(v_x_434_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v_x_434_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_val_453_);
lean_dec(v_x_434_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_val_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
else
{
lean_object* v_one_461_; lean_object* v_n_462_; lean_object* v___y_464_; 
v_one_461_ = lean_unsigned_to_nat(1u);
v_n_462_ = lean_nat_sub(v_x_435_, v_one_461_);
lean_dec(v_x_435_);
if (v_isSome_451_ == 0)
{
goto v___jp_470_;
}
else
{
lean_object* v___x_472_; uint8_t v_isSome_473_; 
v___x_472_ = lean_array_fget_borrowed(v_valueArray_449_, v_x_436_);
v_isSome_473_ = lean_noption_is_some(v___x_472_);
if (v_isSome_473_ == 0)
{
goto v___jp_470_;
}
else
{
lean_object* v_val_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
lean_inc(v___x_450_);
v_val_474_ = lean_noption_get(v___x_450_);
lean_inc_ref(v_inst_431_);
lean_inc(v_query_433_);
lean_inc(v_val_474_);
v___x_475_ = lean_apply_2(v_inst_431_, v_val_474_, v_query_433_);
v___x_476_ = lean_unbox(v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
lean_dec(v_val_474_);
v___x_477_ = lean_array_get_size(v_keyArray_448_);
v___x_478_ = lean_nat_add(v_x_436_, v_one_461_);
lean_dec(v_x_436_);
v___x_479_ = lean_nat_dec_lt(v___x_478_, v___x_477_);
if (v___x_479_ == 0)
{
lean_dec(v___x_478_);
v_x_435_ = v_n_462_;
v_x_436_ = v_zero_437_;
goto _start;
}
else
{
v_x_435_ = v_n_462_;
v_x_436_ = v___x_478_;
goto _start;
}
}
else
{
lean_object* v_val_482_; lean_object* v___x_483_; 
lean_dec(v_n_462_);
lean_dec(v_x_434_);
lean_dec(v_query_433_);
lean_dec_ref(v_inst_431_);
lean_inc(v___x_472_);
v_val_482_ = lean_noption_get(v___x_472_);
v___x_483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_483_, 0, v_x_436_);
lean_ctor_set(v___x_483_, 1, v_val_474_);
lean_ctor_set(v___x_483_, 2, v_val_482_);
return v___x_483_;
}
}
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_465_ = lean_array_get_size(v_keyArray_448_);
v___x_466_ = lean_nat_add(v_x_436_, v_one_461_);
lean_dec(v_x_436_);
v___x_467_ = lean_nat_dec_lt(v___x_466_, v___x_465_);
if (v___x_467_ == 0)
{
lean_dec(v___x_466_);
v_x_434_ = v___y_464_;
v_x_435_ = v_n_462_;
v_x_436_ = v_zero_437_;
goto _start;
}
else
{
v_x_434_ = v___y_464_;
v_x_435_ = v_n_462_;
v_x_436_ = v___x_466_;
goto _start;
}
}
v___jp_470_:
{
if (lean_obj_tag(v_x_434_) == 0)
{
lean_object* v___x_471_; 
lean_inc(v_x_436_);
v___x_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_471_, 0, v_x_436_);
v___y_464_ = v___x_471_;
goto v___jp_463_;
}
else
{
v___y_464_ = v_x_434_;
goto v___jp_463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___redArg___boxed(lean_object* v_inst_484_, lean_object* v_m_485_, lean_object* v_query_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___redArg(v_inst_484_, v_m_485_, v_query_486_, v_x_487_, v_x_488_, v_x_489_);
lean_dec_ref(v_m_485_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux(lean_object* v_00_u03b1_491_, lean_object* v_00_u03b2_492_, lean_object* v_inst_493_, lean_object* v_m_494_, lean_object* v_query_495_, lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___redArg(v_inst_493_, v_m_494_, v_query_495_, v_x_496_, v_x_497_, v_x_498_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___boxed(lean_object* v_00_u03b1_501_, lean_object* v_00_u03b2_502_, lean_object* v_inst_503_, lean_object* v_m_504_, lean_object* v_query_505_, lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux(v_00_u03b1_501_, v_00_u03b2_502_, v_inst_503_, v_m_504_, v_query_505_, v_x_506_, v_x_507_, v_x_508_, v_x_509_);
lean_dec_ref(v_m_504_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFrom___redArg(lean_object* v_inst_511_, lean_object* v_m_512_, lean_object* v_query_513_, lean_object* v_fuel_514_, lean_object* v_i_515_){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_box(0);
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___redArg(v_inst_511_, v_m_512_, v_query_513_, v___x_516_, v_fuel_514_, v_i_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFrom___redArg___boxed(lean_object* v_inst_518_, lean_object* v_m_519_, lean_object* v_query_520_, lean_object* v_fuel_521_, lean_object* v_i_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_DHashMap_Internal_Raw_u2080_probeFrom___redArg(v_inst_518_, v_m_519_, v_query_520_, v_fuel_521_, v_i_522_);
lean_dec_ref(v_m_519_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFrom(lean_object* v_00_u03b1_524_, lean_object* v_00_u03b2_525_, lean_object* v_inst_526_, lean_object* v_m_527_, lean_object* v_query_528_, lean_object* v_fuel_529_, lean_object* v_i_530_, lean_object* v_hi_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_box(0);
v___x_533_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___redArg(v_inst_526_, v_m_527_, v_query_528_, v___x_532_, v_fuel_529_, v_i_530_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFrom___boxed(lean_object* v_00_u03b1_534_, lean_object* v_00_u03b2_535_, lean_object* v_inst_536_, lean_object* v_m_537_, lean_object* v_query_538_, lean_object* v_fuel_539_, lean_object* v_i_540_, lean_object* v_hi_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_DHashMap_Internal_Raw_u2080_probeFrom(v_00_u03b1_534_, v_00_u03b2_535_, v_inst_536_, v_m_537_, v_query_538_, v_fuel_539_, v_i_540_, v_hi_541_);
lean_dec_ref(v_m_537_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_m_545_, lean_object* v_query_546_){
_start:
{
lean_object* v_keyArray_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint64_t v___x_550_; uint64_t v___x_551_; uint64_t v___x_552_; uint64_t v___x_553_; uint64_t v_fold_554_; uint64_t v___x_555_; uint64_t v___x_556_; uint64_t v___x_557_; size_t v___x_558_; size_t v___x_559_; size_t v___x_560_; size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_keyArray_547_ = lean_ctor_get(v_m_545_, 1);
v___x_548_ = lean_array_get_size(v_keyArray_547_);
lean_inc(v_query_546_);
v___x_549_ = lean_apply_1(v_inst_544_, v_query_546_);
v___x_550_ = 32ULL;
v___x_551_ = lean_unbox_uint64(v___x_549_);
v___x_552_ = lean_uint64_shift_right(v___x_551_, v___x_550_);
v___x_553_ = lean_unbox_uint64(v___x_549_);
lean_dec_ref(v___x_549_);
v_fold_554_ = lean_uint64_xor(v___x_553_, v___x_552_);
v___x_555_ = 16ULL;
v___x_556_ = lean_uint64_shift_right(v_fold_554_, v___x_555_);
v___x_557_ = lean_uint64_xor(v_fold_554_, v___x_556_);
v___x_558_ = lean_uint64_to_usize(v___x_557_);
v___x_559_ = lean_usize_of_nat(v___x_548_);
v___x_560_ = ((size_t)1ULL);
v___x_561_ = lean_usize_sub(v___x_559_, v___x_560_);
v___x_562_ = lean_usize_land(v___x_558_, v___x_561_);
v___x_563_ = lean_usize_to_nat(v___x_562_);
v___x_564_ = lean_box(0);
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___redArg(v_inst_543_, v_m_545_, v_query_546_, v___x_564_, v___x_548_, v___x_563_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg___boxed(lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_m_568_, lean_object* v_query_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_566_, v_inst_567_, v_m_568_, v_query_569_);
lean_dec_ref(v_m_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_m_575_, lean_object* v_query_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_573_, v_inst_574_, v_m_575_, v_query_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___boxed(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_m_582_, lean_object* v_query_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_DHashMap_Internal_Raw_u2080_probe(v_00_u03b1_578_, v_00_u03b2_579_, v_inst_580_, v_inst_581_, v_m_582_, v_query_583_);
lean_dec_ref(v_m_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___redArg(lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_m_587_, lean_object* v_query_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_585_, v_inst_586_, v_m_587_, v_query_588_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_index_590_; lean_object* v_key_591_; lean_object* v_value_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
v_index_590_ = lean_ctor_get(v___x_589_, 0);
v_key_591_ = lean_ctor_get(v___x_589_, 1);
v_value_592_ = lean_ctor_get(v___x_589_, 2);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_589_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_value_592_);
lean_inc(v_key_591_);
lean_inc(v_index_590_);
lean_dec(v___x_589_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_index_590_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_key_591_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_value_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
lean_object* v___x_600_; 
lean_dec(v___x_589_);
v___x_600_ = lean_box(1);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___redArg___boxed(lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_m_603_, lean_object* v_query_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Std_DHashMap_Internal_Raw_u2080_scan___redArg(v_inst_601_, v_inst_602_, v_m_603_, v_query_604_);
lean_dec_ref(v_m_603_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan(lean_object* v_00_u03b1_606_, lean_object* v_00_u03b2_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_m_610_, lean_object* v_query_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_scan___redArg(v_inst_608_, v_inst_609_, v_m_610_, v_query_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___boxed(lean_object* v_00_u03b1_613_, lean_object* v_00_u03b2_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_m_617_, lean_object* v_query_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_DHashMap_Internal_Raw_u2080_scan(v_00_u03b1_613_, v_00_u03b2_614_, v_inst_615_, v_inst_616_, v_m_617_, v_query_618_);
lean_dec_ref(v_m_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorIdx___redArg(lean_object* v_x_620_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
lean_object* v___x_621_; 
v___x_621_ = lean_unsigned_to_nat(0u);
return v___x_621_;
}
else
{
lean_object* v___x_622_; 
v___x_622_ = lean_unsigned_to_nat(1u);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorIdx___redArg___boxed(lean_object* v_x_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorIdx___redArg(v_x_623_);
lean_dec(v_x_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorIdx(lean_object* v_n_625_, lean_object* v_x_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorIdx___redArg(v_x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorIdx___boxed(lean_object* v_n_628_, lean_object* v_x_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorIdx(v_n_628_, v_x_629_);
lean_dec(v_x_629_);
lean_dec(v_n_628_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorElim___redArg(lean_object* v_t_631_, lean_object* v_k_632_){
_start:
{
if (lean_obj_tag(v_t_631_) == 0)
{
lean_object* v_index_633_; lean_object* v___x_634_; 
v_index_633_ = lean_ctor_get(v_t_631_, 0);
lean_inc(v_index_633_);
lean_dec_ref_known(v_t_631_, 1);
v___x_634_ = lean_apply_1(v_k_632_, v_index_633_);
return v___x_634_;
}
else
{
return v_k_632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorElim(lean_object* v_n_635_, lean_object* v_motive_636_, lean_object* v_ctorIdx_637_, lean_object* v_t_638_, lean_object* v_h_639_, lean_object* v_k_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorElim___redArg(v_t_638_, v_k_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorElim___boxed(lean_object* v_n_642_, lean_object* v_motive_643_, lean_object* v_ctorIdx_644_, lean_object* v_t_645_, lean_object* v_h_646_, lean_object* v_k_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorElim(v_n_642_, v_motive_643_, v_ctorIdx_644_, v_t_645_, v_h_646_, v_k_647_);
lean_dec(v_ctorIdx_644_);
lean_dec(v_n_642_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_empty_elim___redArg(lean_object* v_t_649_, lean_object* v_empty_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorElim___redArg(v_t_649_, v_empty_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_empty_elim(lean_object* v_n_652_, lean_object* v_motive_653_, lean_object* v_t_654_, lean_object* v_h_655_, lean_object* v_empty_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorElim___redArg(v_t_654_, v_empty_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_empty_elim___boxed(lean_object* v_n_658_, lean_object* v_motive_659_, lean_object* v_t_660_, lean_object* v_h_661_, lean_object* v_empty_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_empty_elim(v_n_658_, v_motive_659_, v_t_660_, v_h_661_, v_empty_662_);
lean_dec(v_n_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_full_elim___redArg(lean_object* v_t_664_, lean_object* v_full_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorElim___redArg(v_t_664_, v_full_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_full_elim(lean_object* v_n_667_, lean_object* v_motive_668_, lean_object* v_t_669_, lean_object* v_h_670_, lean_object* v_full_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_ctorElim___redArg(v_t_669_, v_full_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_full_elim___boxed(lean_object* v_n_673_, lean_object* v_motive_674_, lean_object* v_t_675_, lean_object* v_h_676_, lean_object* v_full_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_DHashMap_Internal_Raw_u2080_EmptyResult_full_elim(v_n_673_, v_motive_674_, v_t_675_, v_h_676_, v_full_677_);
lean_dec(v_n_673_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object* v_m_679_, lean_object* v_i_680_){
_start:
{
lean_object* v_keyArray_681_; lean_object* v_valueArray_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v_keyArray_681_ = lean_ctor_get(v_m_679_, 1);
v_valueArray_682_ = lean_ctor_get(v_m_679_, 2);
v___x_683_ = lean_array_get_size(v_keyArray_681_);
v___x_684_ = lean_nat_dec_lt(v_i_680_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
lean_dec(v_i_680_);
v___x_685_ = lean_box(1);
return v___x_685_;
}
else
{
lean_object* v___x_686_; uint8_t v_isSome_687_; 
v___x_686_ = lean_array_fget_borrowed(v_keyArray_681_, v_i_680_);
v_isSome_687_ = lean_noption_is_some(v___x_686_);
if (v_isSome_687_ == 0)
{
lean_object* v___x_688_; 
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v_i_680_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; uint8_t v_isSome_690_; 
v___x_689_ = lean_array_fget_borrowed(v_valueArray_682_, v_i_680_);
v_isSome_690_ = lean_noption_is_some(v___x_689_);
if (v_isSome_690_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v_i_680_);
return v___x_691_;
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_nat_add(v_i_680_, v___x_692_);
lean_dec(v_i_680_);
v_i_680_ = v___x_693_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg___boxed(lean_object* v_m_695_, lean_object* v_i_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_m_695_, v_i_696_);
lean_dec_ref(v_m_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_m_700_, lean_object* v_i_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_m_700_, v_i_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___boxed(lean_object* v_00_u03b1_703_, lean_object* v_00_u03b2_704_, lean_object* v_m_705_, lean_object* v_i_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom(v_00_u03b1_703_, v_00_u03b2_704_, v_m_705_, v_i_706_);
lean_dec_ref(v_m_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_findEmptyFrom_match__1_splitter___redArg(lean_object* v_x_708_, lean_object* v_h__1_709_, lean_object* v_h__2_710_){
_start:
{
if (lean_obj_tag(v_x_708_) == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec(v_h__2_710_);
v___x_711_ = lean_box(0);
v___x_712_ = lean_apply_1(v_h__1_709_, v___x_711_);
return v___x_712_;
}
else
{
lean_object* v_val_713_; lean_object* v___x_714_; 
lean_dec(v_h__1_709_);
v_val_713_ = lean_ctor_get(v_x_708_, 0);
lean_inc(v_val_713_);
lean_dec_ref_known(v_x_708_, 1);
v___x_714_ = lean_apply_1(v_h__2_710_, v_val_713_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_findEmptyFrom_match__1_splitter(lean_object* v_00_u03b1_715_, lean_object* v_00_u03b2_716_, lean_object* v_motive_717_, lean_object* v_x_718_, lean_object* v_h__1_719_, lean_object* v_h__2_720_){
_start:
{
if (lean_obj_tag(v_x_718_) == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec(v_h__2_720_);
v___x_721_ = lean_box(0);
v___x_722_ = lean_apply_1(v_h__1_719_, v___x_721_);
return v___x_722_;
}
else
{
lean_object* v_val_723_; lean_object* v___x_724_; 
lean_dec(v_h__1_719_);
v_val_723_ = lean_ctor_get(v_x_718_, 0);
lean_inc(v_val_723_);
lean_dec_ref_known(v_x_718_, 1);
v___x_724_ = lean_apply_1(v_h__2_720_, v_val_723_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmpty___redArg(lean_object* v_m_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_m_725_, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmpty___redArg___boxed(lean_object* v_m_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_DHashMap_Internal_Raw_u2080_findEmpty___redArg(v_m_728_);
lean_dec_ref(v_m_728_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmpty(lean_object* v_00_u03b1_730_, lean_object* v_00_u03b2_731_, lean_object* v_m_732_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_m_732_, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmpty___boxed(lean_object* v_00_u03b1_735_, lean_object* v_00_u03b2_736_, lean_object* v_m_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_DHashMap_Internal_Raw_u2080_findEmpty(v_00_u03b1_735_, v_00_u03b2_736_, v_m_737_);
lean_dec_ref(v_m_737_);
return v_res_738_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0(void){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = lean_noption_none();
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object* v_cellCount_740_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0);
v___x_742_ = lean_mk_array(v_cellCount_740_, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray(lean_object* v_00_u03b1_743_, lean_object* v_cellCount_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object* v_cellCount_746_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0);
v___x_748_ = lean_mk_array(v_cellCount_746_, v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray(lean_object* v_00_u03b1_749_, lean_object* v_00_u03b2_750_, lean_object* v_cellCount_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCellCount___redArg(lean_object* v_cellCount_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_754_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_753_);
v___x_755_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_753_);
v___x_756_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_753_);
v___x_757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_757_, 0, v___x_754_);
lean_ctor_set(v___x_757_, 1, v___x_755_);
lean_ctor_set(v___x_757_, 2, v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCellCount(lean_object* v_00_u03b1_758_, lean_object* v_00_u03b2_759_, lean_object* v_cellCount_760_, lean_object* v_h_761_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_762_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_760_);
v___x_763_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_760_);
v___x_764_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_760_);
v___x_765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_765_, 0, v___x_762_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg(lean_object* v_capacity_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v_cellCount_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_767_ = lean_unsigned_to_nat(4u);
v___x_768_ = lean_nat_mul(v_capacity_766_, v___x_767_);
v___x_769_ = lean_unsigned_to_nat(2u);
v___x_770_ = lean_nat_add(v___x_768_, v___x_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_unsigned_to_nat(3u);
v___x_772_ = lean_nat_div(v___x_770_, v___x_771_);
lean_dec(v___x_770_);
v_cellCount_773_ = l_Nat_nextPowerOfTwo(v___x_772_);
lean_dec(v___x_772_);
v___x_774_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_773_);
v___x_775_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_773_);
v___x_776_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_773_);
v___x_777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_777_, 0, v___x_774_);
lean_ctor_set(v___x_777_, 1, v___x_775_);
lean_ctor_set(v___x_777_, 2, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg(v_capacity_778_);
lean_dec(v_capacity_778_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity(lean_object* v_00_u03b1_780_, lean_object* v_00_u03b2_781_, lean_object* v_capacity_782_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v_cellCount_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_783_ = lean_unsigned_to_nat(4u);
v___x_784_ = lean_nat_mul(v_capacity_782_, v___x_783_);
v___x_785_ = lean_unsigned_to_nat(2u);
v___x_786_ = lean_nat_add(v___x_784_, v___x_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_unsigned_to_nat(3u);
v___x_788_ = lean_nat_div(v___x_786_, v___x_787_);
lean_dec(v___x_786_);
v_cellCount_789_ = l_Nat_nextPowerOfTwo(v___x_788_);
lean_dec(v___x_788_);
v___x_790_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_789_);
v___x_791_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_789_);
v___x_792_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_789_);
v___x_793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_793_, 0, v___x_790_);
lean_ctor_set(v___x_793_, 1, v___x_791_);
lean_ctor_set(v___x_793_, 2, v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___boxed(lean_object* v_00_u03b1_794_, lean_object* v_00_u03b2_795_, lean_object* v_capacity_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity(v_00_u03b1_794_, v_00_u03b2_795_, v_capacity_796_);
lean_dec(v_capacity_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertNoExpand___redArg(lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_m_800_, lean_object* v_a_801_, lean_object* v_b_802_){
_start:
{
lean_object* v_i_804_; lean_object* v___x_809_; 
lean_inc(v_a_801_);
v___x_809_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_798_, v_inst_799_, v_m_800_, v_a_801_);
switch(lean_obj_tag(v___x_809_))
{
case 0:
{
lean_object* v_index_810_; lean_object* v_size_811_; lean_object* v___x_812_; 
v_index_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_index_810_);
lean_dec_ref_known(v___x_809_, 3);
v_size_811_ = lean_ctor_get(v_m_800_, 0);
lean_inc(v_size_811_);
v___x_812_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_800_, v_size_811_, v_index_810_, v_a_801_, v_b_802_);
lean_dec(v_index_810_);
return v___x_812_;
}
case 1:
{
lean_object* v_index_813_; 
v_index_813_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_index_813_);
lean_dec_ref_known(v___x_809_, 1);
v_i_804_ = v_index_813_;
goto v___jp_803_;
}
default: 
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_m_800_, v___x_814_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_index_816_; 
v_index_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_index_816_);
lean_dec_ref_known(v___x_815_, 1);
v_i_804_ = v_index_816_;
goto v___jp_803_;
}
else
{
lean_dec(v_b_802_);
lean_dec(v_a_801_);
return v_m_800_;
}
}
}
v___jp_803_:
{
lean_object* v_size_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_size_805_ = lean_ctor_get(v_m_800_, 0);
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_add(v_size_805_, v___x_806_);
v___x_808_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_800_, v___x_807_, v_i_804_, v_a_801_, v_b_802_);
lean_dec(v_i_804_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertNoExpand(lean_object* v_00_u03b1_817_, lean_object* v_00_u03b2_818_, lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_m_821_, lean_object* v_a_822_, lean_object* v_b_823_){
_start:
{
lean_object* v_i_825_; lean_object* v___x_830_; 
lean_inc(v_a_822_);
v___x_830_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_819_, v_inst_820_, v_m_821_, v_a_822_);
switch(lean_obj_tag(v___x_830_))
{
case 0:
{
lean_object* v_index_831_; lean_object* v_size_832_; lean_object* v___x_833_; 
v_index_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_index_831_);
lean_dec_ref_known(v___x_830_, 3);
v_size_832_ = lean_ctor_get(v_m_821_, 0);
lean_inc(v_size_832_);
v___x_833_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_821_, v_size_832_, v_index_831_, v_a_822_, v_b_823_);
lean_dec(v_index_831_);
return v___x_833_;
}
case 1:
{
lean_object* v_index_834_; 
v_index_834_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_index_834_);
lean_dec_ref_known(v___x_830_, 1);
v_i_825_ = v_index_834_;
goto v___jp_824_;
}
default: 
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_m_821_, v___x_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_index_837_; 
v_index_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_index_837_);
lean_dec_ref_known(v___x_836_, 1);
v_i_825_ = v_index_837_;
goto v___jp_824_;
}
else
{
lean_dec(v_b_823_);
lean_dec(v_a_822_);
return v_m_821_;
}
}
}
v___jp_824_:
{
lean_object* v_size_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_size_826_ = lean_ctor_get(v_m_821_, 0);
v___x_827_ = lean_unsigned_to_nat(1u);
v___x_828_ = lean_nat_add(v_size_826_, v___x_827_);
v___x_829_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_821_, v___x_828_, v_i_825_, v_a_822_, v_b_823_);
lean_dec(v_i_825_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg___lam__0(lean_object* v_inst_838_, lean_object* v_inst_839_, lean_object* v_x1_840_, lean_object* v_x2_841_, lean_object* v_x3_842_){
_start:
{
lean_object* v_i_844_; lean_object* v___x_849_; 
lean_inc(v_x2_841_);
v___x_849_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_838_, v_inst_839_, v_x1_840_, v_x2_841_);
switch(lean_obj_tag(v___x_849_))
{
case 0:
{
lean_object* v_index_850_; lean_object* v_size_851_; lean_object* v___x_852_; 
v_index_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_index_850_);
lean_dec_ref_known(v___x_849_, 3);
v_size_851_ = lean_ctor_get(v_x1_840_, 0);
lean_inc(v_size_851_);
v___x_852_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x1_840_, v_size_851_, v_index_850_, v_x2_841_, v_x3_842_);
lean_dec(v_index_850_);
return v___x_852_;
}
case 1:
{
lean_object* v_index_853_; 
v_index_853_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_index_853_);
lean_dec_ref_known(v___x_849_, 1);
v_i_844_ = v_index_853_;
goto v___jp_843_;
}
default: 
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_x1_840_, v___x_854_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_index_856_; 
v_index_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_index_856_);
lean_dec_ref_known(v___x_855_, 1);
v_i_844_ = v_index_856_;
goto v___jp_843_;
}
else
{
lean_dec(v_x3_842_);
lean_dec(v_x2_841_);
return v_x1_840_;
}
}
}
v___jp_843_:
{
lean_object* v_size_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_size_845_ = lean_ctor_get(v_x1_840_, 0);
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = lean_nat_add(v_size_845_, v___x_846_);
v___x_848_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x1_840_, v___x_847_, v_i_844_, v_x2_841_, v_x3_842_);
lean_dec(v_i_844_);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_m_859_){
_start:
{
lean_object* v_keyArray_860_; lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_cellCount_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v_target_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_keyArray_860_ = lean_ctor_get(v_m_859_, 1);
v___f_861_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_expand___redArg___lam__0), 5, 2);
lean_closure_set(v___f_861_, 0, v_inst_857_);
lean_closure_set(v___f_861_, 1, v_inst_858_);
v___x_862_ = lean_array_get_size(v_keyArray_860_);
v___x_863_ = lean_unsigned_to_nat(2u);
v_cellCount_864_ = lean_nat_mul(v___x_862_, v___x_863_);
v___x_865_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_864_);
v___x_866_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_864_);
v___x_867_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_864_);
v_target_868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_868_, 0, v___x_865_);
lean_ctor_set(v_target_868_, 1, v___x_866_);
lean_ctor_set(v_target_868_, 2, v___x_867_);
v___x_869_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_870_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_869_, v___f_861_, v_target_868_, v_m_859_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand(lean_object* v_00_u03b1_871_, lean_object* v_00_u03b2_872_, lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_m_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_873_, v_inst_874_, v_m_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary___redArg(lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_m_879_){
_start:
{
lean_object* v_size_880_; lean_object* v_keyArray_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v_size_880_ = lean_ctor_get(v_m_879_, 0);
v_keyArray_881_ = lean_ctor_get(v_m_879_, 1);
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_883_ = lean_nat_add(v_size_880_, v___x_882_);
v___x_884_ = lean_array_get_size(v_keyArray_881_);
v___x_885_ = lean_nat_dec_lt(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
lean_dec(v___x_883_);
v___x_886_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_877_, v_inst_878_, v_m_879_);
return v___x_886_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_887_ = lean_unsigned_to_nat(4u);
v___x_888_ = lean_nat_mul(v___x_883_, v___x_887_);
lean_dec(v___x_883_);
v___x_889_ = lean_unsigned_to_nat(3u);
v___x_890_ = lean_nat_mul(v___x_884_, v___x_889_);
v___x_891_ = lean_nat_dec_le(v___x_888_, v___x_890_);
lean_dec(v___x_890_);
lean_dec(v___x_888_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
v___x_892_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_877_, v_inst_878_, v_m_879_);
return v___x_892_;
}
else
{
lean_dec_ref(v_inst_878_);
lean_dec_ref(v_inst_877_);
return v_m_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary(lean_object* v_00_u03b1_893_, lean_object* v_00_u03b2_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_m_897_){
_start:
{
lean_object* v_size_898_; lean_object* v_keyArray_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v_size_898_ = lean_ctor_get(v_m_897_, 0);
v_keyArray_899_ = lean_ctor_get(v_m_897_, 1);
v___x_900_ = lean_unsigned_to_nat(1u);
v___x_901_ = lean_nat_add(v_size_898_, v___x_900_);
v___x_902_ = lean_array_get_size(v_keyArray_899_);
v___x_903_ = lean_nat_dec_lt(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_dec(v___x_901_);
v___x_904_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_895_, v_inst_896_, v_m_897_);
return v___x_904_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_905_ = lean_unsigned_to_nat(4u);
v___x_906_ = lean_nat_mul(v___x_901_, v___x_905_);
lean_dec(v___x_901_);
v___x_907_ = lean_unsigned_to_nat(3u);
v___x_908_ = lean_nat_mul(v___x_902_, v___x_907_);
v___x_909_ = lean_nat_dec_le(v___x_906_, v___x_908_);
lean_dec(v___x_908_);
lean_dec(v___x_906_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
v___x_910_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_895_, v_inst_896_, v_m_897_);
return v___x_910_;
}
else
{
lean_dec_ref(v_inst_896_);
lean_dec_ref(v_inst_895_);
return v_m_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertNewAt___redArg(lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_m_913_, lean_object* v_i_914_, lean_object* v_a_915_, lean_object* v_b_916_){
_start:
{
lean_object* v___y_918_; lean_object* v_i_919_; lean_object* v_size_934_; lean_object* v_keyArray_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_size_934_ = lean_ctor_get(v_m_913_, 0);
v_keyArray_935_ = lean_ctor_get(v_m_913_, 1);
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_add(v_size_934_, v___x_936_);
v___x_938_ = lean_array_get_size(v_keyArray_935_);
v___x_939_ = lean_nat_dec_lt(v___x_937_, v___x_938_);
if (v___x_939_ == 0)
{
lean_dec(v___x_937_);
goto v___jp_924_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_940_ = lean_unsigned_to_nat(4u);
v___x_941_ = lean_nat_mul(v___x_937_, v___x_940_);
v___x_942_ = lean_unsigned_to_nat(3u);
v___x_943_ = lean_nat_mul(v___x_938_, v___x_942_);
v___x_944_ = lean_nat_dec_le(v___x_941_, v___x_943_);
lean_dec(v___x_943_);
lean_dec(v___x_941_);
if (v___x_944_ == 0)
{
lean_dec(v___x_937_);
goto v___jp_924_;
}
else
{
lean_object* v___x_945_; 
lean_dec_ref(v_inst_912_);
lean_dec_ref(v_inst_911_);
v___x_945_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_913_, v___x_937_, v_i_914_, v_a_915_, v_b_916_);
return v___x_945_;
}
}
v___jp_917_:
{
lean_object* v_size_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_size_920_ = lean_ctor_get(v___y_918_, 0);
v___x_921_ = lean_unsigned_to_nat(1u);
v___x_922_ = lean_nat_add(v_size_920_, v___x_921_);
v___x_923_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_918_, v___x_922_, v_i_919_, v_a_915_, v_b_916_);
lean_dec(v_i_919_);
return v___x_923_;
}
v___jp_924_:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_inc_ref(v_inst_912_);
lean_inc_ref(v_inst_911_);
v___x_925_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_911_, v_inst_912_, v_m_913_);
lean_inc(v_a_915_);
v___x_926_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_911_, v_inst_912_, v___x_925_, v_a_915_);
switch(lean_obj_tag(v___x_926_))
{
case 0:
{
lean_object* v_index_927_; lean_object* v_size_928_; lean_object* v___x_929_; 
v_index_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_index_927_);
lean_dec_ref_known(v___x_926_, 3);
v_size_928_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_size_928_);
v___x_929_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_925_, v_size_928_, v_index_927_, v_a_915_, v_b_916_);
lean_dec(v_index_927_);
return v___x_929_;
}
case 1:
{
lean_object* v_index_930_; 
v_index_930_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_index_930_);
lean_dec_ref_known(v___x_926_, 1);
v___y_918_ = v___x_925_;
v_i_919_ = v_index_930_;
goto v___jp_917_;
}
default: 
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_932_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_925_, v___x_931_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_index_933_; 
v_index_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_index_933_);
lean_dec_ref_known(v___x_932_, 1);
v___y_918_ = v___x_925_;
v_i_919_ = v_index_933_;
goto v___jp_917_;
}
else
{
lean_dec(v_b_916_);
lean_dec(v_a_915_);
return v___x_925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertNewAt___redArg___boxed(lean_object* v_inst_946_, lean_object* v_inst_947_, lean_object* v_m_948_, lean_object* v_i_949_, lean_object* v_a_950_, lean_object* v_b_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_DHashMap_Internal_Raw_u2080_insertNewAt___redArg(v_inst_946_, v_inst_947_, v_m_948_, v_i_949_, v_a_950_, v_b_951_);
lean_dec(v_i_949_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertNewAt(lean_object* v_00_u03b1_953_, lean_object* v_00_u03b2_954_, lean_object* v_inst_955_, lean_object* v_inst_956_, lean_object* v_m_957_, lean_object* v_i_958_, lean_object* v_a_959_, lean_object* v_b_960_){
_start:
{
lean_object* v___y_962_; lean_object* v_i_963_; lean_object* v_size_978_; lean_object* v_keyArray_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_size_978_ = lean_ctor_get(v_m_957_, 0);
v_keyArray_979_ = lean_ctor_get(v_m_957_, 1);
v___x_980_ = lean_unsigned_to_nat(1u);
v___x_981_ = lean_nat_add(v_size_978_, v___x_980_);
v___x_982_ = lean_array_get_size(v_keyArray_979_);
v___x_983_ = lean_nat_dec_lt(v___x_981_, v___x_982_);
if (v___x_983_ == 0)
{
lean_dec(v___x_981_);
goto v___jp_968_;
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_984_ = lean_unsigned_to_nat(4u);
v___x_985_ = lean_nat_mul(v___x_981_, v___x_984_);
v___x_986_ = lean_unsigned_to_nat(3u);
v___x_987_ = lean_nat_mul(v___x_982_, v___x_986_);
v___x_988_ = lean_nat_dec_le(v___x_985_, v___x_987_);
lean_dec(v___x_987_);
lean_dec(v___x_985_);
if (v___x_988_ == 0)
{
lean_dec(v___x_981_);
goto v___jp_968_;
}
else
{
lean_object* v___x_989_; 
lean_dec_ref(v_inst_956_);
lean_dec_ref(v_inst_955_);
v___x_989_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_957_, v___x_981_, v_i_958_, v_a_959_, v_b_960_);
return v___x_989_;
}
}
v___jp_961_:
{
lean_object* v_size_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_size_964_ = lean_ctor_get(v___y_962_, 0);
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = lean_nat_add(v_size_964_, v___x_965_);
v___x_967_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_962_, v___x_966_, v_i_963_, v_a_959_, v_b_960_);
lean_dec(v_i_963_);
return v___x_967_;
}
v___jp_968_:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
lean_inc_ref(v_inst_956_);
lean_inc_ref(v_inst_955_);
v___x_969_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_955_, v_inst_956_, v_m_957_);
lean_inc(v_a_959_);
v___x_970_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_955_, v_inst_956_, v___x_969_, v_a_959_);
switch(lean_obj_tag(v___x_970_))
{
case 0:
{
lean_object* v_index_971_; lean_object* v_size_972_; lean_object* v___x_973_; 
v_index_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_index_971_);
lean_dec_ref_known(v___x_970_, 3);
v_size_972_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_size_972_);
v___x_973_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_969_, v_size_972_, v_index_971_, v_a_959_, v_b_960_);
lean_dec(v_index_971_);
return v___x_973_;
}
case 1:
{
lean_object* v_index_974_; 
v_index_974_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_index_974_);
lean_dec_ref_known(v___x_970_, 1);
v___y_962_ = v___x_969_;
v_i_963_ = v_index_974_;
goto v___jp_961_;
}
default: 
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_969_, v___x_975_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_index_977_; 
v_index_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_index_977_);
lean_dec_ref_known(v___x_976_, 1);
v___y_962_ = v___x_969_;
v_i_963_ = v_index_977_;
goto v___jp_961_;
}
else
{
lean_dec(v_b_960_);
lean_dec(v_a_959_);
return v___x_969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertNewAt___boxed(lean_object* v_00_u03b1_990_, lean_object* v_00_u03b2_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_m_994_, lean_object* v_i_995_, lean_object* v_a_996_, lean_object* v_b_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_DHashMap_Internal_Raw_u2080_insertNewAt(v_00_u03b1_990_, v_00_u03b2_991_, v_inst_992_, v_inst_993_, v_m_994_, v_i_995_, v_a_996_, v_b_997_);
lean_dec(v_i_995_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertImpl___redArg(lean_object* v_inst_999_, lean_object* v_inst_1000_, lean_object* v_m_1001_, lean_object* v_a_1002_, lean_object* v_b_1003_){
_start:
{
lean_object* v___y_1005_; lean_object* v_i_1006_; lean_object* v___y_1022_; lean_object* v_i_1023_; lean_object* v___y_1029_; lean_object* v___x_1038_; 
lean_inc(v_a_1002_);
lean_inc_ref(v_inst_1000_);
lean_inc_ref(v_inst_999_);
v___x_1038_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_999_, v_inst_1000_, v_m_1001_, v_a_1002_);
switch(lean_obj_tag(v___x_1038_))
{
case 0:
{
lean_object* v_index_1039_; lean_object* v_size_1040_; lean_object* v___x_1041_; 
lean_dec_ref(v_inst_1000_);
lean_dec_ref(v_inst_999_);
v_index_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_index_1039_);
lean_dec_ref_known(v___x_1038_, 3);
v_size_1040_ = lean_ctor_get(v_m_1001_, 0);
lean_inc(v_size_1040_);
v___x_1041_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1001_, v_size_1040_, v_index_1039_, v_a_1002_, v_b_1003_);
lean_dec(v_index_1039_);
return v___x_1041_;
}
case 1:
{
lean_object* v_index_1042_; lean_object* v_size_1043_; lean_object* v_keyArray_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_index_1042_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_index_1042_);
lean_dec_ref_known(v___x_1038_, 1);
v_size_1043_ = lean_ctor_get(v_m_1001_, 0);
v_keyArray_1044_ = lean_ctor_get(v_m_1001_, 1);
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_nat_add(v_size_1043_, v___x_1045_);
v___x_1047_ = lean_array_get_size(v_keyArray_1044_);
v___x_1048_ = lean_nat_dec_lt(v___x_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_dec(v___x_1046_);
lean_dec(v_index_1042_);
goto v___jp_1011_;
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1049_ = lean_unsigned_to_nat(4u);
v___x_1050_ = lean_nat_mul(v___x_1046_, v___x_1049_);
v___x_1051_ = lean_unsigned_to_nat(3u);
v___x_1052_ = lean_nat_mul(v___x_1047_, v___x_1051_);
v___x_1053_ = lean_nat_dec_le(v___x_1050_, v___x_1052_);
lean_dec(v___x_1052_);
lean_dec(v___x_1050_);
if (v___x_1053_ == 0)
{
lean_dec(v___x_1046_);
lean_dec(v_index_1042_);
goto v___jp_1011_;
}
else
{
lean_object* v___x_1054_; 
lean_dec_ref(v_inst_1000_);
lean_dec_ref(v_inst_999_);
v___x_1054_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1001_, v___x_1046_, v_index_1042_, v_a_1002_, v_b_1003_);
lean_dec(v_index_1042_);
return v___x_1054_;
}
}
}
default: 
{
lean_object* v_size_1055_; lean_object* v_keyArray_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v_size_1055_ = lean_ctor_get(v_m_1001_, 0);
v_keyArray_1056_ = lean_ctor_get(v_m_1001_, 1);
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v_size_1055_, v___x_1057_);
v___x_1059_ = lean_array_get_size(v_keyArray_1056_);
v___x_1060_ = lean_nat_dec_lt(v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_dec(v___x_1058_);
lean_inc_ref(v_inst_1000_);
lean_inc_ref(v_inst_999_);
v___x_1061_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_999_, v_inst_1000_, v_m_1001_);
v___y_1029_ = v___x_1061_;
goto v___jp_1028_;
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1062_ = lean_unsigned_to_nat(4u);
v___x_1063_ = lean_nat_mul(v___x_1058_, v___x_1062_);
lean_dec(v___x_1058_);
v___x_1064_ = lean_unsigned_to_nat(3u);
v___x_1065_ = lean_nat_mul(v___x_1059_, v___x_1064_);
v___x_1066_ = lean_nat_dec_le(v___x_1063_, v___x_1065_);
lean_dec(v___x_1065_);
lean_dec(v___x_1063_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
lean_inc_ref(v_inst_1000_);
lean_inc_ref(v_inst_999_);
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_999_, v_inst_1000_, v_m_1001_);
v___y_1029_ = v___x_1067_;
goto v___jp_1028_;
}
else
{
v___y_1029_ = v_m_1001_;
goto v___jp_1028_;
}
}
}
}
v___jp_1004_:
{
lean_object* v_size_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_size_1007_ = lean_ctor_get(v___y_1005_, 0);
v___x_1008_ = lean_unsigned_to_nat(1u);
v___x_1009_ = lean_nat_add(v_size_1007_, v___x_1008_);
v___x_1010_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1005_, v___x_1009_, v_i_1006_, v_a_1002_, v_b_1003_);
lean_dec(v_i_1006_);
return v___x_1010_;
}
v___jp_1011_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_inc_ref(v_inst_1000_);
lean_inc_ref(v_inst_999_);
v___x_1012_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_999_, v_inst_1000_, v_m_1001_);
lean_inc(v_a_1002_);
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_999_, v_inst_1000_, v___x_1012_, v_a_1002_);
switch(lean_obj_tag(v___x_1013_))
{
case 0:
{
lean_object* v_index_1014_; lean_object* v_size_1015_; lean_object* v___x_1016_; 
v_index_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_index_1014_);
lean_dec_ref_known(v___x_1013_, 3);
v_size_1015_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_size_1015_);
v___x_1016_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1012_, v_size_1015_, v_index_1014_, v_a_1002_, v_b_1003_);
lean_dec(v_index_1014_);
return v___x_1016_;
}
case 1:
{
lean_object* v_index_1017_; 
v_index_1017_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_index_1017_);
lean_dec_ref_known(v___x_1013_, 1);
v___y_1005_ = v___x_1012_;
v_i_1006_ = v_index_1017_;
goto v___jp_1004_;
}
default: 
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1012_, v___x_1018_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_index_1020_; 
v_index_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_index_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___y_1005_ = v___x_1012_;
v_i_1006_ = v_index_1020_;
goto v___jp_1004_;
}
else
{
lean_dec(v_b_1003_);
lean_dec(v_a_1002_);
return v___x_1012_;
}
}
}
}
v___jp_1021_:
{
lean_object* v_size_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_size_1024_ = lean_ctor_get(v___y_1022_, 0);
v___x_1025_ = lean_unsigned_to_nat(1u);
v___x_1026_ = lean_nat_add(v_size_1024_, v___x_1025_);
v___x_1027_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1022_, v___x_1026_, v_i_1023_, v_a_1002_, v_b_1003_);
lean_dec(v_i_1023_);
return v___x_1027_;
}
v___jp_1028_:
{
lean_object* v___x_1030_; 
lean_inc(v_a_1002_);
v___x_1030_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_999_, v_inst_1000_, v___y_1029_, v_a_1002_);
switch(lean_obj_tag(v___x_1030_))
{
case 0:
{
lean_object* v_index_1031_; lean_object* v_size_1032_; lean_object* v___x_1033_; 
v_index_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_index_1031_);
lean_dec_ref_known(v___x_1030_, 3);
v_size_1032_ = lean_ctor_get(v___y_1029_, 0);
lean_inc(v_size_1032_);
v___x_1033_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1029_, v_size_1032_, v_index_1031_, v_a_1002_, v_b_1003_);
lean_dec(v_index_1031_);
return v___x_1033_;
}
case 1:
{
lean_object* v_index_1034_; 
v_index_1034_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_index_1034_);
lean_dec_ref_known(v___x_1030_, 1);
v___y_1022_ = v___y_1029_;
v_i_1023_ = v_index_1034_;
goto v___jp_1021_;
}
default: 
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1029_, v___x_1035_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_index_1037_; 
v_index_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_index_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v___y_1022_ = v___y_1029_;
v_i_1023_ = v_index_1037_;
goto v___jp_1021_;
}
else
{
lean_dec(v_b_1003_);
lean_dec(v_a_1002_);
return v___y_1029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertImpl(lean_object* v_00_u03b1_1068_, lean_object* v_00_u03b2_1069_, lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v_m_1072_, lean_object* v_a_1073_, lean_object* v_b_1074_){
_start:
{
lean_object* v___y_1076_; lean_object* v_i_1077_; lean_object* v___y_1093_; lean_object* v_i_1094_; lean_object* v___y_1100_; lean_object* v___x_1109_; 
lean_inc(v_a_1073_);
lean_inc_ref(v_inst_1071_);
lean_inc_ref(v_inst_1070_);
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1070_, v_inst_1071_, v_m_1072_, v_a_1073_);
switch(lean_obj_tag(v___x_1109_))
{
case 0:
{
lean_object* v_index_1110_; lean_object* v_size_1111_; lean_object* v___x_1112_; 
lean_dec_ref(v_inst_1071_);
lean_dec_ref(v_inst_1070_);
v_index_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_index_1110_);
lean_dec_ref_known(v___x_1109_, 3);
v_size_1111_ = lean_ctor_get(v_m_1072_, 0);
lean_inc(v_size_1111_);
v___x_1112_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1072_, v_size_1111_, v_index_1110_, v_a_1073_, v_b_1074_);
lean_dec(v_index_1110_);
return v___x_1112_;
}
case 1:
{
lean_object* v_index_1113_; lean_object* v_size_1114_; lean_object* v_keyArray_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_index_1113_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_index_1113_);
lean_dec_ref_known(v___x_1109_, 1);
v_size_1114_ = lean_ctor_get(v_m_1072_, 0);
v_keyArray_1115_ = lean_ctor_get(v_m_1072_, 1);
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_nat_add(v_size_1114_, v___x_1116_);
v___x_1118_ = lean_array_get_size(v_keyArray_1115_);
v___x_1119_ = lean_nat_dec_lt(v___x_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_dec(v___x_1117_);
lean_dec(v_index_1113_);
goto v___jp_1082_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1120_ = lean_unsigned_to_nat(4u);
v___x_1121_ = lean_nat_mul(v___x_1117_, v___x_1120_);
v___x_1122_ = lean_unsigned_to_nat(3u);
v___x_1123_ = lean_nat_mul(v___x_1118_, v___x_1122_);
v___x_1124_ = lean_nat_dec_le(v___x_1121_, v___x_1123_);
lean_dec(v___x_1123_);
lean_dec(v___x_1121_);
if (v___x_1124_ == 0)
{
lean_dec(v___x_1117_);
lean_dec(v_index_1113_);
goto v___jp_1082_;
}
else
{
lean_object* v___x_1125_; 
lean_dec_ref(v_inst_1071_);
lean_dec_ref(v_inst_1070_);
v___x_1125_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1072_, v___x_1117_, v_index_1113_, v_a_1073_, v_b_1074_);
lean_dec(v_index_1113_);
return v___x_1125_;
}
}
}
default: 
{
lean_object* v_size_1126_; lean_object* v_keyArray_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v_size_1126_ = lean_ctor_get(v_m_1072_, 0);
v_keyArray_1127_ = lean_ctor_get(v_m_1072_, 1);
v___x_1128_ = lean_unsigned_to_nat(1u);
v___x_1129_ = lean_nat_add(v_size_1126_, v___x_1128_);
v___x_1130_ = lean_array_get_size(v_keyArray_1127_);
v___x_1131_ = lean_nat_dec_lt(v___x_1129_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_dec(v___x_1129_);
lean_inc_ref(v_inst_1071_);
lean_inc_ref(v_inst_1070_);
v___x_1132_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1070_, v_inst_1071_, v_m_1072_);
v___y_1100_ = v___x_1132_;
goto v___jp_1099_;
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1133_ = lean_unsigned_to_nat(4u);
v___x_1134_ = lean_nat_mul(v___x_1129_, v___x_1133_);
lean_dec(v___x_1129_);
v___x_1135_ = lean_unsigned_to_nat(3u);
v___x_1136_ = lean_nat_mul(v___x_1130_, v___x_1135_);
v___x_1137_ = lean_nat_dec_le(v___x_1134_, v___x_1136_);
lean_dec(v___x_1136_);
lean_dec(v___x_1134_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_inc_ref(v_inst_1071_);
lean_inc_ref(v_inst_1070_);
v___x_1138_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1070_, v_inst_1071_, v_m_1072_);
v___y_1100_ = v___x_1138_;
goto v___jp_1099_;
}
else
{
v___y_1100_ = v_m_1072_;
goto v___jp_1099_;
}
}
}
}
v___jp_1075_:
{
lean_object* v_size_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_size_1078_ = lean_ctor_get(v___y_1076_, 0);
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = lean_nat_add(v_size_1078_, v___x_1079_);
v___x_1081_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1076_, v___x_1080_, v_i_1077_, v_a_1073_, v_b_1074_);
lean_dec(v_i_1077_);
return v___x_1081_;
}
v___jp_1082_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_inc_ref(v_inst_1071_);
lean_inc_ref(v_inst_1070_);
v___x_1083_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1070_, v_inst_1071_, v_m_1072_);
lean_inc(v_a_1073_);
v___x_1084_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1070_, v_inst_1071_, v___x_1083_, v_a_1073_);
switch(lean_obj_tag(v___x_1084_))
{
case 0:
{
lean_object* v_index_1085_; lean_object* v_size_1086_; lean_object* v___x_1087_; 
v_index_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_index_1085_);
lean_dec_ref_known(v___x_1084_, 3);
v_size_1086_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_size_1086_);
v___x_1087_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1083_, v_size_1086_, v_index_1085_, v_a_1073_, v_b_1074_);
lean_dec(v_index_1085_);
return v___x_1087_;
}
case 1:
{
lean_object* v_index_1088_; 
v_index_1088_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_index_1088_);
lean_dec_ref_known(v___x_1084_, 1);
v___y_1076_ = v___x_1083_;
v_i_1077_ = v_index_1088_;
goto v___jp_1075_;
}
default: 
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1083_, v___x_1089_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_index_1091_; 
v_index_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_index_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v___y_1076_ = v___x_1083_;
v_i_1077_ = v_index_1091_;
goto v___jp_1075_;
}
else
{
lean_dec(v_b_1074_);
lean_dec(v_a_1073_);
return v___x_1083_;
}
}
}
}
v___jp_1092_:
{
lean_object* v_size_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_size_1095_ = lean_ctor_get(v___y_1093_, 0);
v___x_1096_ = lean_unsigned_to_nat(1u);
v___x_1097_ = lean_nat_add(v_size_1095_, v___x_1096_);
v___x_1098_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1093_, v___x_1097_, v_i_1094_, v_a_1073_, v_b_1074_);
lean_dec(v_i_1094_);
return v___x_1098_;
}
v___jp_1099_:
{
lean_object* v___x_1101_; 
lean_inc(v_a_1073_);
v___x_1101_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1070_, v_inst_1071_, v___y_1100_, v_a_1073_);
switch(lean_obj_tag(v___x_1101_))
{
case 0:
{
lean_object* v_index_1102_; lean_object* v_size_1103_; lean_object* v___x_1104_; 
v_index_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_index_1102_);
lean_dec_ref_known(v___x_1101_, 3);
v_size_1103_ = lean_ctor_get(v___y_1100_, 0);
lean_inc(v_size_1103_);
v___x_1104_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1100_, v_size_1103_, v_index_1102_, v_a_1073_, v_b_1074_);
lean_dec(v_index_1102_);
return v___x_1104_;
}
case 1:
{
lean_object* v_index_1105_; 
v_index_1105_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_index_1105_);
lean_dec_ref_known(v___x_1101_, 1);
v___y_1093_ = v___y_1100_;
v_i_1094_ = v_index_1105_;
goto v___jp_1092_;
}
default: 
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1107_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1100_, v___x_1106_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_index_1108_; 
v_index_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_index_1108_);
lean_dec_ref_known(v___x_1107_, 1);
v___y_1093_ = v___y_1100_;
v_i_1094_ = v_index_1108_;
goto v___jp_1092_;
}
else
{
lean_dec(v_b_1074_);
lean_dec(v_a_1073_);
return v___y_1100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_scan_match__1_splitter___redArg(lean_object* v_x_1139_, lean_object* v_h__1_1140_, lean_object* v_h__2_1141_, lean_object* v_h__3_1142_){
_start:
{
switch(lean_obj_tag(v_x_1139_))
{
case 0:
{
lean_object* v_index_1143_; lean_object* v_key_1144_; lean_object* v_value_1145_; lean_object* v___x_1146_; 
lean_dec(v_h__3_1142_);
lean_dec(v_h__2_1141_);
v_index_1143_ = lean_ctor_get(v_x_1139_, 0);
lean_inc(v_index_1143_);
v_key_1144_ = lean_ctor_get(v_x_1139_, 1);
lean_inc(v_key_1144_);
v_value_1145_ = lean_ctor_get(v_x_1139_, 2);
lean_inc(v_value_1145_);
lean_dec_ref_known(v_x_1139_, 3);
v___x_1146_ = lean_apply_4(v_h__1_1140_, v_index_1143_, v_key_1144_, v_value_1145_, lean_box(0));
return v___x_1146_;
}
case 1:
{
lean_object* v_index_1147_; lean_object* v___x_1148_; 
lean_dec(v_h__3_1142_);
lean_dec(v_h__1_1140_);
v_index_1147_ = lean_ctor_get(v_x_1139_, 0);
lean_inc(v_index_1147_);
lean_dec_ref_known(v_x_1139_, 1);
v___x_1148_ = lean_apply_1(v_h__2_1141_, v_index_1147_);
return v___x_1148_;
}
default: 
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec(v_h__2_1141_);
lean_dec(v_h__1_1140_);
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_apply_1(v_h__3_1142_, v___x_1149_);
return v___x_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_scan_match__1_splitter(lean_object* v_00_u03b1_1151_, lean_object* v_00_u03b2_1152_, lean_object* v_inst_1153_, lean_object* v_m_1154_, lean_object* v_query_1155_, lean_object* v_motive_1156_, lean_object* v_x_1157_, lean_object* v_h__1_1158_, lean_object* v_h__2_1159_, lean_object* v_h__3_1160_){
_start:
{
switch(lean_obj_tag(v_x_1157_))
{
case 0:
{
lean_object* v_index_1161_; lean_object* v_key_1162_; lean_object* v_value_1163_; lean_object* v___x_1164_; 
lean_dec(v_h__3_1160_);
lean_dec(v_h__2_1159_);
v_index_1161_ = lean_ctor_get(v_x_1157_, 0);
lean_inc(v_index_1161_);
v_key_1162_ = lean_ctor_get(v_x_1157_, 1);
lean_inc(v_key_1162_);
v_value_1163_ = lean_ctor_get(v_x_1157_, 2);
lean_inc(v_value_1163_);
lean_dec_ref_known(v_x_1157_, 3);
v___x_1164_ = lean_apply_4(v_h__1_1158_, v_index_1161_, v_key_1162_, v_value_1163_, lean_box(0));
return v___x_1164_;
}
case 1:
{
lean_object* v_index_1165_; lean_object* v___x_1166_; 
lean_dec(v_h__3_1160_);
lean_dec(v_h__1_1158_);
v_index_1165_ = lean_ctor_get(v_x_1157_, 0);
lean_inc(v_index_1165_);
lean_dec_ref_known(v_x_1157_, 1);
v___x_1166_ = lean_apply_1(v_h__2_1159_, v_index_1165_);
return v___x_1166_;
}
default: 
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v_h__2_1159_);
lean_dec(v_h__1_1158_);
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_apply_1(v_h__3_1160_, v___x_1167_);
return v___x_1168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_scan_match__1_splitter___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_00_u03b2_1170_, lean_object* v_inst_1171_, lean_object* v_m_1172_, lean_object* v_query_1173_, lean_object* v_motive_1174_, lean_object* v_x_1175_, lean_object* v_h__1_1176_, lean_object* v_h__2_1177_, lean_object* v_h__3_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_scan_match__1_splitter(v_00_u03b1_1169_, v_00_u03b2_1170_, v_inst_1171_, v_m_1172_, v_query_1173_, v_motive_1174_, v_x_1175_, v_h__1_1176_, v_h__2_1177_, v_h__3_1178_);
lean_dec(v_query_1173_);
lean_dec_ref(v_m_1172_);
lean_dec_ref(v_inst_1171_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_insertNoExpand_match__1_splitter___redArg(lean_object* v_x_1180_, lean_object* v_h__1_1181_, lean_object* v_h__2_1182_){
_start:
{
if (lean_obj_tag(v_x_1180_) == 0)
{
lean_object* v_index_1183_; lean_object* v___x_1184_; 
lean_dec(v_h__2_1182_);
v_index_1183_ = lean_ctor_get(v_x_1180_, 0);
lean_inc(v_index_1183_);
lean_dec_ref_known(v_x_1180_, 1);
v___x_1184_ = lean_apply_1(v_h__1_1181_, v_index_1183_);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v_h__1_1181_);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_apply_1(v_h__2_1182_, v___x_1185_);
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_insertNoExpand_match__1_splitter(lean_object* v_00_u03b1_1187_, lean_object* v_00_u03b2_1188_, lean_object* v_m_1189_, lean_object* v_motive_1190_, lean_object* v_x_1191_, lean_object* v_h__1_1192_, lean_object* v_h__2_1193_){
_start:
{
if (lean_obj_tag(v_x_1191_) == 0)
{
lean_object* v_index_1194_; lean_object* v___x_1195_; 
lean_dec(v_h__2_1193_);
v_index_1194_ = lean_ctor_get(v_x_1191_, 0);
lean_inc(v_index_1194_);
lean_dec_ref_known(v_x_1191_, 1);
v___x_1195_ = lean_apply_1(v_h__1_1192_, v_index_1194_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec(v_h__1_1192_);
v___x_1196_ = lean_box(0);
v___x_1197_ = lean_apply_1(v_h__2_1193_, v___x_1196_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_insertNoExpand_match__1_splitter___boxed(lean_object* v_00_u03b1_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_m_1200_, lean_object* v_motive_1201_, lean_object* v_x_1202_, lean_object* v_h__1_1203_, lean_object* v_h__2_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_insertNoExpand_match__1_splitter(v_00_u03b1_1198_, v_00_u03b2_1199_, v_m_1200_, v_motive_1201_, v_x_1202_, v_h__1_1203_, v_h__2_1204_);
lean_dec_ref(v_m_1200_);
return v_res_1205_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_m_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Std_DHashMap_Internal_Raw_u2080_scan___redArg(v_inst_1206_, v_inst_1207_, v_m_1208_, v_a_1209_);
if (lean_obj_tag(v___x_1210_) == 0)
{
uint8_t v___x_1211_; 
lean_dec_ref_known(v___x_1210_, 3);
v___x_1211_ = 1;
return v___x_1211_;
}
else
{
uint8_t v___x_1212_; 
v___x_1212_ = 0;
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___redArg___boxed(lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_m_1215_, lean_object* v_a_1216_){
_start:
{
uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_res_1217_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1213_, v_inst_1214_, v_m_1215_, v_a_1216_);
lean_dec_ref(v_m_1215_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains(lean_object* v_00_u03b1_1219_, lean_object* v_00_u03b2_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_m_1223_, lean_object* v_a_1224_){
_start:
{
uint8_t v___x_1225_; 
v___x_1225_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1221_, v_inst_1222_, v_m_1223_, v_a_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___boxed(lean_object* v_00_u03b1_1226_, lean_object* v_00_u03b2_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_m_1230_, lean_object* v_a_1231_){
_start:
{
uint8_t v_res_1232_; lean_object* v_r_1233_; 
v_res_1232_ = l_Std_DHashMap_Internal_Raw_u2080_contains(v_00_u03b1_1226_, v_00_u03b2_1227_, v_inst_1228_, v_inst_1229_, v_m_1230_, v_a_1231_);
lean_dec_ref(v_m_1230_);
v_r_1233_ = lean_box(v_res_1232_);
return v_r_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_m_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Std_DHashMap_Internal_Raw_u2080_scan___redArg(v_inst_1234_, v_inst_1235_, v_m_1236_, v_a_1237_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_key_1239_; lean_object* v_value_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_key_1239_ = lean_ctor_get(v___x_1238_, 1);
lean_inc(v_key_1239_);
v_value_1240_ = lean_ctor_get(v___x_1238_, 2);
lean_inc(v_value_1240_);
lean_dec_ref_known(v___x_1238_, 3);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_key_1239_);
lean_ctor_set(v___x_1241_, 1, v_value_1240_);
v___x_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
else
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_box(0);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg___boxed(lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_m_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1244_, v_inst_1245_, v_m_1246_, v_a_1247_);
lean_dec_ref(v_m_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f(lean_object* v_00_u03b1_1249_, lean_object* v_00_u03b2_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_m_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1251_, v_inst_1252_, v_m_1253_, v_a_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_00_u03b2_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_m_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f(v_00_u03b1_1256_, v_00_u03b2_1257_, v_inst_1258_, v_inst_1259_, v_m_1260_, v_a_1261_);
lean_dec_ref(v_m_1260_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_m_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v___x_1267_; lean_object* v_val_1268_; 
v___x_1267_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1263_, v_inst_1264_, v_m_1265_, v_a_1266_);
v_val_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_val_1268_);
lean_dec(v___x_1267_);
return v_val_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg___boxed(lean_object* v_inst_1269_, lean_object* v_inst_1270_, lean_object* v_m_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1269_, v_inst_1270_, v_m_1271_, v_a_1272_);
lean_dec_ref(v_m_1271_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_m_1278_, lean_object* v_a_1279_, lean_object* v_hma_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1276_, v_inst_1277_, v_m_1278_, v_a_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_00_u03b2_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_m_1286_, lean_object* v_a_1287_, lean_object* v_hma_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry(v_00_u03b1_1282_, v_00_u03b2_1283_, v_inst_1284_, v_inst_1285_, v_m_1286_, v_a_1287_, v_hma_1288_);
lean_dec_ref(v_m_1286_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_m_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Std_DHashMap_Internal_Raw_u2080_scan___redArg(v_inst_1290_, v_inst_1291_, v_m_1292_, v_a_1293_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_value_1295_; lean_object* v___x_1296_; 
v_value_1295_ = lean_ctor_get(v___x_1294_, 2);
lean_inc(v_value_1295_);
lean_dec_ref_known(v___x_1294_, 3);
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v_value_1295_);
return v___x_1296_;
}
else
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_box(0);
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg___boxed(lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_m_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_1298_, v_inst_1299_, v_m_1300_, v_a_1301_);
lean_dec_ref(v_m_1300_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f(lean_object* v_00_u03b1_1303_, lean_object* v_00_u03b2_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_m_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_1305_, v_inst_1307_, v_m_1308_, v_a_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___boxed(lean_object* v_00_u03b1_1311_, lean_object* v_00_u03b2_1312_, lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_inst_1315_, lean_object* v_m_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f(v_00_u03b1_1311_, v_00_u03b2_1312_, v_inst_1313_, v_inst_1314_, v_inst_1315_, v_m_1316_, v_a_1317_);
lean_dec_ref(v_m_1316_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___redArg(lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_m_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1323_; lean_object* v_val_1324_; 
v___x_1323_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_1319_, v_inst_1320_, v_m_1321_, v_a_1322_);
v_val_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_val_1324_);
lean_dec(v___x_1323_);
return v_val_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___redArg___boxed(lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_m_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_1325_, v_inst_1326_, v_m_1327_, v_a_1328_);
lean_dec_ref(v_m_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get(lean_object* v_00_u03b1_1330_, lean_object* v_00_u03b2_1331_, lean_object* v_inst_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_m_1335_, lean_object* v_a_1336_, lean_object* v_hma_1337_){
_start:
{
lean_object* v___x_1338_; lean_object* v_val_1339_; 
v___x_1338_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_1332_, v_inst_1334_, v_m_1335_, v_a_1336_);
v_val_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_val_1339_);
lean_dec(v___x_1338_);
return v_val_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___boxed(lean_object* v_00_u03b1_1340_, lean_object* v_00_u03b2_1341_, lean_object* v_inst_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_m_1345_, lean_object* v_a_1346_, lean_object* v_hma_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Std_DHashMap_Internal_Raw_u2080_get(v_00_u03b1_1340_, v_00_u03b2_1341_, v_inst_1342_, v_inst_1343_, v_inst_1344_, v_m_1345_, v_a_1346_, v_hma_1347_);
lean_dec_ref(v_m_1345_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_m_1351_, lean_object* v_a_1352_, lean_object* v_fallback_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1349_, v_inst_1350_, v_m_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_inc_ref(v_fallback_1353_);
return v_fallback_1353_;
}
else
{
lean_object* v_val_1355_; 
v_val_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_val_1355_);
lean_dec_ref_known(v___x_1354_, 1);
return v_val_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg___boxed(lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_m_1358_, lean_object* v_a_1359_, lean_object* v_fallback_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1356_, v_inst_1357_, v_m_1358_, v_a_1359_, v_fallback_1360_);
lean_dec_ref(v_fallback_1360_);
lean_dec_ref(v_m_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD(lean_object* v_00_u03b1_1362_, lean_object* v_00_u03b2_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_m_1366_, lean_object* v_a_1367_, lean_object* v_fallback_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1364_, v_inst_1365_, v_m_1366_, v_a_1367_, v_fallback_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___boxed(lean_object* v_00_u03b1_1370_, lean_object* v_00_u03b2_1371_, lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_m_1374_, lean_object* v_a_1375_, lean_object* v_fallback_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD(v_00_u03b1_1370_, v_00_u03b2_1371_, v_inst_1372_, v_inst_1373_, v_m_1374_, v_a_1375_, v_fallback_1376_);
lean_dec_ref(v_fallback_1376_);
lean_dec_ref(v_m_1374_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(lean_object* v_inst_1378_, lean_object* v_inst_1379_, lean_object* v_m_1380_, lean_object* v_a_1381_, lean_object* v_inst_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1378_, v_inst_1379_, v_m_1380_, v_a_1381_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_inc_ref(v_inst_1382_);
return v_inst_1382_;
}
else
{
lean_object* v_val_1384_; 
v_val_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_val_1384_);
lean_dec_ref_known(v___x_1383_, 1);
return v_val_1384_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg___boxed(lean_object* v_inst_1385_, lean_object* v_inst_1386_, lean_object* v_m_1387_, lean_object* v_a_1388_, lean_object* v_inst_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1385_, v_inst_1386_, v_m_1387_, v_a_1388_, v_inst_1389_);
lean_dec_ref(v_inst_1389_);
lean_dec_ref(v_m_1387_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21(lean_object* v_00_u03b1_1391_, lean_object* v_00_u03b2_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_m_1395_, lean_object* v_a_1396_, lean_object* v_inst_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1393_, v_inst_1394_, v_m_1395_, v_a_1396_, v_inst_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___boxed(lean_object* v_00_u03b1_1399_, lean_object* v_00_u03b2_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_m_1403_, lean_object* v_a_1404_, lean_object* v_inst_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21(v_00_u03b1_1399_, v_00_u03b2_1400_, v_inst_1401_, v_inst_1402_, v_m_1403_, v_a_1404_, v_inst_1405_);
lean_dec_ref(v_inst_1405_);
lean_dec_ref(v_m_1403_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_m_1409_, lean_object* v_a_1410_, lean_object* v_fallback_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_1407_, v_inst_1408_, v_m_1409_, v_a_1410_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_inc(v_fallback_1411_);
return v_fallback_1411_;
}
else
{
lean_object* v_val_1413_; 
v_val_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_val_1413_);
lean_dec_ref_known(v___x_1412_, 1);
return v_val_1413_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg___boxed(lean_object* v_inst_1414_, lean_object* v_inst_1415_, lean_object* v_m_1416_, lean_object* v_a_1417_, lean_object* v_fallback_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_1414_, v_inst_1415_, v_m_1416_, v_a_1417_, v_fallback_1418_);
lean_dec(v_fallback_1418_);
lean_dec_ref(v_m_1416_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD(lean_object* v_00_u03b1_1420_, lean_object* v_00_u03b2_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_m_1425_, lean_object* v_a_1426_, lean_object* v_fallback_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_1422_, v_inst_1424_, v_m_1425_, v_a_1426_, v_fallback_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___boxed(lean_object* v_00_u03b1_1429_, lean_object* v_00_u03b2_1430_, lean_object* v_inst_1431_, lean_object* v_inst_1432_, lean_object* v_inst_1433_, lean_object* v_m_1434_, lean_object* v_a_1435_, lean_object* v_fallback_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Std_DHashMap_Internal_Raw_u2080_getD(v_00_u03b1_1429_, v_00_u03b2_1430_, v_inst_1431_, v_inst_1432_, v_inst_1433_, v_m_1434_, v_a_1435_, v_fallback_1436_);
lean_dec(v_fallback_1436_);
lean_dec_ref(v_m_1434_);
return v_res_1437_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1441_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__2));
v___x_1442_ = lean_unsigned_to_nat(12u);
v___x_1443_ = lean_unsigned_to_nat(350u);
v___x_1444_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__1));
v___x_1445_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__0));
v___x_1446_ = l_mkPanicMessageWithDecl(v___x_1445_, v___x_1444_, v___x_1443_, v___x_1442_, v___x_1441_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(lean_object* v_inst_1447_, lean_object* v_inst_1448_, lean_object* v_m_1449_, lean_object* v_a_1450_, lean_object* v_inst_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_1447_, v_inst_1448_, v_m_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__3);
v___x_1454_ = l_panic___redArg(v_inst_1451_, v___x_1453_);
return v___x_1454_;
}
else
{
lean_object* v_val_1455_; 
v_val_1455_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_val_1455_);
lean_dec_ref_known(v___x_1452_, 1);
return v_val_1455_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___boxed(lean_object* v_inst_1456_, lean_object* v_inst_1457_, lean_object* v_m_1458_, lean_object* v_a_1459_, lean_object* v_inst_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_1456_, v_inst_1457_, v_m_1458_, v_a_1459_, v_inst_1460_);
lean_dec(v_inst_1460_);
lean_dec_ref(v_m_1458_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21(lean_object* v_00_u03b1_1462_, lean_object* v_00_u03b2_1463_, lean_object* v_inst_1464_, lean_object* v_inst_1465_, lean_object* v_inst_1466_, lean_object* v_m_1467_, lean_object* v_a_1468_, lean_object* v_inst_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_1464_, v_inst_1466_, v_m_1467_, v_a_1468_, v_inst_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___boxed(lean_object* v_00_u03b1_1471_, lean_object* v_00_u03b2_1472_, lean_object* v_inst_1473_, lean_object* v_inst_1474_, lean_object* v_inst_1475_, lean_object* v_m_1476_, lean_object* v_a_1477_, lean_object* v_inst_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21(v_00_u03b1_1471_, v_00_u03b2_1472_, v_inst_1473_, v_inst_1474_, v_inst_1475_, v_m_1476_, v_a_1477_, v_inst_1478_);
lean_dec(v_inst_1478_);
lean_dec_ref(v_m_1476_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object* v_inst_1480_, lean_object* v_inst_1481_, lean_object* v_m_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Std_DHashMap_Internal_Raw_u2080_scan___redArg(v_inst_1480_, v_inst_1481_, v_m_1482_, v_a_1483_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_index_1485_; lean_object* v_size_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v_index_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_index_1485_);
lean_dec_ref_known(v___x_1484_, 3);
v_size_1486_ = lean_ctor_get(v_m_1482_, 0);
v___x_1487_ = lean_unsigned_to_nat(1u);
v___x_1488_ = lean_nat_sub(v_size_1486_, v___x_1487_);
v___x_1489_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1482_, v___x_1488_, v_index_1485_);
lean_dec(v_index_1485_);
return v___x_1489_;
}
else
{
return v_m_1482_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase(lean_object* v_00_u03b1_1490_, lean_object* v_00_u03b2_1491_, lean_object* v_inst_1492_, lean_object* v_inst_1493_, lean_object* v_m_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1492_, v_inst_1493_, v_m_1494_, v_a_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modifyImpl___redArg(lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_m_1499_, lean_object* v_a_1500_, lean_object* v_f_1501_){
_start:
{
lean_object* v___x_1502_; 
lean_inc(v_a_1500_);
v___x_1502_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1497_, v_inst_1498_, v_m_1499_, v_a_1500_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_index_1503_; lean_object* v_value_1504_; lean_object* v_size_1505_; lean_object* v_v_x27_1506_; lean_object* v___x_1507_; 
v_index_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_index_1503_);
v_value_1504_ = lean_ctor_get(v___x_1502_, 2);
lean_inc(v_value_1504_);
lean_dec_ref_known(v___x_1502_, 3);
v_size_1505_ = lean_ctor_get(v_m_1499_, 0);
lean_inc(v_size_1505_);
v_v_x27_1506_ = lean_apply_1(v_f_1501_, v_value_1504_);
v___x_1507_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1499_, v_size_1505_, v_index_1503_, v_a_1500_, v_v_x27_1506_);
lean_dec(v_index_1503_);
return v___x_1507_;
}
else
{
lean_dec(v___x_1502_);
lean_dec(v_f_1501_);
lean_dec(v_a_1500_);
return v_m_1499_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modifyImpl(lean_object* v_00_u03b1_1508_, lean_object* v_00_u03b2_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_m_1513_, lean_object* v_a_1514_, lean_object* v_f_1515_){
_start:
{
lean_object* v___x_1516_; 
lean_inc(v_a_1514_);
v___x_1516_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1510_, v_inst_1511_, v_m_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_index_1517_; lean_object* v_value_1518_; lean_object* v_size_1519_; lean_object* v_v_x27_1520_; lean_object* v___x_1521_; 
v_index_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_index_1517_);
v_value_1518_ = lean_ctor_get(v___x_1516_, 2);
lean_inc(v_value_1518_);
lean_dec_ref_known(v___x_1516_, 3);
v_size_1519_ = lean_ctor_get(v_m_1513_, 0);
lean_inc(v_size_1519_);
v_v_x27_1520_ = lean_apply_1(v_f_1515_, v_value_1518_);
v___x_1521_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1513_, v_size_1519_, v_index_1517_, v_a_1514_, v_v_x27_1520_);
lean_dec(v_index_1517_);
return v___x_1521_;
}
else
{
lean_dec(v___x_1516_);
lean_dec(v_f_1515_);
lean_dec(v_a_1514_);
return v_m_1513_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alterImpl___redArg(lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_m_1524_, lean_object* v_a_1525_, lean_object* v_f_1526_){
_start:
{
lean_object* v___x_1527_; 
lean_inc(v_a_1525_);
lean_inc_ref(v_inst_1523_);
lean_inc_ref(v_inst_1522_);
v___x_1527_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1522_, v_inst_1523_, v_m_1524_, v_a_1525_);
switch(lean_obj_tag(v___x_1527_))
{
case 0:
{
lean_object* v_index_1528_; lean_object* v_value_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec_ref(v_inst_1523_);
lean_dec_ref(v_inst_1522_);
v_index_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_index_1528_);
v_value_1529_ = lean_ctor_get(v___x_1527_, 2);
lean_inc(v_value_1529_);
lean_dec_ref_known(v___x_1527_, 3);
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_value_1529_);
v___x_1531_ = lean_apply_1(v_f_1526_, v___x_1530_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_size_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_dec(v_a_1525_);
v_size_1532_ = lean_ctor_get(v_m_1524_, 0);
v___x_1533_ = lean_unsigned_to_nat(1u);
v___x_1534_ = lean_nat_sub(v_size_1532_, v___x_1533_);
v___x_1535_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1524_, v___x_1534_, v_index_1528_);
lean_dec(v_index_1528_);
return v___x_1535_;
}
else
{
lean_object* v_val_1536_; lean_object* v_size_1537_; lean_object* v___x_1538_; 
v_val_1536_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v___x_1531_, 1);
v_size_1537_ = lean_ctor_get(v_m_1524_, 0);
lean_inc(v_size_1537_);
v___x_1538_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1524_, v_size_1537_, v_index_1528_, v_a_1525_, v_val_1536_);
lean_dec(v_index_1528_);
return v___x_1538_;
}
}
case 1:
{
lean_object* v_index_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_index_1539_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_index_1539_);
lean_dec_ref_known(v___x_1527_, 1);
v___x_1540_ = lean_box(0);
v___x_1541_ = lean_apply_1(v_f_1526_, v___x_1540_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_dec(v_index_1539_);
lean_dec(v_a_1525_);
lean_dec_ref(v_inst_1523_);
lean_dec_ref(v_inst_1522_);
return v_m_1524_;
}
else
{
lean_object* v_val_1542_; lean_object* v___y_1544_; lean_object* v_i_1545_; lean_object* v_size_1560_; lean_object* v_keyArray_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v_val_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_val_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v_size_1560_ = lean_ctor_get(v_m_1524_, 0);
v_keyArray_1561_ = lean_ctor_get(v_m_1524_, 1);
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = lean_nat_add(v_size_1560_, v___x_1562_);
v___x_1564_ = lean_array_get_size(v_keyArray_1561_);
v___x_1565_ = lean_nat_dec_lt(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_dec(v___x_1563_);
lean_dec(v_index_1539_);
goto v___jp_1550_;
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1566_ = lean_unsigned_to_nat(4u);
v___x_1567_ = lean_nat_mul(v___x_1563_, v___x_1566_);
v___x_1568_ = lean_unsigned_to_nat(3u);
v___x_1569_ = lean_nat_mul(v___x_1564_, v___x_1568_);
v___x_1570_ = lean_nat_dec_le(v___x_1567_, v___x_1569_);
lean_dec(v___x_1569_);
lean_dec(v___x_1567_);
if (v___x_1570_ == 0)
{
lean_dec(v___x_1563_);
lean_dec(v_index_1539_);
goto v___jp_1550_;
}
else
{
lean_object* v___x_1571_; 
lean_dec_ref(v_inst_1523_);
lean_dec_ref(v_inst_1522_);
v___x_1571_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1524_, v___x_1563_, v_index_1539_, v_a_1525_, v_val_1542_);
lean_dec(v_index_1539_);
return v___x_1571_;
}
}
v___jp_1543_:
{
lean_object* v_size_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_size_1546_ = lean_ctor_get(v___y_1544_, 0);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_nat_add(v_size_1546_, v___x_1547_);
v___x_1549_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1544_, v___x_1548_, v_i_1545_, v_a_1525_, v_val_1542_);
lean_dec(v_i_1545_);
return v___x_1549_;
}
v___jp_1550_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_inc_ref(v_inst_1523_);
lean_inc_ref(v_inst_1522_);
v___x_1551_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1522_, v_inst_1523_, v_m_1524_);
lean_inc(v_a_1525_);
v___x_1552_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1522_, v_inst_1523_, v___x_1551_, v_a_1525_);
switch(lean_obj_tag(v___x_1552_))
{
case 0:
{
lean_object* v_index_1553_; lean_object* v_size_1554_; lean_object* v___x_1555_; 
v_index_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_index_1553_);
lean_dec_ref_known(v___x_1552_, 3);
v_size_1554_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_size_1554_);
v___x_1555_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1551_, v_size_1554_, v_index_1553_, v_a_1525_, v_val_1542_);
lean_dec(v_index_1553_);
return v___x_1555_;
}
case 1:
{
lean_object* v_index_1556_; 
v_index_1556_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_index_1556_);
lean_dec_ref_known(v___x_1552_, 1);
v___y_1544_ = v___x_1551_;
v_i_1545_ = v_index_1556_;
goto v___jp_1543_;
}
default: 
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_unsigned_to_nat(0u);
v___x_1558_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1551_, v___x_1557_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_index_1559_; 
v_index_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_index_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___y_1544_ = v___x_1551_;
v_i_1545_ = v_index_1559_;
goto v___jp_1543_;
}
else
{
lean_dec(v_val_1542_);
lean_dec(v_a_1525_);
return v___x_1551_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_apply_1(v_f_1526_, v___x_1572_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_dec(v_a_1525_);
lean_dec_ref(v_inst_1523_);
lean_dec_ref(v_inst_1522_);
return v_m_1524_;
}
else
{
lean_object* v_val_1574_; lean_object* v___y_1576_; lean_object* v_i_1577_; lean_object* v___y_1583_; lean_object* v_size_1592_; lean_object* v_keyArray_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_val_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_val_1574_);
lean_dec_ref_known(v___x_1573_, 1);
v_size_1592_ = lean_ctor_get(v_m_1524_, 0);
v_keyArray_1593_ = lean_ctor_get(v_m_1524_, 1);
v___x_1594_ = lean_unsigned_to_nat(1u);
v___x_1595_ = lean_nat_add(v_size_1592_, v___x_1594_);
v___x_1596_ = lean_array_get_size(v_keyArray_1593_);
v___x_1597_ = lean_nat_dec_lt(v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
lean_dec(v___x_1595_);
lean_inc_ref(v_inst_1523_);
lean_inc_ref(v_inst_1522_);
v___x_1598_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1522_, v_inst_1523_, v_m_1524_);
v___y_1583_ = v___x_1598_;
goto v___jp_1582_;
}
else
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1599_ = lean_unsigned_to_nat(4u);
v___x_1600_ = lean_nat_mul(v___x_1595_, v___x_1599_);
lean_dec(v___x_1595_);
v___x_1601_ = lean_unsigned_to_nat(3u);
v___x_1602_ = lean_nat_mul(v___x_1596_, v___x_1601_);
v___x_1603_ = lean_nat_dec_le(v___x_1600_, v___x_1602_);
lean_dec(v___x_1602_);
lean_dec(v___x_1600_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
lean_inc_ref(v_inst_1523_);
lean_inc_ref(v_inst_1522_);
v___x_1604_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1522_, v_inst_1523_, v_m_1524_);
v___y_1583_ = v___x_1604_;
goto v___jp_1582_;
}
else
{
v___y_1583_ = v_m_1524_;
goto v___jp_1582_;
}
}
v___jp_1575_:
{
lean_object* v_size_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_size_1578_ = lean_ctor_get(v___y_1576_, 0);
v___x_1579_ = lean_unsigned_to_nat(1u);
v___x_1580_ = lean_nat_add(v_size_1578_, v___x_1579_);
v___x_1581_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1576_, v___x_1580_, v_i_1577_, v_a_1525_, v_val_1574_);
lean_dec(v_i_1577_);
return v___x_1581_;
}
v___jp_1582_:
{
lean_object* v___x_1584_; 
lean_inc(v_a_1525_);
v___x_1584_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1522_, v_inst_1523_, v___y_1583_, v_a_1525_);
switch(lean_obj_tag(v___x_1584_))
{
case 0:
{
lean_object* v_index_1585_; lean_object* v_size_1586_; lean_object* v___x_1587_; 
v_index_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_index_1585_);
lean_dec_ref_known(v___x_1584_, 3);
v_size_1586_ = lean_ctor_get(v___y_1583_, 0);
lean_inc(v_size_1586_);
v___x_1587_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1583_, v_size_1586_, v_index_1585_, v_a_1525_, v_val_1574_);
lean_dec(v_index_1585_);
return v___x_1587_;
}
case 1:
{
lean_object* v_index_1588_; 
v_index_1588_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_index_1588_);
lean_dec_ref_known(v___x_1584_, 1);
v___y_1576_ = v___y_1583_;
v_i_1577_ = v_index_1588_;
goto v___jp_1575_;
}
default: 
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_unsigned_to_nat(0u);
v___x_1590_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1583_, v___x_1589_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_index_1591_; 
v_index_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_index_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___y_1576_ = v___y_1583_;
v_i_1577_ = v_index_1591_;
goto v___jp_1575_;
}
else
{
lean_dec(v_val_1574_);
lean_dec(v_a_1525_);
return v___y_1583_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alterImpl(lean_object* v_00_u03b1_1605_, lean_object* v_00_u03b2_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_m_1610_, lean_object* v_a_1611_, lean_object* v_f_1612_){
_start:
{
lean_object* v___x_1613_; 
lean_inc(v_a_1611_);
lean_inc_ref(v_inst_1608_);
lean_inc_ref(v_inst_1607_);
v___x_1613_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1607_, v_inst_1608_, v_m_1610_, v_a_1611_);
switch(lean_obj_tag(v___x_1613_))
{
case 0:
{
lean_object* v_index_1614_; lean_object* v_value_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v_inst_1608_);
lean_dec_ref(v_inst_1607_);
v_index_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_index_1614_);
v_value_1615_ = lean_ctor_get(v___x_1613_, 2);
lean_inc(v_value_1615_);
lean_dec_ref_known(v___x_1613_, 3);
v___x_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1616_, 0, v_value_1615_);
v___x_1617_ = lean_apply_1(v_f_1612_, v___x_1616_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_size_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec(v_a_1611_);
v_size_1618_ = lean_ctor_get(v_m_1610_, 0);
v___x_1619_ = lean_unsigned_to_nat(1u);
v___x_1620_ = lean_nat_sub(v_size_1618_, v___x_1619_);
v___x_1621_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1610_, v___x_1620_, v_index_1614_);
lean_dec(v_index_1614_);
return v___x_1621_;
}
else
{
lean_object* v_val_1622_; lean_object* v_size_1623_; lean_object* v___x_1624_; 
v_val_1622_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_val_1622_);
lean_dec_ref_known(v___x_1617_, 1);
v_size_1623_ = lean_ctor_get(v_m_1610_, 0);
lean_inc(v_size_1623_);
v___x_1624_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1610_, v_size_1623_, v_index_1614_, v_a_1611_, v_val_1622_);
lean_dec(v_index_1614_);
return v___x_1624_;
}
}
case 1:
{
lean_object* v_index_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v_index_1625_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_index_1625_);
lean_dec_ref_known(v___x_1613_, 1);
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_apply_1(v_f_1612_, v___x_1626_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_dec(v_index_1625_);
lean_dec(v_a_1611_);
lean_dec_ref(v_inst_1608_);
lean_dec_ref(v_inst_1607_);
return v_m_1610_;
}
else
{
lean_object* v_val_1628_; lean_object* v___y_1630_; lean_object* v_i_1631_; lean_object* v_size_1646_; lean_object* v_keyArray_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v_val_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_val_1628_);
lean_dec_ref_known(v___x_1627_, 1);
v_size_1646_ = lean_ctor_get(v_m_1610_, 0);
v_keyArray_1647_ = lean_ctor_get(v_m_1610_, 1);
v___x_1648_ = lean_unsigned_to_nat(1u);
v___x_1649_ = lean_nat_add(v_size_1646_, v___x_1648_);
v___x_1650_ = lean_array_get_size(v_keyArray_1647_);
v___x_1651_ = lean_nat_dec_lt(v___x_1649_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_dec(v___x_1649_);
lean_dec(v_index_1625_);
goto v___jp_1636_;
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1652_ = lean_unsigned_to_nat(4u);
v___x_1653_ = lean_nat_mul(v___x_1649_, v___x_1652_);
v___x_1654_ = lean_unsigned_to_nat(3u);
v___x_1655_ = lean_nat_mul(v___x_1650_, v___x_1654_);
v___x_1656_ = lean_nat_dec_le(v___x_1653_, v___x_1655_);
lean_dec(v___x_1655_);
lean_dec(v___x_1653_);
if (v___x_1656_ == 0)
{
lean_dec(v___x_1649_);
lean_dec(v_index_1625_);
goto v___jp_1636_;
}
else
{
lean_object* v___x_1657_; 
lean_dec_ref(v_inst_1608_);
lean_dec_ref(v_inst_1607_);
v___x_1657_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1610_, v___x_1649_, v_index_1625_, v_a_1611_, v_val_1628_);
lean_dec(v_index_1625_);
return v___x_1657_;
}
}
v___jp_1629_:
{
lean_object* v_size_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_size_1632_ = lean_ctor_get(v___y_1630_, 0);
v___x_1633_ = lean_unsigned_to_nat(1u);
v___x_1634_ = lean_nat_add(v_size_1632_, v___x_1633_);
v___x_1635_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1630_, v___x_1634_, v_i_1631_, v_a_1611_, v_val_1628_);
lean_dec(v_i_1631_);
return v___x_1635_;
}
v___jp_1636_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_inc_ref(v_inst_1608_);
lean_inc_ref(v_inst_1607_);
v___x_1637_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1607_, v_inst_1608_, v_m_1610_);
lean_inc(v_a_1611_);
v___x_1638_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1607_, v_inst_1608_, v___x_1637_, v_a_1611_);
switch(lean_obj_tag(v___x_1638_))
{
case 0:
{
lean_object* v_index_1639_; lean_object* v_size_1640_; lean_object* v___x_1641_; 
v_index_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_index_1639_);
lean_dec_ref_known(v___x_1638_, 3);
v_size_1640_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_size_1640_);
v___x_1641_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1637_, v_size_1640_, v_index_1639_, v_a_1611_, v_val_1628_);
lean_dec(v_index_1639_);
return v___x_1641_;
}
case 1:
{
lean_object* v_index_1642_; 
v_index_1642_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_index_1642_);
lean_dec_ref_known(v___x_1638_, 1);
v___y_1630_ = v___x_1637_;
v_i_1631_ = v_index_1642_;
goto v___jp_1629_;
}
default: 
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_unsigned_to_nat(0u);
v___x_1644_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1637_, v___x_1643_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_index_1645_; 
v_index_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_index_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___y_1630_ = v___x_1637_;
v_i_1631_ = v_index_1645_;
goto v___jp_1629_;
}
else
{
lean_dec(v_val_1628_);
lean_dec(v_a_1611_);
return v___x_1637_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_box(0);
v___x_1659_ = lean_apply_1(v_f_1612_, v___x_1658_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_dec(v_a_1611_);
lean_dec_ref(v_inst_1608_);
lean_dec_ref(v_inst_1607_);
return v_m_1610_;
}
else
{
lean_object* v_val_1660_; lean_object* v___y_1662_; lean_object* v_i_1663_; lean_object* v___y_1669_; lean_object* v_size_1678_; lean_object* v_keyArray_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v_val_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_val_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v_size_1678_ = lean_ctor_get(v_m_1610_, 0);
v_keyArray_1679_ = lean_ctor_get(v_m_1610_, 1);
v___x_1680_ = lean_unsigned_to_nat(1u);
v___x_1681_ = lean_nat_add(v_size_1678_, v___x_1680_);
v___x_1682_ = lean_array_get_size(v_keyArray_1679_);
v___x_1683_ = lean_nat_dec_lt(v___x_1681_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; 
lean_dec(v___x_1681_);
lean_inc_ref(v_inst_1608_);
lean_inc_ref(v_inst_1607_);
v___x_1684_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1607_, v_inst_1608_, v_m_1610_);
v___y_1669_ = v___x_1684_;
goto v___jp_1668_;
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1685_ = lean_unsigned_to_nat(4u);
v___x_1686_ = lean_nat_mul(v___x_1681_, v___x_1685_);
lean_dec(v___x_1681_);
v___x_1687_ = lean_unsigned_to_nat(3u);
v___x_1688_ = lean_nat_mul(v___x_1682_, v___x_1687_);
v___x_1689_ = lean_nat_dec_le(v___x_1686_, v___x_1688_);
lean_dec(v___x_1688_);
lean_dec(v___x_1686_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; 
lean_inc_ref(v_inst_1608_);
lean_inc_ref(v_inst_1607_);
v___x_1690_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1607_, v_inst_1608_, v_m_1610_);
v___y_1669_ = v___x_1690_;
goto v___jp_1668_;
}
else
{
v___y_1669_ = v_m_1610_;
goto v___jp_1668_;
}
}
v___jp_1661_:
{
lean_object* v_size_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_size_1664_ = lean_ctor_get(v___y_1662_, 0);
v___x_1665_ = lean_unsigned_to_nat(1u);
v___x_1666_ = lean_nat_add(v_size_1664_, v___x_1665_);
v___x_1667_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1662_, v___x_1666_, v_i_1663_, v_a_1611_, v_val_1660_);
lean_dec(v_i_1663_);
return v___x_1667_;
}
v___jp_1668_:
{
lean_object* v___x_1670_; 
lean_inc(v_a_1611_);
v___x_1670_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1607_, v_inst_1608_, v___y_1669_, v_a_1611_);
switch(lean_obj_tag(v___x_1670_))
{
case 0:
{
lean_object* v_index_1671_; lean_object* v_size_1672_; lean_object* v___x_1673_; 
v_index_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_index_1671_);
lean_dec_ref_known(v___x_1670_, 3);
v_size_1672_ = lean_ctor_get(v___y_1669_, 0);
lean_inc(v_size_1672_);
v___x_1673_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1669_, v_size_1672_, v_index_1671_, v_a_1611_, v_val_1660_);
lean_dec(v_index_1671_);
return v___x_1673_;
}
case 1:
{
lean_object* v_index_1674_; 
v_index_1674_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_index_1674_);
lean_dec_ref_known(v___x_1670_, 1);
v___y_1662_ = v___y_1669_;
v_i_1663_ = v_index_1674_;
goto v___jp_1661_;
}
default: 
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1669_, v___x_1675_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_index_1677_; 
v_index_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_index_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v___y_1662_ = v___y_1669_;
v_i_1663_ = v_index_1677_;
goto v___jp_1661_;
}
else
{
lean_dec(v_val_1660_);
lean_dec(v_a_1611_);
return v___y_1669_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertImpl___redArg(lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_m_1693_, lean_object* v_a_1694_, lean_object* v_b_1695_){
_start:
{
lean_object* v___x_1696_; 
lean_inc(v_a_1694_);
lean_inc_ref(v_inst_1692_);
lean_inc_ref(v_inst_1691_);
v___x_1696_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1691_, v_inst_1692_, v_m_1693_, v_a_1694_);
switch(lean_obj_tag(v___x_1696_))
{
case 0:
{
lean_object* v_index_1697_; lean_object* v_size_1698_; uint8_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec_ref(v_inst_1692_);
lean_dec_ref(v_inst_1691_);
v_index_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_index_1697_);
lean_dec_ref_known(v___x_1696_, 3);
v_size_1698_ = lean_ctor_get(v_m_1693_, 0);
lean_inc(v_size_1698_);
v___x_1699_ = 1;
v___x_1700_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1693_, v_size_1698_, v_index_1697_, v_a_1694_, v_b_1695_);
lean_dec(v_index_1697_);
v___x_1701_ = lean_box(v___x_1699_);
v___x_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
lean_ctor_set(v___x_1702_, 1, v___x_1700_);
return v___x_1702_;
}
case 1:
{
lean_object* v_index_1703_; lean_object* v_size_1704_; lean_object* v_keyArray_1705_; uint8_t v___x_1706_; lean_object* v___y_1708_; lean_object* v_i_1709_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_index_1703_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_index_1703_);
lean_dec_ref_known(v___x_1696_, 1);
v_size_1704_ = lean_ctor_get(v_m_1693_, 0);
v_keyArray_1705_ = lean_ctor_get(v_m_1693_, 1);
v___x_1706_ = 0;
v___x_1730_ = lean_unsigned_to_nat(1u);
v___x_1731_ = lean_nat_add(v_size_1704_, v___x_1730_);
v___x_1732_ = lean_array_get_size(v_keyArray_1705_);
v___x_1733_ = lean_nat_dec_lt(v___x_1731_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_dec(v___x_1731_);
lean_dec(v_index_1703_);
goto v___jp_1716_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1734_ = lean_unsigned_to_nat(4u);
v___x_1735_ = lean_nat_mul(v___x_1731_, v___x_1734_);
v___x_1736_ = lean_unsigned_to_nat(3u);
v___x_1737_ = lean_nat_mul(v___x_1732_, v___x_1736_);
v___x_1738_ = lean_nat_dec_le(v___x_1735_, v___x_1737_);
lean_dec(v___x_1737_);
lean_dec(v___x_1735_);
if (v___x_1738_ == 0)
{
lean_dec(v___x_1731_);
lean_dec(v_index_1703_);
goto v___jp_1716_;
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_dec_ref(v_inst_1692_);
lean_dec_ref(v_inst_1691_);
v___x_1739_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1693_, v___x_1731_, v_index_1703_, v_a_1694_, v_b_1695_);
lean_dec(v_index_1703_);
v___x_1740_ = lean_box(v___x_1706_);
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
lean_ctor_set(v___x_1741_, 1, v___x_1739_);
return v___x_1741_;
}
}
v___jp_1707_:
{
lean_object* v_size_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_size_1710_ = lean_ctor_get(v___y_1708_, 0);
v___x_1711_ = lean_unsigned_to_nat(1u);
v___x_1712_ = lean_nat_add(v_size_1710_, v___x_1711_);
v___x_1713_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1708_, v___x_1712_, v_i_1709_, v_a_1694_, v_b_1695_);
lean_dec(v_i_1709_);
v___x_1714_ = lean_box(v___x_1706_);
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set(v___x_1715_, 1, v___x_1713_);
return v___x_1715_;
}
v___jp_1716_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_inc_ref(v_inst_1692_);
lean_inc_ref(v_inst_1691_);
v___x_1717_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1691_, v_inst_1692_, v_m_1693_);
lean_inc(v_a_1694_);
v___x_1718_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1691_, v_inst_1692_, v___x_1717_, v_a_1694_);
switch(lean_obj_tag(v___x_1718_))
{
case 0:
{
lean_object* v_index_1719_; lean_object* v_size_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_index_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_index_1719_);
lean_dec_ref_known(v___x_1718_, 3);
v_size_1720_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_size_1720_);
v___x_1721_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1717_, v_size_1720_, v_index_1719_, v_a_1694_, v_b_1695_);
lean_dec(v_index_1719_);
v___x_1722_ = lean_box(v___x_1706_);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set(v___x_1723_, 1, v___x_1721_);
return v___x_1723_;
}
case 1:
{
lean_object* v_index_1724_; 
v_index_1724_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_index_1724_);
lean_dec_ref_known(v___x_1718_, 1);
v___y_1708_ = v___x_1717_;
v_i_1709_ = v_index_1724_;
goto v___jp_1707_;
}
default: 
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_unsigned_to_nat(0u);
v___x_1726_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1717_, v___x_1725_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_index_1727_; 
v_index_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_index_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___y_1708_ = v___x_1717_;
v_i_1709_ = v_index_1727_;
goto v___jp_1707_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec(v_b_1695_);
lean_dec(v_a_1694_);
v___x_1728_ = lean_box(v___x_1706_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v___x_1717_);
return v___x_1729_;
}
}
}
}
}
default: 
{
lean_object* v_size_1742_; lean_object* v_keyArray_1743_; uint8_t v___x_1744_; lean_object* v___y_1746_; lean_object* v_i_1747_; lean_object* v___y_1755_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v_size_1742_ = lean_ctor_get(v_m_1693_, 0);
v_keyArray_1743_ = lean_ctor_get(v_m_1693_, 1);
v___x_1744_ = 0;
v___x_1768_ = lean_unsigned_to_nat(1u);
v___x_1769_ = lean_nat_add(v_size_1742_, v___x_1768_);
v___x_1770_ = lean_array_get_size(v_keyArray_1743_);
v___x_1771_ = lean_nat_dec_lt(v___x_1769_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; 
lean_dec(v___x_1769_);
lean_inc_ref(v_inst_1692_);
lean_inc_ref(v_inst_1691_);
v___x_1772_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1691_, v_inst_1692_, v_m_1693_);
v___y_1755_ = v___x_1772_;
goto v___jp_1754_;
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1773_ = lean_unsigned_to_nat(4u);
v___x_1774_ = lean_nat_mul(v___x_1769_, v___x_1773_);
lean_dec(v___x_1769_);
v___x_1775_ = lean_unsigned_to_nat(3u);
v___x_1776_ = lean_nat_mul(v___x_1770_, v___x_1775_);
v___x_1777_ = lean_nat_dec_le(v___x_1774_, v___x_1776_);
lean_dec(v___x_1776_);
lean_dec(v___x_1774_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
lean_inc_ref(v_inst_1692_);
lean_inc_ref(v_inst_1691_);
v___x_1778_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1691_, v_inst_1692_, v_m_1693_);
v___y_1755_ = v___x_1778_;
goto v___jp_1754_;
}
else
{
v___y_1755_ = v_m_1693_;
goto v___jp_1754_;
}
}
v___jp_1745_:
{
lean_object* v_size_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_size_1748_ = lean_ctor_get(v___y_1746_, 0);
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_nat_add(v_size_1748_, v___x_1749_);
v___x_1751_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1746_, v___x_1750_, v_i_1747_, v_a_1694_, v_b_1695_);
lean_dec(v_i_1747_);
v___x_1752_ = lean_box(v___x_1744_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v___x_1751_);
return v___x_1753_;
}
v___jp_1754_:
{
lean_object* v___x_1756_; 
lean_inc(v_a_1694_);
v___x_1756_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1691_, v_inst_1692_, v___y_1755_, v_a_1694_);
switch(lean_obj_tag(v___x_1756_))
{
case 0:
{
lean_object* v_index_1757_; lean_object* v_size_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_index_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_index_1757_);
lean_dec_ref_known(v___x_1756_, 3);
v_size_1758_ = lean_ctor_get(v___y_1755_, 0);
lean_inc(v_size_1758_);
v___x_1759_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1755_, v_size_1758_, v_index_1757_, v_a_1694_, v_b_1695_);
lean_dec(v_index_1757_);
v___x_1760_ = lean_box(v___x_1744_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
lean_ctor_set(v___x_1761_, 1, v___x_1759_);
return v___x_1761_;
}
case 1:
{
lean_object* v_index_1762_; 
v_index_1762_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_index_1762_);
lean_dec_ref_known(v___x_1756_, 1);
v___y_1746_ = v___y_1755_;
v_i_1747_ = v_index_1762_;
goto v___jp_1745_;
}
default: 
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1755_, v___x_1763_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_index_1765_; 
v_index_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_index_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___y_1746_ = v___y_1755_;
v_i_1747_ = v_index_1765_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec(v_b_1695_);
lean_dec(v_a_1694_);
v___x_1766_ = lean_box(v___x_1744_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v___y_1755_);
return v___x_1767_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertImpl(lean_object* v_00_u03b1_1779_, lean_object* v_00_u03b2_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_m_1783_, lean_object* v_a_1784_, lean_object* v_b_1785_){
_start:
{
lean_object* v___x_1786_; 
lean_inc(v_a_1784_);
lean_inc_ref(v_inst_1782_);
lean_inc_ref(v_inst_1781_);
v___x_1786_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1781_, v_inst_1782_, v_m_1783_, v_a_1784_);
switch(lean_obj_tag(v___x_1786_))
{
case 0:
{
lean_object* v_index_1787_; lean_object* v_size_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_dec_ref(v_inst_1782_);
lean_dec_ref(v_inst_1781_);
v_index_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_index_1787_);
lean_dec_ref_known(v___x_1786_, 3);
v_size_1788_ = lean_ctor_get(v_m_1783_, 0);
lean_inc(v_size_1788_);
v___x_1789_ = 1;
v___x_1790_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1783_, v_size_1788_, v_index_1787_, v_a_1784_, v_b_1785_);
lean_dec(v_index_1787_);
v___x_1791_ = lean_box(v___x_1789_);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
lean_ctor_set(v___x_1792_, 1, v___x_1790_);
return v___x_1792_;
}
case 1:
{
lean_object* v_index_1793_; lean_object* v_size_1794_; lean_object* v_keyArray_1795_; uint8_t v___x_1796_; lean_object* v___y_1798_; lean_object* v_i_1799_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v_index_1793_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_index_1793_);
lean_dec_ref_known(v___x_1786_, 1);
v_size_1794_ = lean_ctor_get(v_m_1783_, 0);
v_keyArray_1795_ = lean_ctor_get(v_m_1783_, 1);
v___x_1796_ = 0;
v___x_1820_ = lean_unsigned_to_nat(1u);
v___x_1821_ = lean_nat_add(v_size_1794_, v___x_1820_);
v___x_1822_ = lean_array_get_size(v_keyArray_1795_);
v___x_1823_ = lean_nat_dec_lt(v___x_1821_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_dec(v___x_1821_);
lean_dec(v_index_1793_);
goto v___jp_1806_;
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1824_ = lean_unsigned_to_nat(4u);
v___x_1825_ = lean_nat_mul(v___x_1821_, v___x_1824_);
v___x_1826_ = lean_unsigned_to_nat(3u);
v___x_1827_ = lean_nat_mul(v___x_1822_, v___x_1826_);
v___x_1828_ = lean_nat_dec_le(v___x_1825_, v___x_1827_);
lean_dec(v___x_1827_);
lean_dec(v___x_1825_);
if (v___x_1828_ == 0)
{
lean_dec(v___x_1821_);
lean_dec(v_index_1793_);
goto v___jp_1806_;
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref(v_inst_1782_);
lean_dec_ref(v_inst_1781_);
v___x_1829_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1783_, v___x_1821_, v_index_1793_, v_a_1784_, v_b_1785_);
lean_dec(v_index_1793_);
v___x_1830_ = lean_box(v___x_1796_);
v___x_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
lean_ctor_set(v___x_1831_, 1, v___x_1829_);
return v___x_1831_;
}
}
v___jp_1797_:
{
lean_object* v_size_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_size_1800_ = lean_ctor_get(v___y_1798_, 0);
v___x_1801_ = lean_unsigned_to_nat(1u);
v___x_1802_ = lean_nat_add(v_size_1800_, v___x_1801_);
v___x_1803_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1798_, v___x_1802_, v_i_1799_, v_a_1784_, v_b_1785_);
lean_dec(v_i_1799_);
v___x_1804_ = lean_box(v___x_1796_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v___x_1803_);
return v___x_1805_;
}
v___jp_1806_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_inc_ref(v_inst_1782_);
lean_inc_ref(v_inst_1781_);
v___x_1807_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1781_, v_inst_1782_, v_m_1783_);
lean_inc(v_a_1784_);
v___x_1808_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1781_, v_inst_1782_, v___x_1807_, v_a_1784_);
switch(lean_obj_tag(v___x_1808_))
{
case 0:
{
lean_object* v_index_1809_; lean_object* v_size_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v_index_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_index_1809_);
lean_dec_ref_known(v___x_1808_, 3);
v_size_1810_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_size_1810_);
v___x_1811_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1807_, v_size_1810_, v_index_1809_, v_a_1784_, v_b_1785_);
lean_dec(v_index_1809_);
v___x_1812_ = lean_box(v___x_1796_);
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___x_1811_);
return v___x_1813_;
}
case 1:
{
lean_object* v_index_1814_; 
v_index_1814_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_index_1814_);
lean_dec_ref_known(v___x_1808_, 1);
v___y_1798_ = v___x_1807_;
v_i_1799_ = v_index_1814_;
goto v___jp_1797_;
}
default: 
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1807_, v___x_1815_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_index_1817_; 
v_index_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_index_1817_);
lean_dec_ref_known(v___x_1816_, 1);
v___y_1798_ = v___x_1807_;
v_i_1799_ = v_index_1817_;
goto v___jp_1797_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec(v_b_1785_);
lean_dec(v_a_1784_);
v___x_1818_ = lean_box(v___x_1796_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v___x_1807_);
return v___x_1819_;
}
}
}
}
}
default: 
{
lean_object* v_size_1832_; lean_object* v_keyArray_1833_; uint8_t v___x_1834_; lean_object* v___y_1836_; lean_object* v_i_1837_; lean_object* v___y_1845_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v_size_1832_ = lean_ctor_get(v_m_1783_, 0);
v_keyArray_1833_ = lean_ctor_get(v_m_1783_, 1);
v___x_1834_ = 0;
v___x_1858_ = lean_unsigned_to_nat(1u);
v___x_1859_ = lean_nat_add(v_size_1832_, v___x_1858_);
v___x_1860_ = lean_array_get_size(v_keyArray_1833_);
v___x_1861_ = lean_nat_dec_lt(v___x_1859_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
lean_dec(v___x_1859_);
lean_inc_ref(v_inst_1782_);
lean_inc_ref(v_inst_1781_);
v___x_1862_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1781_, v_inst_1782_, v_m_1783_);
v___y_1845_ = v___x_1862_;
goto v___jp_1844_;
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1863_ = lean_unsigned_to_nat(4u);
v___x_1864_ = lean_nat_mul(v___x_1859_, v___x_1863_);
lean_dec(v___x_1859_);
v___x_1865_ = lean_unsigned_to_nat(3u);
v___x_1866_ = lean_nat_mul(v___x_1860_, v___x_1865_);
v___x_1867_ = lean_nat_dec_le(v___x_1864_, v___x_1866_);
lean_dec(v___x_1866_);
lean_dec(v___x_1864_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
lean_inc_ref(v_inst_1782_);
lean_inc_ref(v_inst_1781_);
v___x_1868_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1781_, v_inst_1782_, v_m_1783_);
v___y_1845_ = v___x_1868_;
goto v___jp_1844_;
}
else
{
v___y_1845_ = v_m_1783_;
goto v___jp_1844_;
}
}
v___jp_1835_:
{
lean_object* v_size_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v_size_1838_ = lean_ctor_get(v___y_1836_, 0);
v___x_1839_ = lean_unsigned_to_nat(1u);
v___x_1840_ = lean_nat_add(v_size_1838_, v___x_1839_);
v___x_1841_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1836_, v___x_1840_, v_i_1837_, v_a_1784_, v_b_1785_);
lean_dec(v_i_1837_);
v___x_1842_ = lean_box(v___x_1834_);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v___x_1841_);
return v___x_1843_;
}
v___jp_1844_:
{
lean_object* v___x_1846_; 
lean_inc(v_a_1784_);
v___x_1846_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1781_, v_inst_1782_, v___y_1845_, v_a_1784_);
switch(lean_obj_tag(v___x_1846_))
{
case 0:
{
lean_object* v_index_1847_; lean_object* v_size_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_index_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_index_1847_);
lean_dec_ref_known(v___x_1846_, 3);
v_size_1848_ = lean_ctor_get(v___y_1845_, 0);
lean_inc(v_size_1848_);
v___x_1849_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1845_, v_size_1848_, v_index_1847_, v_a_1784_, v_b_1785_);
lean_dec(v_index_1847_);
v___x_1850_ = lean_box(v___x_1834_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v___x_1849_);
return v___x_1851_;
}
case 1:
{
lean_object* v_index_1852_; 
v_index_1852_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_index_1852_);
lean_dec_ref_known(v___x_1846_, 1);
v___y_1836_ = v___y_1845_;
v_i_1837_ = v_index_1852_;
goto v___jp_1835_;
}
default: 
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_unsigned_to_nat(0u);
v___x_1854_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1845_, v___x_1853_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_index_1855_; 
v_index_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_index_1855_);
lean_dec_ref_known(v___x_1854_, 1);
v___y_1836_ = v___y_1845_;
v_i_1837_ = v_index_1855_;
goto v___jp_1835_;
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec(v_b_1785_);
lean_dec(v_a_1784_);
v___x_1856_ = lean_box(v___x_1834_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
lean_ctor_set(v___x_1857_, 1, v___y_1845_);
return v___x_1857_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertIfNewImpl___redArg(lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_m_1871_, lean_object* v_a_1872_, lean_object* v_b_1873_){
_start:
{
lean_object* v___x_1874_; 
lean_inc(v_a_1872_);
lean_inc_ref(v_inst_1870_);
lean_inc_ref(v_inst_1869_);
v___x_1874_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1869_, v_inst_1870_, v_m_1871_, v_a_1872_);
switch(lean_obj_tag(v___x_1874_))
{
case 0:
{
uint8_t v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec_ref_known(v___x_1874_, 3);
lean_dec(v_b_1873_);
lean_dec(v_a_1872_);
lean_dec_ref(v_inst_1870_);
lean_dec_ref(v_inst_1869_);
v___x_1875_ = 1;
v___x_1876_ = lean_box(v___x_1875_);
v___x_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v_m_1871_);
return v___x_1877_;
}
case 1:
{
lean_object* v_index_1878_; lean_object* v_size_1879_; lean_object* v_keyArray_1880_; uint8_t v___x_1881_; lean_object* v___y_1883_; lean_object* v_i_1884_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v_index_1878_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_index_1878_);
lean_dec_ref_known(v___x_1874_, 1);
v_size_1879_ = lean_ctor_get(v_m_1871_, 0);
v_keyArray_1880_ = lean_ctor_get(v_m_1871_, 1);
v___x_1881_ = 0;
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = lean_nat_add(v_size_1879_, v___x_1905_);
v___x_1907_ = lean_array_get_size(v_keyArray_1880_);
v___x_1908_ = lean_nat_dec_lt(v___x_1906_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_dec(v___x_1906_);
lean_dec(v_index_1878_);
goto v___jp_1891_;
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1909_ = lean_unsigned_to_nat(4u);
v___x_1910_ = lean_nat_mul(v___x_1906_, v___x_1909_);
v___x_1911_ = lean_unsigned_to_nat(3u);
v___x_1912_ = lean_nat_mul(v___x_1907_, v___x_1911_);
v___x_1913_ = lean_nat_dec_le(v___x_1910_, v___x_1912_);
lean_dec(v___x_1912_);
lean_dec(v___x_1910_);
if (v___x_1913_ == 0)
{
lean_dec(v___x_1906_);
lean_dec(v_index_1878_);
goto v___jp_1891_;
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_dec_ref(v_inst_1870_);
lean_dec_ref(v_inst_1869_);
v___x_1914_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1871_, v___x_1906_, v_index_1878_, v_a_1872_, v_b_1873_);
lean_dec(v_index_1878_);
v___x_1915_ = lean_box(v___x_1881_);
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v___x_1914_);
return v___x_1916_;
}
}
v___jp_1882_:
{
lean_object* v_size_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_size_1885_ = lean_ctor_get(v___y_1883_, 0);
v___x_1886_ = lean_unsigned_to_nat(1u);
v___x_1887_ = lean_nat_add(v_size_1885_, v___x_1886_);
v___x_1888_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1883_, v___x_1887_, v_i_1884_, v_a_1872_, v_b_1873_);
lean_dec(v_i_1884_);
v___x_1889_ = lean_box(v___x_1881_);
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v___x_1888_);
return v___x_1890_;
}
v___jp_1891_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_inc_ref(v_inst_1870_);
lean_inc_ref(v_inst_1869_);
v___x_1892_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1869_, v_inst_1870_, v_m_1871_);
lean_inc(v_a_1872_);
v___x_1893_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1869_, v_inst_1870_, v___x_1892_, v_a_1872_);
switch(lean_obj_tag(v___x_1893_))
{
case 0:
{
lean_object* v_index_1894_; lean_object* v_size_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_index_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_index_1894_);
lean_dec_ref_known(v___x_1893_, 3);
v_size_1895_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_size_1895_);
v___x_1896_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1892_, v_size_1895_, v_index_1894_, v_a_1872_, v_b_1873_);
lean_dec(v_index_1894_);
v___x_1897_ = lean_box(v___x_1881_);
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
lean_ctor_set(v___x_1898_, 1, v___x_1896_);
return v___x_1898_;
}
case 1:
{
lean_object* v_index_1899_; 
v_index_1899_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_index_1899_);
lean_dec_ref_known(v___x_1893_, 1);
v___y_1883_ = v___x_1892_;
v_i_1884_ = v_index_1899_;
goto v___jp_1882_;
}
default: 
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1892_, v___x_1900_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_index_1902_; 
v_index_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_index_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v___y_1883_ = v___x_1892_;
v_i_1884_ = v_index_1902_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_dec(v_b_1873_);
lean_dec(v_a_1872_);
v___x_1903_ = lean_box(v___x_1881_);
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
lean_ctor_set(v___x_1904_, 1, v___x_1892_);
return v___x_1904_;
}
}
}
}
}
default: 
{
lean_object* v_size_1917_; lean_object* v_keyArray_1918_; uint8_t v___x_1919_; lean_object* v___y_1921_; lean_object* v_i_1922_; lean_object* v___y_1930_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v_size_1917_ = lean_ctor_get(v_m_1871_, 0);
v_keyArray_1918_ = lean_ctor_get(v_m_1871_, 1);
v___x_1919_ = 0;
v___x_1943_ = lean_unsigned_to_nat(1u);
v___x_1944_ = lean_nat_add(v_size_1917_, v___x_1943_);
v___x_1945_ = lean_array_get_size(v_keyArray_1918_);
v___x_1946_ = lean_nat_dec_lt(v___x_1944_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; 
lean_dec(v___x_1944_);
lean_inc_ref(v_inst_1870_);
lean_inc_ref(v_inst_1869_);
v___x_1947_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1869_, v_inst_1870_, v_m_1871_);
v___y_1930_ = v___x_1947_;
goto v___jp_1929_;
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1948_ = lean_unsigned_to_nat(4u);
v___x_1949_ = lean_nat_mul(v___x_1944_, v___x_1948_);
lean_dec(v___x_1944_);
v___x_1950_ = lean_unsigned_to_nat(3u);
v___x_1951_ = lean_nat_mul(v___x_1945_, v___x_1950_);
v___x_1952_ = lean_nat_dec_le(v___x_1949_, v___x_1951_);
lean_dec(v___x_1951_);
lean_dec(v___x_1949_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; 
lean_inc_ref(v_inst_1870_);
lean_inc_ref(v_inst_1869_);
v___x_1953_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1869_, v_inst_1870_, v_m_1871_);
v___y_1930_ = v___x_1953_;
goto v___jp_1929_;
}
else
{
v___y_1930_ = v_m_1871_;
goto v___jp_1929_;
}
}
v___jp_1920_:
{
lean_object* v_size_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_size_1923_ = lean_ctor_get(v___y_1921_, 0);
v___x_1924_ = lean_unsigned_to_nat(1u);
v___x_1925_ = lean_nat_add(v_size_1923_, v___x_1924_);
v___x_1926_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1921_, v___x_1925_, v_i_1922_, v_a_1872_, v_b_1873_);
lean_dec(v_i_1922_);
v___x_1927_ = lean_box(v___x_1919_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
lean_ctor_set(v___x_1928_, 1, v___x_1926_);
return v___x_1928_;
}
v___jp_1929_:
{
lean_object* v___x_1931_; 
lean_inc(v_a_1872_);
v___x_1931_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1869_, v_inst_1870_, v___y_1930_, v_a_1872_);
switch(lean_obj_tag(v___x_1931_))
{
case 0:
{
lean_object* v_index_1932_; lean_object* v_size_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_index_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_index_1932_);
lean_dec_ref_known(v___x_1931_, 3);
v_size_1933_ = lean_ctor_get(v___y_1930_, 0);
lean_inc(v_size_1933_);
v___x_1934_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1930_, v_size_1933_, v_index_1932_, v_a_1872_, v_b_1873_);
lean_dec(v_index_1932_);
v___x_1935_ = lean_box(v___x_1919_);
v___x_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
lean_ctor_set(v___x_1936_, 1, v___x_1934_);
return v___x_1936_;
}
case 1:
{
lean_object* v_index_1937_; 
v_index_1937_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_index_1937_);
lean_dec_ref_known(v___x_1931_, 1);
v___y_1921_ = v___y_1930_;
v_i_1922_ = v_index_1937_;
goto v___jp_1920_;
}
default: 
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_unsigned_to_nat(0u);
v___x_1939_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1930_, v___x_1938_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_index_1940_; 
v_index_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_index_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v___y_1921_ = v___y_1930_;
v_i_1922_ = v_index_1940_;
goto v___jp_1920_;
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_dec(v_b_1873_);
lean_dec(v_a_1872_);
v___x_1941_ = lean_box(v___x_1919_);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v___y_1930_);
return v___x_1942_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertIfNewImpl(lean_object* v_00_u03b1_1954_, lean_object* v_00_u03b2_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_, lean_object* v_m_1958_, lean_object* v_a_1959_, lean_object* v_b_1960_){
_start:
{
lean_object* v___x_1961_; 
lean_inc(v_a_1959_);
lean_inc_ref(v_inst_1957_);
lean_inc_ref(v_inst_1956_);
v___x_1961_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1956_, v_inst_1957_, v_m_1958_, v_a_1959_);
switch(lean_obj_tag(v___x_1961_))
{
case 0:
{
uint8_t v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec_ref_known(v___x_1961_, 3);
lean_dec(v_b_1960_);
lean_dec(v_a_1959_);
lean_dec_ref(v_inst_1957_);
lean_dec_ref(v_inst_1956_);
v___x_1962_ = 1;
v___x_1963_ = lean_box(v___x_1962_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
lean_ctor_set(v___x_1964_, 1, v_m_1958_);
return v___x_1964_;
}
case 1:
{
lean_object* v_index_1965_; lean_object* v_size_1966_; lean_object* v_keyArray_1967_; uint8_t v___x_1968_; lean_object* v___y_1970_; lean_object* v_i_1971_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_index_1965_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_index_1965_);
lean_dec_ref_known(v___x_1961_, 1);
v_size_1966_ = lean_ctor_get(v_m_1958_, 0);
v_keyArray_1967_ = lean_ctor_get(v_m_1958_, 1);
v___x_1968_ = 0;
v___x_1992_ = lean_unsigned_to_nat(1u);
v___x_1993_ = lean_nat_add(v_size_1966_, v___x_1992_);
v___x_1994_ = lean_array_get_size(v_keyArray_1967_);
v___x_1995_ = lean_nat_dec_lt(v___x_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_dec(v___x_1993_);
lean_dec(v_index_1965_);
goto v___jp_1978_;
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1996_ = lean_unsigned_to_nat(4u);
v___x_1997_ = lean_nat_mul(v___x_1993_, v___x_1996_);
v___x_1998_ = lean_unsigned_to_nat(3u);
v___x_1999_ = lean_nat_mul(v___x_1994_, v___x_1998_);
v___x_2000_ = lean_nat_dec_le(v___x_1997_, v___x_1999_);
lean_dec(v___x_1999_);
lean_dec(v___x_1997_);
if (v___x_2000_ == 0)
{
lean_dec(v___x_1993_);
lean_dec(v_index_1965_);
goto v___jp_1978_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_dec_ref(v_inst_1957_);
lean_dec_ref(v_inst_1956_);
v___x_2001_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1958_, v___x_1993_, v_index_1965_, v_a_1959_, v_b_1960_);
lean_dec(v_index_1965_);
v___x_2002_ = lean_box(v___x_1968_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v___x_2001_);
return v___x_2003_;
}
}
v___jp_1969_:
{
lean_object* v_size_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v_size_1972_ = lean_ctor_get(v___y_1970_, 0);
v___x_1973_ = lean_unsigned_to_nat(1u);
v___x_1974_ = lean_nat_add(v_size_1972_, v___x_1973_);
v___x_1975_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1970_, v___x_1974_, v_i_1971_, v_a_1959_, v_b_1960_);
lean_dec(v_i_1971_);
v___x_1976_ = lean_box(v___x_1968_);
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set(v___x_1977_, 1, v___x_1975_);
return v___x_1977_;
}
v___jp_1978_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_inc_ref(v_inst_1957_);
lean_inc_ref(v_inst_1956_);
v___x_1979_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1956_, v_inst_1957_, v_m_1958_);
lean_inc(v_a_1959_);
v___x_1980_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1956_, v_inst_1957_, v___x_1979_, v_a_1959_);
switch(lean_obj_tag(v___x_1980_))
{
case 0:
{
lean_object* v_index_1981_; lean_object* v_size_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_index_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_index_1981_);
lean_dec_ref_known(v___x_1980_, 3);
v_size_1982_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_size_1982_);
v___x_1983_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1979_, v_size_1982_, v_index_1981_, v_a_1959_, v_b_1960_);
lean_dec(v_index_1981_);
v___x_1984_ = lean_box(v___x_1968_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
lean_ctor_set(v___x_1985_, 1, v___x_1983_);
return v___x_1985_;
}
case 1:
{
lean_object* v_index_1986_; 
v_index_1986_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_index_1986_);
lean_dec_ref_known(v___x_1980_, 1);
v___y_1970_ = v___x_1979_;
v_i_1971_ = v_index_1986_;
goto v___jp_1969_;
}
default: 
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = lean_unsigned_to_nat(0u);
v___x_1988_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1979_, v___x_1987_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_index_1989_; 
v_index_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_index_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___y_1970_ = v___x_1979_;
v_i_1971_ = v_index_1989_;
goto v___jp_1969_;
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec(v_b_1960_);
lean_dec(v_a_1959_);
v___x_1990_ = lean_box(v___x_1968_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v___x_1979_);
return v___x_1991_;
}
}
}
}
}
default: 
{
lean_object* v_size_2004_; lean_object* v_keyArray_2005_; uint8_t v___x_2006_; lean_object* v___y_2008_; lean_object* v_i_2009_; lean_object* v___y_2017_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_size_2004_ = lean_ctor_get(v_m_1958_, 0);
v_keyArray_2005_ = lean_ctor_get(v_m_1958_, 1);
v___x_2006_ = 0;
v___x_2030_ = lean_unsigned_to_nat(1u);
v___x_2031_ = lean_nat_add(v_size_2004_, v___x_2030_);
v___x_2032_ = lean_array_get_size(v_keyArray_2005_);
v___x_2033_ = lean_nat_dec_lt(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; 
lean_dec(v___x_2031_);
lean_inc_ref(v_inst_1957_);
lean_inc_ref(v_inst_1956_);
v___x_2034_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1956_, v_inst_1957_, v_m_1958_);
v___y_2017_ = v___x_2034_;
goto v___jp_2016_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2035_ = lean_unsigned_to_nat(4u);
v___x_2036_ = lean_nat_mul(v___x_2031_, v___x_2035_);
lean_dec(v___x_2031_);
v___x_2037_ = lean_unsigned_to_nat(3u);
v___x_2038_ = lean_nat_mul(v___x_2032_, v___x_2037_);
v___x_2039_ = lean_nat_dec_le(v___x_2036_, v___x_2038_);
lean_dec(v___x_2038_);
lean_dec(v___x_2036_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; 
lean_inc_ref(v_inst_1957_);
lean_inc_ref(v_inst_1956_);
v___x_2040_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1956_, v_inst_1957_, v_m_1958_);
v___y_2017_ = v___x_2040_;
goto v___jp_2016_;
}
else
{
v___y_2017_ = v_m_1958_;
goto v___jp_2016_;
}
}
v___jp_2007_:
{
lean_object* v_size_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v_size_2010_ = lean_ctor_get(v___y_2008_, 0);
v___x_2011_ = lean_unsigned_to_nat(1u);
v___x_2012_ = lean_nat_add(v_size_2010_, v___x_2011_);
v___x_2013_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2008_, v___x_2012_, v_i_2009_, v_a_1959_, v_b_1960_);
lean_dec(v_i_2009_);
v___x_2014_ = lean_box(v___x_2006_);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
lean_ctor_set(v___x_2015_, 1, v___x_2013_);
return v___x_2015_;
}
v___jp_2016_:
{
lean_object* v___x_2018_; 
lean_inc(v_a_1959_);
v___x_2018_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1956_, v_inst_1957_, v___y_2017_, v_a_1959_);
switch(lean_obj_tag(v___x_2018_))
{
case 0:
{
lean_object* v_index_2019_; lean_object* v_size_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_index_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_index_2019_);
lean_dec_ref_known(v___x_2018_, 3);
v_size_2020_ = lean_ctor_get(v___y_2017_, 0);
lean_inc(v_size_2020_);
v___x_2021_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2017_, v_size_2020_, v_index_2019_, v_a_1959_, v_b_1960_);
lean_dec(v_index_2019_);
v___x_2022_ = lean_box(v___x_2006_);
v___x_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v___x_2021_);
return v___x_2023_;
}
case 1:
{
lean_object* v_index_2024_; 
v_index_2024_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_index_2024_);
lean_dec_ref_known(v___x_2018_, 1);
v___y_2008_ = v___y_2017_;
v_i_2009_ = v_index_2024_;
goto v___jp_2007_;
}
default: 
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2017_, v___x_2025_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_index_2027_; 
v_index_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_index_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v___y_2008_ = v___y_2017_;
v_i_2009_ = v_index_2027_;
goto v___jp_2007_;
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_dec(v_b_1960_);
lean_dec(v_a_1959_);
v___x_2028_ = lean_box(v___x_2006_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
lean_ctor_set(v___x_2029_, 1, v___y_2017_);
return v___x_2029_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNewImpl___redArg(lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_m_2043_, lean_object* v_a_2044_, lean_object* v_b_2045_){
_start:
{
lean_object* v___y_2047_; lean_object* v_i_2048_; lean_object* v___y_2064_; lean_object* v_i_2065_; lean_object* v___y_2071_; lean_object* v___x_2080_; 
lean_inc(v_a_2044_);
lean_inc_ref(v_inst_2042_);
lean_inc_ref(v_inst_2041_);
v___x_2080_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2041_, v_inst_2042_, v_m_2043_, v_a_2044_);
switch(lean_obj_tag(v___x_2080_))
{
case 0:
{
lean_dec_ref_known(v___x_2080_, 3);
lean_dec(v_b_2045_);
lean_dec(v_a_2044_);
lean_dec_ref(v_inst_2042_);
lean_dec_ref(v_inst_2041_);
return v_m_2043_;
}
case 1:
{
lean_object* v_index_2081_; lean_object* v_size_2082_; lean_object* v_keyArray_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v_index_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_index_2081_);
lean_dec_ref_known(v___x_2080_, 1);
v_size_2082_ = lean_ctor_get(v_m_2043_, 0);
v_keyArray_2083_ = lean_ctor_get(v_m_2043_, 1);
v___x_2084_ = lean_unsigned_to_nat(1u);
v___x_2085_ = lean_nat_add(v_size_2082_, v___x_2084_);
v___x_2086_ = lean_array_get_size(v_keyArray_2083_);
v___x_2087_ = lean_nat_dec_lt(v___x_2085_, v___x_2086_);
if (v___x_2087_ == 0)
{
lean_dec(v___x_2085_);
lean_dec(v_index_2081_);
goto v___jp_2053_;
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2088_ = lean_unsigned_to_nat(4u);
v___x_2089_ = lean_nat_mul(v___x_2085_, v___x_2088_);
v___x_2090_ = lean_unsigned_to_nat(3u);
v___x_2091_ = lean_nat_mul(v___x_2086_, v___x_2090_);
v___x_2092_ = lean_nat_dec_le(v___x_2089_, v___x_2091_);
lean_dec(v___x_2091_);
lean_dec(v___x_2089_);
if (v___x_2092_ == 0)
{
lean_dec(v___x_2085_);
lean_dec(v_index_2081_);
goto v___jp_2053_;
}
else
{
lean_object* v___x_2093_; 
lean_dec_ref(v_inst_2042_);
lean_dec_ref(v_inst_2041_);
v___x_2093_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2043_, v___x_2085_, v_index_2081_, v_a_2044_, v_b_2045_);
lean_dec(v_index_2081_);
return v___x_2093_;
}
}
}
default: 
{
lean_object* v_size_2094_; lean_object* v_keyArray_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_size_2094_ = lean_ctor_get(v_m_2043_, 0);
v_keyArray_2095_ = lean_ctor_get(v_m_2043_, 1);
v___x_2096_ = lean_unsigned_to_nat(1u);
v___x_2097_ = lean_nat_add(v_size_2094_, v___x_2096_);
v___x_2098_ = lean_array_get_size(v_keyArray_2095_);
v___x_2099_ = lean_nat_dec_lt(v___x_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; 
lean_dec(v___x_2097_);
lean_inc_ref(v_inst_2042_);
lean_inc_ref(v_inst_2041_);
v___x_2100_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2041_, v_inst_2042_, v_m_2043_);
v___y_2071_ = v___x_2100_;
goto v___jp_2070_;
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
v___x_2101_ = lean_unsigned_to_nat(4u);
v___x_2102_ = lean_nat_mul(v___x_2097_, v___x_2101_);
lean_dec(v___x_2097_);
v___x_2103_ = lean_unsigned_to_nat(3u);
v___x_2104_ = lean_nat_mul(v___x_2098_, v___x_2103_);
v___x_2105_ = lean_nat_dec_le(v___x_2102_, v___x_2104_);
lean_dec(v___x_2104_);
lean_dec(v___x_2102_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; 
lean_inc_ref(v_inst_2042_);
lean_inc_ref(v_inst_2041_);
v___x_2106_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2041_, v_inst_2042_, v_m_2043_);
v___y_2071_ = v___x_2106_;
goto v___jp_2070_;
}
else
{
v___y_2071_ = v_m_2043_;
goto v___jp_2070_;
}
}
}
}
v___jp_2046_:
{
lean_object* v_size_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_size_2049_ = lean_ctor_get(v___y_2047_, 0);
v___x_2050_ = lean_unsigned_to_nat(1u);
v___x_2051_ = lean_nat_add(v_size_2049_, v___x_2050_);
v___x_2052_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2047_, v___x_2051_, v_i_2048_, v_a_2044_, v_b_2045_);
lean_dec(v_i_2048_);
return v___x_2052_;
}
v___jp_2053_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_inc_ref(v_inst_2042_);
lean_inc_ref(v_inst_2041_);
v___x_2054_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2041_, v_inst_2042_, v_m_2043_);
lean_inc(v_a_2044_);
v___x_2055_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2041_, v_inst_2042_, v___x_2054_, v_a_2044_);
switch(lean_obj_tag(v___x_2055_))
{
case 0:
{
lean_object* v_index_2056_; lean_object* v_size_2057_; lean_object* v___x_2058_; 
v_index_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_index_2056_);
lean_dec_ref_known(v___x_2055_, 3);
v_size_2057_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_size_2057_);
v___x_2058_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2054_, v_size_2057_, v_index_2056_, v_a_2044_, v_b_2045_);
lean_dec(v_index_2056_);
return v___x_2058_;
}
case 1:
{
lean_object* v_index_2059_; 
v_index_2059_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_index_2059_);
lean_dec_ref_known(v___x_2055_, 1);
v___y_2047_ = v___x_2054_;
v_i_2048_ = v_index_2059_;
goto v___jp_2046_;
}
default: 
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2054_, v___x_2060_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_index_2062_; 
v_index_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_index_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___y_2047_ = v___x_2054_;
v_i_2048_ = v_index_2062_;
goto v___jp_2046_;
}
else
{
lean_dec(v_b_2045_);
lean_dec(v_a_2044_);
return v___x_2054_;
}
}
}
}
v___jp_2063_:
{
lean_object* v_size_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v_size_2066_ = lean_ctor_get(v___y_2064_, 0);
v___x_2067_ = lean_unsigned_to_nat(1u);
v___x_2068_ = lean_nat_add(v_size_2066_, v___x_2067_);
v___x_2069_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2064_, v___x_2068_, v_i_2065_, v_a_2044_, v_b_2045_);
lean_dec(v_i_2065_);
return v___x_2069_;
}
v___jp_2070_:
{
lean_object* v___x_2072_; 
lean_inc(v_a_2044_);
v___x_2072_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2041_, v_inst_2042_, v___y_2071_, v_a_2044_);
switch(lean_obj_tag(v___x_2072_))
{
case 0:
{
lean_object* v_index_2073_; lean_object* v_size_2074_; lean_object* v___x_2075_; 
v_index_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_index_2073_);
lean_dec_ref_known(v___x_2072_, 3);
v_size_2074_ = lean_ctor_get(v___y_2071_, 0);
lean_inc(v_size_2074_);
v___x_2075_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2071_, v_size_2074_, v_index_2073_, v_a_2044_, v_b_2045_);
lean_dec(v_index_2073_);
return v___x_2075_;
}
case 1:
{
lean_object* v_index_2076_; 
v_index_2076_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_index_2076_);
lean_dec_ref_known(v___x_2072_, 1);
v___y_2064_ = v___y_2071_;
v_i_2065_ = v_index_2076_;
goto v___jp_2063_;
}
default: 
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2071_, v___x_2077_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_index_2079_; 
v_index_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_index_2079_);
lean_dec_ref_known(v___x_2078_, 1);
v___y_2064_ = v___y_2071_;
v_i_2065_ = v_index_2079_;
goto v___jp_2063_;
}
else
{
lean_dec(v_b_2045_);
lean_dec(v_a_2044_);
return v___y_2071_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNewImpl(lean_object* v_00_u03b1_2107_, lean_object* v_00_u03b2_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_m_2111_, lean_object* v_a_2112_, lean_object* v_b_2113_){
_start:
{
lean_object* v___y_2115_; lean_object* v_i_2116_; lean_object* v___y_2132_; lean_object* v_i_2133_; lean_object* v___y_2139_; lean_object* v___x_2148_; 
lean_inc(v_a_2112_);
lean_inc_ref(v_inst_2110_);
lean_inc_ref(v_inst_2109_);
v___x_2148_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2109_, v_inst_2110_, v_m_2111_, v_a_2112_);
switch(lean_obj_tag(v___x_2148_))
{
case 0:
{
lean_dec_ref_known(v___x_2148_, 3);
lean_dec(v_b_2113_);
lean_dec(v_a_2112_);
lean_dec_ref(v_inst_2110_);
lean_dec_ref(v_inst_2109_);
return v_m_2111_;
}
case 1:
{
lean_object* v_index_2149_; lean_object* v_size_2150_; lean_object* v_keyArray_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
v_index_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_index_2149_);
lean_dec_ref_known(v___x_2148_, 1);
v_size_2150_ = lean_ctor_get(v_m_2111_, 0);
v_keyArray_2151_ = lean_ctor_get(v_m_2111_, 1);
v___x_2152_ = lean_unsigned_to_nat(1u);
v___x_2153_ = lean_nat_add(v_size_2150_, v___x_2152_);
v___x_2154_ = lean_array_get_size(v_keyArray_2151_);
v___x_2155_ = lean_nat_dec_lt(v___x_2153_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_dec(v___x_2153_);
lean_dec(v_index_2149_);
goto v___jp_2121_;
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2156_ = lean_unsigned_to_nat(4u);
v___x_2157_ = lean_nat_mul(v___x_2153_, v___x_2156_);
v___x_2158_ = lean_unsigned_to_nat(3u);
v___x_2159_ = lean_nat_mul(v___x_2154_, v___x_2158_);
v___x_2160_ = lean_nat_dec_le(v___x_2157_, v___x_2159_);
lean_dec(v___x_2159_);
lean_dec(v___x_2157_);
if (v___x_2160_ == 0)
{
lean_dec(v___x_2153_);
lean_dec(v_index_2149_);
goto v___jp_2121_;
}
else
{
lean_object* v___x_2161_; 
lean_dec_ref(v_inst_2110_);
lean_dec_ref(v_inst_2109_);
v___x_2161_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2111_, v___x_2153_, v_index_2149_, v_a_2112_, v_b_2113_);
lean_dec(v_index_2149_);
return v___x_2161_;
}
}
}
default: 
{
lean_object* v_size_2162_; lean_object* v_keyArray_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v_size_2162_ = lean_ctor_get(v_m_2111_, 0);
v_keyArray_2163_ = lean_ctor_get(v_m_2111_, 1);
v___x_2164_ = lean_unsigned_to_nat(1u);
v___x_2165_ = lean_nat_add(v_size_2162_, v___x_2164_);
v___x_2166_ = lean_array_get_size(v_keyArray_2163_);
v___x_2167_ = lean_nat_dec_lt(v___x_2165_, v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; 
lean_dec(v___x_2165_);
lean_inc_ref(v_inst_2110_);
lean_inc_ref(v_inst_2109_);
v___x_2168_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2109_, v_inst_2110_, v_m_2111_);
v___y_2139_ = v___x_2168_;
goto v___jp_2138_;
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2169_ = lean_unsigned_to_nat(4u);
v___x_2170_ = lean_nat_mul(v___x_2165_, v___x_2169_);
lean_dec(v___x_2165_);
v___x_2171_ = lean_unsigned_to_nat(3u);
v___x_2172_ = lean_nat_mul(v___x_2166_, v___x_2171_);
v___x_2173_ = lean_nat_dec_le(v___x_2170_, v___x_2172_);
lean_dec(v___x_2172_);
lean_dec(v___x_2170_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
lean_inc_ref(v_inst_2110_);
lean_inc_ref(v_inst_2109_);
v___x_2174_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2109_, v_inst_2110_, v_m_2111_);
v___y_2139_ = v___x_2174_;
goto v___jp_2138_;
}
else
{
v___y_2139_ = v_m_2111_;
goto v___jp_2138_;
}
}
}
}
v___jp_2114_:
{
lean_object* v_size_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_size_2117_ = lean_ctor_get(v___y_2115_, 0);
v___x_2118_ = lean_unsigned_to_nat(1u);
v___x_2119_ = lean_nat_add(v_size_2117_, v___x_2118_);
v___x_2120_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2115_, v___x_2119_, v_i_2116_, v_a_2112_, v_b_2113_);
lean_dec(v_i_2116_);
return v___x_2120_;
}
v___jp_2121_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_inc_ref(v_inst_2110_);
lean_inc_ref(v_inst_2109_);
v___x_2122_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2109_, v_inst_2110_, v_m_2111_);
lean_inc(v_a_2112_);
v___x_2123_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2109_, v_inst_2110_, v___x_2122_, v_a_2112_);
switch(lean_obj_tag(v___x_2123_))
{
case 0:
{
lean_object* v_index_2124_; lean_object* v_size_2125_; lean_object* v___x_2126_; 
v_index_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_index_2124_);
lean_dec_ref_known(v___x_2123_, 3);
v_size_2125_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_size_2125_);
v___x_2126_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2122_, v_size_2125_, v_index_2124_, v_a_2112_, v_b_2113_);
lean_dec(v_index_2124_);
return v___x_2126_;
}
case 1:
{
lean_object* v_index_2127_; 
v_index_2127_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_index_2127_);
lean_dec_ref_known(v___x_2123_, 1);
v___y_2115_ = v___x_2122_;
v_i_2116_ = v_index_2127_;
goto v___jp_2114_;
}
default: 
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = lean_unsigned_to_nat(0u);
v___x_2129_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2122_, v___x_2128_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_index_2130_; 
v_index_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_index_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___y_2115_ = v___x_2122_;
v_i_2116_ = v_index_2130_;
goto v___jp_2114_;
}
else
{
lean_dec(v_b_2113_);
lean_dec(v_a_2112_);
return v___x_2122_;
}
}
}
}
v___jp_2131_:
{
lean_object* v_size_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_size_2134_ = lean_ctor_get(v___y_2132_, 0);
v___x_2135_ = lean_unsigned_to_nat(1u);
v___x_2136_ = lean_nat_add(v_size_2134_, v___x_2135_);
v___x_2137_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2132_, v___x_2136_, v_i_2133_, v_a_2112_, v_b_2113_);
lean_dec(v_i_2133_);
return v___x_2137_;
}
v___jp_2138_:
{
lean_object* v___x_2140_; 
lean_inc(v_a_2112_);
v___x_2140_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2109_, v_inst_2110_, v___y_2139_, v_a_2112_);
switch(lean_obj_tag(v___x_2140_))
{
case 0:
{
lean_object* v_index_2141_; lean_object* v_size_2142_; lean_object* v___x_2143_; 
v_index_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_index_2141_);
lean_dec_ref_known(v___x_2140_, 3);
v_size_2142_ = lean_ctor_get(v___y_2139_, 0);
lean_inc(v_size_2142_);
v___x_2143_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2139_, v_size_2142_, v_index_2141_, v_a_2112_, v_b_2113_);
lean_dec(v_index_2141_);
return v___x_2143_;
}
case 1:
{
lean_object* v_index_2144_; 
v_index_2144_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_index_2144_);
lean_dec_ref_known(v___x_2140_, 1);
v___y_2132_ = v___y_2139_;
v_i_2133_ = v_index_2144_;
goto v___jp_2131_;
}
default: 
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_unsigned_to_nat(0u);
v___x_2146_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2139_, v___x_2145_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_index_2147_; 
v_index_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_index_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___y_2132_ = v___y_2139_;
v_i_2133_ = v_index_2147_;
goto v___jp_2131_;
}
else
{
lean_dec(v_b_2113_);
lean_dec(v_a_2112_);
return v___y_2139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getThenInsertIfNewImpl_x3f___redArg(lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_m_2177_, lean_object* v_a_2178_, lean_object* v_b_2179_){
_start:
{
lean_object* v___x_2180_; 
lean_inc(v_a_2178_);
lean_inc_ref(v_inst_2176_);
lean_inc_ref(v_inst_2175_);
v___x_2180_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2175_, v_inst_2176_, v_m_2177_, v_a_2178_);
switch(lean_obj_tag(v___x_2180_))
{
case 0:
{
lean_object* v_value_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec(v_b_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_inst_2176_);
lean_dec_ref(v_inst_2175_);
v_value_2181_ = lean_ctor_get(v___x_2180_, 2);
lean_inc(v_value_2181_);
lean_dec_ref_known(v___x_2180_, 3);
v___x_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2182_, 0, v_value_2181_);
v___x_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
lean_ctor_set(v___x_2183_, 1, v_m_2177_);
return v___x_2183_;
}
case 1:
{
lean_object* v_index_2184_; lean_object* v_size_2185_; lean_object* v_keyArray_2186_; lean_object* v___x_2187_; lean_object* v___y_2189_; lean_object* v_i_2190_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v_index_2184_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_index_2184_);
lean_dec_ref_known(v___x_2180_, 1);
v_size_2185_ = lean_ctor_get(v_m_2177_, 0);
v_keyArray_2186_ = lean_ctor_get(v_m_2177_, 1);
v___x_2187_ = lean_box(0);
v___x_2208_ = lean_unsigned_to_nat(1u);
v___x_2209_ = lean_nat_add(v_size_2185_, v___x_2208_);
v___x_2210_ = lean_array_get_size(v_keyArray_2186_);
v___x_2211_ = lean_nat_dec_lt(v___x_2209_, v___x_2210_);
if (v___x_2211_ == 0)
{
lean_dec(v___x_2209_);
lean_dec(v_index_2184_);
goto v___jp_2196_;
}
else
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2212_ = lean_unsigned_to_nat(4u);
v___x_2213_ = lean_nat_mul(v___x_2209_, v___x_2212_);
v___x_2214_ = lean_unsigned_to_nat(3u);
v___x_2215_ = lean_nat_mul(v___x_2210_, v___x_2214_);
v___x_2216_ = lean_nat_dec_le(v___x_2213_, v___x_2215_);
lean_dec(v___x_2215_);
lean_dec(v___x_2213_);
if (v___x_2216_ == 0)
{
lean_dec(v___x_2209_);
lean_dec(v_index_2184_);
goto v___jp_2196_;
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec_ref(v_inst_2176_);
lean_dec_ref(v_inst_2175_);
v___x_2217_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2177_, v___x_2209_, v_index_2184_, v_a_2178_, v_b_2179_);
lean_dec(v_index_2184_);
v___x_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2187_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
return v___x_2218_;
}
}
v___jp_2188_:
{
lean_object* v_size_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_size_2191_ = lean_ctor_get(v___y_2189_, 0);
v___x_2192_ = lean_unsigned_to_nat(1u);
v___x_2193_ = lean_nat_add(v_size_2191_, v___x_2192_);
v___x_2194_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2189_, v___x_2193_, v_i_2190_, v_a_2178_, v_b_2179_);
lean_dec(v_i_2190_);
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2187_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
return v___x_2195_;
}
v___jp_2196_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_inc_ref(v_inst_2176_);
lean_inc_ref(v_inst_2175_);
v___x_2197_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2175_, v_inst_2176_, v_m_2177_);
lean_inc(v_a_2178_);
v___x_2198_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2175_, v_inst_2176_, v___x_2197_, v_a_2178_);
switch(lean_obj_tag(v___x_2198_))
{
case 0:
{
lean_object* v_index_2199_; lean_object* v_size_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v_index_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_index_2199_);
lean_dec_ref_known(v___x_2198_, 3);
v_size_2200_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_size_2200_);
v___x_2201_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2197_, v_size_2200_, v_index_2199_, v_a_2178_, v_b_2179_);
lean_dec(v_index_2199_);
v___x_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2187_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
return v___x_2202_;
}
case 1:
{
lean_object* v_index_2203_; 
v_index_2203_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_index_2203_);
lean_dec_ref_known(v___x_2198_, 1);
v___y_2189_ = v___x_2197_;
v_i_2190_ = v_index_2203_;
goto v___jp_2188_;
}
default: 
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2197_, v___x_2204_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_index_2206_; 
v_index_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_index_2206_);
lean_dec_ref_known(v___x_2205_, 1);
v___y_2189_ = v___x_2197_;
v_i_2190_ = v_index_2206_;
goto v___jp_2188_;
}
else
{
lean_object* v___x_2207_; 
lean_dec(v_b_2179_);
lean_dec(v_a_2178_);
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2187_);
lean_ctor_set(v___x_2207_, 1, v___x_2197_);
return v___x_2207_;
}
}
}
}
}
default: 
{
lean_object* v_size_2219_; lean_object* v_keyArray_2220_; lean_object* v___x_2221_; lean_object* v___y_2223_; lean_object* v_i_2224_; lean_object* v___y_2231_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v_size_2219_ = lean_ctor_get(v_m_2177_, 0);
v_keyArray_2220_ = lean_ctor_get(v_m_2177_, 1);
v___x_2221_ = lean_box(0);
v___x_2242_ = lean_unsigned_to_nat(1u);
v___x_2243_ = lean_nat_add(v_size_2219_, v___x_2242_);
v___x_2244_ = lean_array_get_size(v_keyArray_2220_);
v___x_2245_ = lean_nat_dec_lt(v___x_2243_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; 
lean_dec(v___x_2243_);
lean_inc_ref(v_inst_2176_);
lean_inc_ref(v_inst_2175_);
v___x_2246_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2175_, v_inst_2176_, v_m_2177_);
v___y_2231_ = v___x_2246_;
goto v___jp_2230_;
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v___x_2247_ = lean_unsigned_to_nat(4u);
v___x_2248_ = lean_nat_mul(v___x_2243_, v___x_2247_);
lean_dec(v___x_2243_);
v___x_2249_ = lean_unsigned_to_nat(3u);
v___x_2250_ = lean_nat_mul(v___x_2244_, v___x_2249_);
v___x_2251_ = lean_nat_dec_le(v___x_2248_, v___x_2250_);
lean_dec(v___x_2250_);
lean_dec(v___x_2248_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; 
lean_inc_ref(v_inst_2176_);
lean_inc_ref(v_inst_2175_);
v___x_2252_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2175_, v_inst_2176_, v_m_2177_);
v___y_2231_ = v___x_2252_;
goto v___jp_2230_;
}
else
{
v___y_2231_ = v_m_2177_;
goto v___jp_2230_;
}
}
v___jp_2222_:
{
lean_object* v_size_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_size_2225_ = lean_ctor_get(v___y_2223_, 0);
v___x_2226_ = lean_unsigned_to_nat(1u);
v___x_2227_ = lean_nat_add(v_size_2225_, v___x_2226_);
v___x_2228_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2223_, v___x_2227_, v_i_2224_, v_a_2178_, v_b_2179_);
lean_dec(v_i_2224_);
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2221_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
return v___x_2229_;
}
v___jp_2230_:
{
lean_object* v___x_2232_; 
lean_inc(v_a_2178_);
v___x_2232_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2175_, v_inst_2176_, v___y_2231_, v_a_2178_);
switch(lean_obj_tag(v___x_2232_))
{
case 0:
{
lean_object* v_index_2233_; lean_object* v_size_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v_index_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_index_2233_);
lean_dec_ref_known(v___x_2232_, 3);
v_size_2234_ = lean_ctor_get(v___y_2231_, 0);
lean_inc(v_size_2234_);
v___x_2235_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2231_, v_size_2234_, v_index_2233_, v_a_2178_, v_b_2179_);
lean_dec(v_index_2233_);
v___x_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2221_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
return v___x_2236_;
}
case 1:
{
lean_object* v_index_2237_; 
v_index_2237_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_index_2237_);
lean_dec_ref_known(v___x_2232_, 1);
v___y_2223_ = v___y_2231_;
v_i_2224_ = v_index_2237_;
goto v___jp_2222_;
}
default: 
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2231_, v___x_2238_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_index_2240_; 
v_index_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_index_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v___y_2223_ = v___y_2231_;
v_i_2224_ = v_index_2240_;
goto v___jp_2222_;
}
else
{
lean_object* v___x_2241_; 
lean_dec(v_b_2179_);
lean_dec(v_a_2178_);
v___x_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2221_);
lean_ctor_set(v___x_2241_, 1, v___y_2231_);
return v___x_2241_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getThenInsertIfNewImpl_x3f(lean_object* v_00_u03b1_2253_, lean_object* v_00_u03b2_2254_, lean_object* v_inst_2255_, lean_object* v_inst_2256_, lean_object* v_inst_2257_, lean_object* v_m_2258_, lean_object* v_a_2259_, lean_object* v_b_2260_){
_start:
{
lean_object* v___x_2261_; 
lean_inc(v_a_2259_);
lean_inc_ref(v_inst_2256_);
lean_inc_ref(v_inst_2255_);
v___x_2261_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2255_, v_inst_2256_, v_m_2258_, v_a_2259_);
switch(lean_obj_tag(v___x_2261_))
{
case 0:
{
lean_object* v_value_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_dec(v_b_2260_);
lean_dec(v_a_2259_);
lean_dec_ref(v_inst_2256_);
lean_dec_ref(v_inst_2255_);
v_value_2262_ = lean_ctor_get(v___x_2261_, 2);
lean_inc(v_value_2262_);
lean_dec_ref_known(v___x_2261_, 3);
v___x_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2263_, 0, v_value_2262_);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set(v___x_2264_, 1, v_m_2258_);
return v___x_2264_;
}
case 1:
{
lean_object* v_index_2265_; lean_object* v_size_2266_; lean_object* v_keyArray_2267_; lean_object* v___x_2268_; lean_object* v___y_2270_; lean_object* v_i_2271_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v_index_2265_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_index_2265_);
lean_dec_ref_known(v___x_2261_, 1);
v_size_2266_ = lean_ctor_get(v_m_2258_, 0);
v_keyArray_2267_ = lean_ctor_get(v_m_2258_, 1);
v___x_2268_ = lean_box(0);
v___x_2289_ = lean_unsigned_to_nat(1u);
v___x_2290_ = lean_nat_add(v_size_2266_, v___x_2289_);
v___x_2291_ = lean_array_get_size(v_keyArray_2267_);
v___x_2292_ = lean_nat_dec_lt(v___x_2290_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_dec(v___x_2290_);
lean_dec(v_index_2265_);
goto v___jp_2277_;
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2293_ = lean_unsigned_to_nat(4u);
v___x_2294_ = lean_nat_mul(v___x_2290_, v___x_2293_);
v___x_2295_ = lean_unsigned_to_nat(3u);
v___x_2296_ = lean_nat_mul(v___x_2291_, v___x_2295_);
v___x_2297_ = lean_nat_dec_le(v___x_2294_, v___x_2296_);
lean_dec(v___x_2296_);
lean_dec(v___x_2294_);
if (v___x_2297_ == 0)
{
lean_dec(v___x_2290_);
lean_dec(v_index_2265_);
goto v___jp_2277_;
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
lean_dec_ref(v_inst_2256_);
lean_dec_ref(v_inst_2255_);
v___x_2298_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2258_, v___x_2290_, v_index_2265_, v_a_2259_, v_b_2260_);
lean_dec(v_index_2265_);
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2268_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
return v___x_2299_;
}
}
v___jp_2269_:
{
lean_object* v_size_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v_size_2272_ = lean_ctor_get(v___y_2270_, 0);
v___x_2273_ = lean_unsigned_to_nat(1u);
v___x_2274_ = lean_nat_add(v_size_2272_, v___x_2273_);
v___x_2275_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2270_, v___x_2274_, v_i_2271_, v_a_2259_, v_b_2260_);
lean_dec(v_i_2271_);
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2268_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
return v___x_2276_;
}
v___jp_2277_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_inc_ref(v_inst_2256_);
lean_inc_ref(v_inst_2255_);
v___x_2278_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2255_, v_inst_2256_, v_m_2258_);
lean_inc(v_a_2259_);
v___x_2279_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2255_, v_inst_2256_, v___x_2278_, v_a_2259_);
switch(lean_obj_tag(v___x_2279_))
{
case 0:
{
lean_object* v_index_2280_; lean_object* v_size_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_index_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_index_2280_);
lean_dec_ref_known(v___x_2279_, 3);
v_size_2281_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_size_2281_);
v___x_2282_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2278_, v_size_2281_, v_index_2280_, v_a_2259_, v_b_2260_);
lean_dec(v_index_2280_);
v___x_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2268_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
return v___x_2283_;
}
case 1:
{
lean_object* v_index_2284_; 
v_index_2284_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_index_2284_);
lean_dec_ref_known(v___x_2279_, 1);
v___y_2270_ = v___x_2278_;
v_i_2271_ = v_index_2284_;
goto v___jp_2269_;
}
default: 
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_unsigned_to_nat(0u);
v___x_2286_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2278_, v___x_2285_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_index_2287_; 
v_index_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_index_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___y_2270_ = v___x_2278_;
v_i_2271_ = v_index_2287_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2288_; 
lean_dec(v_b_2260_);
lean_dec(v_a_2259_);
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2268_);
lean_ctor_set(v___x_2288_, 1, v___x_2278_);
return v___x_2288_;
}
}
}
}
}
default: 
{
lean_object* v_size_2300_; lean_object* v_keyArray_2301_; lean_object* v___x_2302_; lean_object* v___y_2304_; lean_object* v_i_2305_; lean_object* v___y_2312_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_size_2300_ = lean_ctor_get(v_m_2258_, 0);
v_keyArray_2301_ = lean_ctor_get(v_m_2258_, 1);
v___x_2302_ = lean_box(0);
v___x_2323_ = lean_unsigned_to_nat(1u);
v___x_2324_ = lean_nat_add(v_size_2300_, v___x_2323_);
v___x_2325_ = lean_array_get_size(v_keyArray_2301_);
v___x_2326_ = lean_nat_dec_lt(v___x_2324_, v___x_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; 
lean_dec(v___x_2324_);
lean_inc_ref(v_inst_2256_);
lean_inc_ref(v_inst_2255_);
v___x_2327_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2255_, v_inst_2256_, v_m_2258_);
v___y_2312_ = v___x_2327_;
goto v___jp_2311_;
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2328_ = lean_unsigned_to_nat(4u);
v___x_2329_ = lean_nat_mul(v___x_2324_, v___x_2328_);
lean_dec(v___x_2324_);
v___x_2330_ = lean_unsigned_to_nat(3u);
v___x_2331_ = lean_nat_mul(v___x_2325_, v___x_2330_);
v___x_2332_ = lean_nat_dec_le(v___x_2329_, v___x_2331_);
lean_dec(v___x_2331_);
lean_dec(v___x_2329_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; 
lean_inc_ref(v_inst_2256_);
lean_inc_ref(v_inst_2255_);
v___x_2333_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2255_, v_inst_2256_, v_m_2258_);
v___y_2312_ = v___x_2333_;
goto v___jp_2311_;
}
else
{
v___y_2312_ = v_m_2258_;
goto v___jp_2311_;
}
}
v___jp_2303_:
{
lean_object* v_size_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_size_2306_ = lean_ctor_get(v___y_2304_, 0);
v___x_2307_ = lean_unsigned_to_nat(1u);
v___x_2308_ = lean_nat_add(v_size_2306_, v___x_2307_);
v___x_2309_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2304_, v___x_2308_, v_i_2305_, v_a_2259_, v_b_2260_);
lean_dec(v_i_2305_);
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2302_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
return v___x_2310_;
}
v___jp_2311_:
{
lean_object* v___x_2313_; 
lean_inc(v_a_2259_);
v___x_2313_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2255_, v_inst_2256_, v___y_2312_, v_a_2259_);
switch(lean_obj_tag(v___x_2313_))
{
case 0:
{
lean_object* v_index_2314_; lean_object* v_size_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v_index_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_index_2314_);
lean_dec_ref_known(v___x_2313_, 3);
v_size_2315_ = lean_ctor_get(v___y_2312_, 0);
lean_inc(v_size_2315_);
v___x_2316_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2312_, v_size_2315_, v_index_2314_, v_a_2259_, v_b_2260_);
lean_dec(v_index_2314_);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2302_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
return v___x_2317_;
}
case 1:
{
lean_object* v_index_2318_; 
v_index_2318_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_index_2318_);
lean_dec_ref_known(v___x_2313_, 1);
v___y_2304_ = v___y_2312_;
v_i_2305_ = v_index_2318_;
goto v___jp_2303_;
}
default: 
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_unsigned_to_nat(0u);
v___x_2320_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2312_, v___x_2319_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_index_2321_; 
v_index_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_index_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___y_2304_ = v___y_2312_;
v_i_2305_ = v_index_2321_;
goto v___jp_2303_;
}
else
{
lean_object* v___x_2322_; 
lean_dec(v_b_2260_);
lean_dec(v_a_2259_);
v___x_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2302_);
lean_ctor_set(v___x_2322_, 1, v___y_2312_);
return v___x_2322_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter___redArg(lean_object* v_x_2334_, lean_object* v_h__1_2335_, lean_object* v_h__2_2336_){
_start:
{
if (lean_obj_tag(v_x_2334_) == 0)
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec(v_h__2_2336_);
v___x_2337_ = lean_box(0);
v___x_2338_ = lean_apply_1(v_h__1_2335_, v___x_2337_);
return v___x_2338_;
}
else
{
lean_object* v_val_2339_; lean_object* v___x_2340_; 
lean_dec(v_h__1_2335_);
v_val_2339_ = lean_ctor_get(v_x_2334_, 0);
lean_inc(v_val_2339_);
lean_dec_ref_known(v_x_2334_, 1);
v___x_2340_ = lean_apply_1(v_h__2_2336_, v_val_2339_);
return v___x_2340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter(lean_object* v_00_u03b1_2341_, lean_object* v_00_u03b2_2342_, lean_object* v_a_2343_, lean_object* v_motive_2344_, lean_object* v_x_2345_, lean_object* v_h__1_2346_, lean_object* v_h__2_2347_){
_start:
{
if (lean_obj_tag(v_x_2345_) == 0)
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
lean_dec(v_h__2_2347_);
v___x_2348_ = lean_box(0);
v___x_2349_ = lean_apply_1(v_h__1_2346_, v___x_2348_);
return v___x_2349_;
}
else
{
lean_object* v_val_2350_; lean_object* v___x_2351_; 
lean_dec(v_h__1_2346_);
v_val_2350_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_val_2350_);
lean_dec_ref_known(v_x_2345_, 1);
v___x_2351_ = lean_apply_1(v_h__2_2347_, v_val_2350_);
return v___x_2351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter___boxed(lean_object* v_00_u03b1_2352_, lean_object* v_00_u03b2_2353_, lean_object* v_a_2354_, lean_object* v_motive_2355_, lean_object* v_x_2356_, lean_object* v_h__1_2357_, lean_object* v_h__2_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_modify_match__1_splitter(v_00_u03b1_2352_, v_00_u03b2_2353_, v_a_2354_, v_motive_2355_, v_x_2356_, v_h__1_2357_, v_h__2_2358_);
lean_dec(v_a_2354_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapStep___redArg(lean_object* v_f_2360_, lean_object* v_m_2361_, lean_object* v_target_2362_, lean_object* v_i_2363_){
_start:
{
lean_object* v_keyArray_2364_; lean_object* v_valueArray_2365_; lean_object* v___x_2366_; uint8_t v_isSome_2367_; 
v_keyArray_2364_ = lean_ctor_get(v_m_2361_, 1);
v_valueArray_2365_ = lean_ctor_get(v_m_2361_, 2);
v___x_2366_ = lean_array_fget_borrowed(v_keyArray_2364_, v_i_2363_);
v_isSome_2367_ = lean_noption_is_some(v___x_2366_);
if (v_isSome_2367_ == 0)
{
lean_dec_ref(v_f_2360_);
return v_target_2362_;
}
else
{
lean_object* v___x_2368_; uint8_t v_isSome_2369_; 
v___x_2368_ = lean_array_fget_borrowed(v_valueArray_2365_, v_i_2363_);
v_isSome_2369_ = lean_noption_is_some(v___x_2368_);
if (v_isSome_2369_ == 0)
{
lean_dec_ref(v_f_2360_);
return v_target_2362_;
}
else
{
lean_object* v_val_2370_; lean_object* v_val_2371_; lean_object* v___x_2372_; 
lean_inc(v___x_2366_);
v_val_2370_ = lean_noption_get(v___x_2366_);
lean_inc(v___x_2368_);
v_val_2371_ = lean_noption_get(v___x_2368_);
v___x_2372_ = lean_apply_2(v_f_2360_, v_val_2370_, v_val_2371_);
if (lean_obj_tag(v___x_2372_) == 0)
{
return v_target_2362_;
}
else
{
lean_object* v_val_2373_; lean_object* v_size_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_next_2377_; 
v_val_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_val_2373_);
lean_dec_ref_known(v___x_2372_, 1);
v_size_2374_ = lean_ctor_get(v_target_2362_, 0);
v___x_2375_ = lean_unsigned_to_nat(1u);
v___x_2376_ = lean_nat_add(v_size_2374_, v___x_2375_);
v_next_2377_ = l_Std_DHashMap_Raw_setValue___redArg(v_target_2362_, v___x_2376_, v_i_2363_, v_val_2373_);
return v_next_2377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapStep___redArg___boxed(lean_object* v_f_2378_, lean_object* v_m_2379_, lean_object* v_target_2380_, lean_object* v_i_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Std_DHashMap_Internal_Raw_u2080_filterMapStep___redArg(v_f_2378_, v_m_2379_, v_target_2380_, v_i_2381_);
lean_dec(v_i_2381_);
lean_dec_ref(v_m_2379_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapStep(lean_object* v_00_u03b1_2383_, lean_object* v_00_u03b2_2384_, lean_object* v_00_u03b3_2385_, lean_object* v_f_2386_, lean_object* v_m_2387_, lean_object* v_target_2388_, lean_object* v_i_2389_, lean_object* v_hi_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Std_DHashMap_Internal_Raw_u2080_filterMapStep___redArg(v_f_2386_, v_m_2387_, v_target_2388_, v_i_2389_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapStep___boxed(lean_object* v_00_u03b1_2392_, lean_object* v_00_u03b2_2393_, lean_object* v_00_u03b3_2394_, lean_object* v_f_2395_, lean_object* v_m_2396_, lean_object* v_target_2397_, lean_object* v_i_2398_, lean_object* v_hi_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Std_DHashMap_Internal_Raw_u2080_filterMapStep(v_00_u03b1_2392_, v_00_u03b2_2393_, v_00_u03b3_2394_, v_f_2395_, v_m_2396_, v_target_2397_, v_i_2398_, v_hi_2399_);
lean_dec(v_i_2398_);
lean_dec_ref(v_m_2396_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg(lean_object* v_f_2401_, lean_object* v_m_2402_, lean_object* v_target_2403_, lean_object* v_i_2404_){
_start:
{
lean_object* v_keyArray_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
v_keyArray_2405_ = lean_ctor_get(v_m_2402_, 1);
v___x_2406_ = lean_array_get_size(v_keyArray_2405_);
v___x_2407_ = lean_nat_dec_lt(v_i_2404_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_dec(v_i_2404_);
lean_dec_ref(v_f_2401_);
return v_target_2403_;
}
else
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_inc_ref(v_f_2401_);
v___x_2408_ = l_Std_DHashMap_Internal_Raw_u2080_filterMapStep___redArg(v_f_2401_, v_m_2402_, v_target_2403_, v_i_2404_);
v___x_2409_ = lean_unsigned_to_nat(1u);
v___x_2410_ = lean_nat_add(v_i_2404_, v___x_2409_);
lean_dec(v_i_2404_);
v_target_2403_ = v___x_2408_;
v_i_2404_ = v___x_2410_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg___boxed(lean_object* v_f_2412_, lean_object* v_m_2413_, lean_object* v_target_2414_, lean_object* v_i_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg(v_f_2412_, v_m_2413_, v_target_2414_, v_i_2415_);
lean_dec_ref(v_m_2413_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop(lean_object* v_00_u03b1_2417_, lean_object* v_00_u03b2_2418_, lean_object* v_00_u03b3_2419_, lean_object* v_f_2420_, lean_object* v_m_2421_, lean_object* v_target_2422_, lean_object* v_i_2423_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg(v_f_2420_, v_m_2421_, v_target_2422_, v_i_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___boxed(lean_object* v_00_u03b1_2425_, lean_object* v_00_u03b2_2426_, lean_object* v_00_u03b3_2427_, lean_object* v_f_2428_, lean_object* v_m_2429_, lean_object* v_target_2430_, lean_object* v_i_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop(v_00_u03b1_2425_, v_00_u03b2_2426_, v_00_u03b3_2427_, v_f_2428_, v_m_2429_, v_target_2430_, v_i_2431_);
lean_dec_ref(v_m_2429_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapTarget___redArg(lean_object* v_m_2433_){
_start:
{
lean_object* v_keyArray_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2445_; 
v_keyArray_2434_ = lean_ctor_get(v_m_2433_, 1);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_m_2433_);
if (v_isSharedCheck_2445_ == 0)
{
lean_object* v_unused_2446_; lean_object* v_unused_2447_; 
v_unused_2446_ = lean_ctor_get(v_m_2433_, 2);
lean_dec(v_unused_2446_);
v_unused_2447_ = lean_ctor_get(v_m_2433_, 0);
lean_dec(v_unused_2447_);
v___x_2436_ = v_m_2433_;
v_isShared_2437_ = v_isSharedCheck_2445_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_keyArray_2434_);
lean_dec(v_m_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2445_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2438_ = lean_unsigned_to_nat(0u);
v___x_2439_ = lean_array_get_size(v_keyArray_2434_);
v___x_2440_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0);
v___x_2441_ = lean_mk_array(v___x_2439_, v___x_2440_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 2, v___x_2441_);
lean_ctor_set(v___x_2436_, 0, v___x_2438_);
v___x_2443_ = v___x_2436_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_keyArray_2434_);
lean_ctor_set(v_reuseFailAlloc_2444_, 2, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapTarget(lean_object* v_00_u03b1_2448_, lean_object* v_00_u03b2_2449_, lean_object* v_00_u03b3_2450_, lean_object* v_m_2451_){
_start:
{
lean_object* v_keyArray_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2463_; 
v_keyArray_2452_ = lean_ctor_get(v_m_2451_, 1);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_m_2451_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; lean_object* v_unused_2465_; 
v_unused_2464_ = lean_ctor_get(v_m_2451_, 2);
lean_dec(v_unused_2464_);
v_unused_2465_ = lean_ctor_get(v_m_2451_, 0);
lean_dec(v_unused_2465_);
v___x_2454_ = v_m_2451_;
v_isShared_2455_ = v_isSharedCheck_2463_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_keyArray_2452_);
lean_dec(v_m_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2463_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2456_ = lean_unsigned_to_nat(0u);
v___x_2457_ = lean_array_get_size(v_keyArray_2452_);
v___x_2458_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0);
v___x_2459_ = lean_mk_array(v___x_2457_, v___x_2458_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 2, v___x_2459_);
lean_ctor_set(v___x_2454_, 0, v___x_2456_);
v___x_2461_ = v___x_2454_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2456_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_keyArray_2452_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object* v_f_2466_, lean_object* v_m_2467_){
_start:
{
lean_object* v_keyArray_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v_keyArray_2468_ = lean_ctor_get(v_m_2467_, 1);
v___x_2469_ = lean_unsigned_to_nat(0u);
v___x_2470_ = lean_array_get_size(v_keyArray_2468_);
v___x_2471_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg___closed__0);
v___x_2472_ = lean_mk_array(v___x_2470_, v___x_2471_);
lean_inc_ref(v_keyArray_2468_);
v___x_2473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2469_);
lean_ctor_set(v___x_2473_, 1, v_keyArray_2468_);
lean_ctor_set(v___x_2473_, 2, v___x_2472_);
v___x_2474_ = l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg(v_f_2466_, v_m_2467_, v___x_2473_, v___x_2469_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg___boxed(lean_object* v_f_2475_, lean_object* v_m_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2475_, v_m_2476_);
lean_dec_ref(v_m_2476_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap(lean_object* v_00_u03b1_2478_, lean_object* v_00_u03b2_2479_, lean_object* v_00_u03b3_2480_, lean_object* v_f_2481_, lean_object* v_m_2482_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2481_, v_m_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___boxed(lean_object* v_00_u03b1_2484_, lean_object* v_00_u03b2_2485_, lean_object* v_00_u03b3_2486_, lean_object* v_f_2487_, lean_object* v_m_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap(v_00_u03b1_2484_, v_00_u03b2_2485_, v_00_u03b3_2486_, v_f_2487_, v_m_2488_);
lean_dec_ref(v_m_2488_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg___lam__0(lean_object* v_f_2490_, lean_object* v_k_2491_, lean_object* v_v_2492_){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_apply_2(v_f_2490_, v_k_2491_, v_v_2492_);
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object* v_f_2495_, lean_object* v_m_2496_){
_start:
{
lean_object* v___f_2497_; lean_object* v___x_2498_; 
v___f_2497_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_map___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2497_, 0, v_f_2495_);
v___x_2498_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v___f_2497_, v_m_2496_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg___boxed(lean_object* v_f_2499_, lean_object* v_m_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2499_, v_m_2500_);
lean_dec_ref(v_m_2500_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map(lean_object* v_00_u03b1_2502_, lean_object* v_00_u03b2_2503_, lean_object* v_00_u03b3_2504_, lean_object* v_f_2505_, lean_object* v_m_2506_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2505_, v_m_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___boxed(lean_object* v_00_u03b1_2508_, lean_object* v_00_u03b2_2509_, lean_object* v_00_u03b3_2510_, lean_object* v_f_2511_, lean_object* v_m_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Std_DHashMap_Internal_Raw_u2080_map(v_00_u03b1_2508_, v_00_u03b2_2509_, v_00_u03b3_2510_, v_f_2511_, v_m_2512_);
lean_dec_ref(v_m_2512_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg___lam__0(lean_object* v_f_2514_, lean_object* v_k_2515_, lean_object* v_v_2516_){
_start:
{
lean_object* v___x_2517_; uint8_t v___x_2518_; 
lean_inc(v_v_2516_);
v___x_2517_ = lean_apply_2(v_f_2514_, v_k_2515_, v_v_2516_);
v___x_2518_ = lean_unbox(v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; 
lean_dec(v_v_2516_);
v___x_2519_ = lean_box(0);
return v___x_2519_;
}
else
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2520_, 0, v_v_2516_);
return v___x_2520_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object* v_f_2521_, lean_object* v_m_2522_){
_start:
{
lean_object* v___f_2523_; lean_object* v___x_2524_; 
v___f_2523_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2523_, 0, v_f_2521_);
v___x_2524_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v___f_2523_, v_m_2522_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg___boxed(lean_object* v_f_2525_, lean_object* v_m_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2525_, v_m_2526_);
lean_dec_ref(v_m_2526_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter(lean_object* v_00_u03b1_2528_, lean_object* v_00_u03b2_2529_, lean_object* v_f_2530_, lean_object* v_m_2531_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2530_, v_m_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___boxed(lean_object* v_00_u03b1_2533_, lean_object* v_00_u03b2_2534_, lean_object* v_f_2535_, lean_object* v_m_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Std_DHashMap_Internal_Raw_u2080_filter(v_00_u03b1_2533_, v_00_u03b2_2534_, v_f_2535_, v_m_2536_);
lean_dec_ref(v_m_2536_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg___lam__0(lean_object* v_inst_2538_, lean_object* v_inst_2539_, lean_object* v_x_2540_, lean_object* v_____s_2541_){
_start:
{
lean_object* v_fst_2542_; lean_object* v_snd_2543_; lean_object* v___y_2545_; lean_object* v_i_2546_; lean_object* v___y_2553_; lean_object* v___y_2565_; lean_object* v_i_2566_; lean_object* v___x_2584_; 
v_fst_2542_ = lean_ctor_get(v_x_2540_, 0);
lean_inc_n(v_fst_2542_, 2);
v_snd_2543_ = lean_ctor_get(v_x_2540_, 1);
lean_inc(v_snd_2543_);
lean_dec_ref(v_x_2540_);
lean_inc_ref(v_inst_2539_);
lean_inc_ref(v_inst_2538_);
v___x_2584_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2538_, v_inst_2539_, v_____s_2541_, v_fst_2542_);
switch(lean_obj_tag(v___x_2584_))
{
case 0:
{
lean_object* v_index_2585_; lean_object* v_size_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_dec_ref(v_inst_2539_);
lean_dec_ref(v_inst_2538_);
v_index_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_index_2585_);
lean_dec_ref_known(v___x_2584_, 3);
v_size_2586_ = lean_ctor_get(v_____s_2541_, 0);
lean_inc(v_size_2586_);
v___x_2587_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_2541_, v_size_2586_, v_index_2585_, v_fst_2542_, v_snd_2543_);
lean_dec(v_index_2585_);
v___x_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
return v___x_2588_;
}
case 1:
{
lean_object* v_index_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2608_; 
v_index_2589_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2591_ = v___x_2584_;
v_isShared_2592_ = v_isSharedCheck_2608_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_index_2589_);
lean_dec(v___x_2584_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2608_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v_size_2593_; lean_object* v_keyArray_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v_size_2593_ = lean_ctor_get(v_____s_2541_, 0);
v_keyArray_2594_ = lean_ctor_get(v_____s_2541_, 1);
v___x_2595_ = lean_unsigned_to_nat(1u);
v___x_2596_ = lean_nat_add(v_size_2593_, v___x_2595_);
v___x_2597_ = lean_array_get_size(v_keyArray_2594_);
v___x_2598_ = lean_nat_dec_lt(v___x_2596_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_dec(v___x_2596_);
lean_del_object(v___x_2591_);
lean_dec(v_index_2589_);
goto v___jp_2572_;
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2599_ = lean_unsigned_to_nat(4u);
v___x_2600_ = lean_nat_mul(v___x_2596_, v___x_2599_);
v___x_2601_ = lean_unsigned_to_nat(3u);
v___x_2602_ = lean_nat_mul(v___x_2597_, v___x_2601_);
v___x_2603_ = lean_nat_dec_le(v___x_2600_, v___x_2602_);
lean_dec(v___x_2602_);
lean_dec(v___x_2600_);
if (v___x_2603_ == 0)
{
lean_dec(v___x_2596_);
lean_del_object(v___x_2591_);
lean_dec(v_index_2589_);
goto v___jp_2572_;
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
lean_dec_ref(v_inst_2539_);
lean_dec_ref(v_inst_2538_);
v___x_2604_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_2541_, v___x_2596_, v_index_2589_, v_fst_2542_, v_snd_2543_);
lean_dec(v_index_2589_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2604_);
v___x_2606_ = v___x_2591_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
default: 
{
lean_object* v_size_2609_; lean_object* v_keyArray_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v_size_2609_ = lean_ctor_get(v_____s_2541_, 0);
v_keyArray_2610_ = lean_ctor_get(v_____s_2541_, 1);
v___x_2611_ = lean_unsigned_to_nat(1u);
v___x_2612_ = lean_nat_add(v_size_2609_, v___x_2611_);
v___x_2613_ = lean_array_get_size(v_keyArray_2610_);
v___x_2614_ = lean_nat_dec_lt(v___x_2612_, v___x_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; 
lean_dec(v___x_2612_);
lean_inc_ref(v_inst_2539_);
lean_inc_ref(v_inst_2538_);
v___x_2615_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2538_, v_inst_2539_, v_____s_2541_);
v___y_2553_ = v___x_2615_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; uint8_t v___x_2620_; 
v___x_2616_ = lean_unsigned_to_nat(4u);
v___x_2617_ = lean_nat_mul(v___x_2612_, v___x_2616_);
lean_dec(v___x_2612_);
v___x_2618_ = lean_unsigned_to_nat(3u);
v___x_2619_ = lean_nat_mul(v___x_2613_, v___x_2618_);
v___x_2620_ = lean_nat_dec_le(v___x_2617_, v___x_2619_);
lean_dec(v___x_2619_);
lean_dec(v___x_2617_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; 
lean_inc_ref(v_inst_2539_);
lean_inc_ref(v_inst_2538_);
v___x_2621_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2538_, v_inst_2539_, v_____s_2541_);
v___y_2553_ = v___x_2621_;
goto v___jp_2552_;
}
else
{
v___y_2553_ = v_____s_2541_;
goto v___jp_2552_;
}
}
}
}
v___jp_2544_:
{
lean_object* v_size_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_size_2547_ = lean_ctor_get(v___y_2545_, 0);
v___x_2548_ = lean_unsigned_to_nat(1u);
v___x_2549_ = lean_nat_add(v_size_2547_, v___x_2548_);
v___x_2550_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2545_, v___x_2549_, v_i_2546_, v_fst_2542_, v_snd_2543_);
lean_dec(v_i_2546_);
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
return v___x_2551_;
}
v___jp_2552_:
{
lean_object* v___x_2554_; 
lean_inc(v_fst_2542_);
v___x_2554_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2538_, v_inst_2539_, v___y_2553_, v_fst_2542_);
switch(lean_obj_tag(v___x_2554_))
{
case 0:
{
lean_object* v_index_2555_; lean_object* v_size_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_index_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_index_2555_);
lean_dec_ref_known(v___x_2554_, 3);
v_size_2556_ = lean_ctor_get(v___y_2553_, 0);
lean_inc(v_size_2556_);
v___x_2557_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2553_, v_size_2556_, v_index_2555_, v_fst_2542_, v_snd_2543_);
lean_dec(v_index_2555_);
v___x_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
return v___x_2558_;
}
case 1:
{
lean_object* v_index_2559_; 
v_index_2559_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_index_2559_);
lean_dec_ref_known(v___x_2554_, 1);
v___y_2545_ = v___y_2553_;
v_i_2546_ = v_index_2559_;
goto v___jp_2544_;
}
default: 
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = lean_unsigned_to_nat(0u);
v___x_2561_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2553_, v___x_2560_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_index_2562_; 
v_index_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_index_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v___y_2545_ = v___y_2553_;
v_i_2546_ = v_index_2562_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2563_; 
lean_dec(v_snd_2543_);
lean_dec(v_fst_2542_);
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___y_2553_);
return v___x_2563_;
}
}
}
}
v___jp_2564_:
{
lean_object* v_size_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v_size_2567_ = lean_ctor_get(v___y_2565_, 0);
v___x_2568_ = lean_unsigned_to_nat(1u);
v___x_2569_ = lean_nat_add(v_size_2567_, v___x_2568_);
v___x_2570_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2565_, v___x_2569_, v_i_2566_, v_fst_2542_, v_snd_2543_);
lean_dec(v_i_2566_);
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
v___jp_2572_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_inc_ref(v_inst_2539_);
lean_inc_ref(v_inst_2538_);
v___x_2573_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2538_, v_inst_2539_, v_____s_2541_);
lean_inc(v_fst_2542_);
v___x_2574_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2538_, v_inst_2539_, v___x_2573_, v_fst_2542_);
switch(lean_obj_tag(v___x_2574_))
{
case 0:
{
lean_object* v_index_2575_; lean_object* v_size_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_index_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_index_2575_);
lean_dec_ref_known(v___x_2574_, 3);
v_size_2576_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_size_2576_);
v___x_2577_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2573_, v_size_2576_, v_index_2575_, v_fst_2542_, v_snd_2543_);
lean_dec(v_index_2575_);
v___x_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
return v___x_2578_;
}
case 1:
{
lean_object* v_index_2579_; 
v_index_2579_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_index_2579_);
lean_dec_ref_known(v___x_2574_, 1);
v___y_2565_ = v___x_2573_;
v_i_2566_ = v_index_2579_;
goto v___jp_2564_;
}
default: 
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = lean_unsigned_to_nat(0u);
v___x_2581_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2573_, v___x_2580_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_index_2582_; 
v_index_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_index_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v___y_2565_ = v___x_2573_;
v_i_2566_ = v_index_2582_;
goto v___jp_2564_;
}
else
{
lean_object* v___x_2583_; 
lean_dec(v_snd_2543_);
lean_dec(v_fst_2542_);
v___x_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2573_);
return v___x_2583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object* v_inst_2622_, lean_object* v_inst_2623_, lean_object* v_inst_2624_, lean_object* v_m_2625_, lean_object* v_l_2626_){
_start:
{
lean_object* v___f_2627_; lean_object* v___x_2628_; 
v___f_2627_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2627_, 0, v_inst_2623_);
lean_closure_set(v___f_2627_, 1, v_inst_2624_);
v___x_2628_ = lean_apply_4(v_inst_2622_, lean_box(0), v_l_2626_, v_m_2625_, v___f_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany(lean_object* v_00_u03b1_2629_, lean_object* v_00_u03b2_2630_, lean_object* v_00_u03c1_2631_, lean_object* v_inst_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_m_2635_, lean_object* v_l_2636_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v_inst_2632_, v_inst_2633_, v_inst_2634_, v_m_2635_, v_l_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg___lam__0(lean_object* v_inst_2638_, lean_object* v_inst_2639_, lean_object* v_x_2640_, lean_object* v_____s_2641_){
_start:
{
lean_object* v_fst_2642_; lean_object* v_r_2643_; lean_object* v___x_2644_; 
v_fst_2642_ = lean_ctor_get(v_x_2640_, 0);
lean_inc(v_fst_2642_);
lean_dec_ref(v_x_2640_);
v_r_2643_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_2638_, v_inst_2639_, v_____s_2641_, v_fst_2642_);
v___x_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2644_, 0, v_r_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object* v_inst_2645_, lean_object* v_inst_2646_, lean_object* v_inst_2647_, lean_object* v_m_2648_, lean_object* v_l_2649_){
_start:
{
lean_object* v___f_2650_; lean_object* v___x_2651_; 
v___f_2650_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2650_, 0, v_inst_2646_);
lean_closure_set(v___f_2650_, 1, v_inst_2647_);
v___x_2651_ = lean_apply_4(v_inst_2645_, lean_box(0), v_l_2649_, v_m_2648_, v___f_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries(lean_object* v_00_u03b1_2652_, lean_object* v_00_u03b2_2653_, lean_object* v_00_u03c1_2654_, lean_object* v_inst_2655_, lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_m_2658_, lean_object* v_l_2659_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v_inst_2655_, v_inst_2656_, v_inst_2657_, v_m_2658_, v_l_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0(lean_object* v_inst_2661_, lean_object* v_inst_2662_, lean_object* v_x_2663_, lean_object* v_____s_2664_){
_start:
{
lean_object* v_fst_2665_; lean_object* v_snd_2666_; lean_object* v___y_2668_; lean_object* v_i_2669_; lean_object* v___y_2676_; lean_object* v___y_2688_; lean_object* v_i_2689_; lean_object* v___x_2707_; 
v_fst_2665_ = lean_ctor_get(v_x_2663_, 0);
lean_inc_n(v_fst_2665_, 2);
v_snd_2666_ = lean_ctor_get(v_x_2663_, 1);
lean_inc(v_snd_2666_);
lean_dec_ref(v_x_2663_);
lean_inc_ref(v_inst_2662_);
lean_inc_ref(v_inst_2661_);
v___x_2707_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2661_, v_inst_2662_, v_____s_2664_, v_fst_2665_);
switch(lean_obj_tag(v___x_2707_))
{
case 0:
{
lean_object* v___x_2708_; 
lean_dec_ref_known(v___x_2707_, 3);
lean_dec(v_snd_2666_);
lean_dec(v_fst_2665_);
lean_dec_ref(v_inst_2662_);
lean_dec_ref(v_inst_2661_);
v___x_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2708_, 0, v_____s_2664_);
return v___x_2708_;
}
case 1:
{
lean_object* v_index_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2728_; 
v_index_2709_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2711_ = v___x_2707_;
v_isShared_2712_ = v_isSharedCheck_2728_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_index_2709_);
lean_dec(v___x_2707_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2728_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v_size_2713_; lean_object* v_keyArray_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; 
v_size_2713_ = lean_ctor_get(v_____s_2664_, 0);
v_keyArray_2714_ = lean_ctor_get(v_____s_2664_, 1);
v___x_2715_ = lean_unsigned_to_nat(1u);
v___x_2716_ = lean_nat_add(v_size_2713_, v___x_2715_);
v___x_2717_ = lean_array_get_size(v_keyArray_2714_);
v___x_2718_ = lean_nat_dec_lt(v___x_2716_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_dec(v___x_2716_);
lean_del_object(v___x_2711_);
lean_dec(v_index_2709_);
goto v___jp_2695_;
}
else
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; uint8_t v___x_2723_; 
v___x_2719_ = lean_unsigned_to_nat(4u);
v___x_2720_ = lean_nat_mul(v___x_2716_, v___x_2719_);
v___x_2721_ = lean_unsigned_to_nat(3u);
v___x_2722_ = lean_nat_mul(v___x_2717_, v___x_2721_);
v___x_2723_ = lean_nat_dec_le(v___x_2720_, v___x_2722_);
lean_dec(v___x_2722_);
lean_dec(v___x_2720_);
if (v___x_2723_ == 0)
{
lean_dec(v___x_2716_);
lean_del_object(v___x_2711_);
lean_dec(v_index_2709_);
goto v___jp_2695_;
}
else
{
lean_object* v___x_2724_; lean_object* v___x_2726_; 
lean_dec_ref(v_inst_2662_);
lean_dec_ref(v_inst_2661_);
v___x_2724_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_2664_, v___x_2716_, v_index_2709_, v_fst_2665_, v_snd_2666_);
lean_dec(v_index_2709_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2724_);
v___x_2726_ = v___x_2711_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
default: 
{
lean_object* v_size_2729_; lean_object* v_keyArray_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v_size_2729_ = lean_ctor_get(v_____s_2664_, 0);
v_keyArray_2730_ = lean_ctor_get(v_____s_2664_, 1);
v___x_2731_ = lean_unsigned_to_nat(1u);
v___x_2732_ = lean_nat_add(v_size_2729_, v___x_2731_);
v___x_2733_ = lean_array_get_size(v_keyArray_2730_);
v___x_2734_ = lean_nat_dec_lt(v___x_2732_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; 
lean_dec(v___x_2732_);
lean_inc_ref(v_inst_2662_);
lean_inc_ref(v_inst_2661_);
v___x_2735_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2661_, v_inst_2662_, v_____s_2664_);
v___y_2676_ = v___x_2735_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2736_ = lean_unsigned_to_nat(4u);
v___x_2737_ = lean_nat_mul(v___x_2732_, v___x_2736_);
lean_dec(v___x_2732_);
v___x_2738_ = lean_unsigned_to_nat(3u);
v___x_2739_ = lean_nat_mul(v___x_2733_, v___x_2738_);
v___x_2740_ = lean_nat_dec_le(v___x_2737_, v___x_2739_);
lean_dec(v___x_2739_);
lean_dec(v___x_2737_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; 
lean_inc_ref(v_inst_2662_);
lean_inc_ref(v_inst_2661_);
v___x_2741_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2661_, v_inst_2662_, v_____s_2664_);
v___y_2676_ = v___x_2741_;
goto v___jp_2675_;
}
else
{
v___y_2676_ = v_____s_2664_;
goto v___jp_2675_;
}
}
}
}
v___jp_2667_:
{
lean_object* v_size_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_size_2670_ = lean_ctor_get(v___y_2668_, 0);
v___x_2671_ = lean_unsigned_to_nat(1u);
v___x_2672_ = lean_nat_add(v_size_2670_, v___x_2671_);
v___x_2673_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2668_, v___x_2672_, v_i_2669_, v_fst_2665_, v_snd_2666_);
lean_dec(v_i_2669_);
v___x_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
return v___x_2674_;
}
v___jp_2675_:
{
lean_object* v___x_2677_; 
lean_inc(v_fst_2665_);
v___x_2677_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2661_, v_inst_2662_, v___y_2676_, v_fst_2665_);
switch(lean_obj_tag(v___x_2677_))
{
case 0:
{
lean_object* v_index_2678_; lean_object* v_size_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v_index_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_index_2678_);
lean_dec_ref_known(v___x_2677_, 3);
v_size_2679_ = lean_ctor_get(v___y_2676_, 0);
lean_inc(v_size_2679_);
v___x_2680_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2676_, v_size_2679_, v_index_2678_, v_fst_2665_, v_snd_2666_);
lean_dec(v_index_2678_);
v___x_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
return v___x_2681_;
}
case 1:
{
lean_object* v_index_2682_; 
v_index_2682_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_index_2682_);
lean_dec_ref_known(v___x_2677_, 1);
v___y_2668_ = v___y_2676_;
v_i_2669_ = v_index_2682_;
goto v___jp_2667_;
}
default: 
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = lean_unsigned_to_nat(0u);
v___x_2684_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2676_, v___x_2683_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_index_2685_; 
v_index_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_index_2685_);
lean_dec_ref_known(v___x_2684_, 1);
v___y_2668_ = v___y_2676_;
v_i_2669_ = v_index_2685_;
goto v___jp_2667_;
}
else
{
lean_object* v___x_2686_; 
lean_dec(v_snd_2666_);
lean_dec(v_fst_2665_);
v___x_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___y_2676_);
return v___x_2686_;
}
}
}
}
v___jp_2687_:
{
lean_object* v_size_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v_size_2690_ = lean_ctor_get(v___y_2688_, 0);
v___x_2691_ = lean_unsigned_to_nat(1u);
v___x_2692_ = lean_nat_add(v_size_2690_, v___x_2691_);
v___x_2693_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2688_, v___x_2692_, v_i_2689_, v_fst_2665_, v_snd_2666_);
lean_dec(v_i_2689_);
v___x_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
return v___x_2694_;
}
v___jp_2695_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_inc_ref(v_inst_2662_);
lean_inc_ref(v_inst_2661_);
v___x_2696_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2661_, v_inst_2662_, v_____s_2664_);
lean_inc(v_fst_2665_);
v___x_2697_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2661_, v_inst_2662_, v___x_2696_, v_fst_2665_);
switch(lean_obj_tag(v___x_2697_))
{
case 0:
{
lean_object* v_index_2698_; lean_object* v_size_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v_index_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_index_2698_);
lean_dec_ref_known(v___x_2697_, 3);
v_size_2699_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_size_2699_);
v___x_2700_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2696_, v_size_2699_, v_index_2698_, v_fst_2665_, v_snd_2666_);
lean_dec(v_index_2698_);
v___x_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
return v___x_2701_;
}
case 1:
{
lean_object* v_index_2702_; 
v_index_2702_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_index_2702_);
lean_dec_ref_known(v___x_2697_, 1);
v___y_2688_ = v___x_2696_;
v_i_2689_ = v_index_2702_;
goto v___jp_2687_;
}
default: 
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2696_, v___x_2703_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_index_2705_; 
v_index_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_index_2705_);
lean_dec_ref_known(v___x_2704_, 1);
v___y_2688_ = v___x_2696_;
v_i_2689_ = v_index_2705_;
goto v___jp_2687_;
}
else
{
lean_object* v___x_2706_; 
lean_dec(v_snd_2666_);
lean_dec(v_fst_2665_);
v___x_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2696_);
return v___x_2706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg(lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v_inst_2744_, lean_object* v_m_2745_, lean_object* v_l_2746_){
_start:
{
lean_object* v___f_2747_; lean_object* v___x_2748_; 
v___f_2747_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2747_, 0, v_inst_2743_);
lean_closure_set(v___f_2747_, 1, v_inst_2744_);
v___x_2748_ = lean_apply_4(v_inst_2742_, lean_box(0), v_l_2746_, v_m_2745_, v___f_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew(lean_object* v_00_u03b1_2749_, lean_object* v_00_u03b2_2750_, lean_object* v_00_u03c1_2751_, lean_object* v_inst_2752_, lean_object* v_inst_2753_, lean_object* v_inst_2754_, lean_object* v_m_2755_, lean_object* v_l_2756_){
_start:
{
lean_object* v___f_2757_; lean_object* v___x_2758_; 
v___f_2757_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2757_, 0, v_inst_2753_);
lean_closure_set(v___f_2757_, 1, v_inst_2754_);
v___x_2758_ = lean_apply_4(v_inst_2752_, lean_box(0), v_l_2756_, v_m_2755_, v___f_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg(lean_object* v_inst_2759_, lean_object* v_inst_2760_, lean_object* v_m_2761_, lean_object* v_sofar_2762_, lean_object* v_k_2763_){
_start:
{
lean_object* v___x_2764_; 
lean_inc_ref(v_inst_2760_);
lean_inc_ref(v_inst_2759_);
v___x_2764_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_2759_, v_inst_2760_, v_m_2761_, v_k_2763_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_dec_ref(v_inst_2760_);
lean_dec_ref(v_inst_2759_);
return v_sofar_2762_;
}
else
{
lean_object* v_val_2765_; lean_object* v_fst_2766_; lean_object* v_snd_2767_; lean_object* v___y_2769_; lean_object* v_i_2770_; lean_object* v___y_2776_; lean_object* v___y_2786_; lean_object* v_i_2787_; lean_object* v___x_2802_; 
v_val_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_val_2765_);
lean_dec_ref_known(v___x_2764_, 1);
v_fst_2766_ = lean_ctor_get(v_val_2765_, 0);
lean_inc_n(v_fst_2766_, 2);
v_snd_2767_ = lean_ctor_get(v_val_2765_, 1);
lean_inc(v_snd_2767_);
lean_dec(v_val_2765_);
lean_inc_ref(v_inst_2760_);
lean_inc_ref(v_inst_2759_);
v___x_2802_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2759_, v_inst_2760_, v_sofar_2762_, v_fst_2766_);
switch(lean_obj_tag(v___x_2802_))
{
case 0:
{
lean_object* v_index_2803_; lean_object* v_size_2804_; lean_object* v___x_2805_; 
lean_dec_ref(v_inst_2760_);
lean_dec_ref(v_inst_2759_);
v_index_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_index_2803_);
lean_dec_ref_known(v___x_2802_, 3);
v_size_2804_ = lean_ctor_get(v_sofar_2762_, 0);
lean_inc(v_size_2804_);
v___x_2805_ = l_Std_DHashMap_Raw_setEntry___redArg(v_sofar_2762_, v_size_2804_, v_index_2803_, v_fst_2766_, v_snd_2767_);
lean_dec(v_index_2803_);
return v___x_2805_;
}
case 1:
{
lean_object* v_index_2806_; lean_object* v_size_2807_; lean_object* v_keyArray_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v_index_2806_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_index_2806_);
lean_dec_ref_known(v___x_2802_, 1);
v_size_2807_ = lean_ctor_get(v_sofar_2762_, 0);
v_keyArray_2808_ = lean_ctor_get(v_sofar_2762_, 1);
v___x_2809_ = lean_unsigned_to_nat(1u);
v___x_2810_ = lean_nat_add(v_size_2807_, v___x_2809_);
v___x_2811_ = lean_array_get_size(v_keyArray_2808_);
v___x_2812_ = lean_nat_dec_lt(v___x_2810_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_dec(v___x_2810_);
lean_dec(v_index_2806_);
goto v___jp_2792_;
}
else
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2813_ = lean_unsigned_to_nat(4u);
v___x_2814_ = lean_nat_mul(v___x_2810_, v___x_2813_);
v___x_2815_ = lean_unsigned_to_nat(3u);
v___x_2816_ = lean_nat_mul(v___x_2811_, v___x_2815_);
v___x_2817_ = lean_nat_dec_le(v___x_2814_, v___x_2816_);
lean_dec(v___x_2816_);
lean_dec(v___x_2814_);
if (v___x_2817_ == 0)
{
lean_dec(v___x_2810_);
lean_dec(v_index_2806_);
goto v___jp_2792_;
}
else
{
lean_object* v___x_2818_; 
lean_dec_ref(v_inst_2760_);
lean_dec_ref(v_inst_2759_);
v___x_2818_ = l_Std_DHashMap_Raw_setEntry___redArg(v_sofar_2762_, v___x_2810_, v_index_2806_, v_fst_2766_, v_snd_2767_);
lean_dec(v_index_2806_);
return v___x_2818_;
}
}
}
default: 
{
lean_object* v_size_2819_; lean_object* v_keyArray_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v_size_2819_ = lean_ctor_get(v_sofar_2762_, 0);
v_keyArray_2820_ = lean_ctor_get(v_sofar_2762_, 1);
v___x_2821_ = lean_unsigned_to_nat(1u);
v___x_2822_ = lean_nat_add(v_size_2819_, v___x_2821_);
v___x_2823_ = lean_array_get_size(v_keyArray_2820_);
v___x_2824_ = lean_nat_dec_lt(v___x_2822_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; 
lean_dec(v___x_2822_);
lean_inc_ref(v_inst_2760_);
lean_inc_ref(v_inst_2759_);
v___x_2825_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2759_, v_inst_2760_, v_sofar_2762_);
v___y_2776_ = v___x_2825_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; 
v___x_2826_ = lean_unsigned_to_nat(4u);
v___x_2827_ = lean_nat_mul(v___x_2822_, v___x_2826_);
lean_dec(v___x_2822_);
v___x_2828_ = lean_unsigned_to_nat(3u);
v___x_2829_ = lean_nat_mul(v___x_2823_, v___x_2828_);
v___x_2830_ = lean_nat_dec_le(v___x_2827_, v___x_2829_);
lean_dec(v___x_2829_);
lean_dec(v___x_2827_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; 
lean_inc_ref(v_inst_2760_);
lean_inc_ref(v_inst_2759_);
v___x_2831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2759_, v_inst_2760_, v_sofar_2762_);
v___y_2776_ = v___x_2831_;
goto v___jp_2775_;
}
else
{
v___y_2776_ = v_sofar_2762_;
goto v___jp_2775_;
}
}
}
}
v___jp_2768_:
{
lean_object* v_size_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v_size_2771_ = lean_ctor_get(v___y_2769_, 0);
v___x_2772_ = lean_unsigned_to_nat(1u);
v___x_2773_ = lean_nat_add(v_size_2771_, v___x_2772_);
v___x_2774_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2769_, v___x_2773_, v_i_2770_, v_fst_2766_, v_snd_2767_);
lean_dec(v_i_2770_);
return v___x_2774_;
}
v___jp_2775_:
{
lean_object* v___x_2777_; 
lean_inc(v_fst_2766_);
v___x_2777_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2759_, v_inst_2760_, v___y_2776_, v_fst_2766_);
switch(lean_obj_tag(v___x_2777_))
{
case 0:
{
lean_object* v_index_2778_; lean_object* v_size_2779_; lean_object* v___x_2780_; 
v_index_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_index_2778_);
lean_dec_ref_known(v___x_2777_, 3);
v_size_2779_ = lean_ctor_get(v___y_2776_, 0);
lean_inc(v_size_2779_);
v___x_2780_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2776_, v_size_2779_, v_index_2778_, v_fst_2766_, v_snd_2767_);
lean_dec(v_index_2778_);
return v___x_2780_;
}
case 1:
{
lean_object* v_index_2781_; 
v_index_2781_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_index_2781_);
lean_dec_ref_known(v___x_2777_, 1);
v___y_2769_ = v___y_2776_;
v_i_2770_ = v_index_2781_;
goto v___jp_2768_;
}
default: 
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = lean_unsigned_to_nat(0u);
v___x_2783_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2776_, v___x_2782_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_index_2784_; 
v_index_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_index_2784_);
lean_dec_ref_known(v___x_2783_, 1);
v___y_2769_ = v___y_2776_;
v_i_2770_ = v_index_2784_;
goto v___jp_2768_;
}
else
{
lean_dec(v_snd_2767_);
lean_dec(v_fst_2766_);
return v___y_2776_;
}
}
}
}
v___jp_2785_:
{
lean_object* v_size_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_size_2788_ = lean_ctor_get(v___y_2786_, 0);
v___x_2789_ = lean_unsigned_to_nat(1u);
v___x_2790_ = lean_nat_add(v_size_2788_, v___x_2789_);
v___x_2791_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2786_, v___x_2790_, v_i_2787_, v_fst_2766_, v_snd_2767_);
lean_dec(v_i_2787_);
return v___x_2791_;
}
v___jp_2792_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_inc_ref(v_inst_2760_);
lean_inc_ref(v_inst_2759_);
v___x_2793_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2759_, v_inst_2760_, v_sofar_2762_);
lean_inc(v_fst_2766_);
v___x_2794_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2759_, v_inst_2760_, v___x_2793_, v_fst_2766_);
switch(lean_obj_tag(v___x_2794_))
{
case 0:
{
lean_object* v_index_2795_; lean_object* v_size_2796_; lean_object* v___x_2797_; 
v_index_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_index_2795_);
lean_dec_ref_known(v___x_2794_, 3);
v_size_2796_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_size_2796_);
v___x_2797_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2793_, v_size_2796_, v_index_2795_, v_fst_2766_, v_snd_2767_);
lean_dec(v_index_2795_);
return v___x_2797_;
}
case 1:
{
lean_object* v_index_2798_; 
v_index_2798_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_index_2798_);
lean_dec_ref_known(v___x_2794_, 1);
v___y_2786_ = v___x_2793_;
v_i_2787_ = v_index_2798_;
goto v___jp_2785_;
}
default: 
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_unsigned_to_nat(0u);
v___x_2800_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2793_, v___x_2799_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_index_2801_; 
v_index_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_index_2801_);
lean_dec_ref_known(v___x_2800_, 1);
v___y_2786_ = v___x_2793_;
v_i_2787_ = v_index_2801_;
goto v___jp_2785_;
}
else
{
lean_dec(v_snd_2767_);
lean_dec(v_fst_2766_);
return v___x_2793_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg___boxed(lean_object* v_inst_2832_, lean_object* v_inst_2833_, lean_object* v_m_2834_, lean_object* v_sofar_2835_, lean_object* v_k_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg(v_inst_2832_, v_inst_2833_, v_m_2834_, v_sofar_2835_, v_k_2836_);
lean_dec_ref(v_m_2834_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn(lean_object* v_00_u03b1_2838_, lean_object* v_00_u03b2_2839_, lean_object* v_inst_2840_, lean_object* v_inst_2841_, lean_object* v_m_2842_, lean_object* v_sofar_2843_, lean_object* v_k_2844_){
_start:
{
lean_object* v___x_2845_; 
lean_inc_ref(v_inst_2841_);
lean_inc_ref(v_inst_2840_);
v___x_2845_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_2840_, v_inst_2841_, v_m_2842_, v_k_2844_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_dec_ref(v_inst_2841_);
lean_dec_ref(v_inst_2840_);
return v_sofar_2843_;
}
else
{
lean_object* v_val_2846_; lean_object* v_fst_2847_; lean_object* v_snd_2848_; lean_object* v___y_2850_; lean_object* v_i_2851_; lean_object* v___y_2857_; lean_object* v___y_2867_; lean_object* v_i_2868_; lean_object* v___x_2883_; 
v_val_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_val_2846_);
lean_dec_ref_known(v___x_2845_, 1);
v_fst_2847_ = lean_ctor_get(v_val_2846_, 0);
lean_inc_n(v_fst_2847_, 2);
v_snd_2848_ = lean_ctor_get(v_val_2846_, 1);
lean_inc(v_snd_2848_);
lean_dec(v_val_2846_);
lean_inc_ref(v_inst_2841_);
lean_inc_ref(v_inst_2840_);
v___x_2883_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2840_, v_inst_2841_, v_sofar_2843_, v_fst_2847_);
switch(lean_obj_tag(v___x_2883_))
{
case 0:
{
lean_object* v_index_2884_; lean_object* v_size_2885_; lean_object* v___x_2886_; 
lean_dec_ref(v_inst_2841_);
lean_dec_ref(v_inst_2840_);
v_index_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_index_2884_);
lean_dec_ref_known(v___x_2883_, 3);
v_size_2885_ = lean_ctor_get(v_sofar_2843_, 0);
lean_inc(v_size_2885_);
v___x_2886_ = l_Std_DHashMap_Raw_setEntry___redArg(v_sofar_2843_, v_size_2885_, v_index_2884_, v_fst_2847_, v_snd_2848_);
lean_dec(v_index_2884_);
return v___x_2886_;
}
case 1:
{
lean_object* v_index_2887_; lean_object* v_size_2888_; lean_object* v_keyArray_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; uint8_t v___x_2893_; 
v_index_2887_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_index_2887_);
lean_dec_ref_known(v___x_2883_, 1);
v_size_2888_ = lean_ctor_get(v_sofar_2843_, 0);
v_keyArray_2889_ = lean_ctor_get(v_sofar_2843_, 1);
v___x_2890_ = lean_unsigned_to_nat(1u);
v___x_2891_ = lean_nat_add(v_size_2888_, v___x_2890_);
v___x_2892_ = lean_array_get_size(v_keyArray_2889_);
v___x_2893_ = lean_nat_dec_lt(v___x_2891_, v___x_2892_);
if (v___x_2893_ == 0)
{
lean_dec(v___x_2891_);
lean_dec(v_index_2887_);
goto v___jp_2873_;
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; uint8_t v___x_2898_; 
v___x_2894_ = lean_unsigned_to_nat(4u);
v___x_2895_ = lean_nat_mul(v___x_2891_, v___x_2894_);
v___x_2896_ = lean_unsigned_to_nat(3u);
v___x_2897_ = lean_nat_mul(v___x_2892_, v___x_2896_);
v___x_2898_ = lean_nat_dec_le(v___x_2895_, v___x_2897_);
lean_dec(v___x_2897_);
lean_dec(v___x_2895_);
if (v___x_2898_ == 0)
{
lean_dec(v___x_2891_);
lean_dec(v_index_2887_);
goto v___jp_2873_;
}
else
{
lean_object* v___x_2899_; 
lean_dec_ref(v_inst_2841_);
lean_dec_ref(v_inst_2840_);
v___x_2899_ = l_Std_DHashMap_Raw_setEntry___redArg(v_sofar_2843_, v___x_2891_, v_index_2887_, v_fst_2847_, v_snd_2848_);
lean_dec(v_index_2887_);
return v___x_2899_;
}
}
}
default: 
{
lean_object* v_size_2900_; lean_object* v_keyArray_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v_size_2900_ = lean_ctor_get(v_sofar_2843_, 0);
v_keyArray_2901_ = lean_ctor_get(v_sofar_2843_, 1);
v___x_2902_ = lean_unsigned_to_nat(1u);
v___x_2903_ = lean_nat_add(v_size_2900_, v___x_2902_);
v___x_2904_ = lean_array_get_size(v_keyArray_2901_);
v___x_2905_ = lean_nat_dec_lt(v___x_2903_, v___x_2904_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; 
lean_dec(v___x_2903_);
lean_inc_ref(v_inst_2841_);
lean_inc_ref(v_inst_2840_);
v___x_2906_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2840_, v_inst_2841_, v_sofar_2843_);
v___y_2857_ = v___x_2906_;
goto v___jp_2856_;
}
else
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2907_ = lean_unsigned_to_nat(4u);
v___x_2908_ = lean_nat_mul(v___x_2903_, v___x_2907_);
lean_dec(v___x_2903_);
v___x_2909_ = lean_unsigned_to_nat(3u);
v___x_2910_ = lean_nat_mul(v___x_2904_, v___x_2909_);
v___x_2911_ = lean_nat_dec_le(v___x_2908_, v___x_2910_);
lean_dec(v___x_2910_);
lean_dec(v___x_2908_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; 
lean_inc_ref(v_inst_2841_);
lean_inc_ref(v_inst_2840_);
v___x_2912_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2840_, v_inst_2841_, v_sofar_2843_);
v___y_2857_ = v___x_2912_;
goto v___jp_2856_;
}
else
{
v___y_2857_ = v_sofar_2843_;
goto v___jp_2856_;
}
}
}
}
v___jp_2849_:
{
lean_object* v_size_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_size_2852_ = lean_ctor_get(v___y_2850_, 0);
v___x_2853_ = lean_unsigned_to_nat(1u);
v___x_2854_ = lean_nat_add(v_size_2852_, v___x_2853_);
v___x_2855_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2850_, v___x_2854_, v_i_2851_, v_fst_2847_, v_snd_2848_);
lean_dec(v_i_2851_);
return v___x_2855_;
}
v___jp_2856_:
{
lean_object* v___x_2858_; 
lean_inc(v_fst_2847_);
v___x_2858_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2840_, v_inst_2841_, v___y_2857_, v_fst_2847_);
switch(lean_obj_tag(v___x_2858_))
{
case 0:
{
lean_object* v_index_2859_; lean_object* v_size_2860_; lean_object* v___x_2861_; 
v_index_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_index_2859_);
lean_dec_ref_known(v___x_2858_, 3);
v_size_2860_ = lean_ctor_get(v___y_2857_, 0);
lean_inc(v_size_2860_);
v___x_2861_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2857_, v_size_2860_, v_index_2859_, v_fst_2847_, v_snd_2848_);
lean_dec(v_index_2859_);
return v___x_2861_;
}
case 1:
{
lean_object* v_index_2862_; 
v_index_2862_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_index_2862_);
lean_dec_ref_known(v___x_2858_, 1);
v___y_2850_ = v___y_2857_;
v_i_2851_ = v_index_2862_;
goto v___jp_2849_;
}
default: 
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = lean_unsigned_to_nat(0u);
v___x_2864_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2857_, v___x_2863_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_index_2865_; 
v_index_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_index_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___y_2850_ = v___y_2857_;
v_i_2851_ = v_index_2865_;
goto v___jp_2849_;
}
else
{
lean_dec(v_snd_2848_);
lean_dec(v_fst_2847_);
return v___y_2857_;
}
}
}
}
v___jp_2866_:
{
lean_object* v_size_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v_size_2869_ = lean_ctor_get(v___y_2867_, 0);
v___x_2870_ = lean_unsigned_to_nat(1u);
v___x_2871_ = lean_nat_add(v_size_2869_, v___x_2870_);
v___x_2872_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2867_, v___x_2871_, v_i_2868_, v_fst_2847_, v_snd_2848_);
lean_dec(v_i_2868_);
return v___x_2872_;
}
v___jp_2873_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
lean_inc_ref(v_inst_2841_);
lean_inc_ref(v_inst_2840_);
v___x_2874_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2840_, v_inst_2841_, v_sofar_2843_);
lean_inc(v_fst_2847_);
v___x_2875_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2840_, v_inst_2841_, v___x_2874_, v_fst_2847_);
switch(lean_obj_tag(v___x_2875_))
{
case 0:
{
lean_object* v_index_2876_; lean_object* v_size_2877_; lean_object* v___x_2878_; 
v_index_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_index_2876_);
lean_dec_ref_known(v___x_2875_, 3);
v_size_2877_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_size_2877_);
v___x_2878_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2874_, v_size_2877_, v_index_2876_, v_fst_2847_, v_snd_2848_);
lean_dec(v_index_2876_);
return v___x_2878_;
}
case 1:
{
lean_object* v_index_2879_; 
v_index_2879_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_index_2879_);
lean_dec_ref_known(v___x_2875_, 1);
v___y_2867_ = v___x_2874_;
v_i_2868_ = v_index_2879_;
goto v___jp_2866_;
}
default: 
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = lean_unsigned_to_nat(0u);
v___x_2881_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2874_, v___x_2880_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_index_2882_; 
v_index_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_index_2882_);
lean_dec_ref_known(v___x_2881_, 1);
v___y_2867_ = v___x_2874_;
v_i_2868_ = v_index_2882_;
goto v___jp_2866_;
}
else
{
lean_dec(v_snd_2848_);
lean_dec(v_fst_2847_);
return v___x_2874_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___boxed(lean_object* v_00_u03b1_2913_, lean_object* v_00_u03b2_2914_, lean_object* v_inst_2915_, lean_object* v_inst_2916_, lean_object* v_m_2917_, lean_object* v_sofar_2918_, lean_object* v_k_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn(v_00_u03b1_2913_, v_00_u03b2_2914_, v_inst_2915_, v_inst_2916_, v_m_2917_, v_sofar_2918_, v_k_2919_);
lean_dec_ref(v_m_2917_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0(lean_object* v_inst_2921_, lean_object* v_inst_2922_, lean_object* v_m_u2081_2923_, lean_object* v_x1_2924_, lean_object* v_x2_2925_, lean_object* v_x3_2926_){
_start:
{
lean_object* v___x_2927_; 
lean_inc_ref(v_inst_2922_);
lean_inc_ref(v_inst_2921_);
v___x_2927_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_2921_, v_inst_2922_, v_m_u2081_2923_, v_x2_2925_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_dec_ref(v_inst_2922_);
lean_dec_ref(v_inst_2921_);
return v_x1_2924_;
}
else
{
lean_object* v_val_2928_; lean_object* v_fst_2929_; lean_object* v_snd_2930_; lean_object* v___y_2932_; lean_object* v_i_2933_; lean_object* v___y_2939_; lean_object* v___y_2949_; lean_object* v_i_2950_; lean_object* v___x_2965_; 
v_val_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_val_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v_fst_2929_ = lean_ctor_get(v_val_2928_, 0);
lean_inc_n(v_fst_2929_, 2);
v_snd_2930_ = lean_ctor_get(v_val_2928_, 1);
lean_inc(v_snd_2930_);
lean_dec(v_val_2928_);
lean_inc_ref(v_inst_2922_);
lean_inc_ref(v_inst_2921_);
v___x_2965_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2921_, v_inst_2922_, v_x1_2924_, v_fst_2929_);
switch(lean_obj_tag(v___x_2965_))
{
case 0:
{
lean_object* v_index_2966_; lean_object* v_size_2967_; lean_object* v___x_2968_; 
lean_dec_ref(v_inst_2922_);
lean_dec_ref(v_inst_2921_);
v_index_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_index_2966_);
lean_dec_ref_known(v___x_2965_, 3);
v_size_2967_ = lean_ctor_get(v_x1_2924_, 0);
lean_inc(v_size_2967_);
v___x_2968_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x1_2924_, v_size_2967_, v_index_2966_, v_fst_2929_, v_snd_2930_);
lean_dec(v_index_2966_);
return v___x_2968_;
}
case 1:
{
lean_object* v_index_2969_; lean_object* v_size_2970_; lean_object* v_keyArray_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; uint8_t v___x_2975_; 
v_index_2969_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_index_2969_);
lean_dec_ref_known(v___x_2965_, 1);
v_size_2970_ = lean_ctor_get(v_x1_2924_, 0);
v_keyArray_2971_ = lean_ctor_get(v_x1_2924_, 1);
v___x_2972_ = lean_unsigned_to_nat(1u);
v___x_2973_ = lean_nat_add(v_size_2970_, v___x_2972_);
v___x_2974_ = lean_array_get_size(v_keyArray_2971_);
v___x_2975_ = lean_nat_dec_lt(v___x_2973_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_dec(v___x_2973_);
lean_dec(v_index_2969_);
goto v___jp_2955_;
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v___x_2976_ = lean_unsigned_to_nat(4u);
v___x_2977_ = lean_nat_mul(v___x_2973_, v___x_2976_);
v___x_2978_ = lean_unsigned_to_nat(3u);
v___x_2979_ = lean_nat_mul(v___x_2974_, v___x_2978_);
v___x_2980_ = lean_nat_dec_le(v___x_2977_, v___x_2979_);
lean_dec(v___x_2979_);
lean_dec(v___x_2977_);
if (v___x_2980_ == 0)
{
lean_dec(v___x_2973_);
lean_dec(v_index_2969_);
goto v___jp_2955_;
}
else
{
lean_object* v___x_2981_; 
lean_dec_ref(v_inst_2922_);
lean_dec_ref(v_inst_2921_);
v___x_2981_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x1_2924_, v___x_2973_, v_index_2969_, v_fst_2929_, v_snd_2930_);
lean_dec(v_index_2969_);
return v___x_2981_;
}
}
}
default: 
{
lean_object* v_size_2982_; lean_object* v_keyArray_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v_size_2982_ = lean_ctor_get(v_x1_2924_, 0);
v_keyArray_2983_ = lean_ctor_get(v_x1_2924_, 1);
v___x_2984_ = lean_unsigned_to_nat(1u);
v___x_2985_ = lean_nat_add(v_size_2982_, v___x_2984_);
v___x_2986_ = lean_array_get_size(v_keyArray_2983_);
v___x_2987_ = lean_nat_dec_lt(v___x_2985_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; 
lean_dec(v___x_2985_);
lean_inc_ref(v_inst_2922_);
lean_inc_ref(v_inst_2921_);
v___x_2988_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2921_, v_inst_2922_, v_x1_2924_);
v___y_2939_ = v___x_2988_;
goto v___jp_2938_;
}
else
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; uint8_t v___x_2993_; 
v___x_2989_ = lean_unsigned_to_nat(4u);
v___x_2990_ = lean_nat_mul(v___x_2985_, v___x_2989_);
lean_dec(v___x_2985_);
v___x_2991_ = lean_unsigned_to_nat(3u);
v___x_2992_ = lean_nat_mul(v___x_2986_, v___x_2991_);
v___x_2993_ = lean_nat_dec_le(v___x_2990_, v___x_2992_);
lean_dec(v___x_2992_);
lean_dec(v___x_2990_);
if (v___x_2993_ == 0)
{
lean_object* v___x_2994_; 
lean_inc_ref(v_inst_2922_);
lean_inc_ref(v_inst_2921_);
v___x_2994_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2921_, v_inst_2922_, v_x1_2924_);
v___y_2939_ = v___x_2994_;
goto v___jp_2938_;
}
else
{
v___y_2939_ = v_x1_2924_;
goto v___jp_2938_;
}
}
}
}
v___jp_2931_:
{
lean_object* v_size_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_size_2934_ = lean_ctor_get(v___y_2932_, 0);
v___x_2935_ = lean_unsigned_to_nat(1u);
v___x_2936_ = lean_nat_add(v_size_2934_, v___x_2935_);
v___x_2937_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2932_, v___x_2936_, v_i_2933_, v_fst_2929_, v_snd_2930_);
lean_dec(v_i_2933_);
return v___x_2937_;
}
v___jp_2938_:
{
lean_object* v___x_2940_; 
lean_inc(v_fst_2929_);
v___x_2940_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2921_, v_inst_2922_, v___y_2939_, v_fst_2929_);
switch(lean_obj_tag(v___x_2940_))
{
case 0:
{
lean_object* v_index_2941_; lean_object* v_size_2942_; lean_object* v___x_2943_; 
v_index_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_index_2941_);
lean_dec_ref_known(v___x_2940_, 3);
v_size_2942_ = lean_ctor_get(v___y_2939_, 0);
lean_inc(v_size_2942_);
v___x_2943_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2939_, v_size_2942_, v_index_2941_, v_fst_2929_, v_snd_2930_);
lean_dec(v_index_2941_);
return v___x_2943_;
}
case 1:
{
lean_object* v_index_2944_; 
v_index_2944_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_index_2944_);
lean_dec_ref_known(v___x_2940_, 1);
v___y_2932_ = v___y_2939_;
v_i_2933_ = v_index_2944_;
goto v___jp_2931_;
}
default: 
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = lean_unsigned_to_nat(0u);
v___x_2946_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2939_, v___x_2945_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_index_2947_; 
v_index_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_index_2947_);
lean_dec_ref_known(v___x_2946_, 1);
v___y_2932_ = v___y_2939_;
v_i_2933_ = v_index_2947_;
goto v___jp_2931_;
}
else
{
lean_dec(v_snd_2930_);
lean_dec(v_fst_2929_);
return v___y_2939_;
}
}
}
}
v___jp_2948_:
{
lean_object* v_size_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_size_2951_ = lean_ctor_get(v___y_2949_, 0);
v___x_2952_ = lean_unsigned_to_nat(1u);
v___x_2953_ = lean_nat_add(v_size_2951_, v___x_2952_);
v___x_2954_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2949_, v___x_2953_, v_i_2950_, v_fst_2929_, v_snd_2930_);
lean_dec(v_i_2950_);
return v___x_2954_;
}
v___jp_2955_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
lean_inc_ref(v_inst_2922_);
lean_inc_ref(v_inst_2921_);
v___x_2956_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2921_, v_inst_2922_, v_x1_2924_);
lean_inc(v_fst_2929_);
v___x_2957_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2921_, v_inst_2922_, v___x_2956_, v_fst_2929_);
switch(lean_obj_tag(v___x_2957_))
{
case 0:
{
lean_object* v_index_2958_; lean_object* v_size_2959_; lean_object* v___x_2960_; 
v_index_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_index_2958_);
lean_dec_ref_known(v___x_2957_, 3);
v_size_2959_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_size_2959_);
v___x_2960_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2956_, v_size_2959_, v_index_2958_, v_fst_2929_, v_snd_2930_);
lean_dec(v_index_2958_);
return v___x_2960_;
}
case 1:
{
lean_object* v_index_2961_; 
v_index_2961_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_index_2961_);
lean_dec_ref_known(v___x_2957_, 1);
v___y_2949_ = v___x_2956_;
v_i_2950_ = v_index_2961_;
goto v___jp_2948_;
}
default: 
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_unsigned_to_nat(0u);
v___x_2963_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2956_, v___x_2962_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_index_2964_; 
v_index_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_index_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v___y_2949_ = v___x_2956_;
v_i_2950_ = v_index_2964_;
goto v___jp_2948_;
}
else
{
lean_dec(v_snd_2930_);
lean_dec(v_fst_2929_);
return v___x_2956_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0___boxed(lean_object* v_inst_2995_, lean_object* v_inst_2996_, lean_object* v_m_u2081_2997_, lean_object* v_x1_2998_, lean_object* v_x2_2999_, lean_object* v_x3_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0(v_inst_2995_, v_inst_2996_, v_m_u2081_2997_, v_x1_2998_, v_x2_2999_, v_x3_3000_);
lean_dec(v_x3_3000_);
lean_dec_ref(v_m_u2081_2997_);
return v_res_3001_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_3002_; lean_object* v___x_3003_; 
v_cellCount_3002_ = lean_unsigned_to_nat(16u);
v___x_3003_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3002_);
return v___x_3003_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_3004_; lean_object* v___x_3005_; 
v_cellCount_3004_ = lean_unsigned_to_nat(16u);
v___x_3005_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3004_);
return v___x_3005_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__2(void){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3006_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1);
v___x_3007_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0);
v___x_3008_ = lean_unsigned_to_nat(0u);
v___x_3009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
lean_ctor_set(v___x_3009_, 1, v___x_3007_);
lean_ctor_set(v___x_3009_, 2, v___x_3006_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(lean_object* v_inst_3010_, lean_object* v_inst_3011_, lean_object* v_m_u2081_3012_, lean_object* v_m_u2082_3013_){
_start:
{
lean_object* v___f_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___f_3014_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3014_, 0, v_inst_3010_);
lean_closure_set(v___f_3014_, 1, v_inst_3011_);
lean_closure_set(v___f_3014_, 2, v_m_u2081_3012_);
v___x_3015_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__2, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__2_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__2);
v___x_3016_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_3017_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_3016_, v___f_3014_, v___x_3015_, v_m_u2082_3013_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller(lean_object* v_00_u03b1_3018_, lean_object* v_00_u03b2_3019_, lean_object* v_inst_3020_, lean_object* v_inst_3021_, lean_object* v_m_u2081_3022_, lean_object* v_m_u2082_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(v_inst_3020_, v_inst_3021_, v_m_u2081_3022_, v_m_u2082_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0(lean_object* v_inst_3025_, lean_object* v_inst_3026_, lean_object* v_a_3027_, lean_object* v_b_3028_, lean_object* v_acc_3029_){
_start:
{
lean_object* v___y_3031_; lean_object* v_i_3032_; lean_object* v___y_3051_; lean_object* v_i_3052_; lean_object* v___y_3059_; lean_object* v___x_3070_; 
lean_inc(v_a_3027_);
lean_inc_ref(v_inst_3026_);
lean_inc_ref(v_inst_3025_);
v___x_3070_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3025_, v_inst_3026_, v_acc_3029_, v_a_3027_);
switch(lean_obj_tag(v___x_3070_))
{
case 0:
{
lean_object* v___x_3071_; 
lean_dec_ref_known(v___x_3070_, 3);
lean_dec(v_b_3028_);
lean_dec(v_a_3027_);
lean_dec_ref(v_inst_3026_);
lean_dec_ref(v_inst_3025_);
v___x_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3071_, 0, v_acc_3029_);
return v___x_3071_;
}
case 1:
{
lean_object* v_index_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3091_; 
v_index_3072_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3074_ = v___x_3070_;
v_isShared_3075_ = v_isSharedCheck_3091_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_index_3072_);
lean_dec(v___x_3070_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3091_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v_size_3076_; lean_object* v_keyArray_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v_size_3076_ = lean_ctor_get(v_acc_3029_, 0);
v_keyArray_3077_ = lean_ctor_get(v_acc_3029_, 1);
v___x_3078_ = lean_unsigned_to_nat(1u);
v___x_3079_ = lean_nat_add(v_size_3076_, v___x_3078_);
v___x_3080_ = lean_array_get_size(v_keyArray_3077_);
v___x_3081_ = lean_nat_dec_lt(v___x_3079_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_dec(v___x_3079_);
lean_del_object(v___x_3074_);
lean_dec(v_index_3072_);
goto v___jp_3038_;
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3082_ = lean_unsigned_to_nat(4u);
v___x_3083_ = lean_nat_mul(v___x_3079_, v___x_3082_);
v___x_3084_ = lean_unsigned_to_nat(3u);
v___x_3085_ = lean_nat_mul(v___x_3080_, v___x_3084_);
v___x_3086_ = lean_nat_dec_le(v___x_3083_, v___x_3085_);
lean_dec(v___x_3085_);
lean_dec(v___x_3083_);
if (v___x_3086_ == 0)
{
lean_dec(v___x_3079_);
lean_del_object(v___x_3074_);
lean_dec(v_index_3072_);
goto v___jp_3038_;
}
else
{
lean_object* v___x_3087_; lean_object* v___x_3089_; 
lean_dec_ref(v_inst_3026_);
lean_dec_ref(v_inst_3025_);
v___x_3087_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_3029_, v___x_3079_, v_index_3072_, v_a_3027_, v_b_3028_);
lean_dec(v_index_3072_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 0, v___x_3087_);
v___x_3089_ = v___x_3074_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3087_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
default: 
{
lean_object* v_size_3092_; lean_object* v_keyArray_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v_size_3092_ = lean_ctor_get(v_acc_3029_, 0);
v_keyArray_3093_ = lean_ctor_get(v_acc_3029_, 1);
v___x_3094_ = lean_unsigned_to_nat(1u);
v___x_3095_ = lean_nat_add(v_size_3092_, v___x_3094_);
v___x_3096_ = lean_array_get_size(v_keyArray_3093_);
v___x_3097_ = lean_nat_dec_lt(v___x_3095_, v___x_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; 
lean_dec(v___x_3095_);
lean_inc_ref(v_inst_3026_);
lean_inc_ref(v_inst_3025_);
v___x_3098_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3025_, v_inst_3026_, v_acc_3029_);
v___y_3059_ = v___x_3098_;
goto v___jp_3058_;
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3099_ = lean_unsigned_to_nat(4u);
v___x_3100_ = lean_nat_mul(v___x_3095_, v___x_3099_);
lean_dec(v___x_3095_);
v___x_3101_ = lean_unsigned_to_nat(3u);
v___x_3102_ = lean_nat_mul(v___x_3096_, v___x_3101_);
v___x_3103_ = lean_nat_dec_le(v___x_3100_, v___x_3102_);
lean_dec(v___x_3102_);
lean_dec(v___x_3100_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; 
lean_inc_ref(v_inst_3026_);
lean_inc_ref(v_inst_3025_);
v___x_3104_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3025_, v_inst_3026_, v_acc_3029_);
v___y_3059_ = v___x_3104_;
goto v___jp_3058_;
}
else
{
v___y_3059_ = v_acc_3029_;
goto v___jp_3058_;
}
}
}
}
v___jp_3030_:
{
lean_object* v_size_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v_size_3033_ = lean_ctor_get(v___y_3031_, 0);
v___x_3034_ = lean_unsigned_to_nat(1u);
v___x_3035_ = lean_nat_add(v_size_3033_, v___x_3034_);
v___x_3036_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3031_, v___x_3035_, v_i_3032_, v_a_3027_, v_b_3028_);
lean_dec(v_i_3032_);
v___x_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
return v___x_3037_;
}
v___jp_3038_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
lean_inc_ref(v_inst_3026_);
lean_inc_ref(v_inst_3025_);
v___x_3039_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3025_, v_inst_3026_, v_acc_3029_);
lean_inc(v_a_3027_);
v___x_3040_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3025_, v_inst_3026_, v___x_3039_, v_a_3027_);
switch(lean_obj_tag(v___x_3040_))
{
case 0:
{
lean_object* v_index_3041_; lean_object* v_size_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v_index_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_index_3041_);
lean_dec_ref_known(v___x_3040_, 3);
v_size_3042_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_size_3042_);
v___x_3043_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3039_, v_size_3042_, v_index_3041_, v_a_3027_, v_b_3028_);
lean_dec(v_index_3041_);
v___x_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
return v___x_3044_;
}
case 1:
{
lean_object* v_index_3045_; 
v_index_3045_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_index_3045_);
lean_dec_ref_known(v___x_3040_, 1);
v___y_3031_ = v___x_3039_;
v_i_3032_ = v_index_3045_;
goto v___jp_3030_;
}
default: 
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_unsigned_to_nat(0u);
v___x_3047_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3039_, v___x_3046_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_index_3048_; 
v_index_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_index_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v___y_3031_ = v___x_3039_;
v_i_3032_ = v_index_3048_;
goto v___jp_3030_;
}
else
{
lean_object* v___x_3049_; 
lean_dec(v_b_3028_);
lean_dec(v_a_3027_);
v___x_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3039_);
return v___x_3049_;
}
}
}
}
v___jp_3050_:
{
lean_object* v_size_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v_size_3053_ = lean_ctor_get(v___y_3051_, 0);
v___x_3054_ = lean_unsigned_to_nat(1u);
v___x_3055_ = lean_nat_add(v_size_3053_, v___x_3054_);
v___x_3056_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3051_, v___x_3055_, v_i_3052_, v_a_3027_, v_b_3028_);
lean_dec(v_i_3052_);
v___x_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
return v___x_3057_;
}
v___jp_3058_:
{
lean_object* v___x_3060_; 
lean_inc(v_a_3027_);
v___x_3060_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3025_, v_inst_3026_, v___y_3059_, v_a_3027_);
switch(lean_obj_tag(v___x_3060_))
{
case 0:
{
lean_object* v_index_3061_; lean_object* v_size_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v_index_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_index_3061_);
lean_dec_ref_known(v___x_3060_, 3);
v_size_3062_ = lean_ctor_get(v___y_3059_, 0);
lean_inc(v_size_3062_);
v___x_3063_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3059_, v_size_3062_, v_index_3061_, v_a_3027_, v_b_3028_);
lean_dec(v_index_3061_);
v___x_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
return v___x_3064_;
}
case 1:
{
lean_object* v_index_3065_; 
v_index_3065_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_index_3065_);
lean_dec_ref_known(v___x_3060_, 1);
v___y_3051_ = v___y_3059_;
v_i_3052_ = v_index_3065_;
goto v___jp_3050_;
}
default: 
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = lean_unsigned_to_nat(0u);
v___x_3067_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3059_, v___x_3066_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_index_3068_; 
v_index_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_index_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v___y_3051_ = v___y_3059_;
v_i_3052_ = v_index_3068_;
goto v___jp_3050_;
}
else
{
lean_object* v___x_3069_; 
lean_dec(v_b_3028_);
lean_dec(v_a_3027_);
v___x_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3069_, 0, v___y_3059_);
return v___x_3069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg(lean_object* v_inst_3107_, lean_object* v_inst_3108_, lean_object* v_m_u2081_3109_, lean_object* v_m_u2082_3110_){
_start:
{
lean_object* v_size_3111_; lean_object* v_size_3112_; uint8_t v___x_3113_; 
v_size_3111_ = lean_ctor_get(v_m_u2081_3109_, 0);
v_size_3112_ = lean_ctor_get(v_m_u2082_3110_, 0);
v___x_3113_ = lean_nat_dec_le(v_size_3111_, v_size_3112_);
if (v___x_3113_ == 0)
{
lean_object* v___f_3114_; lean_object* v___x_3115_; 
v___f_3114_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0));
v___x_3115_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_3114_, v_inst_3107_, v_inst_3108_, v_m_u2081_3109_, v_m_u2082_3110_);
return v___x_3115_;
}
else
{
lean_object* v___f_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___f_3116_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_3116_, 0, v_inst_3107_);
lean_closure_set(v___f_3116_, 1, v_inst_3108_);
v___x_3117_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_3118_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_3117_, v___f_3116_, v_m_u2082_3110_, v_m_u2081_3109_);
return v___x_3118_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union(lean_object* v_00_u03b1_3119_, lean_object* v_00_u03b2_3120_, lean_object* v_inst_3121_, lean_object* v_inst_3122_, lean_object* v_m_u2081_3123_, lean_object* v_m_u2082_3124_){
_start:
{
lean_object* v_size_3125_; lean_object* v_size_3126_; uint8_t v___x_3127_; 
v_size_3125_ = lean_ctor_get(v_m_u2081_3123_, 0);
v_size_3126_ = lean_ctor_get(v_m_u2082_3124_, 0);
v___x_3127_ = lean_nat_dec_le(v_size_3125_, v_size_3126_);
if (v___x_3127_ == 0)
{
lean_object* v___f_3128_; lean_object* v___x_3129_; 
v___f_3128_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0));
v___x_3129_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_3128_, v_inst_3121_, v_inst_3122_, v_m_u2081_3123_, v_m_u2082_3124_);
return v___x_3129_;
}
else
{
lean_object* v___f_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___f_3130_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_3130_, 0, v_inst_3121_);
lean_closure_set(v___f_3130_, 1, v_inst_3122_);
v___x_3131_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_3132_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_3131_, v___f_3130_, v_m_u2082_3124_, v_m_u2081_3123_);
return v___x_3132_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0(lean_object* v_inst_3133_, lean_object* v_inst_3134_, lean_object* v_m_u2082_3135_, lean_object* v_k_3136_, lean_object* v_x_3137_){
_start:
{
uint8_t v___x_3138_; 
v___x_3138_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_3133_, v_inst_3134_, v_m_u2082_3135_, v_k_3136_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0___boxed(lean_object* v_inst_3139_, lean_object* v_inst_3140_, lean_object* v_m_u2082_3141_, lean_object* v_k_3142_, lean_object* v_x_3143_){
_start:
{
uint8_t v_res_3144_; lean_object* v_r_3145_; 
v_res_3144_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0(v_inst_3139_, v_inst_3140_, v_m_u2082_3141_, v_k_3142_, v_x_3143_);
lean_dec(v_x_3143_);
lean_dec_ref(v_m_u2082_3141_);
v_r_3145_ = lean_box(v_res_3144_);
return v_r_3145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object* v_inst_3146_, lean_object* v_inst_3147_, lean_object* v_m_u2081_3148_, lean_object* v_m_u2082_3149_){
_start:
{
lean_object* v_size_3150_; lean_object* v_size_3151_; uint8_t v___x_3152_; 
v_size_3150_ = lean_ctor_get(v_m_u2081_3148_, 0);
v_size_3151_ = lean_ctor_get(v_m_u2082_3149_, 0);
v___x_3152_ = lean_nat_dec_le(v_size_3150_, v_size_3151_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; 
v___x_3153_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(v_inst_3146_, v_inst_3147_, v_m_u2081_3148_, v_m_u2082_3149_);
return v___x_3153_;
}
else
{
lean_object* v___f_3154_; lean_object* v___x_3155_; 
v___f_3154_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3154_, 0, v_inst_3146_);
lean_closure_set(v___f_3154_, 1, v_inst_3147_);
lean_closure_set(v___f_3154_, 2, v_m_u2082_3149_);
v___x_3155_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_3154_, v_m_u2081_3148_);
lean_dec_ref(v_m_u2081_3148_);
return v___x_3155_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter(lean_object* v_00_u03b1_3156_, lean_object* v_00_u03b2_3157_, lean_object* v_inst_3158_, lean_object* v_inst_3159_, lean_object* v_m_u2081_3160_, lean_object* v_m_u2082_3161_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_3158_, v_inst_3159_, v_m_u2081_3160_, v_m_u2082_3161_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0(lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_inst_3165_, lean_object* v_m_u2082_3166_, uint8_t v___x_3167_, lean_object* v___x_3168_, uint8_t v___x_3169_, lean_object* v___x_3170_, lean_object* v_a_3171_, lean_object* v_b_3172_, lean_object* v_acc_3173_){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
lean_inc(v_a_3171_);
v___x_3174_ = lean_apply_1(v_inst_3163_, v_a_3171_);
v___x_3175_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_3164_, v_inst_3165_, v_m_u2082_3166_, v_a_3171_);
v___x_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3176_, 0, v_b_3172_);
v___x_3177_ = l_Option_instBEq_beq___redArg(v___x_3174_, v___x_3175_, v___x_3176_);
if (v___x_3177_ == 0)
{
if (v___x_3167_ == 0)
{
lean_object* v___x_3178_; 
v___x_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3168_);
return v___x_3178_;
}
else
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
lean_dec_ref(v___x_3168_);
v___x_3179_ = lean_box(v___x_3169_);
v___x_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
lean_ctor_set(v___x_3181_, 1, v___x_3170_);
v___x_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
return v___x_3182_;
}
}
else
{
lean_object* v___x_3183_; 
v___x_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3168_);
return v___x_3183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0___boxed(lean_object* v_inst_3184_, lean_object* v_inst_3185_, lean_object* v_inst_3186_, lean_object* v_m_u2082_3187_, lean_object* v___x_3188_, lean_object* v___x_3189_, lean_object* v___x_3190_, lean_object* v___x_3191_, lean_object* v_a_3192_, lean_object* v_b_3193_, lean_object* v_acc_3194_){
_start:
{
uint8_t v___x_240__boxed_3195_; uint8_t v___x_242__boxed_3196_; lean_object* v_res_3197_; 
v___x_240__boxed_3195_ = lean_unbox(v___x_3188_);
v___x_242__boxed_3196_ = lean_unbox(v___x_3190_);
v_res_3197_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0(v_inst_3184_, v_inst_3185_, v_inst_3186_, v_m_u2082_3187_, v___x_240__boxed_3195_, v___x_3189_, v___x_242__boxed_3196_, v___x_3191_, v_a_3192_, v_b_3193_, v_acc_3194_);
lean_dec_ref(v_acc_3194_);
lean_dec_ref(v_m_u2082_3187_);
return v_res_3197_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(lean_object* v_inst_3201_, lean_object* v_inst_3202_, lean_object* v_inst_3203_, lean_object* v_m_u2081_3204_, lean_object* v_m_u2082_3205_){
_start:
{
lean_object* v_size_3206_; lean_object* v_size_3207_; uint8_t v___x_3208_; 
v_size_3206_ = lean_ctor_get(v_m_u2081_3204_, 0);
v_size_3207_ = lean_ctor_get(v_m_u2082_3205_, 0);
v___x_3208_ = lean_nat_dec_eq(v_size_3206_, v_size_3207_);
if (v___x_3208_ == 0)
{
lean_dec_ref(v_m_u2082_3205_);
lean_dec_ref(v_m_u2081_3204_);
lean_dec_ref(v_inst_3203_);
lean_dec_ref(v_inst_3202_);
lean_dec_ref(v_inst_3201_);
return v___x_3208_;
}
else
{
uint8_t v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___f_3215_; lean_object* v___x_3216_; lean_object* v_fst_3217_; 
v___x_3209_ = 0;
v___x_3210_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_3211_ = lean_box(0);
v___x_3212_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0));
v___x_3213_ = lean_box(v___x_3208_);
v___x_3214_ = lean_box(v___x_3209_);
v___f_3215_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0___boxed), 11, 8);
lean_closure_set(v___f_3215_, 0, v_inst_3203_);
lean_closure_set(v___f_3215_, 1, v_inst_3201_);
lean_closure_set(v___f_3215_, 2, v_inst_3202_);
lean_closure_set(v___f_3215_, 3, v_m_u2082_3205_);
lean_closure_set(v___f_3215_, 4, v___x_3213_);
lean_closure_set(v___f_3215_, 5, v___x_3212_);
lean_closure_set(v___f_3215_, 6, v___x_3214_);
lean_closure_set(v___f_3215_, 7, v___x_3211_);
v___x_3216_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_3210_, v___f_3215_, v___x_3212_, v_m_u2081_3204_);
v_fst_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_fst_3217_);
lean_dec(v___x_3216_);
if (lean_obj_tag(v_fst_3217_) == 0)
{
return v___x_3208_;
}
else
{
lean_object* v_val_3218_; uint8_t v___x_3219_; 
v_val_3218_ = lean_ctor_get(v_fst_3217_, 0);
lean_inc(v_val_3218_);
lean_dec_ref_known(v_fst_3217_, 1);
v___x_3219_ = lean_unbox(v_val_3218_);
lean_dec(v_val_3218_);
return v___x_3219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___boxed(lean_object* v_inst_3220_, lean_object* v_inst_3221_, lean_object* v_inst_3222_, lean_object* v_m_u2081_3223_, lean_object* v_m_u2082_3224_){
_start:
{
uint8_t v_res_3225_; lean_object* v_r_3226_; 
v_res_3225_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_3220_, v_inst_3221_, v_inst_3222_, v_m_u2081_3223_, v_m_u2082_3224_);
v_r_3226_ = lean_box(v_res_3225_);
return v_r_3226_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq(lean_object* v_00_u03b1_3227_, lean_object* v_00_u03b2_3228_, lean_object* v_inst_3229_, lean_object* v_inst_3230_, lean_object* v_inst_3231_, lean_object* v_inst_3232_, lean_object* v_m_u2081_3233_, lean_object* v_m_u2082_3234_){
_start:
{
uint8_t v___x_3235_; 
v___x_3235_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_3229_, v_inst_3231_, v_inst_3232_, v_m_u2081_3233_, v_m_u2082_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___boxed(lean_object* v_00_u03b1_3236_, lean_object* v_00_u03b2_3237_, lean_object* v_inst_3238_, lean_object* v_inst_3239_, lean_object* v_inst_3240_, lean_object* v_inst_3241_, lean_object* v_m_u2081_3242_, lean_object* v_m_u2082_3243_){
_start:
{
uint8_t v_res_3244_; lean_object* v_r_3245_; 
v_res_3244_ = l_Std_DHashMap_Internal_Raw_u2080_beq(v_00_u03b1_3236_, v_00_u03b2_3237_, v_inst_3238_, v_inst_3239_, v_inst_3240_, v_inst_3241_, v_m_u2081_3242_, v_m_u2082_3243_);
v_r_3245_ = lean_box(v_res_3244_);
return v_r_3245_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0(lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_m_u2082_3248_, uint8_t v___x_3249_, lean_object* v_k_3250_, lean_object* v_x_3251_){
_start:
{
uint8_t v___x_3252_; 
v___x_3252_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_3246_, v_inst_3247_, v_m_u2082_3248_, v_k_3250_);
if (v___x_3252_ == 0)
{
return v___x_3249_;
}
else
{
uint8_t v___x_3253_; 
v___x_3253_ = 0;
return v___x_3253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed(lean_object* v_inst_3254_, lean_object* v_inst_3255_, lean_object* v_m_u2082_3256_, lean_object* v___x_3257_, lean_object* v_k_3258_, lean_object* v_x_3259_){
_start:
{
uint8_t v___x_70__boxed_3260_; uint8_t v_res_3261_; lean_object* v_r_3262_; 
v___x_70__boxed_3260_ = lean_unbox(v___x_3257_);
v_res_3261_ = l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0(v_inst_3254_, v_inst_3255_, v_m_u2082_3256_, v___x_70__boxed_3260_, v_k_3258_, v_x_3259_);
lean_dec(v_x_3259_);
lean_dec_ref(v_m_u2082_3256_);
v_r_3262_ = lean_box(v_res_3261_);
return v_r_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff___redArg(lean_object* v_inst_3263_, lean_object* v_inst_3264_, lean_object* v_m_u2081_3265_, lean_object* v_m_u2082_3266_){
_start:
{
lean_object* v_size_3267_; lean_object* v_size_3268_; uint8_t v___x_3269_; 
v_size_3267_ = lean_ctor_get(v_m_u2081_3265_, 0);
v_size_3268_ = lean_ctor_get(v_m_u2082_3266_, 0);
v___x_3269_ = lean_nat_dec_le(v_size_3267_, v_size_3268_);
if (v___x_3269_ == 0)
{
lean_object* v___f_3270_; lean_object* v___x_3271_; 
v___f_3270_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0));
v___x_3271_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_3270_, v_inst_3263_, v_inst_3264_, v_m_u2081_3265_, v_m_u2082_3266_);
return v___x_3271_;
}
else
{
lean_object* v___x_3272_; lean_object* v___f_3273_; lean_object* v___x_3274_; 
v___x_3272_ = lean_box(v___x_3269_);
v___f_3273_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3273_, 0, v_inst_3263_);
lean_closure_set(v___f_3273_, 1, v_inst_3264_);
lean_closure_set(v___f_3273_, 2, v_m_u2082_3266_);
lean_closure_set(v___f_3273_, 3, v___x_3272_);
v___x_3274_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_3273_, v_m_u2081_3265_);
lean_dec_ref(v_m_u2081_3265_);
return v___x_3274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff(lean_object* v_00_u03b1_3275_, lean_object* v_00_u03b2_3276_, lean_object* v_inst_3277_, lean_object* v_inst_3278_, lean_object* v_m_u2081_3279_, lean_object* v_m_u2082_3280_){
_start:
{
lean_object* v_size_3281_; lean_object* v_size_3282_; uint8_t v___x_3283_; 
v_size_3281_ = lean_ctor_get(v_m_u2081_3279_, 0);
v_size_3282_ = lean_ctor_get(v_m_u2082_3280_, 0);
v___x_3283_ = lean_nat_dec_le(v_size_3281_, v_size_3282_);
if (v___x_3283_ == 0)
{
lean_object* v___f_3284_; lean_object* v___x_3285_; 
v___f_3284_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0));
v___x_3285_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_3284_, v_inst_3277_, v_inst_3278_, v_m_u2081_3279_, v_m_u2082_3280_);
return v___x_3285_;
}
else
{
lean_object* v___x_3286_; lean_object* v___f_3287_; lean_object* v___x_3288_; 
v___x_3286_ = lean_box(v___x_3283_);
v___f_3287_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_3287_, 0, v_inst_3277_);
lean_closure_set(v___f_3287_, 1, v_inst_3278_);
lean_closure_set(v___f_3287_, 2, v_m_u2082_3280_);
lean_closure_set(v___f_3287_, 3, v___x_3286_);
v___x_3288_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_3287_, v_m_u2081_3279_);
lean_dec_ref(v_m_u2081_3279_);
return v___x_3288_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object* v_inst_3289_, lean_object* v_inst_3290_, lean_object* v_m_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Std_DHashMap_Internal_Raw_u2080_scan___redArg(v_inst_3289_, v_inst_3290_, v_m_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_value_3294_; lean_object* v___x_3295_; 
v_value_3294_ = lean_ctor_get(v___x_3293_, 2);
lean_inc(v_value_3294_);
lean_dec_ref_known(v___x_3293_, 3);
v___x_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3295_, 0, v_value_3294_);
return v___x_3295_;
}
else
{
lean_object* v___x_3296_; 
v___x_3296_ = lean_box(0);
return v___x_3296_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg___boxed(lean_object* v_inst_3297_, lean_object* v_inst_3298_, lean_object* v_m_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_3297_, v_inst_3298_, v_m_3299_, v_a_3300_);
lean_dec_ref(v_m_3299_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f(lean_object* v_00_u03b1_3302_, lean_object* v_00_u03b2_3303_, lean_object* v_inst_3304_, lean_object* v_inst_3305_, lean_object* v_m_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_3304_, v_inst_3305_, v_m_3306_, v_a_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___boxed(lean_object* v_00_u03b1_3309_, lean_object* v_00_u03b2_3310_, lean_object* v_inst_3311_, lean_object* v_inst_3312_, lean_object* v_m_3313_, lean_object* v_a_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f(v_00_u03b1_3309_, v_00_u03b2_3310_, v_inst_3311_, v_inst_3312_, v_m_3313_, v_a_3314_);
lean_dec_ref(v_m_3313_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object* v_inst_3316_, lean_object* v_inst_3317_, lean_object* v_m_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v___x_3320_; lean_object* v_val_3321_; 
v___x_3320_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_3316_, v_inst_3317_, v_m_3318_, v_a_3319_);
v_val_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_val_3321_);
lean_dec(v___x_3320_);
return v_val_3321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg___boxed(lean_object* v_inst_3322_, lean_object* v_inst_3323_, lean_object* v_m_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_3322_, v_inst_3323_, v_m_3324_, v_a_3325_);
lean_dec_ref(v_m_3324_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get(lean_object* v_00_u03b1_3327_, lean_object* v_00_u03b2_3328_, lean_object* v_inst_3329_, lean_object* v_inst_3330_, lean_object* v_m_3331_, lean_object* v_a_3332_, lean_object* v_hma_3333_){
_start:
{
lean_object* v___x_3334_; lean_object* v_val_3335_; 
v___x_3334_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_3329_, v_inst_3330_, v_m_3331_, v_a_3332_);
v_val_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_val_3335_);
lean_dec(v___x_3334_);
return v_val_3335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___boxed(lean_object* v_00_u03b1_3336_, lean_object* v_00_u03b2_3337_, lean_object* v_inst_3338_, lean_object* v_inst_3339_, lean_object* v_m_3340_, lean_object* v_a_3341_, lean_object* v_hma_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get(v_00_u03b1_3336_, v_00_u03b2_3337_, v_inst_3338_, v_inst_3339_, v_m_3340_, v_a_3341_, v_hma_3342_);
lean_dec_ref(v_m_3340_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object* v_inst_3344_, lean_object* v_inst_3345_, lean_object* v_m_3346_, lean_object* v_a_3347_, lean_object* v_fallback_3348_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_3344_, v_inst_3345_, v_m_3346_, v_a_3347_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_inc(v_fallback_3348_);
return v_fallback_3348_;
}
else
{
lean_object* v_val_3350_; 
v_val_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_val_3350_);
lean_dec_ref_known(v___x_3349_, 1);
return v_val_3350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg___boxed(lean_object* v_inst_3351_, lean_object* v_inst_3352_, lean_object* v_m_3353_, lean_object* v_a_3354_, lean_object* v_fallback_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_3351_, v_inst_3352_, v_m_3353_, v_a_3354_, v_fallback_3355_);
lean_dec(v_fallback_3355_);
lean_dec_ref(v_m_3353_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD(lean_object* v_00_u03b1_3357_, lean_object* v_00_u03b2_3358_, lean_object* v_inst_3359_, lean_object* v_inst_3360_, lean_object* v_m_3361_, lean_object* v_a_3362_, lean_object* v_fallback_3363_){
_start:
{
lean_object* v___x_3364_; 
v___x_3364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_3359_, v_inst_3360_, v_m_3361_, v_a_3362_, v_fallback_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___boxed(lean_object* v_00_u03b1_3365_, lean_object* v_00_u03b2_3366_, lean_object* v_inst_3367_, lean_object* v_inst_3368_, lean_object* v_m_3369_, lean_object* v_a_3370_, lean_object* v_fallback_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD(v_00_u03b1_3365_, v_00_u03b2_3366_, v_inst_3367_, v_inst_3368_, v_m_3369_, v_a_3370_, v_fallback_3371_);
lean_dec(v_fallback_3371_);
lean_dec_ref(v_m_3369_);
return v_res_3372_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3374_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__2));
v___x_3375_ = lean_unsigned_to_nat(12u);
v___x_3376_ = lean_unsigned_to_nat(672u);
v___x_3377_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___closed__0));
v___x_3378_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__0));
v___x_3379_ = l_mkPanicMessageWithDecl(v___x_3378_, v___x_3377_, v___x_3376_, v___x_3375_, v___x_3374_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object* v_inst_3380_, lean_object* v_inst_3381_, lean_object* v_inst_3382_, lean_object* v_m_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_3380_, v_inst_3381_, v_m_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___closed__1, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___closed__1_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___closed__1);
v___x_3387_ = l_panic___redArg(v_inst_3382_, v___x_3386_);
return v___x_3387_;
}
else
{
lean_object* v_val_3388_; 
v_val_3388_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_val_3388_);
lean_dec_ref_known(v___x_3385_, 1);
return v_val_3388_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___boxed(lean_object* v_inst_3389_, lean_object* v_inst_3390_, lean_object* v_inst_3391_, lean_object* v_m_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_3389_, v_inst_3390_, v_inst_3391_, v_m_3392_, v_a_3393_);
lean_dec_ref(v_m_3392_);
lean_dec(v_inst_3391_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21(lean_object* v_00_u03b1_3395_, lean_object* v_00_u03b2_3396_, lean_object* v_inst_3397_, lean_object* v_inst_3398_, lean_object* v_inst_3399_, lean_object* v_m_3400_, lean_object* v_a_3401_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_3397_, v_inst_3398_, v_inst_3399_, v_m_3400_, v_a_3401_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___boxed(lean_object* v_00_u03b1_3403_, lean_object* v_00_u03b2_3404_, lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_m_3408_, lean_object* v_a_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21(v_00_u03b1_3403_, v_00_u03b2_3404_, v_inst_3405_, v_inst_3406_, v_inst_3407_, v_m_3408_, v_a_3409_);
lean_dec_ref(v_m_3408_);
lean_dec(v_inst_3407_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modifyImpl___redArg(lean_object* v_inst_3411_, lean_object* v_inst_3412_, lean_object* v_m_3413_, lean_object* v_a_3414_, lean_object* v_f_3415_){
_start:
{
lean_object* v___x_3416_; 
lean_inc(v_a_3414_);
v___x_3416_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3411_, v_inst_3412_, v_m_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_index_3417_; lean_object* v_value_3418_; lean_object* v_size_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v_index_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_index_3417_);
v_value_3418_ = lean_ctor_get(v___x_3416_, 2);
lean_inc(v_value_3418_);
lean_dec_ref_known(v___x_3416_, 3);
v_size_3419_ = lean_ctor_get(v_m_3413_, 0);
lean_inc(v_size_3419_);
v___x_3420_ = lean_apply_1(v_f_3415_, v_value_3418_);
v___x_3421_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_3413_, v_size_3419_, v_index_3417_, v_a_3414_, v___x_3420_);
lean_dec(v_index_3417_);
return v___x_3421_;
}
else
{
lean_dec(v___x_3416_);
lean_dec(v_f_3415_);
lean_dec(v_a_3414_);
return v_m_3413_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modifyImpl(lean_object* v_00_u03b1_3422_, lean_object* v_00_u03b2_3423_, lean_object* v_inst_3424_, lean_object* v_inst_3425_, lean_object* v_m_3426_, lean_object* v_a_3427_, lean_object* v_f_3428_){
_start:
{
lean_object* v___x_3429_; 
lean_inc(v_a_3427_);
v___x_3429_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3424_, v_inst_3425_, v_m_3426_, v_a_3427_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_index_3430_; lean_object* v_value_3431_; lean_object* v_size_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v_index_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_index_3430_);
v_value_3431_ = lean_ctor_get(v___x_3429_, 2);
lean_inc(v_value_3431_);
lean_dec_ref_known(v___x_3429_, 3);
v_size_3432_ = lean_ctor_get(v_m_3426_, 0);
lean_inc(v_size_3432_);
v___x_3433_ = lean_apply_1(v_f_3428_, v_value_3431_);
v___x_3434_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_3426_, v_size_3432_, v_index_3430_, v_a_3427_, v___x_3433_);
lean_dec(v_index_3430_);
return v___x_3434_;
}
else
{
lean_dec(v___x_3429_);
lean_dec(v_f_3428_);
lean_dec(v_a_3427_);
return v_m_3426_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alterImpl___redArg(lean_object* v_inst_3435_, lean_object* v_inst_3436_, lean_object* v_m_3437_, lean_object* v_a_3438_, lean_object* v_f_3439_){
_start:
{
lean_object* v___x_3440_; 
lean_inc(v_a_3438_);
lean_inc_ref(v_inst_3436_);
lean_inc_ref(v_inst_3435_);
v___x_3440_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3435_, v_inst_3436_, v_m_3437_, v_a_3438_);
switch(lean_obj_tag(v___x_3440_))
{
case 0:
{
lean_object* v_index_3441_; lean_object* v_value_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_dec_ref(v_inst_3436_);
lean_dec_ref(v_inst_3435_);
v_index_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_index_3441_);
v_value_3442_ = lean_ctor_get(v___x_3440_, 2);
lean_inc(v_value_3442_);
lean_dec_ref_known(v___x_3440_, 3);
v___x_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3443_, 0, v_value_3442_);
v___x_3444_ = lean_apply_1(v_f_3439_, v___x_3443_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_size_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_dec(v_a_3438_);
v_size_3445_ = lean_ctor_get(v_m_3437_, 0);
v___x_3446_ = lean_unsigned_to_nat(1u);
v___x_3447_ = lean_nat_sub(v_size_3445_, v___x_3446_);
v___x_3448_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_3437_, v___x_3447_, v_index_3441_);
lean_dec(v_index_3441_);
return v___x_3448_;
}
else
{
lean_object* v_val_3449_; lean_object* v_size_3450_; lean_object* v___x_3451_; 
v_val_3449_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_val_3449_);
lean_dec_ref_known(v___x_3444_, 1);
v_size_3450_ = lean_ctor_get(v_m_3437_, 0);
lean_inc(v_size_3450_);
v___x_3451_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_3437_, v_size_3450_, v_index_3441_, v_a_3438_, v_val_3449_);
lean_dec(v_index_3441_);
return v___x_3451_;
}
}
case 1:
{
lean_object* v_index_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v_index_3452_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_index_3452_);
lean_dec_ref_known(v___x_3440_, 1);
v___x_3453_ = lean_box(0);
v___x_3454_ = lean_apply_1(v_f_3439_, v___x_3453_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_dec(v_index_3452_);
lean_dec(v_a_3438_);
lean_dec_ref(v_inst_3436_);
lean_dec_ref(v_inst_3435_);
return v_m_3437_;
}
else
{
lean_object* v_val_3455_; lean_object* v___y_3457_; lean_object* v_i_3458_; lean_object* v_size_3473_; lean_object* v_keyArray_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; uint8_t v___x_3478_; 
v_val_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_val_3455_);
lean_dec_ref_known(v___x_3454_, 1);
v_size_3473_ = lean_ctor_get(v_m_3437_, 0);
v_keyArray_3474_ = lean_ctor_get(v_m_3437_, 1);
v___x_3475_ = lean_unsigned_to_nat(1u);
v___x_3476_ = lean_nat_add(v_size_3473_, v___x_3475_);
v___x_3477_ = lean_array_get_size(v_keyArray_3474_);
v___x_3478_ = lean_nat_dec_lt(v___x_3476_, v___x_3477_);
if (v___x_3478_ == 0)
{
lean_dec(v___x_3476_);
lean_dec(v_index_3452_);
goto v___jp_3463_;
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; 
v___x_3479_ = lean_unsigned_to_nat(4u);
v___x_3480_ = lean_nat_mul(v___x_3476_, v___x_3479_);
v___x_3481_ = lean_unsigned_to_nat(3u);
v___x_3482_ = lean_nat_mul(v___x_3477_, v___x_3481_);
v___x_3483_ = lean_nat_dec_le(v___x_3480_, v___x_3482_);
lean_dec(v___x_3482_);
lean_dec(v___x_3480_);
if (v___x_3483_ == 0)
{
lean_dec(v___x_3476_);
lean_dec(v_index_3452_);
goto v___jp_3463_;
}
else
{
lean_object* v___x_3484_; 
lean_dec_ref(v_inst_3436_);
lean_dec_ref(v_inst_3435_);
v___x_3484_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_3437_, v___x_3476_, v_index_3452_, v_a_3438_, v_val_3455_);
lean_dec(v_index_3452_);
return v___x_3484_;
}
}
v___jp_3456_:
{
lean_object* v_size_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v_size_3459_ = lean_ctor_get(v___y_3457_, 0);
v___x_3460_ = lean_unsigned_to_nat(1u);
v___x_3461_ = lean_nat_add(v_size_3459_, v___x_3460_);
v___x_3462_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3457_, v___x_3461_, v_i_3458_, v_a_3438_, v_val_3455_);
lean_dec(v_i_3458_);
return v___x_3462_;
}
v___jp_3463_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
lean_inc_ref(v_inst_3436_);
lean_inc_ref(v_inst_3435_);
v___x_3464_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3435_, v_inst_3436_, v_m_3437_);
lean_inc(v_a_3438_);
v___x_3465_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3435_, v_inst_3436_, v___x_3464_, v_a_3438_);
switch(lean_obj_tag(v___x_3465_))
{
case 0:
{
lean_object* v_index_3466_; lean_object* v_size_3467_; lean_object* v___x_3468_; 
v_index_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_index_3466_);
lean_dec_ref_known(v___x_3465_, 3);
v_size_3467_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_size_3467_);
v___x_3468_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3464_, v_size_3467_, v_index_3466_, v_a_3438_, v_val_3455_);
lean_dec(v_index_3466_);
return v___x_3468_;
}
case 1:
{
lean_object* v_index_3469_; 
v_index_3469_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_index_3469_);
lean_dec_ref_known(v___x_3465_, 1);
v___y_3457_ = v___x_3464_;
v_i_3458_ = v_index_3469_;
goto v___jp_3456_;
}
default: 
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3470_ = lean_unsigned_to_nat(0u);
v___x_3471_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3464_, v___x_3470_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_index_3472_; 
v_index_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_index_3472_);
lean_dec_ref_known(v___x_3471_, 1);
v___y_3457_ = v___x_3464_;
v_i_3458_ = v_index_3472_;
goto v___jp_3456_;
}
else
{
lean_dec(v_val_3455_);
lean_dec(v_a_3438_);
return v___x_3464_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = lean_box(0);
v___x_3486_ = lean_apply_1(v_f_3439_, v___x_3485_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_dec(v_a_3438_);
lean_dec_ref(v_inst_3436_);
lean_dec_ref(v_inst_3435_);
return v_m_3437_;
}
else
{
lean_object* v_val_3487_; lean_object* v___y_3489_; lean_object* v_i_3490_; lean_object* v___y_3496_; lean_object* v_size_3505_; lean_object* v_keyArray_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; uint8_t v___x_3510_; 
v_val_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_val_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v_size_3505_ = lean_ctor_get(v_m_3437_, 0);
v_keyArray_3506_ = lean_ctor_get(v_m_3437_, 1);
v___x_3507_ = lean_unsigned_to_nat(1u);
v___x_3508_ = lean_nat_add(v_size_3505_, v___x_3507_);
v___x_3509_ = lean_array_get_size(v_keyArray_3506_);
v___x_3510_ = lean_nat_dec_lt(v___x_3508_, v___x_3509_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; 
lean_dec(v___x_3508_);
lean_inc_ref(v_inst_3436_);
lean_inc_ref(v_inst_3435_);
v___x_3511_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3435_, v_inst_3436_, v_m_3437_);
v___y_3496_ = v___x_3511_;
goto v___jp_3495_;
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; 
v___x_3512_ = lean_unsigned_to_nat(4u);
v___x_3513_ = lean_nat_mul(v___x_3508_, v___x_3512_);
lean_dec(v___x_3508_);
v___x_3514_ = lean_unsigned_to_nat(3u);
v___x_3515_ = lean_nat_mul(v___x_3509_, v___x_3514_);
v___x_3516_ = lean_nat_dec_le(v___x_3513_, v___x_3515_);
lean_dec(v___x_3515_);
lean_dec(v___x_3513_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
lean_inc_ref(v_inst_3436_);
lean_inc_ref(v_inst_3435_);
v___x_3517_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3435_, v_inst_3436_, v_m_3437_);
v___y_3496_ = v___x_3517_;
goto v___jp_3495_;
}
else
{
v___y_3496_ = v_m_3437_;
goto v___jp_3495_;
}
}
v___jp_3488_:
{
lean_object* v_size_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v_size_3491_ = lean_ctor_get(v___y_3489_, 0);
v___x_3492_ = lean_unsigned_to_nat(1u);
v___x_3493_ = lean_nat_add(v_size_3491_, v___x_3492_);
v___x_3494_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3489_, v___x_3493_, v_i_3490_, v_a_3438_, v_val_3487_);
lean_dec(v_i_3490_);
return v___x_3494_;
}
v___jp_3495_:
{
lean_object* v___x_3497_; 
lean_inc(v_a_3438_);
v___x_3497_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3435_, v_inst_3436_, v___y_3496_, v_a_3438_);
switch(lean_obj_tag(v___x_3497_))
{
case 0:
{
lean_object* v_index_3498_; lean_object* v_size_3499_; lean_object* v___x_3500_; 
v_index_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_index_3498_);
lean_dec_ref_known(v___x_3497_, 3);
v_size_3499_ = lean_ctor_get(v___y_3496_, 0);
lean_inc(v_size_3499_);
v___x_3500_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3496_, v_size_3499_, v_index_3498_, v_a_3438_, v_val_3487_);
lean_dec(v_index_3498_);
return v___x_3500_;
}
case 1:
{
lean_object* v_index_3501_; 
v_index_3501_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_index_3501_);
lean_dec_ref_known(v___x_3497_, 1);
v___y_3489_ = v___y_3496_;
v_i_3490_ = v_index_3501_;
goto v___jp_3488_;
}
default: 
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = lean_unsigned_to_nat(0u);
v___x_3503_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3496_, v___x_3502_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_index_3504_; 
v_index_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_index_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v___y_3489_ = v___y_3496_;
v_i_3490_ = v_index_3504_;
goto v___jp_3488_;
}
else
{
lean_dec(v_val_3487_);
lean_dec(v_a_3438_);
return v___y_3496_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alterImpl(lean_object* v_00_u03b1_3518_, lean_object* v_00_u03b2_3519_, lean_object* v_inst_3520_, lean_object* v_inst_3521_, lean_object* v_m_3522_, lean_object* v_a_3523_, lean_object* v_f_3524_){
_start:
{
lean_object* v___x_3525_; 
lean_inc(v_a_3523_);
lean_inc_ref(v_inst_3521_);
lean_inc_ref(v_inst_3520_);
v___x_3525_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3520_, v_inst_3521_, v_m_3522_, v_a_3523_);
switch(lean_obj_tag(v___x_3525_))
{
case 0:
{
lean_object* v_index_3526_; lean_object* v_value_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
lean_dec_ref(v_inst_3521_);
lean_dec_ref(v_inst_3520_);
v_index_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_index_3526_);
v_value_3527_ = lean_ctor_get(v___x_3525_, 2);
lean_inc(v_value_3527_);
lean_dec_ref_known(v___x_3525_, 3);
v___x_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3528_, 0, v_value_3527_);
v___x_3529_ = lean_apply_1(v_f_3524_, v___x_3528_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_size_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
lean_dec(v_a_3523_);
v_size_3530_ = lean_ctor_get(v_m_3522_, 0);
v___x_3531_ = lean_unsigned_to_nat(1u);
v___x_3532_ = lean_nat_sub(v_size_3530_, v___x_3531_);
v___x_3533_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_3522_, v___x_3532_, v_index_3526_);
lean_dec(v_index_3526_);
return v___x_3533_;
}
else
{
lean_object* v_val_3534_; lean_object* v_size_3535_; lean_object* v___x_3536_; 
v_val_3534_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_val_3534_);
lean_dec_ref_known(v___x_3529_, 1);
v_size_3535_ = lean_ctor_get(v_m_3522_, 0);
lean_inc(v_size_3535_);
v___x_3536_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_3522_, v_size_3535_, v_index_3526_, v_a_3523_, v_val_3534_);
lean_dec(v_index_3526_);
return v___x_3536_;
}
}
case 1:
{
lean_object* v_index_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v_index_3537_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_index_3537_);
lean_dec_ref_known(v___x_3525_, 1);
v___x_3538_ = lean_box(0);
v___x_3539_ = lean_apply_1(v_f_3524_, v___x_3538_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_dec(v_index_3537_);
lean_dec(v_a_3523_);
lean_dec_ref(v_inst_3521_);
lean_dec_ref(v_inst_3520_);
return v_m_3522_;
}
else
{
lean_object* v_val_3540_; lean_object* v___y_3542_; lean_object* v_i_3543_; lean_object* v_size_3558_; lean_object* v_keyArray_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; uint8_t v___x_3563_; 
v_val_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_val_3540_);
lean_dec_ref_known(v___x_3539_, 1);
v_size_3558_ = lean_ctor_get(v_m_3522_, 0);
v_keyArray_3559_ = lean_ctor_get(v_m_3522_, 1);
v___x_3560_ = lean_unsigned_to_nat(1u);
v___x_3561_ = lean_nat_add(v_size_3558_, v___x_3560_);
v___x_3562_ = lean_array_get_size(v_keyArray_3559_);
v___x_3563_ = lean_nat_dec_lt(v___x_3561_, v___x_3562_);
if (v___x_3563_ == 0)
{
lean_dec(v___x_3561_);
lean_dec(v_index_3537_);
goto v___jp_3548_;
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; 
v___x_3564_ = lean_unsigned_to_nat(4u);
v___x_3565_ = lean_nat_mul(v___x_3561_, v___x_3564_);
v___x_3566_ = lean_unsigned_to_nat(3u);
v___x_3567_ = lean_nat_mul(v___x_3562_, v___x_3566_);
v___x_3568_ = lean_nat_dec_le(v___x_3565_, v___x_3567_);
lean_dec(v___x_3567_);
lean_dec(v___x_3565_);
if (v___x_3568_ == 0)
{
lean_dec(v___x_3561_);
lean_dec(v_index_3537_);
goto v___jp_3548_;
}
else
{
lean_object* v___x_3569_; 
lean_dec_ref(v_inst_3521_);
lean_dec_ref(v_inst_3520_);
v___x_3569_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_3522_, v___x_3561_, v_index_3537_, v_a_3523_, v_val_3540_);
lean_dec(v_index_3537_);
return v___x_3569_;
}
}
v___jp_3541_:
{
lean_object* v_size_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v_size_3544_ = lean_ctor_get(v___y_3542_, 0);
v___x_3545_ = lean_unsigned_to_nat(1u);
v___x_3546_ = lean_nat_add(v_size_3544_, v___x_3545_);
v___x_3547_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3542_, v___x_3546_, v_i_3543_, v_a_3523_, v_val_3540_);
lean_dec(v_i_3543_);
return v___x_3547_;
}
v___jp_3548_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_inc_ref(v_inst_3521_);
lean_inc_ref(v_inst_3520_);
v___x_3549_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3520_, v_inst_3521_, v_m_3522_);
lean_inc(v_a_3523_);
v___x_3550_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3520_, v_inst_3521_, v___x_3549_, v_a_3523_);
switch(lean_obj_tag(v___x_3550_))
{
case 0:
{
lean_object* v_index_3551_; lean_object* v_size_3552_; lean_object* v___x_3553_; 
v_index_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_index_3551_);
lean_dec_ref_known(v___x_3550_, 3);
v_size_3552_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_size_3552_);
v___x_3553_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3549_, v_size_3552_, v_index_3551_, v_a_3523_, v_val_3540_);
lean_dec(v_index_3551_);
return v___x_3553_;
}
case 1:
{
lean_object* v_index_3554_; 
v_index_3554_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_index_3554_);
lean_dec_ref_known(v___x_3550_, 1);
v___y_3542_ = v___x_3549_;
v_i_3543_ = v_index_3554_;
goto v___jp_3541_;
}
default: 
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = lean_unsigned_to_nat(0u);
v___x_3556_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3549_, v___x_3555_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_index_3557_; 
v_index_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_index_3557_);
lean_dec_ref_known(v___x_3556_, 1);
v___y_3542_ = v___x_3549_;
v_i_3543_ = v_index_3557_;
goto v___jp_3541_;
}
else
{
lean_dec(v_val_3540_);
lean_dec(v_a_3523_);
return v___x_3549_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = lean_box(0);
v___x_3571_ = lean_apply_1(v_f_3524_, v___x_3570_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_dec(v_a_3523_);
lean_dec_ref(v_inst_3521_);
lean_dec_ref(v_inst_3520_);
return v_m_3522_;
}
else
{
lean_object* v_val_3572_; lean_object* v___y_3574_; lean_object* v_i_3575_; lean_object* v___y_3581_; lean_object* v_size_3590_; lean_object* v_keyArray_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; 
v_val_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_val_3572_);
lean_dec_ref_known(v___x_3571_, 1);
v_size_3590_ = lean_ctor_get(v_m_3522_, 0);
v_keyArray_3591_ = lean_ctor_get(v_m_3522_, 1);
v___x_3592_ = lean_unsigned_to_nat(1u);
v___x_3593_ = lean_nat_add(v_size_3590_, v___x_3592_);
v___x_3594_ = lean_array_get_size(v_keyArray_3591_);
v___x_3595_ = lean_nat_dec_lt(v___x_3593_, v___x_3594_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; 
lean_dec(v___x_3593_);
lean_inc_ref(v_inst_3521_);
lean_inc_ref(v_inst_3520_);
v___x_3596_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3520_, v_inst_3521_, v_m_3522_);
v___y_3581_ = v___x_3596_;
goto v___jp_3580_;
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3597_ = lean_unsigned_to_nat(4u);
v___x_3598_ = lean_nat_mul(v___x_3593_, v___x_3597_);
lean_dec(v___x_3593_);
v___x_3599_ = lean_unsigned_to_nat(3u);
v___x_3600_ = lean_nat_mul(v___x_3594_, v___x_3599_);
v___x_3601_ = lean_nat_dec_le(v___x_3598_, v___x_3600_);
lean_dec(v___x_3600_);
lean_dec(v___x_3598_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; 
lean_inc_ref(v_inst_3521_);
lean_inc_ref(v_inst_3520_);
v___x_3602_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3520_, v_inst_3521_, v_m_3522_);
v___y_3581_ = v___x_3602_;
goto v___jp_3580_;
}
else
{
v___y_3581_ = v_m_3522_;
goto v___jp_3580_;
}
}
v___jp_3573_:
{
lean_object* v_size_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v_size_3576_ = lean_ctor_get(v___y_3574_, 0);
v___x_3577_ = lean_unsigned_to_nat(1u);
v___x_3578_ = lean_nat_add(v_size_3576_, v___x_3577_);
v___x_3579_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3574_, v___x_3578_, v_i_3575_, v_a_3523_, v_val_3572_);
lean_dec(v_i_3575_);
return v___x_3579_;
}
v___jp_3580_:
{
lean_object* v___x_3582_; 
lean_inc(v_a_3523_);
v___x_3582_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3520_, v_inst_3521_, v___y_3581_, v_a_3523_);
switch(lean_obj_tag(v___x_3582_))
{
case 0:
{
lean_object* v_index_3583_; lean_object* v_size_3584_; lean_object* v___x_3585_; 
v_index_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_index_3583_);
lean_dec_ref_known(v___x_3582_, 3);
v_size_3584_ = lean_ctor_get(v___y_3581_, 0);
lean_inc(v_size_3584_);
v___x_3585_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3581_, v_size_3584_, v_index_3583_, v_a_3523_, v_val_3572_);
lean_dec(v_index_3583_);
return v___x_3585_;
}
case 1:
{
lean_object* v_index_3586_; 
v_index_3586_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_index_3586_);
lean_dec_ref_known(v___x_3582_, 1);
v___y_3574_ = v___y_3581_;
v_i_3575_ = v_index_3586_;
goto v___jp_3573_;
}
default: 
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3587_ = lean_unsigned_to_nat(0u);
v___x_3588_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3581_, v___x_3587_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_index_3589_; 
v_index_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_index_3589_);
lean_dec_ref_known(v___x_3588_, 1);
v___y_3574_ = v___y_3581_;
v_i_3575_ = v_index_3589_;
goto v___jp_3573_;
}
else
{
lean_dec(v_val_3572_);
lean_dec(v_a_3523_);
return v___y_3581_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getThenInsertIfNewImpl_x3f___redArg(lean_object* v_inst_3603_, lean_object* v_inst_3604_, lean_object* v_m_3605_, lean_object* v_a_3606_, lean_object* v_b_3607_){
_start:
{
lean_object* v___x_3608_; 
lean_inc(v_a_3606_);
lean_inc_ref(v_inst_3604_);
lean_inc_ref(v_inst_3603_);
v___x_3608_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3603_, v_inst_3604_, v_m_3605_, v_a_3606_);
switch(lean_obj_tag(v___x_3608_))
{
case 0:
{
lean_object* v_value_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
lean_dec(v_b_3607_);
lean_dec(v_a_3606_);
lean_dec_ref(v_inst_3604_);
lean_dec_ref(v_inst_3603_);
v_value_3609_ = lean_ctor_get(v___x_3608_, 2);
lean_inc(v_value_3609_);
lean_dec_ref_known(v___x_3608_, 3);
v___x_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3610_, 0, v_value_3609_);
v___x_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3610_);
lean_ctor_set(v___x_3611_, 1, v_m_3605_);
return v___x_3611_;
}
case 1:
{
lean_object* v_index_3612_; lean_object* v_size_3613_; lean_object* v_keyArray_3614_; lean_object* v___x_3615_; lean_object* v___y_3617_; lean_object* v_i_3618_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; uint8_t v___x_3639_; 
v_index_3612_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_index_3612_);
lean_dec_ref_known(v___x_3608_, 1);
v_size_3613_ = lean_ctor_get(v_m_3605_, 0);
v_keyArray_3614_ = lean_ctor_get(v_m_3605_, 1);
v___x_3615_ = lean_box(0);
v___x_3636_ = lean_unsigned_to_nat(1u);
v___x_3637_ = lean_nat_add(v_size_3613_, v___x_3636_);
v___x_3638_ = lean_array_get_size(v_keyArray_3614_);
v___x_3639_ = lean_nat_dec_lt(v___x_3637_, v___x_3638_);
if (v___x_3639_ == 0)
{
lean_dec(v___x_3637_);
lean_dec(v_index_3612_);
goto v___jp_3624_;
}
else
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
v___x_3640_ = lean_unsigned_to_nat(4u);
v___x_3641_ = lean_nat_mul(v___x_3637_, v___x_3640_);
v___x_3642_ = lean_unsigned_to_nat(3u);
v___x_3643_ = lean_nat_mul(v___x_3638_, v___x_3642_);
v___x_3644_ = lean_nat_dec_le(v___x_3641_, v___x_3643_);
lean_dec(v___x_3643_);
lean_dec(v___x_3641_);
if (v___x_3644_ == 0)
{
lean_dec(v___x_3637_);
lean_dec(v_index_3612_);
goto v___jp_3624_;
}
else
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
lean_dec_ref(v_inst_3604_);
lean_dec_ref(v_inst_3603_);
v___x_3645_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_3605_, v___x_3637_, v_index_3612_, v_a_3606_, v_b_3607_);
lean_dec(v_index_3612_);
v___x_3646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3615_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
return v___x_3646_;
}
}
v___jp_3616_:
{
lean_object* v_size_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v_size_3619_ = lean_ctor_get(v___y_3617_, 0);
v___x_3620_ = lean_unsigned_to_nat(1u);
v___x_3621_ = lean_nat_add(v_size_3619_, v___x_3620_);
v___x_3622_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3617_, v___x_3621_, v_i_3618_, v_a_3606_, v_b_3607_);
lean_dec(v_i_3618_);
v___x_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3615_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
return v___x_3623_;
}
v___jp_3624_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
lean_inc_ref(v_inst_3604_);
lean_inc_ref(v_inst_3603_);
v___x_3625_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3603_, v_inst_3604_, v_m_3605_);
lean_inc(v_a_3606_);
v___x_3626_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3603_, v_inst_3604_, v___x_3625_, v_a_3606_);
switch(lean_obj_tag(v___x_3626_))
{
case 0:
{
lean_object* v_index_3627_; lean_object* v_size_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v_index_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_index_3627_);
lean_dec_ref_known(v___x_3626_, 3);
v_size_3628_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_size_3628_);
v___x_3629_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3625_, v_size_3628_, v_index_3627_, v_a_3606_, v_b_3607_);
lean_dec(v_index_3627_);
v___x_3630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3615_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
return v___x_3630_;
}
case 1:
{
lean_object* v_index_3631_; 
v_index_3631_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_index_3631_);
lean_dec_ref_known(v___x_3626_, 1);
v___y_3617_ = v___x_3625_;
v_i_3618_ = v_index_3631_;
goto v___jp_3616_;
}
default: 
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = lean_unsigned_to_nat(0u);
v___x_3633_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3625_, v___x_3632_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_index_3634_; 
v_index_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_index_3634_);
lean_dec_ref_known(v___x_3633_, 1);
v___y_3617_ = v___x_3625_;
v_i_3618_ = v_index_3634_;
goto v___jp_3616_;
}
else
{
lean_object* v___x_3635_; 
lean_dec(v_b_3607_);
lean_dec(v_a_3606_);
v___x_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3615_);
lean_ctor_set(v___x_3635_, 1, v___x_3625_);
return v___x_3635_;
}
}
}
}
}
default: 
{
lean_object* v_size_3647_; lean_object* v_keyArray_3648_; lean_object* v___x_3649_; lean_object* v___y_3651_; lean_object* v_i_3652_; lean_object* v___y_3659_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
v_size_3647_ = lean_ctor_get(v_m_3605_, 0);
v_keyArray_3648_ = lean_ctor_get(v_m_3605_, 1);
v___x_3649_ = lean_box(0);
v___x_3670_ = lean_unsigned_to_nat(1u);
v___x_3671_ = lean_nat_add(v_size_3647_, v___x_3670_);
v___x_3672_ = lean_array_get_size(v_keyArray_3648_);
v___x_3673_ = lean_nat_dec_lt(v___x_3671_, v___x_3672_);
if (v___x_3673_ == 0)
{
lean_object* v___x_3674_; 
lean_dec(v___x_3671_);
lean_inc_ref(v_inst_3604_);
lean_inc_ref(v_inst_3603_);
v___x_3674_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3603_, v_inst_3604_, v_m_3605_);
v___y_3659_ = v___x_3674_;
goto v___jp_3658_;
}
else
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; uint8_t v___x_3679_; 
v___x_3675_ = lean_unsigned_to_nat(4u);
v___x_3676_ = lean_nat_mul(v___x_3671_, v___x_3675_);
lean_dec(v___x_3671_);
v___x_3677_ = lean_unsigned_to_nat(3u);
v___x_3678_ = lean_nat_mul(v___x_3672_, v___x_3677_);
v___x_3679_ = lean_nat_dec_le(v___x_3676_, v___x_3678_);
lean_dec(v___x_3678_);
lean_dec(v___x_3676_);
if (v___x_3679_ == 0)
{
lean_object* v___x_3680_; 
lean_inc_ref(v_inst_3604_);
lean_inc_ref(v_inst_3603_);
v___x_3680_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3603_, v_inst_3604_, v_m_3605_);
v___y_3659_ = v___x_3680_;
goto v___jp_3658_;
}
else
{
v___y_3659_ = v_m_3605_;
goto v___jp_3658_;
}
}
v___jp_3650_:
{
lean_object* v_size_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v_size_3653_ = lean_ctor_get(v___y_3651_, 0);
v___x_3654_ = lean_unsigned_to_nat(1u);
v___x_3655_ = lean_nat_add(v_size_3653_, v___x_3654_);
v___x_3656_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3651_, v___x_3655_, v_i_3652_, v_a_3606_, v_b_3607_);
lean_dec(v_i_3652_);
v___x_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3649_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
return v___x_3657_;
}
v___jp_3658_:
{
lean_object* v___x_3660_; 
lean_inc(v_a_3606_);
v___x_3660_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3603_, v_inst_3604_, v___y_3659_, v_a_3606_);
switch(lean_obj_tag(v___x_3660_))
{
case 0:
{
lean_object* v_index_3661_; lean_object* v_size_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v_index_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_index_3661_);
lean_dec_ref_known(v___x_3660_, 3);
v_size_3662_ = lean_ctor_get(v___y_3659_, 0);
lean_inc(v_size_3662_);
v___x_3663_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3659_, v_size_3662_, v_index_3661_, v_a_3606_, v_b_3607_);
lean_dec(v_index_3661_);
v___x_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3649_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
return v___x_3664_;
}
case 1:
{
lean_object* v_index_3665_; 
v_index_3665_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_index_3665_);
lean_dec_ref_known(v___x_3660_, 1);
v___y_3651_ = v___y_3659_;
v_i_3652_ = v_index_3665_;
goto v___jp_3650_;
}
default: 
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_unsigned_to_nat(0u);
v___x_3667_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3659_, v___x_3666_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_index_3668_; 
v_index_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_index_3668_);
lean_dec_ref_known(v___x_3667_, 1);
v___y_3651_ = v___y_3659_;
v_i_3652_ = v_index_3668_;
goto v___jp_3650_;
}
else
{
lean_object* v___x_3669_; 
lean_dec(v_b_3607_);
lean_dec(v_a_3606_);
v___x_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3649_);
lean_ctor_set(v___x_3669_, 1, v___y_3659_);
return v___x_3669_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getThenInsertIfNewImpl_x3f(lean_object* v_00_u03b1_3681_, lean_object* v_00_u03b2_3682_, lean_object* v_inst_3683_, lean_object* v_inst_3684_, lean_object* v_m_3685_, lean_object* v_a_3686_, lean_object* v_b_3687_){
_start:
{
lean_object* v___x_3688_; 
lean_inc(v_a_3686_);
lean_inc_ref(v_inst_3684_);
lean_inc_ref(v_inst_3683_);
v___x_3688_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3683_, v_inst_3684_, v_m_3685_, v_a_3686_);
switch(lean_obj_tag(v___x_3688_))
{
case 0:
{
lean_object* v_value_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
lean_dec(v_b_3687_);
lean_dec(v_a_3686_);
lean_dec_ref(v_inst_3684_);
lean_dec_ref(v_inst_3683_);
v_value_3689_ = lean_ctor_get(v___x_3688_, 2);
lean_inc(v_value_3689_);
lean_dec_ref_known(v___x_3688_, 3);
v___x_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3690_, 0, v_value_3689_);
v___x_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
lean_ctor_set(v___x_3691_, 1, v_m_3685_);
return v___x_3691_;
}
case 1:
{
lean_object* v_index_3692_; lean_object* v_size_3693_; lean_object* v_keyArray_3694_; lean_object* v___x_3695_; lean_object* v___y_3697_; lean_object* v_i_3698_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v_index_3692_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_index_3692_);
lean_dec_ref_known(v___x_3688_, 1);
v_size_3693_ = lean_ctor_get(v_m_3685_, 0);
v_keyArray_3694_ = lean_ctor_get(v_m_3685_, 1);
v___x_3695_ = lean_box(0);
v___x_3716_ = lean_unsigned_to_nat(1u);
v___x_3717_ = lean_nat_add(v_size_3693_, v___x_3716_);
v___x_3718_ = lean_array_get_size(v_keyArray_3694_);
v___x_3719_ = lean_nat_dec_lt(v___x_3717_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_dec(v___x_3717_);
lean_dec(v_index_3692_);
goto v___jp_3704_;
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; uint8_t v___x_3724_; 
v___x_3720_ = lean_unsigned_to_nat(4u);
v___x_3721_ = lean_nat_mul(v___x_3717_, v___x_3720_);
v___x_3722_ = lean_unsigned_to_nat(3u);
v___x_3723_ = lean_nat_mul(v___x_3718_, v___x_3722_);
v___x_3724_ = lean_nat_dec_le(v___x_3721_, v___x_3723_);
lean_dec(v___x_3723_);
lean_dec(v___x_3721_);
if (v___x_3724_ == 0)
{
lean_dec(v___x_3717_);
lean_dec(v_index_3692_);
goto v___jp_3704_;
}
else
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
lean_dec_ref(v_inst_3684_);
lean_dec_ref(v_inst_3683_);
v___x_3725_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_3685_, v___x_3717_, v_index_3692_, v_a_3686_, v_b_3687_);
lean_dec(v_index_3692_);
v___x_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3695_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
return v___x_3726_;
}
}
v___jp_3696_:
{
lean_object* v_size_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v_size_3699_ = lean_ctor_get(v___y_3697_, 0);
v___x_3700_ = lean_unsigned_to_nat(1u);
v___x_3701_ = lean_nat_add(v_size_3699_, v___x_3700_);
v___x_3702_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3697_, v___x_3701_, v_i_3698_, v_a_3686_, v_b_3687_);
lean_dec(v_i_3698_);
v___x_3703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3695_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
return v___x_3703_;
}
v___jp_3704_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
lean_inc_ref(v_inst_3684_);
lean_inc_ref(v_inst_3683_);
v___x_3705_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3683_, v_inst_3684_, v_m_3685_);
lean_inc(v_a_3686_);
v___x_3706_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3683_, v_inst_3684_, v___x_3705_, v_a_3686_);
switch(lean_obj_tag(v___x_3706_))
{
case 0:
{
lean_object* v_index_3707_; lean_object* v_size_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v_index_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_index_3707_);
lean_dec_ref_known(v___x_3706_, 3);
v_size_3708_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_size_3708_);
v___x_3709_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3705_, v_size_3708_, v_index_3707_, v_a_3686_, v_b_3687_);
lean_dec(v_index_3707_);
v___x_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3695_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
return v___x_3710_;
}
case 1:
{
lean_object* v_index_3711_; 
v_index_3711_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_index_3711_);
lean_dec_ref_known(v___x_3706_, 1);
v___y_3697_ = v___x_3705_;
v_i_3698_ = v_index_3711_;
goto v___jp_3696_;
}
default: 
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = lean_unsigned_to_nat(0u);
v___x_3713_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3705_, v___x_3712_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_index_3714_; 
v_index_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_index_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v___y_3697_ = v___x_3705_;
v_i_3698_ = v_index_3714_;
goto v___jp_3696_;
}
else
{
lean_object* v___x_3715_; 
lean_dec(v_b_3687_);
lean_dec(v_a_3686_);
v___x_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3695_);
lean_ctor_set(v___x_3715_, 1, v___x_3705_);
return v___x_3715_;
}
}
}
}
}
default: 
{
lean_object* v_size_3727_; lean_object* v_keyArray_3728_; lean_object* v___x_3729_; lean_object* v___y_3731_; lean_object* v_i_3732_; lean_object* v___y_3739_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; 
v_size_3727_ = lean_ctor_get(v_m_3685_, 0);
v_keyArray_3728_ = lean_ctor_get(v_m_3685_, 1);
v___x_3729_ = lean_box(0);
v___x_3750_ = lean_unsigned_to_nat(1u);
v___x_3751_ = lean_nat_add(v_size_3727_, v___x_3750_);
v___x_3752_ = lean_array_get_size(v_keyArray_3728_);
v___x_3753_ = lean_nat_dec_lt(v___x_3751_, v___x_3752_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; 
lean_dec(v___x_3751_);
lean_inc_ref(v_inst_3684_);
lean_inc_ref(v_inst_3683_);
v___x_3754_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3683_, v_inst_3684_, v_m_3685_);
v___y_3739_ = v___x_3754_;
goto v___jp_3738_;
}
else
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v___x_3755_ = lean_unsigned_to_nat(4u);
v___x_3756_ = lean_nat_mul(v___x_3751_, v___x_3755_);
lean_dec(v___x_3751_);
v___x_3757_ = lean_unsigned_to_nat(3u);
v___x_3758_ = lean_nat_mul(v___x_3752_, v___x_3757_);
v___x_3759_ = lean_nat_dec_le(v___x_3756_, v___x_3758_);
lean_dec(v___x_3758_);
lean_dec(v___x_3756_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; 
lean_inc_ref(v_inst_3684_);
lean_inc_ref(v_inst_3683_);
v___x_3760_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3683_, v_inst_3684_, v_m_3685_);
v___y_3739_ = v___x_3760_;
goto v___jp_3738_;
}
else
{
v___y_3739_ = v_m_3685_;
goto v___jp_3738_;
}
}
v___jp_3730_:
{
lean_object* v_size_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_size_3733_ = lean_ctor_get(v___y_3731_, 0);
v___x_3734_ = lean_unsigned_to_nat(1u);
v___x_3735_ = lean_nat_add(v_size_3733_, v___x_3734_);
v___x_3736_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3731_, v___x_3735_, v_i_3732_, v_a_3686_, v_b_3687_);
lean_dec(v_i_3732_);
v___x_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3729_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
return v___x_3737_;
}
v___jp_3738_:
{
lean_object* v___x_3740_; 
lean_inc(v_a_3686_);
v___x_3740_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3683_, v_inst_3684_, v___y_3739_, v_a_3686_);
switch(lean_obj_tag(v___x_3740_))
{
case 0:
{
lean_object* v_index_3741_; lean_object* v_size_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v_index_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_index_3741_);
lean_dec_ref_known(v___x_3740_, 3);
v_size_3742_ = lean_ctor_get(v___y_3739_, 0);
lean_inc(v_size_3742_);
v___x_3743_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3739_, v_size_3742_, v_index_3741_, v_a_3686_, v_b_3687_);
lean_dec(v_index_3741_);
v___x_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3729_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
return v___x_3744_;
}
case 1:
{
lean_object* v_index_3745_; 
v_index_3745_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_index_3745_);
lean_dec_ref_known(v___x_3740_, 1);
v___y_3731_ = v___y_3739_;
v_i_3732_ = v_index_3745_;
goto v___jp_3730_;
}
default: 
{
lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3746_ = lean_unsigned_to_nat(0u);
v___x_3747_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3739_, v___x_3746_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_index_3748_; 
v_index_3748_ = lean_ctor_get(v___x_3747_, 0);
lean_inc(v_index_3748_);
lean_dec_ref_known(v___x_3747_, 1);
v___y_3731_ = v___y_3739_;
v_i_3732_ = v_index_3748_;
goto v___jp_3730_;
}
else
{
lean_object* v___x_3749_; 
lean_dec(v_b_3687_);
lean_dec(v_a_3686_);
v___x_3749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3729_);
lean_ctor_set(v___x_3749_, 1, v___y_3739_);
return v___x_3749_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(lean_object* v_x_3761_, lean_object* v_h__1_3762_, lean_object* v_h__2_3763_){
_start:
{
if (lean_obj_tag(v_x_3761_) == 0)
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
lean_dec(v_h__2_3763_);
v___x_3764_ = lean_box(0);
v___x_3765_ = lean_apply_1(v_h__1_3762_, v___x_3764_);
return v___x_3765_;
}
else
{
lean_object* v_val_3766_; lean_object* v___x_3767_; 
lean_dec(v_h__1_3762_);
v_val_3766_ = lean_ctor_get(v_x_3761_, 0);
lean_inc(v_val_3766_);
lean_dec_ref_known(v_x_3761_, 1);
v___x_3767_ = lean_apply_1(v_h__2_3763_, v_val_3766_);
return v___x_3767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(lean_object* v_00_u03b2_3768_, lean_object* v_motive_3769_, lean_object* v_x_3770_, lean_object* v_h__1_3771_, lean_object* v_h__2_3772_){
_start:
{
if (lean_obj_tag(v_x_3770_) == 0)
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
lean_dec(v_h__2_3772_);
v___x_3773_ = lean_box(0);
v___x_3774_ = lean_apply_1(v_h__1_3771_, v___x_3773_);
return v___x_3774_;
}
else
{
lean_object* v_val_3775_; lean_object* v___x_3776_; 
lean_dec(v_h__1_3771_);
v_val_3775_ = lean_ctor_get(v_x_3770_, 0);
lean_inc(v_val_3775_);
lean_dec_ref_known(v_x_3770_, 1);
v___x_3776_ = lean_apply_1(v_h__2_3772_, v_val_3775_);
return v___x_3776_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg___lam__0(lean_object* v_inst_3777_, lean_object* v_inst_3778_, lean_object* v_x_3779_, lean_object* v_____s_3780_){
_start:
{
lean_object* v_fst_3781_; lean_object* v_snd_3782_; lean_object* v___y_3784_; lean_object* v_i_3785_; lean_object* v___y_3792_; lean_object* v___y_3804_; lean_object* v_i_3805_; lean_object* v___x_3823_; 
v_fst_3781_ = lean_ctor_get(v_x_3779_, 0);
lean_inc_n(v_fst_3781_, 2);
v_snd_3782_ = lean_ctor_get(v_x_3779_, 1);
lean_inc(v_snd_3782_);
lean_dec_ref(v_x_3779_);
lean_inc_ref(v_inst_3778_);
lean_inc_ref(v_inst_3777_);
v___x_3823_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3777_, v_inst_3778_, v_____s_3780_, v_fst_3781_);
switch(lean_obj_tag(v___x_3823_))
{
case 0:
{
lean_object* v_index_3824_; lean_object* v_size_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
lean_dec_ref(v_inst_3778_);
lean_dec_ref(v_inst_3777_);
v_index_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_index_3824_);
lean_dec_ref_known(v___x_3823_, 3);
v_size_3825_ = lean_ctor_get(v_____s_3780_, 0);
lean_inc(v_size_3825_);
v___x_3826_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_3780_, v_size_3825_, v_index_3824_, v_fst_3781_, v_snd_3782_);
lean_dec(v_index_3824_);
v___x_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
return v___x_3827_;
}
case 1:
{
lean_object* v_index_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3847_; 
v_index_3828_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3830_ = v___x_3823_;
v_isShared_3831_ = v_isSharedCheck_3847_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_index_3828_);
lean_dec(v___x_3823_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3847_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v_size_3832_; lean_object* v_keyArray_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; uint8_t v___x_3837_; 
v_size_3832_ = lean_ctor_get(v_____s_3780_, 0);
v_keyArray_3833_ = lean_ctor_get(v_____s_3780_, 1);
v___x_3834_ = lean_unsigned_to_nat(1u);
v___x_3835_ = lean_nat_add(v_size_3832_, v___x_3834_);
v___x_3836_ = lean_array_get_size(v_keyArray_3833_);
v___x_3837_ = lean_nat_dec_lt(v___x_3835_, v___x_3836_);
if (v___x_3837_ == 0)
{
lean_dec(v___x_3835_);
lean_del_object(v___x_3830_);
lean_dec(v_index_3828_);
goto v___jp_3811_;
}
else
{
lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v___x_3838_ = lean_unsigned_to_nat(4u);
v___x_3839_ = lean_nat_mul(v___x_3835_, v___x_3838_);
v___x_3840_ = lean_unsigned_to_nat(3u);
v___x_3841_ = lean_nat_mul(v___x_3836_, v___x_3840_);
v___x_3842_ = lean_nat_dec_le(v___x_3839_, v___x_3841_);
lean_dec(v___x_3841_);
lean_dec(v___x_3839_);
if (v___x_3842_ == 0)
{
lean_dec(v___x_3835_);
lean_del_object(v___x_3830_);
lean_dec(v_index_3828_);
goto v___jp_3811_;
}
else
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
lean_dec_ref(v_inst_3778_);
lean_dec_ref(v_inst_3777_);
v___x_3843_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_3780_, v___x_3835_, v_index_3828_, v_fst_3781_, v_snd_3782_);
lean_dec(v_index_3828_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v___x_3843_);
v___x_3845_ = v___x_3830_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
}
default: 
{
lean_object* v_size_3848_; lean_object* v_keyArray_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; uint8_t v___x_3853_; 
v_size_3848_ = lean_ctor_get(v_____s_3780_, 0);
v_keyArray_3849_ = lean_ctor_get(v_____s_3780_, 1);
v___x_3850_ = lean_unsigned_to_nat(1u);
v___x_3851_ = lean_nat_add(v_size_3848_, v___x_3850_);
v___x_3852_ = lean_array_get_size(v_keyArray_3849_);
v___x_3853_ = lean_nat_dec_lt(v___x_3851_, v___x_3852_);
if (v___x_3853_ == 0)
{
lean_object* v___x_3854_; 
lean_dec(v___x_3851_);
lean_inc_ref(v_inst_3778_);
lean_inc_ref(v_inst_3777_);
v___x_3854_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3777_, v_inst_3778_, v_____s_3780_);
v___y_3792_ = v___x_3854_;
goto v___jp_3791_;
}
else
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v___x_3855_ = lean_unsigned_to_nat(4u);
v___x_3856_ = lean_nat_mul(v___x_3851_, v___x_3855_);
lean_dec(v___x_3851_);
v___x_3857_ = lean_unsigned_to_nat(3u);
v___x_3858_ = lean_nat_mul(v___x_3852_, v___x_3857_);
v___x_3859_ = lean_nat_dec_le(v___x_3856_, v___x_3858_);
lean_dec(v___x_3858_);
lean_dec(v___x_3856_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; 
lean_inc_ref(v_inst_3778_);
lean_inc_ref(v_inst_3777_);
v___x_3860_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3777_, v_inst_3778_, v_____s_3780_);
v___y_3792_ = v___x_3860_;
goto v___jp_3791_;
}
else
{
v___y_3792_ = v_____s_3780_;
goto v___jp_3791_;
}
}
}
}
v___jp_3783_:
{
lean_object* v_size_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v_size_3786_ = lean_ctor_get(v___y_3784_, 0);
v___x_3787_ = lean_unsigned_to_nat(1u);
v___x_3788_ = lean_nat_add(v_size_3786_, v___x_3787_);
v___x_3789_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3784_, v___x_3788_, v_i_3785_, v_fst_3781_, v_snd_3782_);
lean_dec(v_i_3785_);
v___x_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
return v___x_3790_;
}
v___jp_3791_:
{
lean_object* v___x_3793_; 
lean_inc(v_fst_3781_);
v___x_3793_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3777_, v_inst_3778_, v___y_3792_, v_fst_3781_);
switch(lean_obj_tag(v___x_3793_))
{
case 0:
{
lean_object* v_index_3794_; lean_object* v_size_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v_index_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_index_3794_);
lean_dec_ref_known(v___x_3793_, 3);
v_size_3795_ = lean_ctor_get(v___y_3792_, 0);
lean_inc(v_size_3795_);
v___x_3796_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3792_, v_size_3795_, v_index_3794_, v_fst_3781_, v_snd_3782_);
lean_dec(v_index_3794_);
v___x_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
return v___x_3797_;
}
case 1:
{
lean_object* v_index_3798_; 
v_index_3798_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_index_3798_);
lean_dec_ref_known(v___x_3793_, 1);
v___y_3784_ = v___y_3792_;
v_i_3785_ = v_index_3798_;
goto v___jp_3783_;
}
default: 
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = lean_unsigned_to_nat(0u);
v___x_3800_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3792_, v___x_3799_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_index_3801_; 
v_index_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_index_3801_);
lean_dec_ref_known(v___x_3800_, 1);
v___y_3784_ = v___y_3792_;
v_i_3785_ = v_index_3801_;
goto v___jp_3783_;
}
else
{
lean_object* v___x_3802_; 
lean_dec(v_snd_3782_);
lean_dec(v_fst_3781_);
v___x_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3802_, 0, v___y_3792_);
return v___x_3802_;
}
}
}
}
v___jp_3803_:
{
lean_object* v_size_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
v_size_3806_ = lean_ctor_get(v___y_3804_, 0);
v___x_3807_ = lean_unsigned_to_nat(1u);
v___x_3808_ = lean_nat_add(v_size_3806_, v___x_3807_);
v___x_3809_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3804_, v___x_3808_, v_i_3805_, v_fst_3781_, v_snd_3782_);
lean_dec(v_i_3805_);
v___x_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
return v___x_3810_;
}
v___jp_3811_:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
lean_inc_ref(v_inst_3778_);
lean_inc_ref(v_inst_3777_);
v___x_3812_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3777_, v_inst_3778_, v_____s_3780_);
lean_inc(v_fst_3781_);
v___x_3813_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3777_, v_inst_3778_, v___x_3812_, v_fst_3781_);
switch(lean_obj_tag(v___x_3813_))
{
case 0:
{
lean_object* v_index_3814_; lean_object* v_size_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v_index_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_index_3814_);
lean_dec_ref_known(v___x_3813_, 3);
v_size_3815_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_size_3815_);
v___x_3816_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3812_, v_size_3815_, v_index_3814_, v_fst_3781_, v_snd_3782_);
lean_dec(v_index_3814_);
v___x_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
return v___x_3817_;
}
case 1:
{
lean_object* v_index_3818_; 
v_index_3818_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_index_3818_);
lean_dec_ref_known(v___x_3813_, 1);
v___y_3804_ = v___x_3812_;
v_i_3805_ = v_index_3818_;
goto v___jp_3803_;
}
default: 
{
lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3819_ = lean_unsigned_to_nat(0u);
v___x_3820_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3812_, v___x_3819_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_index_3821_; 
v_index_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_index_3821_);
lean_dec_ref_known(v___x_3820_, 1);
v___y_3804_ = v___x_3812_;
v_i_3805_ = v_index_3821_;
goto v___jp_3803_;
}
else
{
lean_object* v___x_3822_; 
lean_dec(v_snd_3782_);
lean_dec(v_fst_3781_);
v___x_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3812_);
return v___x_3822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object* v_inst_3861_, lean_object* v_inst_3862_, lean_object* v_inst_3863_, lean_object* v_m_3864_, lean_object* v_l_3865_){
_start:
{
lean_object* v___f_3866_; lean_object* v___x_3867_; 
v___f_3866_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_3866_, 0, v_inst_3862_);
lean_closure_set(v___f_3866_, 1, v_inst_3863_);
v___x_3867_ = lean_apply_4(v_inst_3861_, lean_box(0), v_l_3865_, v_m_3864_, v___f_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany(lean_object* v_00_u03b1_3868_, lean_object* v_00_u03b2_3869_, lean_object* v_00_u03c1_3870_, lean_object* v_inst_3871_, lean_object* v_inst_3872_, lean_object* v_inst_3873_, lean_object* v_m_3874_, lean_object* v_l_3875_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_3871_, v_inst_3872_, v_inst_3873_, v_m_3874_, v_l_3875_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_inst_3877_, lean_object* v_inst_3878_, lean_object* v_a_3879_, lean_object* v_____s_3880_){
_start:
{
lean_object* v___x_3881_; lean_object* v___y_3883_; lean_object* v_i_3884_; lean_object* v___y_3891_; lean_object* v___y_3903_; lean_object* v_i_3904_; lean_object* v___x_3922_; 
v___x_3881_ = lean_box(0);
lean_inc(v_a_3879_);
lean_inc_ref(v_inst_3878_);
lean_inc_ref(v_inst_3877_);
v___x_3922_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3877_, v_inst_3878_, v_____s_3880_, v_a_3879_);
switch(lean_obj_tag(v___x_3922_))
{
case 0:
{
lean_object* v___x_3923_; 
lean_dec_ref_known(v___x_3922_, 3);
lean_dec(v_a_3879_);
lean_dec_ref(v_inst_3878_);
lean_dec_ref(v_inst_3877_);
v___x_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3923_, 0, v_____s_3880_);
return v___x_3923_;
}
case 1:
{
lean_object* v_index_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3943_; 
v_index_3924_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3926_ = v___x_3922_;
v_isShared_3927_ = v_isSharedCheck_3943_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_index_3924_);
lean_dec(v___x_3922_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3943_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v_size_3928_; lean_object* v_keyArray_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; uint8_t v___x_3933_; 
v_size_3928_ = lean_ctor_get(v_____s_3880_, 0);
v_keyArray_3929_ = lean_ctor_get(v_____s_3880_, 1);
v___x_3930_ = lean_unsigned_to_nat(1u);
v___x_3931_ = lean_nat_add(v_size_3928_, v___x_3930_);
v___x_3932_ = lean_array_get_size(v_keyArray_3929_);
v___x_3933_ = lean_nat_dec_lt(v___x_3931_, v___x_3932_);
if (v___x_3933_ == 0)
{
lean_dec(v___x_3931_);
lean_del_object(v___x_3926_);
lean_dec(v_index_3924_);
goto v___jp_3910_;
}
else
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; uint8_t v___x_3938_; 
v___x_3934_ = lean_unsigned_to_nat(4u);
v___x_3935_ = lean_nat_mul(v___x_3931_, v___x_3934_);
v___x_3936_ = lean_unsigned_to_nat(3u);
v___x_3937_ = lean_nat_mul(v___x_3932_, v___x_3936_);
v___x_3938_ = lean_nat_dec_le(v___x_3935_, v___x_3937_);
lean_dec(v___x_3937_);
lean_dec(v___x_3935_);
if (v___x_3938_ == 0)
{
lean_dec(v___x_3931_);
lean_del_object(v___x_3926_);
lean_dec(v_index_3924_);
goto v___jp_3910_;
}
else
{
lean_object* v___x_3939_; lean_object* v___x_3941_; 
lean_dec_ref(v_inst_3878_);
lean_dec_ref(v_inst_3877_);
v___x_3939_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_3880_, v___x_3931_, v_index_3924_, v_a_3879_, v___x_3881_);
lean_dec(v_index_3924_);
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 0, v___x_3939_);
v___x_3941_ = v___x_3926_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3939_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
}
default: 
{
lean_object* v_size_3944_; lean_object* v_keyArray_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; uint8_t v___x_3949_; 
v_size_3944_ = lean_ctor_get(v_____s_3880_, 0);
v_keyArray_3945_ = lean_ctor_get(v_____s_3880_, 1);
v___x_3946_ = lean_unsigned_to_nat(1u);
v___x_3947_ = lean_nat_add(v_size_3944_, v___x_3946_);
v___x_3948_ = lean_array_get_size(v_keyArray_3945_);
v___x_3949_ = lean_nat_dec_lt(v___x_3947_, v___x_3948_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; 
lean_dec(v___x_3947_);
lean_inc_ref(v_inst_3878_);
lean_inc_ref(v_inst_3877_);
v___x_3950_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3877_, v_inst_3878_, v_____s_3880_);
v___y_3891_ = v___x_3950_;
goto v___jp_3890_;
}
else
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; uint8_t v___x_3955_; 
v___x_3951_ = lean_unsigned_to_nat(4u);
v___x_3952_ = lean_nat_mul(v___x_3947_, v___x_3951_);
lean_dec(v___x_3947_);
v___x_3953_ = lean_unsigned_to_nat(3u);
v___x_3954_ = lean_nat_mul(v___x_3948_, v___x_3953_);
v___x_3955_ = lean_nat_dec_le(v___x_3952_, v___x_3954_);
lean_dec(v___x_3954_);
lean_dec(v___x_3952_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; 
lean_inc_ref(v_inst_3878_);
lean_inc_ref(v_inst_3877_);
v___x_3956_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3877_, v_inst_3878_, v_____s_3880_);
v___y_3891_ = v___x_3956_;
goto v___jp_3890_;
}
else
{
v___y_3891_ = v_____s_3880_;
goto v___jp_3890_;
}
}
}
}
v___jp_3882_:
{
lean_object* v_size_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v_size_3885_ = lean_ctor_get(v___y_3883_, 0);
v___x_3886_ = lean_unsigned_to_nat(1u);
v___x_3887_ = lean_nat_add(v_size_3885_, v___x_3886_);
v___x_3888_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3883_, v___x_3887_, v_i_3884_, v_a_3879_, v___x_3881_);
lean_dec(v_i_3884_);
v___x_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
return v___x_3889_;
}
v___jp_3890_:
{
lean_object* v___x_3892_; 
lean_inc(v_a_3879_);
v___x_3892_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3877_, v_inst_3878_, v___y_3891_, v_a_3879_);
switch(lean_obj_tag(v___x_3892_))
{
case 0:
{
lean_object* v_index_3893_; lean_object* v_size_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v_index_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_index_3893_);
lean_dec_ref_known(v___x_3892_, 3);
v_size_3894_ = lean_ctor_get(v___y_3891_, 0);
lean_inc(v_size_3894_);
v___x_3895_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3891_, v_size_3894_, v_index_3893_, v_a_3879_, v___x_3881_);
lean_dec(v_index_3893_);
v___x_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
return v___x_3896_;
}
case 1:
{
lean_object* v_index_3897_; 
v_index_3897_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_index_3897_);
lean_dec_ref_known(v___x_3892_, 1);
v___y_3883_ = v___y_3891_;
v_i_3884_ = v_index_3897_;
goto v___jp_3882_;
}
default: 
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = lean_unsigned_to_nat(0u);
v___x_3899_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3891_, v___x_3898_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_index_3900_; 
v_index_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_index_3900_);
lean_dec_ref_known(v___x_3899_, 1);
v___y_3883_ = v___y_3891_;
v_i_3884_ = v_index_3900_;
goto v___jp_3882_;
}
else
{
lean_object* v___x_3901_; 
lean_dec(v_a_3879_);
v___x_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3901_, 0, v___y_3891_);
return v___x_3901_;
}
}
}
}
v___jp_3902_:
{
lean_object* v_size_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_size_3905_ = lean_ctor_get(v___y_3903_, 0);
v___x_3906_ = lean_unsigned_to_nat(1u);
v___x_3907_ = lean_nat_add(v_size_3905_, v___x_3906_);
v___x_3908_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3903_, v___x_3907_, v_i_3904_, v_a_3879_, v___x_3881_);
lean_dec(v_i_3904_);
v___x_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
return v___x_3909_;
}
v___jp_3910_:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
lean_inc_ref(v_inst_3878_);
lean_inc_ref(v_inst_3877_);
v___x_3911_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_3877_, v_inst_3878_, v_____s_3880_);
lean_inc(v_a_3879_);
v___x_3912_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_3877_, v_inst_3878_, v___x_3911_, v_a_3879_);
switch(lean_obj_tag(v___x_3912_))
{
case 0:
{
lean_object* v_index_3913_; lean_object* v_size_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_index_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_index_3913_);
lean_dec_ref_known(v___x_3912_, 3);
v_size_3914_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_size_3914_);
v___x_3915_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3911_, v_size_3914_, v_index_3913_, v_a_3879_, v___x_3881_);
lean_dec(v_index_3913_);
v___x_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
return v___x_3916_;
}
case 1:
{
lean_object* v_index_3917_; 
v_index_3917_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_index_3917_);
lean_dec_ref_known(v___x_3912_, 1);
v___y_3903_ = v___x_3911_;
v_i_3904_ = v_index_3917_;
goto v___jp_3902_;
}
default: 
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = lean_unsigned_to_nat(0u);
v___x_3919_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3911_, v___x_3918_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v_index_3920_; 
v_index_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_index_3920_);
lean_dec_ref_known(v___x_3919_, 1);
v___y_3903_ = v___x_3911_;
v_i_3904_ = v_index_3920_;
goto v___jp_3902_;
}
else
{
lean_object* v___x_3921_; 
lean_dec(v_a_3879_);
v___x_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3911_);
return v___x_3921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object* v_inst_3957_, lean_object* v_inst_3958_, lean_object* v_inst_3959_, lean_object* v_m_3960_, lean_object* v_l_3961_){
_start:
{
lean_object* v___f_3962_; lean_object* v___x_3963_; 
v___f_3962_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_3962_, 0, v_inst_3958_);
lean_closure_set(v___f_3962_, 1, v_inst_3959_);
v___x_3963_ = lean_apply_4(v_inst_3957_, lean_box(0), v_l_3961_, v_m_3960_, v___f_3962_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_3964_, lean_object* v_00_u03c1_3965_, lean_object* v_inst_3966_, lean_object* v_inst_3967_, lean_object* v_inst_3968_, lean_object* v_m_3969_, lean_object* v_l_3970_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_3966_, v_inst_3967_, v_inst_3968_, v_m_3969_, v_l_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0(lean_object* v_inst_3972_, lean_object* v_inst_3973_, lean_object* v_m_u2082_3974_, lean_object* v_inst_3975_, uint8_t v___x_3976_, lean_object* v___x_3977_, uint8_t v___x_3978_, lean_object* v___x_3979_, lean_object* v_a_3980_, lean_object* v_b_3981_, lean_object* v_acc_3982_){
_start:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; uint8_t v___x_3985_; 
v___x_3983_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_3972_, v_inst_3973_, v_m_u2082_3974_, v_a_3980_);
v___x_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3984_, 0, v_b_3981_);
v___x_3985_ = l_Option_instBEq_beq___redArg(v_inst_3975_, v___x_3983_, v___x_3984_);
if (v___x_3985_ == 0)
{
if (v___x_3976_ == 0)
{
lean_object* v___x_3986_; 
v___x_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3977_);
return v___x_3986_;
}
else
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
lean_dec_ref(v___x_3977_);
v___x_3987_ = lean_box(v___x_3978_);
v___x_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3987_);
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
lean_ctor_set(v___x_3989_, 1, v___x_3979_);
v___x_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
return v___x_3990_;
}
}
else
{
lean_object* v___x_3991_; 
v___x_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3977_);
return v___x_3991_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0___boxed(lean_object* v_inst_3992_, lean_object* v_inst_3993_, lean_object* v_m_u2082_3994_, lean_object* v_inst_3995_, lean_object* v___x_3996_, lean_object* v___x_3997_, lean_object* v___x_3998_, lean_object* v___x_3999_, lean_object* v_a_4000_, lean_object* v_b_4001_, lean_object* v_acc_4002_){
_start:
{
uint8_t v___x_231__boxed_4003_; uint8_t v___x_233__boxed_4004_; lean_object* v_res_4005_; 
v___x_231__boxed_4003_ = lean_unbox(v___x_3996_);
v___x_233__boxed_4004_ = lean_unbox(v___x_3998_);
v_res_4005_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0(v_inst_3992_, v_inst_3993_, v_m_u2082_3994_, v_inst_3995_, v___x_231__boxed_4003_, v___x_3997_, v___x_233__boxed_4004_, v___x_3999_, v_a_4000_, v_b_4001_, v_acc_4002_);
lean_dec_ref(v_acc_4002_);
lean_dec_ref(v_m_u2082_3994_);
return v_res_4005_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object* v_inst_4006_, lean_object* v_inst_4007_, lean_object* v_inst_4008_, lean_object* v_m_u2081_4009_, lean_object* v_m_u2082_4010_){
_start:
{
lean_object* v_size_4011_; lean_object* v_size_4012_; uint8_t v___x_4013_; 
v_size_4011_ = lean_ctor_get(v_m_u2081_4009_, 0);
v_size_4012_ = lean_ctor_get(v_m_u2082_4010_, 0);
v___x_4013_ = lean_nat_dec_eq(v_size_4011_, v_size_4012_);
if (v___x_4013_ == 0)
{
lean_dec_ref(v_m_u2082_4010_);
lean_dec_ref(v_m_u2081_4009_);
lean_dec_ref(v_inst_4008_);
lean_dec_ref(v_inst_4007_);
lean_dec_ref(v_inst_4006_);
return v___x_4013_;
}
else
{
uint8_t v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___f_4020_; lean_object* v___x_4021_; lean_object* v_fst_4022_; 
v___x_4014_ = 0;
v___x_4015_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_4016_ = lean_box(0);
v___x_4017_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0));
v___x_4018_ = lean_box(v___x_4013_);
v___x_4019_ = lean_box(v___x_4014_);
v___f_4020_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0___boxed), 11, 8);
lean_closure_set(v___f_4020_, 0, v_inst_4006_);
lean_closure_set(v___f_4020_, 1, v_inst_4007_);
lean_closure_set(v___f_4020_, 2, v_m_u2082_4010_);
lean_closure_set(v___f_4020_, 3, v_inst_4008_);
lean_closure_set(v___f_4020_, 4, v___x_4018_);
lean_closure_set(v___f_4020_, 5, v___x_4017_);
lean_closure_set(v___f_4020_, 6, v___x_4019_);
lean_closure_set(v___f_4020_, 7, v___x_4016_);
v___x_4021_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_4015_, v___f_4020_, v___x_4017_, v_m_u2081_4009_);
v_fst_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_fst_4022_);
lean_dec(v___x_4021_);
if (lean_obj_tag(v_fst_4022_) == 0)
{
return v___x_4013_;
}
else
{
lean_object* v_val_4023_; uint8_t v___x_4024_; 
v_val_4023_ = lean_ctor_get(v_fst_4022_, 0);
lean_inc(v_val_4023_);
lean_dec_ref_known(v_fst_4022_, 1);
v___x_4024_ = lean_unbox(v_val_4023_);
lean_dec(v_val_4023_);
return v___x_4024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___boxed(lean_object* v_inst_4025_, lean_object* v_inst_4026_, lean_object* v_inst_4027_, lean_object* v_m_u2081_4028_, lean_object* v_m_u2082_4029_){
_start:
{
uint8_t v_res_4030_; lean_object* v_r_4031_; 
v_res_4030_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_4025_, v_inst_4026_, v_inst_4027_, v_m_u2081_4028_, v_m_u2082_4029_);
v_r_4031_ = lean_box(v_res_4030_);
return v_r_4031_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq(lean_object* v_00_u03b1_4032_, lean_object* v_00_u03b2_4033_, lean_object* v_inst_4034_, lean_object* v_inst_4035_, lean_object* v_inst_4036_, lean_object* v_m_u2081_4037_, lean_object* v_m_u2082_4038_){
_start:
{
uint8_t v___x_4039_; 
v___x_4039_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_4034_, v_inst_4035_, v_inst_4036_, v_m_u2081_4037_, v_m_u2082_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___boxed(lean_object* v_00_u03b1_4040_, lean_object* v_00_u03b2_4041_, lean_object* v_inst_4042_, lean_object* v_inst_4043_, lean_object* v_inst_4044_, lean_object* v_m_u2081_4045_, lean_object* v_m_u2082_4046_){
_start:
{
uint8_t v_res_4047_; lean_object* v_r_4048_; 
v_res_4047_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq(v_00_u03b1_4040_, v_00_u03b2_4041_, v_inst_4042_, v_inst_4043_, v_inst_4044_, v_m_u2081_4045_, v_m_u2082_4046_);
v_r_4048_ = lean_box(v_res_4047_);
return v_r_4048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object* v_inst_4049_, lean_object* v_inst_4050_, lean_object* v_m_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Std_DHashMap_Internal_Raw_u2080_scan___redArg(v_inst_4049_, v_inst_4050_, v_m_4051_, v_a_4052_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_key_4054_; lean_object* v___x_4055_; 
v_key_4054_ = lean_ctor_get(v___x_4053_, 1);
lean_inc(v_key_4054_);
lean_dec_ref_known(v___x_4053_, 3);
v___x_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4055_, 0, v_key_4054_);
return v___x_4055_;
}
else
{
lean_object* v___x_4056_; 
v___x_4056_ = lean_box(0);
return v___x_4056_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg___boxed(lean_object* v_inst_4057_, lean_object* v_inst_4058_, lean_object* v_m_4059_, lean_object* v_a_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_4057_, v_inst_4058_, v_m_4059_, v_a_4060_);
lean_dec_ref(v_m_4059_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f(lean_object* v_00_u03b1_4062_, lean_object* v_00_u03b2_4063_, lean_object* v_inst_4064_, lean_object* v_inst_4065_, lean_object* v_m_4066_, lean_object* v_a_4067_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_4064_, v_inst_4065_, v_m_4066_, v_a_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___boxed(lean_object* v_00_u03b1_4069_, lean_object* v_00_u03b2_4070_, lean_object* v_inst_4071_, lean_object* v_inst_4072_, lean_object* v_m_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f(v_00_u03b1_4069_, v_00_u03b2_4070_, v_inst_4071_, v_inst_4072_, v_m_4073_, v_a_4074_);
lean_dec_ref(v_m_4073_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object* v_inst_4076_, lean_object* v_inst_4077_, lean_object* v_m_4078_, lean_object* v_a_4079_){
_start:
{
lean_object* v___x_4080_; lean_object* v_val_4081_; 
v___x_4080_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_4076_, v_inst_4077_, v_m_4078_, v_a_4079_);
v_val_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_val_4081_);
lean_dec(v___x_4080_);
return v_val_4081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg___boxed(lean_object* v_inst_4082_, lean_object* v_inst_4083_, lean_object* v_m_4084_, lean_object* v_a_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_4082_, v_inst_4083_, v_m_4084_, v_a_4085_);
lean_dec_ref(v_m_4084_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey(lean_object* v_00_u03b1_4087_, lean_object* v_00_u03b2_4088_, lean_object* v_inst_4089_, lean_object* v_inst_4090_, lean_object* v_m_4091_, lean_object* v_a_4092_, lean_object* v_hma_4093_){
_start:
{
lean_object* v___x_4094_; lean_object* v_val_4095_; 
v___x_4094_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_4089_, v_inst_4090_, v_m_4091_, v_a_4092_);
v_val_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_val_4095_);
lean_dec(v___x_4094_);
return v_val_4095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___boxed(lean_object* v_00_u03b1_4096_, lean_object* v_00_u03b2_4097_, lean_object* v_inst_4098_, lean_object* v_inst_4099_, lean_object* v_m_4100_, lean_object* v_a_4101_, lean_object* v_hma_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_Std_DHashMap_Internal_Raw_u2080_getKey(v_00_u03b1_4096_, v_00_u03b2_4097_, v_inst_4098_, v_inst_4099_, v_m_4100_, v_a_4101_, v_hma_4102_);
lean_dec_ref(v_m_4100_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object* v_inst_4104_, lean_object* v_inst_4105_, lean_object* v_m_4106_, lean_object* v_a_4107_, lean_object* v_fallback_4108_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_4104_, v_inst_4105_, v_m_4106_, v_a_4107_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_inc(v_fallback_4108_);
return v_fallback_4108_;
}
else
{
lean_object* v_val_4110_; 
v_val_4110_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_val_4110_);
lean_dec_ref_known(v___x_4109_, 1);
return v_val_4110_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg___boxed(lean_object* v_inst_4111_, lean_object* v_inst_4112_, lean_object* v_m_4113_, lean_object* v_a_4114_, lean_object* v_fallback_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_4111_, v_inst_4112_, v_m_4113_, v_a_4114_, v_fallback_4115_);
lean_dec(v_fallback_4115_);
lean_dec_ref(v_m_4113_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD(lean_object* v_00_u03b1_4117_, lean_object* v_00_u03b2_4118_, lean_object* v_inst_4119_, lean_object* v_inst_4120_, lean_object* v_m_4121_, lean_object* v_a_4122_, lean_object* v_fallback_4123_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_4119_, v_inst_4120_, v_m_4121_, v_a_4122_, v_fallback_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___boxed(lean_object* v_00_u03b1_4125_, lean_object* v_00_u03b2_4126_, lean_object* v_inst_4127_, lean_object* v_inst_4128_, lean_object* v_m_4129_, lean_object* v_a_4130_, lean_object* v_fallback_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD(v_00_u03b1_4125_, v_00_u03b2_4126_, v_inst_4127_, v_inst_4128_, v_m_4129_, v_a_4130_, v_fallback_4131_);
lean_dec(v_fallback_4131_);
lean_dec_ref(v_m_4129_);
return v_res_4132_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4134_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__2));
v___x_4135_ = lean_unsigned_to_nat(12u);
v___x_4136_ = lean_unsigned_to_nat(813u);
v___x_4137_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___closed__0));
v___x_4138_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___closed__0));
v___x_4139_ = l_mkPanicMessageWithDecl(v___x_4138_, v___x_4137_, v___x_4136_, v___x_4135_, v___x_4134_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object* v_inst_4140_, lean_object* v_inst_4141_, lean_object* v_inst_4142_, lean_object* v_m_4143_, lean_object* v_a_4144_){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_4140_, v_inst_4141_, v_m_4143_, v_a_4144_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4146_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___closed__1, &l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___closed__1_once, _init_l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___closed__1);
v___x_4147_ = l_panic___redArg(v_inst_4142_, v___x_4146_);
return v___x_4147_;
}
else
{
lean_object* v_val_4148_; 
v_val_4148_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_val_4148_);
lean_dec_ref_known(v___x_4145_, 1);
return v_val_4148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___boxed(lean_object* v_inst_4149_, lean_object* v_inst_4150_, lean_object* v_inst_4151_, lean_object* v_m_4152_, lean_object* v_a_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_4149_, v_inst_4150_, v_inst_4151_, v_m_4152_, v_a_4153_);
lean_dec_ref(v_m_4152_);
lean_dec(v_inst_4151_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21(lean_object* v_00_u03b1_4155_, lean_object* v_00_u03b2_4156_, lean_object* v_inst_4157_, lean_object* v_inst_4158_, lean_object* v_inst_4159_, lean_object* v_m_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v___x_4162_; 
v___x_4162_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_4157_, v_inst_4158_, v_inst_4159_, v_m_4160_, v_a_4161_);
return v___x_4162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___boxed(lean_object* v_00_u03b1_4163_, lean_object* v_00_u03b2_4164_, lean_object* v_inst_4165_, lean_object* v_inst_4166_, lean_object* v_inst_4167_, lean_object* v_m_4168_, lean_object* v_a_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21(v_00_u03b1_4163_, v_00_u03b2_4164_, v_inst_4165_, v_inst_4166_, v_inst_4167_, v_m_4168_, v_a_4169_);
lean_dec_ref(v_m_4168_);
lean_dec(v_inst_4167_);
return v_res_4170_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_RawDef(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Internal_List_Defs(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Index(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Power2_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Power2_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_RawDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Internal_List_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Index(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Power2_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Power2_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_RawDef(uint8_t builtin);
lean_object* initialize_Std_Data_Internal_List_Defs(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Index(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Power2_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Power2_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_RawDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Internal_List_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Index(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Power2_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Power2_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_Internal_Defs(builtin);
}
#ifdef __cplusplus
}
#endif
