// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.OmegaM
// Imports: public import Lean.Meta.AppBuilder public import Lean.Meta.Canonicalizer public import Init.Omega
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_nat_x3f(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_int_x3f(lean_object*);
lean_object* l_Nat_pow___boxed(lean_object*, lean_object*);
lean_object* l_Nat_div___boxed(lean_object*, lean_object*);
lean_object* l_Nat_sub___boxed(lean_object*, lean_object*);
lean_object* l_Nat_mul___boxed(lean_object*, lean_object*);
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_Int_ediv___boxed(lean_object*, lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
lean_object* l_Int_mul___boxed(lean_object*, lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Omega"};
static const lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Coeffs"};
static const lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofList"};
static const lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(200, 12, 56, 206, 160, 32, 217, 148)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(16, 98, 247, 173, 146, 185, 161, 158)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_Tactic_Omega_intCast_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_intCast_x3f(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_ediv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Min"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Max"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "max"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "le_max_left"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(202, 116, 120, 162, 144, 249, 91, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "le_max_right"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 64, 160, 147, 232, 106, 148, 64)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "min"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "min_le_left"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(18, 98, 222, 238, 10, 11, 175, 208)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "min_le_right"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(89, 109, 128, 29, 84, 251, 120, 13)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "emod_ofNat_nonneg"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 141, 7, 147, 89, 24, 200, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(193, 64, 179, 146, 49, 216, 163, 147)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTNat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(141, 27, 201, 217, 48, 203, 85, 203)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pow_pos"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_value),LEAN_SCALAR_PTR_LITERAL(8, 188, 92, 81, 98, 125, 214, 195)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ofNat_pos_of_pos"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 141, 7, 147, 89, 24, 200, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value),LEAN_SCALAR_PTR_LITERAL(40, 203, 156, 230, 39, 171, 106, 183)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "emod_nonneg"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(61, 100, 115, 114, 207, 135, 28, 238)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ne_of_gt"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value),LEAN_SCALAR_PTR_LITERAL(124, 85, 105, 24, 138, 4, 9, 162)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "emod_lt_of_pos"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value),LEAN_SCALAR_PTR_LITERAL(179, 253, 191, 46, 213, 199, 79, 210)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTInt"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value),LEAN_SCALAR_PTR_LITERAL(174, 212, 102, 196, 69, 170, 149, 126)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "pos_pow_of_pos"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 141, 7, 147, 89, 24, 200, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_value),LEAN_SCALAR_PTR_LITERAL(145, 25, 143, 59, 16, 211, 163, 116)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mul_ediv_self_le"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value),LEAN_SCALAR_PTR_LITERAL(252, 253, 214, 154, 97, 254, 157, 214)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "lt_mul_ediv_self_add"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value),LEAN_SCALAR_PTR_LITERAL(94, 156, 157, 133, 195, 57, 68, 244)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "neg_le_natAbs"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 141, 7, 147, 89, 24, 200, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value),LEAN_SCALAR_PTR_LITERAL(217, 253, 117, 167, 254, 111, 180, 184)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "natCast_nonneg"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value),LEAN_SCALAR_PTR_LITERAL(78, 189, 5, 123, 91, 219, 85, 246)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "isLt"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value),LEAN_SCALAR_PTR_LITERAL(196, 26, 231, 251, 226, 55, 19, 117)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value),LEAN_SCALAR_PTR_LITERAL(222, 150, 50, 101, 25, 222, 136, 68)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "le_natAbs"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value),LEAN_SCALAR_PTR_LITERAL(90, 82, 63, 108, 86, 248, 24, 88)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natAbs"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "ofNat_sub_dichotomy"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 141, 7, 147, 89, 24, 200, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89_value),LEAN_SCALAR_PTR_LITERAL(132, 176, 7, 204, 155, 0, 78, 60)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ite_disjunction"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92_value),LEAN_SCALAR_PTR_LITERAL(77, 139, 125, 42, 52, 100, 157, 106)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_lookup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_lookup___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_lookup___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_lookup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 155, 144, 136, 132, 122, 189, 157)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_lookup___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_lookup___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_lookup___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_lookup___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_lookup___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_lookup___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_lookup___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_Omega_lookup___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "New facts: "};
static const lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_lookup___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_lookup___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Omega_lookup___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "New atom: "};
static const lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_lookup___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_lookup___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v_m_3_, lean_object* v_cfg_4_, uint8_t v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_12_ = lean_st_mk_ref(v___x_1_);
v___x_13_ = lean_st_mk_ref(v___x_2_);
v___x_14_ = lean_box(v___y_5_);
lean_inc(v___y_10_);
lean_inc_ref(v___y_9_);
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc(v___x_12_);
lean_inc(v___x_13_);
v___x_15_ = lean_apply_10(v_m_3_, v___x_13_, v___x_12_, v_cfg_4_, v___x_14_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, lean_box(0));
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_25_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_25_ == 0)
{
v___x_18_ = v___x_15_;
v_isShared_19_ = v_isSharedCheck_25_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_a_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_25_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_20_ = lean_st_ref_get(v___x_13_);
lean_dec(v___x_13_);
lean_dec(v___x_20_);
v___x_21_ = lean_st_ref_get(v___x_12_);
lean_dec(v___x_12_);
lean_dec(v___x_21_);
if (v_isShared_19_ == 0)
{
v___x_23_ = v___x_18_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_a_16_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
else
{
lean_dec(v___x_13_);
lean_dec(v___x_12_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed(lean_object* v___x_26_, lean_object* v___x_27_, lean_object* v_m_28_, lean_object* v_cfg_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
uint8_t v___y_4819__boxed_37_; lean_object* v_res_38_; 
v___y_4819__boxed_37_ = lean_unbox(v___y_30_);
v_res_38_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(v___x_26_, v___x_27_, v_m_28_, v_cfg_29_, v___y_4819__boxed_37_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
return v_res_38_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_39_; lean_object* v___x_40_; 
v_cellCount_39_ = lean_unsigned_to_nat(16u);
v___x_40_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_41_; lean_object* v___x_42_; 
v_cellCount_41_ = lean_unsigned_to_nat(16u);
v___x_42_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_43_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1);
v___x_44_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0, &l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v___x_44_);
lean_ctor_set(v___x_46_, 2, v___x_43_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(lean_object* v_m_49_, lean_object* v_cfg_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_56_; lean_object* v___f_57_; uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_56_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2);
v___f_57_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_57_, 0, v___x_56_);
lean_closure_set(v___f_57_, 1, v___x_56_);
lean_closure_set(v___f_57_, 2, v_m_49_);
lean_closure_set(v___f_57_, 3, v_cfg_50_);
v___x_58_ = 3;
v___x_59_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3, &l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3);
v___x_60_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(v___f_57_, v___x_58_, v___x_59_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___boxed(lean_object* v_m_61_, lean_object* v_cfg_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(v_m_61_, v_cfg_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_object* v_00_u03b1_69_, lean_object* v_m_70_, lean_object* v_cfg_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(v_m_70_, v_cfg_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___boxed(lean_object* v_00_u03b1_78_, lean_object* v_m_79_, lean_object* v_cfg_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Elab_Tactic_Omega_OmegaM_run(v_00_u03b1_78_, v_m_79_, v_cfg_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg(lean_object* v_a_87_){
_start:
{
lean_object* v___x_89_; 
lean_inc_ref(v_a_87_);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v_a_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg___boxed(lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Elab_Tactic_Omega_cfg___redArg(v_a_90_);
lean_dec_ref(v_a_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg(lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, uint8_t v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_103_; 
lean_inc_ref(v_a_95_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v_a_95_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___boxed(lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
uint8_t v_a_boxed_114_; lean_object* v_res_115_; 
v_a_boxed_114_ = lean_unbox(v_a_107_);
v_res_115_ = l_Lean_Elab_Tactic_Omega_cfg(v_a_104_, v_a_105_, v_a_106_, v_a_boxed_114_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec(v_a_104_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(lean_object* v_b_116_, lean_object* v_acc_117_, lean_object* v_i_118_){
_start:
{
lean_object* v_keyArray_123_; lean_object* v_valueArray_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_keyArray_123_ = lean_ctor_get(v_b_116_, 1);
v_valueArray_124_ = lean_ctor_get(v_b_116_, 2);
v___x_125_ = lean_array_get_size(v_keyArray_123_);
v___x_126_ = lean_nat_dec_lt(v_i_118_, v___x_125_);
if (v___x_126_ == 0)
{
lean_dec(v_i_118_);
return v_acc_117_;
}
else
{
lean_object* v___x_127_; uint8_t v_isSome_128_; 
v___x_127_ = lean_array_fget_borrowed(v_keyArray_123_, v_i_118_);
v_isSome_128_ = lean_noption_is_some(v___x_127_);
if (v_isSome_128_ == 0)
{
goto v___jp_119_;
}
else
{
lean_object* v___x_129_; uint8_t v_isSome_130_; 
v___x_129_ = lean_array_fget_borrowed(v_valueArray_124_, v_i_118_);
v_isSome_130_ = lean_noption_is_some(v___x_129_);
if (v_isSome_130_ == 0)
{
goto v___jp_119_;
}
else
{
lean_object* v_val_131_; lean_object* v_val_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
lean_inc(v___x_127_);
v_val_131_ = lean_noption_get(v___x_127_);
lean_inc(v___x_129_);
v_val_132_ = lean_noption_get(v___x_129_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_val_131_);
lean_ctor_set(v___x_133_, 1, v_val_132_);
v___x_134_ = lean_array_push(v_acc_117_, v___x_133_);
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = lean_nat_add(v_i_118_, v___x_135_);
lean_dec(v_i_118_);
v_acc_117_ = v___x_134_;
v_i_118_ = v___x_136_;
goto _start;
}
}
}
v___jp_119_:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_add(v_i_118_, v___x_120_);
lean_dec(v_i_118_);
v_i_118_ = v___x_121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___boxed(lean_object* v_b_138_, lean_object* v_acc_139_, lean_object* v_i_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(v_b_138_, v_acc_139_, v_i_140_);
lean_dec_ref(v_b_138_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(lean_object* v_init_142_, lean_object* v_b_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(v_b_143_, v_init_142_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(lean_object* v_init_146_, lean_object* v_b_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(v_init_146_, v_b_147_);
lean_dec_ref(v_b_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2_spec__3___redArg(lean_object* v_hi_149_, lean_object* v_pivot_150_, lean_object* v_as_151_, lean_object* v_i_152_, lean_object* v_k_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = lean_nat_dec_lt(v_k_153_, v_hi_149_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v_k_153_);
v___x_155_ = lean_array_fswap(v_as_151_, v_i_152_, v_hi_149_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v_i_152_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
return v___x_156_;
}
else
{
lean_object* v___x_157_; lean_object* v_snd_158_; lean_object* v_snd_159_; uint8_t v___x_160_; 
v___x_157_ = lean_array_fget_borrowed(v_as_151_, v_k_153_);
v_snd_158_ = lean_ctor_get(v___x_157_, 1);
v_snd_159_ = lean_ctor_get(v_pivot_150_, 1);
v___x_160_ = lean_nat_dec_lt(v_snd_158_, v_snd_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_add(v_k_153_, v___x_161_);
lean_dec(v_k_153_);
v_k_153_ = v___x_162_;
goto _start;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_164_ = lean_array_fswap(v_as_151_, v_i_152_, v_k_153_);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_add(v_i_152_, v___x_165_);
lean_dec(v_i_152_);
v___x_167_ = lean_nat_add(v_k_153_, v___x_165_);
lean_dec(v_k_153_);
v_as_151_ = v___x_164_;
v_i_152_ = v___x_166_;
v_k_153_ = v___x_167_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2_spec__3___redArg___boxed(lean_object* v_hi_169_, lean_object* v_pivot_170_, lean_object* v_as_171_, lean_object* v_i_172_, lean_object* v_k_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2_spec__3___redArg(v_hi_169_, v_pivot_170_, v_as_171_, v_i_172_, v_k_173_);
lean_dec_ref(v_pivot_170_);
lean_dec(v_hi_169_);
return v_res_174_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg___lam__0(lean_object* v_x1_175_, lean_object* v_x2_176_){
_start:
{
lean_object* v_snd_177_; lean_object* v_snd_178_; uint8_t v___x_179_; 
v_snd_177_ = lean_ctor_get(v_x1_175_, 1);
v_snd_178_ = lean_ctor_get(v_x2_176_, 1);
v___x_179_ = lean_nat_dec_lt(v_snd_177_, v_snd_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg___lam__0___boxed(lean_object* v_x1_180_, lean_object* v_x2_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg___lam__0(v_x1_180_, v_x2_181_);
lean_dec_ref(v_x2_181_);
lean_dec_ref(v_x1_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg(lean_object* v_n_184_, lean_object* v_as_185_, lean_object* v_lo_186_, lean_object* v_hi_187_){
_start:
{
lean_object* v___y_189_; uint8_t v___x_199_; 
v___x_199_ = lean_nat_dec_lt(v_lo_186_, v_hi_187_);
if (v___x_199_ == 0)
{
lean_dec(v_lo_186_);
return v_as_185_;
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_mid_202_; lean_object* v___y_204_; lean_object* v___y_210_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_200_ = lean_nat_add(v_lo_186_, v_hi_187_);
v___x_201_ = lean_unsigned_to_nat(1u);
v_mid_202_ = lean_nat_shiftr(v___x_200_, v___x_201_);
lean_dec(v___x_200_);
v___x_215_ = lean_array_fget_borrowed(v_as_185_, v_mid_202_);
v___x_216_ = lean_array_fget_borrowed(v_as_185_, v_lo_186_);
v___x_217_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg___lam__0(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
v___y_210_ = v_as_185_;
goto v___jp_209_;
}
else
{
lean_object* v___x_218_; 
v___x_218_ = lean_array_fswap(v_as_185_, v_lo_186_, v_mid_202_);
v___y_210_ = v___x_218_;
goto v___jp_209_;
}
v___jp_203_:
{
lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_205_ = lean_array_fget_borrowed(v___y_204_, v_mid_202_);
v___x_206_ = lean_array_fget_borrowed(v___y_204_, v_hi_187_);
v___x_207_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg___lam__0(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_dec(v_mid_202_);
v___y_189_ = v___y_204_;
goto v___jp_188_;
}
else
{
lean_object* v___x_208_; 
v___x_208_ = lean_array_fswap(v___y_204_, v_mid_202_, v_hi_187_);
lean_dec(v_mid_202_);
v___y_189_ = v___x_208_;
goto v___jp_188_;
}
}
v___jp_209_:
{
lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_211_ = lean_array_fget_borrowed(v___y_210_, v_hi_187_);
v___x_212_ = lean_array_fget_borrowed(v___y_210_, v_lo_186_);
v___x_213_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg___lam__0(v___x_211_, v___x_212_);
if (v___x_213_ == 0)
{
v___y_204_ = v___y_210_;
goto v___jp_203_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = lean_array_fswap(v___y_210_, v_lo_186_, v_hi_187_);
v___y_204_ = v___x_214_;
goto v___jp_203_;
}
}
}
v___jp_188_:
{
lean_object* v_pivot_190_; lean_object* v___x_191_; lean_object* v_fst_192_; lean_object* v_snd_193_; uint8_t v___x_194_; 
v_pivot_190_ = lean_array_fget(v___y_189_, v_hi_187_);
lean_inc_n(v_lo_186_, 2);
v___x_191_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2_spec__3___redArg(v_hi_187_, v_pivot_190_, v___y_189_, v_lo_186_, v_lo_186_);
lean_dec(v_pivot_190_);
v_fst_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_fst_192_);
v_snd_193_ = lean_ctor_get(v___x_191_, 1);
lean_inc(v_snd_193_);
lean_dec_ref(v___x_191_);
v___x_194_ = lean_nat_dec_le(v_hi_187_, v_fst_192_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg(v_n_184_, v_snd_193_, v_lo_186_, v_fst_192_);
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_add(v_fst_192_, v___x_196_);
lean_dec(v_fst_192_);
v_as_185_ = v___x_195_;
v_lo_186_ = v___x_197_;
goto _start;
}
else
{
lean_dec(v_fst_192_);
lean_dec(v_lo_186_);
return v_snd_193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg___boxed(lean_object* v_n_219_, lean_object* v_as_220_, lean_object* v_lo_221_, lean_object* v_hi_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg(v_n_219_, v_as_220_, v_lo_221_, v_hi_222_);
lean_dec(v_hi_222_);
lean_dec(v_n_219_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(size_t v_sz_224_, size_t v_i_225_, lean_object* v_bs_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = lean_usize_dec_lt(v_i_225_, v_sz_224_);
if (v___x_227_ == 0)
{
return v_bs_226_;
}
else
{
lean_object* v_v_228_; lean_object* v_fst_229_; lean_object* v___x_230_; lean_object* v_bs_x27_231_; size_t v___x_232_; size_t v___x_233_; lean_object* v___x_234_; 
v_v_228_ = lean_array_uget_borrowed(v_bs_226_, v_i_225_);
v_fst_229_ = lean_ctor_get(v_v_228_, 0);
lean_inc(v_fst_229_);
v___x_230_ = lean_unsigned_to_nat(0u);
v_bs_x27_231_ = lean_array_uset(v_bs_226_, v_i_225_, v___x_230_);
v___x_232_ = ((size_t)1ULL);
v___x_233_ = lean_usize_add(v_i_225_, v___x_232_);
v___x_234_ = lean_array_uset(v_bs_x27_231_, v_i_225_, v_fst_229_);
v_i_225_ = v___x_233_;
v_bs_226_ = v___x_234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(lean_object* v_sz_236_, lean_object* v_i_237_, lean_object* v_bs_238_){
_start:
{
size_t v_sz_boxed_239_; size_t v_i_boxed_240_; lean_object* v_res_241_; 
v_sz_boxed_239_ = lean_unbox_usize(v_sz_236_);
lean_dec(v_sz_236_);
v_i_boxed_240_ = lean_unbox_usize(v_i_237_);
lean_dec(v_i_237_);
v_res_241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_boxed_239_, v_i_boxed_240_, v_bs_238_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg(lean_object* v_a_242_){
_start:
{
lean_object* v___x_244_; lean_object* v___y_246_; lean_object* v_size_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_244_ = lean_st_ref_get(v_a_242_);
v_size_251_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_size_251_);
v___x_252_ = lean_mk_empty_array_with_capacity(v_size_251_);
lean_dec(v_size_251_);
v___x_253_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(v___x_252_, v___x_244_);
lean_dec(v___x_244_);
v___x_254_ = lean_array_get_size(v___x_253_);
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_nat_dec_eq(v___x_254_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___y_264_; uint8_t v___x_266_; 
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_sub(v___x_254_, v___x_261_);
v___x_266_ = lean_nat_dec_le(v___x_259_, v___x_262_);
if (v___x_266_ == 0)
{
lean_inc(v___x_262_);
v___y_264_ = v___x_262_;
goto v___jp_263_;
}
else
{
v___y_264_ = v___x_259_;
goto v___jp_263_;
}
v___jp_263_:
{
uint8_t v___x_265_; 
v___x_265_ = lean_nat_dec_le(v___y_264_, v___x_262_);
if (v___x_265_ == 0)
{
lean_dec(v___x_262_);
lean_inc(v___y_264_);
v___y_256_ = v___y_264_;
v___y_257_ = v___y_264_;
goto v___jp_255_;
}
else
{
v___y_256_ = v___y_264_;
v___y_257_ = v___x_262_;
goto v___jp_255_;
}
}
}
else
{
v___y_246_ = v___x_253_;
goto v___jp_245_;
}
v___jp_245_:
{
size_t v_sz_247_; size_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_sz_247_ = lean_array_size(v___y_246_);
v___x_248_ = ((size_t)0ULL);
v___x_249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_247_, v___x_248_, v___y_246_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
v___jp_255_:
{
lean_object* v___x_258_; 
v___x_258_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg(v___x_254_, v___x_253_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
v___y_246_ = v___x_258_;
goto v___jp_245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg___boxed(lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_267_);
lean_dec(v_a_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, uint8_t v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_271_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
uint8_t v_a_boxed_291_; lean_object* v_res_292_; 
v_a_boxed_291_ = lean_unbox(v_a_284_);
v_res_292_ = l_Lean_Elab_Tactic_Omega_atoms(v_a_281_, v_a_282_, v_a_283_, v_a_boxed_291_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec(v_a_281_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(lean_object* v_n_293_, lean_object* v_as_294_, lean_object* v_lo_295_, lean_object* v_hi_296_, lean_object* v_w_297_, lean_object* v_hlo_298_, lean_object* v_hhi_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___redArg(v_n_293_, v_as_294_, v_lo_295_, v_hi_296_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___boxed(lean_object* v_n_301_, lean_object* v_as_302_, lean_object* v_lo_303_, lean_object* v_hi_304_, lean_object* v_w_305_, lean_object* v_hlo_306_, lean_object* v_hhi_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(v_n_301_, v_as_302_, v_lo_303_, v_hi_304_, v_w_305_, v_hlo_306_, v_hhi_307_);
lean_dec(v_hi_304_);
lean_dec(v_n_301_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2_spec__3(lean_object* v_n_309_, lean_object* v_lo_310_, lean_object* v_hi_311_, lean_object* v_hhi_312_, lean_object* v_pivot_313_, lean_object* v_as_314_, lean_object* v_i_315_, lean_object* v_k_316_, lean_object* v_ilo_317_, lean_object* v_ik_318_, lean_object* v_w_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2_spec__3___redArg(v_hi_311_, v_pivot_313_, v_as_314_, v_i_315_, v_k_316_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2_spec__3___boxed(lean_object* v_n_321_, lean_object* v_lo_322_, lean_object* v_hi_323_, lean_object* v_hhi_324_, lean_object* v_pivot_325_, lean_object* v_as_326_, lean_object* v_i_327_, lean_object* v_k_328_, lean_object* v_ilo_329_, lean_object* v_ik_330_, lean_object* v_w_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__2_spec__3(v_n_321_, v_lo_322_, v_hi_323_, v_hhi_324_, v_pivot_325_, v_as_326_, v_i_327_, v_k_328_, v_ilo_329_, v_ik_330_, v_w_331_);
lean_dec_ref(v_pivot_325_);
lean_dec(v_hi_323_);
lean_dec(v_lo_322_);
lean_dec(v_n_321_);
return v_res_332_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_box(0);
v___x_337_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1));
v___x_338_ = l_Lean_Expr_const___override(v___x_337_, v___x_336_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg(lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_345_; lean_object* v_a_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_345_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_339_);
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref(v___x_345_);
v___x_347_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_348_ = lean_array_to_list(v_a_346_);
v___x_349_ = l_Lean_Meta_mkListLit(v___x_347_, v___x_348_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___boxed(lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList(lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, uint8_t v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(v_a_358_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___boxed(lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
uint8_t v_a_boxed_378_; lean_object* v_res_379_; 
v_a_boxed_378_ = lean_unbox(v_a_371_);
v_res_379_ = l_Lean_Elab_Tactic_Omega_atomsList(v_a_368_, v_a_369_, v_a_370_, v_a_boxed_378_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec(v_a_368_);
return v_res_379_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_box(0);
v___x_390_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4));
v___x_391_ = l_Lean_Expr_const___override(v___x_390_, v___x_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_408_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_408_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_403_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5, &l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5);
v___x_404_ = l_Lean_Expr_app___override(v___x_403_, v_a_399_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_404_);
v___x_406_ = v___x_401_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
else
{
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___boxed(lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs(lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, uint8_t v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_417_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
uint8_t v_a_boxed_437_; lean_object* v_res_438_; 
v_a_boxed_437_ = lean_unbox(v_a_430_);
v_res_438_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs(v_a_427_, v_a_428_, v_a_429_, v_a_boxed_437_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec(v_a_427_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg(lean_object* v_t_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, uint8_t v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_450_ = lean_st_ref_get(v_a_441_);
v___x_451_ = lean_st_ref_get(v_a_440_);
v___x_452_ = lean_box(v_a_443_);
lean_inc(v_a_448_);
lean_inc_ref(v_a_447_);
lean_inc(v_a_446_);
lean_inc_ref(v_a_445_);
lean_inc(v_a_444_);
lean_inc_ref(v_a_442_);
lean_inc(v_a_441_);
lean_inc(v_a_440_);
v___x_453_ = lean_apply_10(v_t_439_, v_a_440_, v_a_441_, v_a_442_, v___x_452_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, lean_box(0));
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_472_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_472_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_472_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_472_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_snd_458_; uint8_t v___x_459_; 
v_snd_458_ = lean_ctor_get(v_a_454_, 1);
v___x_459_ = lean_unbox(v_snd_458_);
if (v___x_459_ == 0)
{
lean_object* v_fst_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v_fst_460_ = lean_ctor_get(v_a_454_, 0);
lean_inc(v_fst_460_);
lean_dec(v_a_454_);
v___x_461_ = lean_st_ref_take(v_a_441_);
lean_dec(v___x_461_);
v___x_462_ = lean_st_ref_put(v_a_441_, v___x_450_);
v___x_463_ = lean_st_ref_take(v_a_440_);
lean_dec(v___x_463_);
v___x_464_ = lean_st_ref_put(v_a_440_, v___x_451_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v_fst_460_);
v___x_466_ = v___x_456_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_fst_460_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
else
{
lean_object* v_fst_468_; lean_object* v___x_470_; 
lean_dec(v___x_451_);
lean_dec(v___x_450_);
v_fst_468_ = lean_ctor_get(v_a_454_, 0);
lean_inc(v_fst_468_);
lean_dec(v_a_454_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v_fst_468_);
v___x_470_ = v___x_456_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_fst_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v___x_451_);
lean_dec(v___x_450_);
v_a_473_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_453_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_453_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg___boxed(lean_object* v_t_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
uint8_t v_a_boxed_492_; lean_object* v_res_493_; 
v_a_boxed_492_ = lean_unbox(v_a_485_);
v_res_493_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(v_t_481_, v_a_482_, v_a_483_, v_a_484_, v_a_boxed_492_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec(v_a_482_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen(lean_object* v_00_u03b1_494_, lean_object* v_t_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, uint8_t v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(v_t_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___boxed(lean_object* v_00_u03b1_507_, lean_object* v_t_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
uint8_t v_a_boxed_519_; lean_object* v_res_520_; 
v_a_boxed_519_ = lean_unbox(v_a_512_);
v_res_520_ = l_Lean_Elab_Tactic_Omega_commitWhen(v_00_u03b1_507_, v_t_508_, v_a_509_, v_a_510_, v_a_511_, v_a_boxed_519_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec(v_a_509_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(lean_object* v_t_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, uint8_t v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_box(v___y_525_);
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
lean_inc(v___y_528_);
lean_inc_ref(v___y_527_);
lean_inc(v___y_526_);
lean_inc_ref(v___y_524_);
lean_inc(v___y_523_);
lean_inc(v___y_522_);
v___x_533_ = lean_apply_10(v_t_521_, v___y_522_, v___y_523_, v___y_524_, v___x_532_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, lean_box(0));
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_544_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_544_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_544_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_544_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_538_ = 0;
v___x_539_ = lean_box(v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v_a_534_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_540_);
v___x_542_ = v___x_536_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_a_545_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_533_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_533_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed(lean_object* v_t_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
uint8_t v___y_672__boxed_564_; lean_object* v_res_565_; 
v___y_672__boxed_564_ = lean_unbox(v___y_557_);
v_res_565_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(v_t_553_, v___y_554_, v___y_555_, v___y_556_, v___y_672__boxed_564_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec(v___y_554_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(lean_object* v_t_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, uint8_t v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___f_577_; lean_object* v___x_578_; 
v___f_577_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_577_, 0, v_t_566_);
v___x_578_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(v___f_577_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___boxed(lean_object* v_t_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
uint8_t v_a_boxed_590_; lean_object* v_res_591_; 
v_a_boxed_590_ = lean_unbox(v_a_583_);
v_res_591_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(v_t_579_, v_a_580_, v_a_581_, v_a_582_, v_a_boxed_590_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec(v_a_580_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_object* v_00_u03b1_592_, lean_object* v_t_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, uint8_t v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(v_t_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(lean_object* v_00_u03b1_605_, lean_object* v_t_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
uint8_t v_a_boxed_617_; lean_object* v_res_618_; 
v_a_boxed_617_ = lean_unbox(v_a_610_);
v_res_618_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState(v_00_u03b1_605_, v_t_606_, v_a_607_, v_a_608_, v_a_609_, v_a_boxed_617_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec(v_a_607_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f(lean_object* v_n_621_){
_start:
{
lean_object* v___x_622_; lean_object* v_fst_623_; 
lean_inc_ref(v_n_621_);
v___x_622_ = l_Lean_Expr_getAppFnArgs(v_n_621_);
v_fst_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_fst_623_);
if (lean_obj_tag(v_fst_623_) == 1)
{
lean_object* v_pre_624_; 
v_pre_624_ = lean_ctor_get(v_fst_623_, 0);
lean_inc(v_pre_624_);
if (lean_obj_tag(v_pre_624_) == 1)
{
lean_object* v_pre_625_; 
v_pre_625_ = lean_ctor_get(v_pre_624_, 0);
if (lean_obj_tag(v_pre_625_) == 0)
{
lean_object* v_snd_626_; lean_object* v_str_627_; lean_object* v_str_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_snd_626_ = lean_ctor_get(v___x_622_, 1);
lean_inc(v_snd_626_);
lean_dec_ref(v___x_622_);
v_str_627_ = lean_ctor_get(v_fst_623_, 1);
lean_inc_ref(v_str_627_);
lean_dec_ref_known(v_fst_623_, 2);
v_str_628_ = lean_ctor_get(v_pre_624_, 1);
lean_inc_ref(v_str_628_);
lean_dec_ref_known(v_pre_624_, 2);
v___x_629_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_630_ = lean_string_dec_eq(v_str_628_, v___x_629_);
lean_dec_ref(v_str_628_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
lean_dec_ref(v_str_627_);
lean_dec(v_snd_626_);
v___x_631_ = l_Lean_Expr_nat_x3f(v_n_621_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_633_ = lean_string_dec_eq(v_str_627_, v___x_632_);
lean_dec_ref(v_str_627_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
lean_dec(v_snd_626_);
v___x_634_ = l_Lean_Expr_nat_x3f(v_n_621_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_635_ = lean_array_get_size(v_snd_626_);
v___x_636_ = lean_unsigned_to_nat(3u);
v___x_637_ = lean_nat_dec_eq(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_dec(v_snd_626_);
v___x_638_ = l_Lean_Expr_nat_x3f(v_n_621_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec_ref(v_n_621_);
v___x_639_ = lean_unsigned_to_nat(2u);
v___x_640_ = lean_array_fget(v_snd_626_, v___x_639_);
lean_dec(v_snd_626_);
v___x_641_ = l_Lean_Expr_nat_x3f(v___x_640_);
return v___x_641_;
}
}
}
}
else
{
lean_object* v___x_642_; 
lean_dec_ref_known(v_pre_624_, 2);
lean_dec_ref_known(v_fst_623_, 2);
lean_dec_ref(v___x_622_);
v___x_642_ = l_Lean_Expr_nat_x3f(v_n_621_);
return v___x_642_;
}
}
else
{
lean_object* v___x_643_; 
lean_dec(v_pre_624_);
lean_dec_ref_known(v_fst_623_, 2);
lean_dec_ref(v___x_622_);
v___x_643_ = l_Lean_Expr_nat_x3f(v_n_621_);
return v___x_643_;
}
}
else
{
lean_object* v___x_644_; 
lean_dec(v_fst_623_);
lean_dec_ref(v___x_622_);
v___x_644_ = l_Lean_Expr_nat_x3f(v_n_621_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_Tactic_Omega_intCast_x3f_spec__0(lean_object* v_a_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = lean_nat_to_int(v_a_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_intCast_x3f(lean_object* v_n_647_){
_start:
{
lean_object* v___x_648_; lean_object* v_fst_649_; 
lean_inc_ref(v_n_647_);
v___x_648_ = l_Lean_Expr_getAppFnArgs(v_n_647_);
v_fst_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_fst_649_);
if (lean_obj_tag(v_fst_649_) == 1)
{
lean_object* v_pre_650_; 
v_pre_650_ = lean_ctor_get(v_fst_649_, 0);
lean_inc(v_pre_650_);
if (lean_obj_tag(v_pre_650_) == 1)
{
lean_object* v_pre_651_; 
v_pre_651_ = lean_ctor_get(v_pre_650_, 0);
if (lean_obj_tag(v_pre_651_) == 0)
{
lean_object* v_snd_652_; lean_object* v_str_653_; lean_object* v_str_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_snd_652_ = lean_ctor_get(v___x_648_, 1);
lean_inc(v_snd_652_);
lean_dec_ref(v___x_648_);
v_str_653_ = lean_ctor_get(v_fst_649_, 1);
lean_inc_ref(v_str_653_);
lean_dec_ref_known(v_fst_649_, 2);
v_str_654_ = lean_ctor_get(v_pre_650_, 1);
lean_inc_ref(v_str_654_);
lean_dec_ref_known(v_pre_650_, 2);
v___x_655_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_656_ = lean_string_dec_eq(v_str_654_, v___x_655_);
lean_dec_ref(v_str_654_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
lean_dec_ref(v_str_653_);
lean_dec(v_snd_652_);
v___x_657_ = l_Lean_Expr_int_x3f(v_n_647_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_659_ = lean_string_dec_eq(v_str_653_, v___x_658_);
lean_dec_ref(v_str_653_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec(v_snd_652_);
v___x_660_ = l_Lean_Expr_int_x3f(v_n_647_);
return v___x_660_;
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_661_ = lean_array_get_size(v_snd_652_);
v___x_662_ = lean_unsigned_to_nat(3u);
v___x_663_ = lean_nat_dec_eq(v___x_661_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_dec(v_snd_652_);
v___x_664_ = l_Lean_Expr_int_x3f(v_n_647_);
return v___x_664_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec_ref(v_n_647_);
v___x_665_ = lean_unsigned_to_nat(2u);
v___x_666_ = lean_array_fget(v_snd_652_, v___x_665_);
lean_dec(v_snd_652_);
v___x_667_ = l_Lean_Expr_nat_x3f(v___x_666_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v___x_668_; 
v___x_668_ = lean_box(0);
return v___x_668_;
}
else
{
lean_object* v_val_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
v_val_669_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_677_ == 0)
{
v___x_671_ = v___x_667_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_val_669_);
lean_dec(v___x_667_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_nat_to_int(v_val_669_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_678_; 
lean_dec_ref_known(v_pre_650_, 2);
lean_dec_ref_known(v_fst_649_, 2);
lean_dec_ref(v___x_648_);
v___x_678_ = l_Lean_Expr_int_x3f(v_n_647_);
return v___x_678_;
}
}
else
{
lean_object* v___x_679_; 
lean_dec_ref_known(v_fst_649_, 2);
lean_dec(v_pre_650_);
lean_dec_ref(v___x_648_);
v___x_679_ = l_Lean_Expr_int_x3f(v_n_647_);
return v___x_679_;
}
}
else
{
lean_object* v___x_680_; 
lean_dec(v_fst_649_);
lean_dec_ref(v___x_648_);
v___x_680_ = l_Lean_Expr_int_x3f(v_n_647_);
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f(lean_object* v_e_696_){
_start:
{
lean_object* v___x_697_; lean_object* v_fst_698_; 
lean_inc_ref(v_e_696_);
v___x_697_ = l_Lean_Expr_getAppFnArgs(v_e_696_);
v_fst_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_fst_698_);
if (lean_obj_tag(v_fst_698_) == 1)
{
lean_object* v_pre_699_; 
v_pre_699_ = lean_ctor_get(v_fst_698_, 0);
lean_inc(v_pre_699_);
if (lean_obj_tag(v_pre_699_) == 1)
{
lean_object* v_pre_700_; 
v_pre_700_ = lean_ctor_get(v_pre_699_, 0);
if (lean_obj_tag(v_pre_700_) == 0)
{
lean_object* v_snd_701_; lean_object* v_str_702_; lean_object* v_str_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_snd_701_ = lean_ctor_get(v___x_697_, 1);
lean_inc(v_snd_701_);
lean_dec_ref(v___x_697_);
v_str_702_ = lean_ctor_get(v_fst_698_, 1);
lean_inc_ref(v_str_702_);
lean_dec_ref_known(v_fst_698_, 2);
v_str_703_ = lean_ctor_get(v_pre_699_, 1);
lean_inc_ref(v_str_703_);
lean_dec_ref_known(v_pre_699_, 2);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_705_ = lean_string_dec_eq(v_str_703_, v___x_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0));
v___x_707_ = lean_string_dec_eq(v_str_703_, v___x_706_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_708_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1));
v___x_709_ = lean_string_dec_eq(v_str_703_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_710_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2));
v___x_711_ = lean_string_dec_eq(v_str_703_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3));
v___x_713_ = lean_string_dec_eq(v_str_703_, v___x_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4));
v___x_715_ = lean_string_dec_eq(v_str_703_, v___x_714_);
lean_dec_ref(v_str_703_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec_ref(v_str_702_);
lean_dec(v_snd_701_);
v___x_716_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_718_ = lean_string_dec_eq(v_str_702_, v___x_717_);
lean_dec_ref(v_str_702_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_dec(v_snd_701_);
v___x_719_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_720_ = lean_array_get_size(v_snd_701_);
v___x_721_ = lean_unsigned_to_nat(6u);
v___x_722_ = lean_nat_dec_eq(v___x_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_dec(v_snd_701_);
v___x_723_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_723_;
}
else
{
lean_object* v___f_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec_ref(v_e_696_);
v___f_724_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6));
v___x_725_ = lean_unsigned_to_nat(4u);
v___x_726_ = lean_array_fget(v_snd_701_, v___x_725_);
v___x_727_ = lean_unsigned_to_nat(5u);
v___x_728_ = lean_array_fget(v_snd_701_, v___x_727_);
lean_dec(v_snd_701_);
v___x_729_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_724_, v___x_726_, v___x_728_);
return v___x_729_;
}
}
}
}
else
{
lean_object* v___x_730_; uint8_t v___x_731_; 
lean_dec_ref(v_str_703_);
v___x_730_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7));
v___x_731_ = lean_string_dec_eq(v_str_702_, v___x_730_);
lean_dec_ref(v_str_702_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
lean_dec(v_snd_701_);
v___x_732_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_732_;
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_733_ = lean_array_get_size(v_snd_701_);
v___x_734_ = lean_unsigned_to_nat(6u);
v___x_735_ = lean_nat_dec_eq(v___x_733_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
lean_dec(v_snd_701_);
v___x_736_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_736_;
}
else
{
lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec_ref(v_e_696_);
v___f_737_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8));
v___x_738_ = lean_unsigned_to_nat(4u);
v___x_739_ = lean_array_fget(v_snd_701_, v___x_738_);
v___x_740_ = lean_unsigned_to_nat(5u);
v___x_741_ = lean_array_fget(v_snd_701_, v___x_740_);
lean_dec(v_snd_701_);
v___x_742_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_737_, v___x_739_, v___x_741_);
return v___x_742_;
}
}
}
}
else
{
lean_object* v___x_743_; uint8_t v___x_744_; 
lean_dec_ref(v_str_703_);
v___x_743_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9));
v___x_744_ = lean_string_dec_eq(v_str_702_, v___x_743_);
lean_dec_ref(v_str_702_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
lean_dec(v_snd_701_);
v___x_745_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_745_;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_746_ = lean_array_get_size(v_snd_701_);
v___x_747_ = lean_unsigned_to_nat(6u);
v___x_748_ = lean_nat_dec_eq(v___x_746_, v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
lean_dec(v_snd_701_);
v___x_749_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_749_;
}
else
{
lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec_ref(v_e_696_);
v___f_750_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10));
v___x_751_ = lean_unsigned_to_nat(4u);
v___x_752_ = lean_array_fget(v_snd_701_, v___x_751_);
v___x_753_ = lean_unsigned_to_nat(5u);
v___x_754_ = lean_array_fget(v_snd_701_, v___x_753_);
lean_dec(v_snd_701_);
v___x_755_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_750_, v___x_752_, v___x_754_);
return v___x_755_;
}
}
}
}
else
{
lean_object* v___x_756_; uint8_t v___x_757_; 
lean_dec_ref(v_str_703_);
v___x_756_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11));
v___x_757_ = lean_string_dec_eq(v_str_702_, v___x_756_);
lean_dec_ref(v_str_702_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_dec(v_snd_701_);
v___x_758_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_758_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_759_ = lean_array_get_size(v_snd_701_);
v___x_760_ = lean_unsigned_to_nat(6u);
v___x_761_ = lean_nat_dec_eq(v___x_759_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; 
lean_dec(v_snd_701_);
v___x_762_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_762_;
}
else
{
lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec_ref(v_e_696_);
v___f_763_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12));
v___x_764_ = lean_unsigned_to_nat(4u);
v___x_765_ = lean_array_fget(v_snd_701_, v___x_764_);
v___x_766_ = lean_unsigned_to_nat(5u);
v___x_767_ = lean_array_fget(v_snd_701_, v___x_766_);
lean_dec(v_snd_701_);
v___x_768_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_763_, v___x_765_, v___x_767_);
return v___x_768_;
}
}
}
}
else
{
lean_object* v___x_769_; uint8_t v___x_770_; 
lean_dec_ref(v_str_703_);
v___x_769_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13));
v___x_770_ = lean_string_dec_eq(v_str_702_, v___x_769_);
lean_dec_ref(v_str_702_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
lean_dec(v_snd_701_);
v___x_771_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_771_;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_772_ = lean_array_get_size(v_snd_701_);
v___x_773_ = lean_unsigned_to_nat(6u);
v___x_774_ = lean_nat_dec_eq(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_dec(v_snd_701_);
v___x_775_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_775_;
}
else
{
lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref(v_e_696_);
v___f_776_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14));
v___x_777_ = lean_unsigned_to_nat(4u);
v___x_778_ = lean_array_fget(v_snd_701_, v___x_777_);
v___x_779_ = lean_unsigned_to_nat(5u);
v___x_780_ = lean_array_fget(v_snd_701_, v___x_779_);
lean_dec(v_snd_701_);
v___x_781_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_776_, v___x_778_, v___x_780_);
return v___x_781_;
}
}
}
}
else
{
lean_object* v___x_782_; uint8_t v___x_783_; 
lean_dec_ref(v_str_703_);
v___x_782_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_783_ = lean_string_dec_eq(v_str_702_, v___x_782_);
lean_dec_ref(v_str_702_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; 
lean_dec(v_snd_701_);
v___x_784_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_785_ = lean_array_get_size(v_snd_701_);
v___x_786_ = lean_unsigned_to_nat(3u);
v___x_787_ = lean_nat_dec_eq(v___x_785_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
lean_dec(v_snd_701_);
v___x_788_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_788_;
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec_ref(v_e_696_);
v___x_789_ = lean_unsigned_to_nat(2u);
v___x_790_ = lean_array_fget(v_snd_701_, v___x_789_);
lean_dec(v_snd_701_);
v_e_696_ = v___x_790_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_792_; 
lean_dec_ref_known(v_pre_699_, 2);
lean_dec_ref_known(v_fst_698_, 2);
lean_dec_ref(v___x_697_);
v___x_792_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_792_;
}
}
else
{
lean_object* v___x_793_; 
lean_dec(v_pre_699_);
lean_dec_ref_known(v_fst_698_, 2);
lean_dec_ref(v___x_697_);
v___x_793_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_793_;
}
}
else
{
lean_object* v___x_794_; 
lean_dec(v_fst_698_);
lean_dec_ref(v___x_697_);
v___x_794_ = l_Lean_Expr_nat_x3f(v_e_696_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(lean_object* v_f_795_, lean_object* v_x_796_, lean_object* v_y_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_x_796_);
if (lean_obj_tag(v___x_798_) == 1)
{
lean_object* v_val_799_; lean_object* v___x_800_; 
v_val_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v___x_798_, 1);
v___x_800_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_y_797_);
if (lean_obj_tag(v___x_800_) == 1)
{
lean_object* v_val_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_809_; 
v_val_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_809_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_val_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_805_ = lean_apply_2(v_f_795_, v_val_799_, v_val_801_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_805_);
v___x_807_ = v___x_803_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
else
{
lean_object* v___x_810_; 
lean_dec(v___x_800_);
lean_dec(v_val_799_);
lean_dec_ref(v_f_795_);
v___x_810_ = lean_box(0);
return v___x_810_;
}
}
else
{
lean_object* v___x_811_; 
lean_dec(v___x_798_);
lean_dec_ref(v_y_797_);
lean_dec_ref(v_f_795_);
v___x_811_ = lean_box(0);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f(lean_object* v_e_816_){
_start:
{
lean_object* v___x_817_; lean_object* v_fst_818_; 
lean_inc_ref(v_e_816_);
v___x_817_ = l_Lean_Expr_getAppFnArgs(v_e_816_);
v_fst_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_fst_818_);
if (lean_obj_tag(v_fst_818_) == 1)
{
lean_object* v_pre_819_; 
v_pre_819_ = lean_ctor_get(v_fst_818_, 0);
lean_inc(v_pre_819_);
if (lean_obj_tag(v_pre_819_) == 1)
{
lean_object* v_pre_820_; 
v_pre_820_ = lean_ctor_get(v_pre_819_, 0);
if (lean_obj_tag(v_pre_820_) == 0)
{
lean_object* v_snd_821_; lean_object* v_str_822_; lean_object* v_str_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_snd_821_ = lean_ctor_get(v___x_817_, 1);
lean_inc(v_snd_821_);
lean_dec_ref(v___x_817_);
v_str_822_ = lean_ctor_get(v_fst_818_, 1);
lean_inc_ref(v_str_822_);
lean_dec_ref_known(v_fst_818_, 2);
v_str_823_ = lean_ctor_get(v_pre_819_, 1);
lean_inc_ref(v_str_823_);
lean_dec_ref_known(v_pre_819_, 2);
v___x_824_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_825_ = lean_string_dec_eq(v_str_823_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0));
v___x_827_ = lean_string_dec_eq(v_str_823_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1));
v___x_829_ = lean_string_dec_eq(v_str_823_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2));
v___x_831_ = lean_string_dec_eq(v_str_823_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3));
v___x_833_ = lean_string_dec_eq(v_str_823_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4));
v___x_835_ = lean_string_dec_eq(v_str_823_, v___x_834_);
lean_dec_ref(v_str_823_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_dec_ref(v_str_822_);
lean_dec(v_snd_821_);
v___x_836_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_837_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_838_ = lean_string_dec_eq(v_str_822_, v___x_837_);
lean_dec_ref(v_str_822_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; 
lean_dec(v_snd_821_);
v___x_839_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_839_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_840_ = lean_array_get_size(v_snd_821_);
v___x_841_ = lean_unsigned_to_nat(6u);
v___x_842_ = lean_nat_dec_eq(v___x_840_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
lean_dec(v_snd_821_);
v___x_843_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec_ref(v_e_816_);
v___x_844_ = lean_unsigned_to_nat(4u);
v___x_845_ = lean_array_fget_borrowed(v_snd_821_, v___x_844_);
lean_inc(v___x_845_);
v___x_846_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v___x_845_);
if (lean_obj_tag(v___x_846_) == 1)
{
lean_object* v_val_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_val_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = lean_unsigned_to_nat(5u);
v___x_849_ = lean_array_fget(v_snd_821_, v___x_848_);
lean_dec(v_snd_821_);
v___x_850_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_849_);
if (lean_obj_tag(v___x_850_) == 1)
{
lean_object* v_val_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
v_val_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_859_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_val_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = l_Int_pow(v_val_847_, v_val_851_);
lean_dec(v_val_851_);
lean_dec(v_val_847_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
else
{
lean_object* v___x_860_; 
lean_dec(v___x_850_);
lean_dec(v_val_847_);
v___x_860_ = lean_box(0);
return v___x_860_;
}
}
else
{
lean_object* v___x_861_; 
lean_dec(v___x_846_);
lean_dec(v_snd_821_);
v___x_861_ = lean_box(0);
return v___x_861_;
}
}
}
}
}
else
{
lean_object* v___x_862_; uint8_t v___x_863_; 
lean_dec_ref(v_str_823_);
v___x_862_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7));
v___x_863_ = lean_string_dec_eq(v_str_822_, v___x_862_);
lean_dec_ref(v_str_822_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; 
lean_dec(v_snd_821_);
v___x_864_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_864_;
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_865_ = lean_array_get_size(v_snd_821_);
v___x_866_ = lean_unsigned_to_nat(6u);
v___x_867_ = lean_nat_dec_eq(v___x_865_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
lean_dec(v_snd_821_);
v___x_868_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_868_;
}
else
{
lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec_ref(v_e_816_);
v___f_869_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0));
v___x_870_ = lean_unsigned_to_nat(4u);
v___x_871_ = lean_array_fget(v_snd_821_, v___x_870_);
v___x_872_ = lean_unsigned_to_nat(5u);
v___x_873_ = lean_array_fget(v_snd_821_, v___x_872_);
lean_dec(v_snd_821_);
v___x_874_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_869_, v___x_871_, v___x_873_);
return v___x_874_;
}
}
}
}
else
{
lean_object* v___x_875_; uint8_t v___x_876_; 
lean_dec_ref(v_str_823_);
v___x_875_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9));
v___x_876_ = lean_string_dec_eq(v_str_822_, v___x_875_);
lean_dec_ref(v_str_822_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; 
lean_dec(v_snd_821_);
v___x_877_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_877_;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_878_ = lean_array_get_size(v_snd_821_);
v___x_879_ = lean_unsigned_to_nat(6u);
v___x_880_ = lean_nat_dec_eq(v___x_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
lean_dec(v_snd_821_);
v___x_881_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_881_;
}
else
{
lean_object* v___f_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec_ref(v_e_816_);
v___f_882_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1));
v___x_883_ = lean_unsigned_to_nat(4u);
v___x_884_ = lean_array_fget(v_snd_821_, v___x_883_);
v___x_885_ = lean_unsigned_to_nat(5u);
v___x_886_ = lean_array_fget(v_snd_821_, v___x_885_);
lean_dec(v_snd_821_);
v___x_887_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_882_, v___x_884_, v___x_886_);
return v___x_887_;
}
}
}
}
else
{
lean_object* v___x_888_; uint8_t v___x_889_; 
lean_dec_ref(v_str_823_);
v___x_888_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11));
v___x_889_ = lean_string_dec_eq(v_str_822_, v___x_888_);
lean_dec_ref(v_str_822_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_dec(v_snd_821_);
v___x_890_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_890_;
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_891_ = lean_array_get_size(v_snd_821_);
v___x_892_ = lean_unsigned_to_nat(6u);
v___x_893_ = lean_nat_dec_eq(v___x_891_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; 
lean_dec(v_snd_821_);
v___x_894_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_894_;
}
else
{
lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
lean_dec_ref(v_e_816_);
v___f_895_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2));
v___x_896_ = lean_unsigned_to_nat(4u);
v___x_897_ = lean_array_fget(v_snd_821_, v___x_896_);
v___x_898_ = lean_unsigned_to_nat(5u);
v___x_899_ = lean_array_fget(v_snd_821_, v___x_898_);
lean_dec(v_snd_821_);
v___x_900_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_895_, v___x_897_, v___x_899_);
return v___x_900_;
}
}
}
}
else
{
lean_object* v___x_901_; uint8_t v___x_902_; 
lean_dec_ref(v_str_823_);
v___x_901_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13));
v___x_902_ = lean_string_dec_eq(v_str_822_, v___x_901_);
lean_dec_ref(v_str_822_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_dec(v_snd_821_);
v___x_903_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_903_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_904_ = lean_array_get_size(v_snd_821_);
v___x_905_ = lean_unsigned_to_nat(6u);
v___x_906_ = lean_nat_dec_eq(v___x_904_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
lean_dec(v_snd_821_);
v___x_907_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_907_;
}
else
{
lean_object* v___f_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec_ref(v_e_816_);
v___f_908_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3));
v___x_909_ = lean_unsigned_to_nat(4u);
v___x_910_ = lean_array_fget(v_snd_821_, v___x_909_);
v___x_911_ = lean_unsigned_to_nat(5u);
v___x_912_ = lean_array_fget(v_snd_821_, v___x_911_);
lean_dec(v_snd_821_);
v___x_913_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_908_, v___x_910_, v___x_912_);
return v___x_913_;
}
}
}
}
else
{
lean_object* v___x_914_; uint8_t v___x_915_; 
lean_dec_ref(v_str_823_);
v___x_914_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_915_ = lean_string_dec_eq(v_str_822_, v___x_914_);
lean_dec_ref(v_str_822_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
lean_dec(v_snd_821_);
v___x_916_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_916_;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_917_ = lean_array_get_size(v_snd_821_);
v___x_918_ = lean_unsigned_to_nat(3u);
v___x_919_ = lean_nat_dec_eq(v___x_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; 
lean_dec(v_snd_821_);
v___x_920_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_920_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec_ref(v_e_816_);
v___x_921_ = lean_unsigned_to_nat(2u);
v___x_922_ = lean_array_fget(v_snd_821_, v___x_921_);
lean_dec(v_snd_821_);
v___x_923_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_922_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v___x_924_; 
v___x_924_ = lean_box(0);
return v___x_924_;
}
else
{
lean_object* v_val_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_933_; 
v_val_925_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_933_ == 0)
{
v___x_927_ = v___x_923_;
v_isShared_928_ = v_isSharedCheck_933_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_val_925_);
lean_dec(v___x_923_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_933_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_929_ = lean_nat_to_int(v_val_925_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_929_);
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_934_; 
lean_dec_ref_known(v_pre_819_, 2);
lean_dec_ref_known(v_fst_818_, 2);
lean_dec_ref(v___x_817_);
v___x_934_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_934_;
}
}
else
{
lean_object* v___x_935_; 
lean_dec_ref_known(v_fst_818_, 2);
lean_dec(v_pre_819_);
lean_dec_ref(v___x_817_);
v___x_935_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_935_;
}
}
else
{
lean_object* v___x_936_; 
lean_dec(v_fst_818_);
lean_dec_ref(v___x_817_);
v___x_936_ = l_Lean_Expr_int_x3f(v_e_816_);
return v___x_936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object* v_f_937_, lean_object* v_x_938_, lean_object* v_y_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_x_938_);
if (lean_obj_tag(v___x_940_) == 1)
{
lean_object* v_val_941_; lean_object* v___x_942_; 
v_val_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_val_941_);
lean_dec_ref_known(v___x_940_, 1);
v___x_942_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_y_939_);
if (lean_obj_tag(v___x_942_) == 1)
{
lean_object* v_val_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_951_; 
v_val_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_951_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_val_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = lean_apply_2(v_f_937_, v_val_941_, v_val_943_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_947_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
else
{
lean_object* v___x_952_; 
lean_dec(v___x_942_);
lean_dec(v_val_941_);
lean_dec_ref(v_f_937_);
v___x_952_ = lean_box(0);
return v___x_952_;
}
}
else
{
lean_object* v___x_953_; 
lean_dec(v___x_940_);
lean_dec_ref(v_y_939_);
lean_dec_ref(v_f_937_);
v___x_953_ = lean_box(0);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object* v_a_954_, lean_object* v_b_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v___x_961_; 
lean_inc_ref(v_a_954_);
v___x_961_ = l_Lean_Meta_mkEqRefl(v_a_954_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_963_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
v___x_963_ = l_Lean_Meta_mkEq(v_a_954_, v_b_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_972_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_972_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = l_Lean_Meta_mkExpectedPropHint(v_a_962_, v_a_964_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_968_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
else
{
lean_dec(v_a_962_);
return v___x_963_;
}
}
else
{
lean_dec_ref(v_b_955_);
lean_dec_ref(v_a_954_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType___boxed(lean_object* v_a_973_, lean_object* v_b_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v_a_973_, v_b_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
return v_res_980_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(lean_object* v_a_981_, lean_object* v_x_982_){
_start:
{
if (lean_obj_tag(v_x_982_) == 0)
{
uint8_t v___x_983_; 
v___x_983_ = 0;
return v___x_983_;
}
else
{
lean_object* v_head_984_; lean_object* v_tail_985_; uint8_t v___x_986_; 
v_head_984_ = lean_ctor_get(v_x_982_, 0);
v_tail_985_ = lean_ctor_get(v_x_982_, 1);
v___x_986_ = lean_expr_eqv(v_a_981_, v_head_984_);
if (v___x_986_ == 0)
{
v_x_982_ = v_tail_985_;
goto _start;
}
else
{
return v___x_986_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0___boxed(lean_object* v_a_988_, lean_object* v_x_989_){
_start:
{
uint8_t v_res_990_; lean_object* v_r_991_; 
v_res_990_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v_a_988_, v_x_989_);
lean_dec(v_x_989_);
lean_dec_ref(v_a_988_);
v_r_991_ = lean_box(v_res_990_);
return v_r_991_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_box(0);
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5));
v___x_1002_ = l_Lean_Expr_const___override(v___x_1001_, v___x_1000_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_box(0);
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8));
v___x_1009_ = l_Lean_Expr_const___override(v___x_1008_, v___x_1007_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12));
v___x_1017_ = l_Lean_Expr_const___override(v___x_1016_, v___x_1015_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = lean_box(0);
v___x_1023_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15));
v___x_1024_ = l_Lean_Expr_const___override(v___x_1023_, v___x_1022_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_unsigned_to_nat(0u);
v___x_1038_ = l_Lean_Level_ofNat(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = l_Lean_mkNatLit(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = lean_nat_to_int(v___x_1068_);
return v___x_1069_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39(void){
_start:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
v___x_1071_ = lean_int_dec_le(v___x_1070_, v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
v___x_1082_ = lean_int_neg(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45);
v___x_1084_ = l_Int_toNat(v___x_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46);
v___x_1086_ = l_Lean_instToExprInt_mkNat(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
v___x_1088_ = l_Int_toNat(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48);
v___x_1090_ = l_Lean_instToExprInt_mkNat(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_box(0);
v___x_1092_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23);
v___x_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v___x_1091_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1095_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22));
v___x_1096_ = l_Lean_Expr_const___override(v___x_1095_, v___x_1094_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = lean_box(0);
v___x_1102_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53));
v___x_1103_ = l_Lean_Expr_const___override(v___x_1102_, v___x_1101_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56));
v___x_1112_ = l_Lean_Expr_const___override(v___x_1111_, v___x_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33));
v___x_1115_ = l_Lean_Expr_const___override(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_box(0);
v___x_1117_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35));
v___x_1118_ = l_Lean_Expr_const___override(v___x_1117_, v___x_1116_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_box(0);
v___x_1120_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37));
v___x_1121_ = l_Lean_Expr_const___override(v___x_1120_, v___x_1119_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1123_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42));
v___x_1124_ = l_Lean_Expr_const___override(v___x_1123_, v___x_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = lean_box(0);
v___x_1126_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44));
v___x_1127_ = l_Lean_Expr_const___override(v___x_1126_, v___x_1125_);
return v___x_1127_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1128_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47);
v___x_1129_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62);
v___x_1130_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1131_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61);
v___x_1132_ = l_Lean_mkApp3(v___x_1131_, v___x_1130_, v___x_1129_, v___x_1128_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_unsigned_to_nat(1u);
v___x_1137_ = l_Lean_Level_ofNat(v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66);
v___x_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___x_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67);
v___x_1142_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65));
v___x_1143_ = l_Lean_Expr_const___override(v___x_1142_, v___x_1141_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = lean_box(0);
v___x_1149_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70));
v___x_1150_ = l_Lean_Expr_const___override(v___x_1149_, v___x_1148_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = lean_box(0);
v___x_1156_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73));
v___x_1157_ = l_Lean_Expr_const___override(v___x_1156_, v___x_1155_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93));
v___x_1198_ = l_Lean_Expr_const___override(v___x_1197_, v___x_1196_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(lean_object* v_e_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v___x_1224_; lean_object* v_fst_1225_; 
v___x_1224_ = l_Lean_Expr_getAppFnArgs(v_e_1199_);
v_fst_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_fst_1225_);
if (lean_obj_tag(v_fst_1225_) == 1)
{
lean_object* v_pre_1226_; 
v_pre_1226_ = lean_ctor_get(v_fst_1225_, 0);
switch(lean_obj_tag(v_pre_1226_))
{
case 1:
{
lean_object* v_pre_1227_; 
lean_inc_ref(v_pre_1226_);
v_pre_1227_ = lean_ctor_get(v_pre_1226_, 0);
if (lean_obj_tag(v_pre_1227_) == 0)
{
lean_object* v_snd_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1725_; 
v_snd_1228_ = lean_ctor_get(v___x_1224_, 1);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v___x_1224_, 0);
lean_dec(v_unused_1726_);
v___x_1230_ = v___x_1224_;
v_isShared_1231_ = v_isSharedCheck_1725_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_snd_1228_);
lean_dec(v___x_1224_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1725_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_str_1232_; lean_object* v_str_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v_str_1232_ = lean_ctor_get(v_fst_1225_, 1);
lean_inc_ref(v_str_1232_);
lean_dec_ref_known(v_fst_1225_, 2);
v_str_1233_ = lean_ctor_get(v_pre_1226_, 1);
lean_inc_ref(v_str_1233_);
lean_dec_ref_known(v_pre_1226_, 2);
v___x_1234_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_1235_ = lean_string_dec_eq(v_str_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3));
v___x_1237_ = lean_string_dec_eq(v_str_1233_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0));
v___x_1239_ = lean_string_dec_eq(v_str_1233_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1));
v___x_1241_ = lean_string_dec_eq(v_str_1233_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2));
v___x_1243_ = lean_string_dec_eq(v_str_1233_, v___x_1242_);
lean_dec_ref(v_str_1233_);
if (v___x_1243_ == 0)
{
lean_dec_ref(v_str_1232_);
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
else
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3));
v___x_1245_ = lean_string_dec_eq(v_str_1232_, v___x_1244_);
lean_dec_ref(v_str_1232_);
if (v___x_1245_ == 0)
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1246_ = lean_array_get_size(v_snd_1228_);
v___x_1247_ = lean_unsigned_to_nat(4u);
v___x_1248_ = lean_nat_dec_eq(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1249_ = lean_unsigned_to_nat(2u);
v___x_1250_ = lean_array_fget(v_snd_1228_, v___x_1249_);
v___x_1251_ = lean_unsigned_to_nat(3u);
v___x_1252_ = lean_array_fget(v_snd_1228_, v___x_1251_);
lean_dec(v_snd_1228_);
v___x_1253_ = lean_box(0);
v___x_1254_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6);
lean_inc(v___x_1252_);
lean_inc(v___x_1250_);
v___x_1255_ = l_Lean_mkAppB(v___x_1254_, v___x_1250_, v___x_1252_);
v___x_1256_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9);
v___x_1257_ = l_Lean_mkAppB(v___x_1256_, v___x_1250_, v___x_1252_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 1);
lean_ctor_set(v___x_1230_, 1, v___x_1253_);
lean_ctor_set(v___x_1230_, 0, v___x_1257_);
v___x_1259_ = v___x_1230_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1253_);
v___x_1259_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1255_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
}
}
}
}
else
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
lean_dec_ref(v_str_1233_);
v___x_1263_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10));
v___x_1264_ = lean_string_dec_eq(v_str_1232_, v___x_1263_);
lean_dec_ref(v_str_1232_);
if (v___x_1264_ == 0)
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = lean_array_get_size(v_snd_1228_);
v___x_1266_ = lean_unsigned_to_nat(4u);
v___x_1267_ = lean_nat_dec_eq(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1268_ = lean_unsigned_to_nat(2u);
v___x_1269_ = lean_array_fget(v_snd_1228_, v___x_1268_);
v___x_1270_ = lean_unsigned_to_nat(3u);
v___x_1271_ = lean_array_fget(v_snd_1228_, v___x_1270_);
lean_dec(v_snd_1228_);
v___x_1272_ = lean_box(0);
v___x_1273_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13);
lean_inc(v___x_1271_);
lean_inc(v___x_1269_);
v___x_1274_ = l_Lean_mkAppB(v___x_1273_, v___x_1269_, v___x_1271_);
v___x_1275_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16);
v___x_1276_ = l_Lean_mkAppB(v___x_1275_, v___x_1269_, v___x_1271_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 1);
lean_ctor_set(v___x_1230_, 1, v___x_1272_);
lean_ctor_set(v___x_1230_, 0, v___x_1276_);
v___x_1278_ = v___x_1230_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v___x_1272_);
v___x_1278_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1274_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
return v___x_1280_;
}
}
}
}
}
else
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
lean_dec_ref(v_str_1233_);
v___x_1282_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17));
v___x_1283_ = lean_string_dec_eq(v_str_1232_, v___x_1282_);
lean_dec_ref(v_str_1232_);
if (v___x_1283_ == 0)
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1284_ = lean_array_get_size(v_snd_1228_);
v___x_1285_ = lean_unsigned_to_nat(6u);
v___x_1286_ = lean_nat_dec_eq(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v_fst_1290_; 
v___x_1287_ = lean_unsigned_to_nat(5u);
v___x_1288_ = lean_array_fget(v_snd_1228_, v___x_1287_);
lean_inc(v___x_1288_);
v___x_1289_ = l_Lean_Expr_getAppFnArgs(v___x_1288_);
v_fst_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_fst_1290_);
if (lean_obj_tag(v_fst_1290_) == 1)
{
lean_object* v_pre_1291_; 
v_pre_1291_ = lean_ctor_get(v_fst_1290_, 0);
lean_inc(v_pre_1291_);
if (lean_obj_tag(v_pre_1291_) == 1)
{
lean_object* v_pre_1292_; 
v_pre_1292_ = lean_ctor_get(v_pre_1291_, 0);
if (lean_obj_tag(v_pre_1292_) == 0)
{
lean_object* v_snd_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1492_; 
v_snd_1293_ = lean_ctor_get(v___x_1289_, 1);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; 
v_unused_1493_ = lean_ctor_get(v___x_1289_, 0);
lean_dec(v_unused_1493_);
v___x_1295_ = v___x_1289_;
v_isShared_1296_ = v_isSharedCheck_1492_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_snd_1293_);
lean_dec(v___x_1289_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1492_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v_str_1297_; lean_object* v_str_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_str_1297_ = lean_ctor_get(v_fst_1290_, 1);
lean_inc_ref(v_str_1297_);
lean_dec_ref_known(v_fst_1290_, 2);
v_str_1298_ = lean_ctor_get(v_pre_1291_, 1);
lean_inc_ref(v_str_1298_);
lean_dec_ref_known(v_pre_1291_, 2);
v___x_1299_ = lean_unsigned_to_nat(4u);
v___x_1300_ = lean_array_fget(v_snd_1228_, v___x_1299_);
lean_dec(v_snd_1228_);
v___x_1338_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4));
v___x_1339_ = lean_string_dec_eq(v_str_1298_, v___x_1338_);
if (v___x_1339_ == 0)
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_string_dec_eq(v_str_1298_, v___x_1234_);
lean_dec_ref(v_str_1298_);
if (v___x_1340_ == 0)
{
lean_dec(v___x_1300_);
lean_dec_ref(v_str_1297_);
lean_del_object(v___x_1295_);
lean_dec(v_snd_1293_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1215_;
}
else
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1342_ = lean_string_dec_eq(v_str_1297_, v___x_1341_);
lean_dec_ref(v_str_1297_);
if (v___x_1342_ == 0)
{
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v_snd_1293_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1215_;
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1343_ = lean_array_get_size(v_snd_1293_);
v___x_1344_ = lean_unsigned_to_nat(3u);
v___x_1345_ = lean_nat_dec_eq(v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v_snd_1293_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1215_;
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = lean_array_fget_borrowed(v_snd_1293_, v___x_1346_);
if (lean_obj_tag(v___x_1347_) == 4)
{
lean_object* v_declName_1348_; 
v_declName_1348_ = lean_ctor_get(v___x_1347_, 0);
if (lean_obj_tag(v_declName_1348_) == 1)
{
lean_object* v_pre_1349_; 
v_pre_1349_ = lean_ctor_get(v_declName_1348_, 0);
if (lean_obj_tag(v_pre_1349_) == 0)
{
lean_object* v_us_1350_; lean_object* v_str_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_us_1350_ = lean_ctor_get(v___x_1347_, 1);
lean_inc(v_us_1350_);
v_str_1351_ = lean_ctor_get(v_declName_1348_, 1);
v___x_1352_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1353_ = lean_string_dec_eq(v_str_1351_, v___x_1352_);
if (v___x_1353_ == 0)
{
lean_dec(v_us_1350_);
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v_snd_1293_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1215_;
}
else
{
if (lean_obj_tag(v_us_1350_) == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v_fst_1357_; 
v___x_1354_ = lean_unsigned_to_nat(2u);
v___x_1355_ = lean_array_fget(v_snd_1293_, v___x_1354_);
lean_dec(v_snd_1293_);
lean_inc(v___x_1355_);
v___x_1356_ = l_Lean_Expr_getAppFnArgs(v___x_1355_);
v_fst_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_fst_1357_);
if (lean_obj_tag(v_fst_1357_) == 1)
{
lean_object* v_pre_1358_; 
v_pre_1358_ = lean_ctor_get(v_fst_1357_, 0);
lean_inc(v_pre_1358_);
if (lean_obj_tag(v_pre_1358_) == 1)
{
lean_object* v_pre_1359_; 
v_pre_1359_ = lean_ctor_get(v_pre_1358_, 0);
if (lean_obj_tag(v_pre_1359_) == 0)
{
lean_object* v_snd_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1439_; 
v_snd_1360_ = lean_ctor_get(v___x_1356_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v___x_1356_, 0);
lean_dec(v_unused_1440_);
v___x_1362_ = v___x_1356_;
v_isShared_1363_ = v_isSharedCheck_1439_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_snd_1360_);
lean_dec(v___x_1356_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1439_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v_str_1364_; lean_object* v_str_1365_; uint8_t v___x_1366_; 
v_str_1364_ = lean_ctor_get(v_fst_1357_, 1);
lean_inc_ref(v_str_1364_);
lean_dec_ref_known(v_fst_1357_, 2);
v_str_1365_ = lean_ctor_get(v_pre_1358_, 1);
lean_inc_ref(v_str_1365_);
lean_dec_ref_known(v_pre_1358_, 2);
v___x_1366_ = lean_string_dec_eq(v_str_1365_, v___x_1338_);
lean_dec_ref(v_str_1365_);
if (v___x_1366_ == 0)
{
lean_dec_ref(v_str_1364_);
lean_del_object(v___x_1362_);
lean_dec(v_snd_1360_);
lean_dec(v___x_1355_);
lean_del_object(v___x_1295_);
lean_del_object(v___x_1230_);
goto v___jp_1301_;
}
else
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_1368_ = lean_string_dec_eq(v_str_1364_, v___x_1367_);
lean_dec_ref(v_str_1364_);
if (v___x_1368_ == 0)
{
lean_del_object(v___x_1362_);
lean_dec(v_snd_1360_);
lean_dec(v___x_1355_);
lean_del_object(v___x_1295_);
lean_del_object(v___x_1230_);
goto v___jp_1301_;
}
else
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = lean_array_get_size(v_snd_1360_);
v___x_1370_ = lean_nat_dec_eq(v___x_1369_, v___x_1285_);
if (v___x_1370_ == 0)
{
lean_del_object(v___x_1362_);
lean_dec(v_snd_1360_);
lean_dec(v___x_1355_);
lean_del_object(v___x_1295_);
lean_del_object(v___x_1230_);
goto v___jp_1301_;
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_array_fget(v_snd_1360_, v___x_1299_);
lean_inc(v___x_1371_);
v___x_1372_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1371_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_dec(v___x_1371_);
lean_del_object(v___x_1362_);
lean_dec(v_snd_1360_);
lean_dec(v___x_1355_);
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1221_;
}
else
{
lean_object* v_val_1373_; uint8_t v___x_1374_; 
v_val_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_val_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = lean_nat_dec_eq(v_val_1373_, v___x_1346_);
lean_dec(v_val_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1375_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22));
v___x_1376_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23);
if (v_isShared_1363_ == 0)
{
lean_ctor_set_tag(v___x_1362_, 1);
lean_ctor_set(v___x_1362_, 1, v_us_1350_);
lean_ctor_set(v___x_1362_, 0, v___x_1376_);
v___x_1378_ = v___x_1362_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_us_1350_);
v___x_1378_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v_b__pos_1385_; lean_object* v___x_1386_; 
lean_inc_ref(v___x_1378_);
v___x_1379_ = l_Lean_Expr_const___override(v___x_1375_, v___x_1378_);
v___x_1380_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24));
v___x_1381_ = l_Lean_Expr_const___override(v___x_1380_, v_us_1350_);
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26));
v___x_1383_ = l_Lean_Expr_const___override(v___x_1382_, v_us_1350_);
v___x_1384_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27);
lean_inc(v___x_1371_);
v_b__pos_1385_ = l_Lean_mkApp4(v___x_1379_, v___x_1381_, v___x_1383_, v___x_1384_, v___x_1371_);
v___x_1386_ = l_Lean_Meta_mkDecideProof(v_b__pos_1385_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1429_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1429_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1429_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___y_1403_; uint8_t v___x_1419_; 
v___x_1391_ = lean_array_fget(v_snd_1360_, v___x_1287_);
lean_dec(v_snd_1360_);
v___x_1392_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29));
v___x_1393_ = l_Lean_Expr_const___override(v___x_1392_, v_us_1350_);
v___x_1394_ = l_Lean_mkApp3(v___x_1393_, v___x_1371_, v___x_1391_, v_a_1387_);
v___x_1395_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31));
v___x_1396_ = l_Lean_Expr_const___override(v___x_1395_, v_us_1350_);
v___x_1397_ = l_Lean_mkAppB(v___x_1396_, v___x_1355_, v___x_1394_);
v___x_1398_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33));
v___x_1399_ = l_Lean_Expr_const___override(v___x_1398_, v_us_1350_);
v___x_1400_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35));
v___x_1401_ = l_Lean_Expr_const___override(v___x_1400_, v_us_1350_);
v___x_1419_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1420_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42));
v___x_1421_ = l_Lean_Expr_const___override(v___x_1420_, v___x_1378_);
v___x_1422_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1));
v___x_1423_ = l_Lean_Expr_const___override(v___x_1422_, v_us_1350_);
v___x_1424_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44));
v___x_1425_ = l_Lean_Expr_const___override(v___x_1424_, v_us_1350_);
v___x_1426_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47);
v___x_1427_ = l_Lean_mkApp3(v___x_1421_, v___x_1423_, v___x_1425_, v___x_1426_);
v___y_1403_ = v___x_1427_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1428_; 
lean_dec_ref(v___x_1378_);
v___x_1428_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1403_ = v___x_1428_;
goto v___jp_1402_;
}
v___jp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
lean_inc_ref(v___x_1397_);
lean_inc_n(v___x_1288_, 2);
v___x_1404_ = l_Lean_mkApp3(v___x_1401_, v___x_1288_, v___y_1403_, v___x_1397_);
lean_inc(v___x_1300_);
v___x_1405_ = l_Lean_mkApp3(v___x_1399_, v___x_1300_, v___x_1288_, v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37));
v___x_1407_ = l_Lean_Expr_const___override(v___x_1406_, v_us_1350_);
v___x_1408_ = l_Lean_mkApp3(v___x_1407_, v___x_1300_, v___x_1288_, v___x_1397_);
v___x_1409_ = lean_box(0);
if (v_isShared_1296_ == 0)
{
lean_ctor_set_tag(v___x_1295_, 1);
lean_ctor_set(v___x_1295_, 1, v___x_1409_);
lean_ctor_set(v___x_1295_, 0, v___x_1408_);
v___x_1411_ = v___x_1295_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1413_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 1);
lean_ctor_set(v___x_1230_, 1, v___x_1411_);
lean_ctor_set(v___x_1230_, 0, v___x_1405_);
v___x_1413_ = v___x_1230_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1415_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1413_);
v___x_1415_ = v___x_1389_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v___x_1378_);
lean_dec(v___x_1371_);
lean_dec(v_snd_1360_);
lean_dec(v___x_1355_);
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
v_a_1430_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1386_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1386_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
else
{
lean_dec(v___x_1371_);
lean_del_object(v___x_1362_);
lean_dec(v_snd_1360_);
lean_dec(v___x_1355_);
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1221_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1358_, 2);
lean_dec_ref_known(v_fst_1357_, 2);
lean_dec_ref(v___x_1356_);
lean_dec(v___x_1355_);
lean_del_object(v___x_1295_);
lean_del_object(v___x_1230_);
goto v___jp_1301_;
}
}
else
{
lean_dec(v_pre_1358_);
lean_dec_ref_known(v_fst_1357_, 2);
lean_dec_ref(v___x_1356_);
lean_dec(v___x_1355_);
lean_del_object(v___x_1295_);
lean_del_object(v___x_1230_);
goto v___jp_1301_;
}
}
else
{
lean_dec(v_fst_1357_);
lean_dec_ref(v___x_1356_);
lean_dec(v___x_1355_);
lean_del_object(v___x_1295_);
lean_del_object(v___x_1230_);
goto v___jp_1301_;
}
}
else
{
lean_dec(v_us_1350_);
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v_snd_1293_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1215_;
}
}
}
else
{
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v_snd_1293_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1215_;
}
}
else
{
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v_snd_1293_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1215_;
}
}
else
{
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v_snd_1293_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1215_;
}
}
}
}
}
else
{
lean_object* v___x_1441_; uint8_t v___x_1442_; 
lean_dec_ref(v_str_1298_);
v___x_1441_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_1442_ = lean_string_dec_eq(v_str_1297_, v___x_1441_);
lean_dec_ref(v_str_1297_);
if (v___x_1442_ == 0)
{
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v_snd_1293_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1215_;
}
else
{
lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1443_ = lean_array_get_size(v_snd_1293_);
v___x_1444_ = lean_nat_dec_eq(v___x_1443_, v___x_1285_);
if (v___x_1444_ == 0)
{
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v_snd_1293_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1215_;
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_array_fget(v_snd_1293_, v___x_1299_);
lean_inc(v___x_1445_);
v___x_1446_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1445_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_dec(v___x_1445_);
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v_snd_1293_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1209_;
}
else
{
lean_object* v_val_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v_val_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_val_1447_);
lean_dec_ref_known(v___x_1446_, 1);
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = lean_nat_dec_eq(v_val_1447_, v___x_1448_);
lean_dec(v_val_1447_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___y_1456_; uint8_t v___x_1489_; 
v___x_1450_ = lean_array_fget(v_snd_1293_, v___x_1287_);
lean_dec(v_snd_1293_);
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51);
v___x_1453_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1454_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
v___x_1489_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
v___y_1456_ = v___x_1490_;
goto v___jp_1455_;
}
else
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1456_ = v___x_1491_;
goto v___jp_1455_;
}
v___jp_1455_:
{
lean_object* v_b__pos_1457_; lean_object* v___x_1458_; 
lean_inc(v___x_1445_);
lean_inc_ref(v___y_1456_);
v_b__pos_1457_ = l_Lean_mkApp4(v___x_1452_, v___x_1453_, v___x_1454_, v___y_1456_, v___x_1445_);
v___x_1458_ = l_Lean_Meta_mkDecideProof(v_b__pos_1457_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1480_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1480_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1480_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1463_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57);
v___x_1464_ = l_Lean_mkApp3(v___x_1463_, v___x_1445_, v___x_1450_, v_a_1459_);
v___x_1465_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58);
v___x_1466_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59);
lean_inc_ref(v___x_1464_);
lean_inc_ref(v___y_1456_);
lean_inc_n(v___x_1288_, 2);
v___x_1467_ = l_Lean_mkApp3(v___x_1466_, v___x_1288_, v___y_1456_, v___x_1464_);
lean_inc(v___x_1300_);
v___x_1468_ = l_Lean_mkApp3(v___x_1465_, v___x_1300_, v___x_1288_, v___x_1467_);
v___x_1469_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60);
v___x_1470_ = l_Lean_mkApp3(v___x_1469_, v___x_1300_, v___x_1288_, v___x_1464_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set_tag(v___x_1295_, 1);
lean_ctor_set(v___x_1295_, 1, v___x_1451_);
lean_ctor_set(v___x_1295_, 0, v___x_1470_);
v___x_1472_ = v___x_1295_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v___x_1451_);
v___x_1472_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1474_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 1);
lean_ctor_set(v___x_1230_, 1, v___x_1472_);
lean_ctor_set(v___x_1230_, 0, v___x_1468_);
v___x_1474_ = v___x_1230_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1476_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1474_);
v___x_1476_ = v___x_1461_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec(v___x_1450_);
lean_dec(v___x_1445_);
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
v_a_1481_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1458_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1458_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
else
{
lean_dec(v___x_1445_);
lean_dec(v___x_1300_);
lean_del_object(v___x_1295_);
lean_dec(v_snd_1293_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
goto v___jp_1209_;
}
}
}
}
}
v___jp_1301_:
{
lean_object* v___x_1302_; lean_object* v_fst_1303_; 
v___x_1302_ = l_Lean_Expr_getAppFnArgs(v___x_1300_);
v_fst_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_fst_1303_);
if (lean_obj_tag(v_fst_1303_) == 1)
{
lean_object* v_pre_1304_; 
v_pre_1304_ = lean_ctor_get(v_fst_1303_, 0);
lean_inc(v_pre_1304_);
if (lean_obj_tag(v_pre_1304_) == 1)
{
lean_object* v_pre_1305_; 
v_pre_1305_ = lean_ctor_get(v_pre_1304_, 0);
if (lean_obj_tag(v_pre_1305_) == 0)
{
lean_object* v_snd_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1336_; 
v_snd_1306_ = lean_ctor_get(v___x_1302_, 1);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v___x_1302_, 0);
lean_dec(v_unused_1337_);
v___x_1308_ = v___x_1302_;
v_isShared_1309_ = v_isSharedCheck_1336_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_snd_1306_);
lean_dec(v___x_1302_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1336_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v_str_1310_; lean_object* v_str_1311_; uint8_t v___x_1312_; 
v_str_1310_ = lean_ctor_get(v_fst_1303_, 1);
lean_inc_ref(v_str_1310_);
lean_dec_ref_known(v_fst_1303_, 2);
v_str_1311_ = lean_ctor_get(v_pre_1304_, 1);
lean_inc_ref(v_str_1311_);
lean_dec_ref_known(v_pre_1304_, 2);
v___x_1312_ = lean_string_dec_eq(v_str_1311_, v___x_1234_);
lean_dec_ref(v_str_1311_);
if (v___x_1312_ == 0)
{
lean_dec_ref(v_str_1310_);
lean_del_object(v___x_1308_);
lean_dec(v_snd_1306_);
lean_dec(v___x_1288_);
goto v___jp_1218_;
}
else
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1314_ = lean_string_dec_eq(v_str_1310_, v___x_1313_);
lean_dec_ref(v_str_1310_);
if (v___x_1314_ == 0)
{
lean_del_object(v___x_1308_);
lean_dec(v_snd_1306_);
lean_dec(v___x_1288_);
goto v___jp_1218_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1315_ = lean_array_get_size(v_snd_1306_);
v___x_1316_ = lean_unsigned_to_nat(3u);
v___x_1317_ = lean_nat_dec_eq(v___x_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_del_object(v___x_1308_);
lean_dec(v_snd_1306_);
lean_dec(v___x_1288_);
goto v___jp_1218_;
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = lean_array_fget_borrowed(v_snd_1306_, v___x_1318_);
if (lean_obj_tag(v___x_1319_) == 4)
{
lean_object* v_declName_1320_; 
v_declName_1320_ = lean_ctor_get(v___x_1319_, 0);
if (lean_obj_tag(v_declName_1320_) == 1)
{
lean_object* v_pre_1321_; 
v_pre_1321_ = lean_ctor_get(v_declName_1320_, 0);
if (lean_obj_tag(v_pre_1321_) == 0)
{
lean_object* v_us_1322_; lean_object* v_str_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_us_1322_ = lean_ctor_get(v___x_1319_, 1);
lean_inc(v_us_1322_);
v_str_1323_ = lean_ctor_get(v_declName_1320_, 1);
v___x_1324_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1325_ = lean_string_dec_eq(v_str_1323_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_dec(v_us_1322_);
lean_del_object(v___x_1308_);
lean_dec(v_snd_1306_);
lean_dec(v___x_1288_);
goto v___jp_1218_;
}
else
{
if (lean_obj_tag(v_us_1322_) == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1326_ = lean_unsigned_to_nat(2u);
v___x_1327_ = lean_array_fget(v_snd_1306_, v___x_1326_);
lean_dec(v_snd_1306_);
v___x_1328_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19));
v___x_1329_ = l_Lean_Expr_const___override(v___x_1328_, v_us_1322_);
v___x_1330_ = l_Lean_mkAppB(v___x_1329_, v___x_1327_, v___x_1288_);
v___x_1331_ = lean_box(0);
if (v_isShared_1309_ == 0)
{
lean_ctor_set_tag(v___x_1308_, 1);
lean_ctor_set(v___x_1308_, 1, v___x_1331_);
lean_ctor_set(v___x_1308_, 0, v___x_1330_);
v___x_1333_ = v___x_1308_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1330_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
}
else
{
lean_dec(v_us_1322_);
lean_del_object(v___x_1308_);
lean_dec(v_snd_1306_);
lean_dec(v___x_1288_);
goto v___jp_1218_;
}
}
}
else
{
lean_del_object(v___x_1308_);
lean_dec(v_snd_1306_);
lean_dec(v___x_1288_);
goto v___jp_1218_;
}
}
else
{
lean_del_object(v___x_1308_);
lean_dec(v_snd_1306_);
lean_dec(v___x_1288_);
goto v___jp_1218_;
}
}
else
{
lean_del_object(v___x_1308_);
lean_dec(v_snd_1306_);
lean_dec(v___x_1288_);
goto v___jp_1218_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1304_, 2);
lean_dec_ref_known(v_fst_1303_, 2);
lean_dec_ref(v___x_1302_);
lean_dec(v___x_1288_);
goto v___jp_1218_;
}
}
else
{
lean_dec(v_pre_1304_);
lean_dec_ref_known(v_fst_1303_, 2);
lean_dec_ref(v___x_1302_);
lean_dec(v___x_1288_);
goto v___jp_1218_;
}
}
else
{
lean_dec(v_fst_1303_);
lean_dec_ref(v___x_1302_);
lean_dec(v___x_1288_);
goto v___jp_1218_;
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1291_, 2);
lean_dec_ref_known(v_fst_1290_, 2);
lean_dec_ref(v___x_1289_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1215_;
}
}
else
{
lean_dec(v_pre_1291_);
lean_dec_ref_known(v_fst_1290_, 2);
lean_dec_ref(v___x_1289_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1215_;
}
}
else
{
lean_dec(v_fst_1290_);
lean_dec_ref(v___x_1289_);
lean_dec(v___x_1288_);
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1215_;
}
}
}
}
}
else
{
lean_object* v___x_1494_; uint8_t v___x_1495_; 
lean_dec_ref(v_str_1233_);
v___x_1494_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7));
v___x_1495_ = lean_string_dec_eq(v_str_1232_, v___x_1494_);
lean_dec_ref(v_str_1232_);
if (v___x_1495_ == 0)
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1496_ = lean_array_get_size(v_snd_1228_);
v___x_1497_ = lean_unsigned_to_nat(6u);
v___x_1498_ = lean_nat_dec_eq(v___x_1496_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1499_ = lean_unsigned_to_nat(5u);
v___x_1500_ = lean_array_fget(v_snd_1228_, v___x_1499_);
lean_inc(v___x_1500_);
v___x_1501_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1500_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_dec(v___x_1500_);
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1206_;
}
else
{
lean_object* v_val_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v_val_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_val_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = lean_nat_dec_eq(v_val_1502_, v___x_1503_);
lean_dec(v_val_1502_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___y_1511_; uint8_t v___x_1551_; 
v___x_1505_ = lean_unsigned_to_nat(4u);
v___x_1506_ = lean_array_fget(v_snd_1228_, v___x_1505_);
lean_dec(v_snd_1228_);
v___x_1507_ = lean_box(0);
v___x_1508_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68);
v___x_1509_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1551_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
v___y_1511_ = v___x_1552_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1511_ = v___x_1553_;
goto v___jp_1510_;
}
v___jp_1510_:
{
lean_object* v_ne__zero_1512_; lean_object* v___x_1513_; 
lean_inc_ref(v___y_1511_);
lean_inc(v___x_1500_);
v_ne__zero_1512_ = l_Lean_mkApp3(v___x_1508_, v___x_1509_, v___x_1500_, v___y_1511_);
v___x_1513_ = l_Lean_Meta_mkDecideProof(v_ne__zero_1512_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v_pos_1517_; lean_object* v___x_1518_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1515_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51);
v___x_1516_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
lean_inc(v___x_1500_);
lean_inc_ref(v___y_1511_);
v_pos_1517_ = l_Lean_mkApp4(v___x_1515_, v___x_1509_, v___x_1516_, v___y_1511_, v___x_1500_);
v___x_1518_ = l_Lean_Meta_mkDecideProof(v_pos_1517_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1534_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1521_ = v___x_1518_;
v_isShared_1522_ = v_isSharedCheck_1534_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1534_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1523_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71);
lean_inc(v___x_1500_);
lean_inc(v___x_1506_);
v___x_1524_ = l_Lean_mkApp3(v___x_1523_, v___x_1506_, v___x_1500_, v_a_1514_);
v___x_1525_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74);
v___x_1526_ = l_Lean_mkApp3(v___x_1525_, v___x_1506_, v___x_1500_, v_a_1519_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 1);
lean_ctor_set(v___x_1230_, 1, v___x_1507_);
lean_ctor_set(v___x_1230_, 0, v___x_1526_);
v___x_1528_ = v___x_1230_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v___x_1507_);
v___x_1528_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1524_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1529_);
v___x_1531_ = v___x_1521_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec(v_a_1514_);
lean_dec(v___x_1506_);
lean_dec(v___x_1500_);
lean_del_object(v___x_1230_);
v_a_1535_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1518_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1518_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec(v___x_1506_);
lean_dec(v___x_1500_);
lean_del_object(v___x_1230_);
v_a_1543_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1513_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1513_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
else
{
lean_dec(v___x_1500_);
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1206_;
}
}
}
}
}
}
else
{
lean_object* v___x_1554_; uint8_t v___x_1555_; 
lean_dec_ref(v_str_1233_);
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1555_ = lean_string_dec_eq(v_str_1232_, v___x_1554_);
lean_dec_ref(v_str_1232_);
if (v___x_1555_ == 0)
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1556_ = lean_array_get_size(v_snd_1228_);
v___x_1557_ = lean_unsigned_to_nat(3u);
v___x_1558_ = lean_nat_dec_eq(v___x_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = lean_unsigned_to_nat(0u);
v___x_1560_ = lean_array_fget_borrowed(v_snd_1228_, v___x_1559_);
if (lean_obj_tag(v___x_1560_) == 4)
{
lean_object* v_declName_1561_; 
v_declName_1561_ = lean_ctor_get(v___x_1560_, 0);
if (lean_obj_tag(v_declName_1561_) == 1)
{
lean_object* v_pre_1562_; 
v_pre_1562_ = lean_ctor_get(v_declName_1561_, 0);
if (lean_obj_tag(v_pre_1562_) == 0)
{
lean_object* v_us_1563_; lean_object* v_str_1564_; lean_object* v___x_1565_; lean_object* v___y_1567_; lean_object* v___y_1568_; uint8_t v___x_1578_; 
v_us_1563_ = lean_ctor_get(v___x_1560_, 1);
lean_inc(v_us_1563_);
v_str_1564_ = lean_ctor_get(v_declName_1561_, 1);
v___x_1565_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1578_ = lean_string_dec_eq(v_str_1564_, v___x_1565_);
if (v___x_1578_ == 0)
{
lean_dec(v_us_1563_);
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
else
{
if (lean_obj_tag(v_us_1563_) == 0)
{
uint8_t v_splitNatSub_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v_r_1586_; lean_object* v_n_1588_; lean_object* v_x_1589_; lean_object* v_n_1598_; lean_object* v_i_1599_; lean_object* v_x_1608_; 
v_splitNatSub_1579_ = lean_ctor_get_uint8(v_a_1200_, 1);
v___x_1580_ = lean_unsigned_to_nat(2u);
v___x_1581_ = lean_array_fget(v_snd_1228_, v___x_1580_);
lean_dec(v_snd_1228_);
v___x_1582_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78));
v___x_1583_ = l_Lean_Expr_const___override(v___x_1582_, v_us_1563_);
lean_inc(v___x_1581_);
v___x_1584_ = l_Lean_Expr_app___override(v___x_1583_, v___x_1581_);
v___x_1585_ = lean_box(0);
v_r_1586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_r_1586_, 0, v___x_1584_);
lean_ctor_set(v_r_1586_, 1, v___x_1585_);
if (v_splitNatSub_1579_ == 1)
{
lean_object* v___x_1614_; lean_object* v_fst_1615_; 
v___x_1614_ = l_Lean_Expr_getAppFnArgs(v___x_1581_);
v_fst_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_fst_1615_);
if (lean_obj_tag(v_fst_1615_) == 1)
{
lean_object* v_pre_1616_; 
v_pre_1616_ = lean_ctor_get(v_fst_1615_, 0);
lean_inc(v_pre_1616_);
if (lean_obj_tag(v_pre_1616_) == 1)
{
lean_object* v_pre_1617_; 
v_pre_1617_ = lean_ctor_get(v_pre_1616_, 0);
if (lean_obj_tag(v_pre_1617_) == 0)
{
lean_object* v_snd_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1678_; 
v_snd_1618_ = lean_ctor_get(v___x_1614_, 1);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; 
v_unused_1679_ = lean_ctor_get(v___x_1614_, 0);
lean_dec(v_unused_1679_);
v___x_1620_ = v___x_1614_;
v_isShared_1621_ = v_isSharedCheck_1678_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_snd_1618_);
lean_dec(v___x_1614_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1678_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_str_1622_; lean_object* v_str_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_str_1622_ = lean_ctor_get(v_fst_1615_, 1);
lean_inc_ref(v_str_1622_);
lean_dec_ref_known(v_fst_1615_, 2);
v_str_1623_ = lean_ctor_get(v_pre_1616_, 1);
lean_inc_ref(v_str_1623_);
lean_dec_ref_known(v_pre_1616_, 2);
v___x_1624_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2));
v___x_1625_ = lean_string_dec_eq(v_str_1623_, v___x_1624_);
if (v___x_1625_ == 0)
{
uint8_t v___x_1626_; 
lean_del_object(v___x_1620_);
v___x_1626_ = lean_string_dec_eq(v_str_1623_, v___x_1565_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; uint8_t v___x_1628_; 
lean_del_object(v___x_1230_);
v___x_1627_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82));
v___x_1628_ = lean_string_dec_eq(v_str_1623_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79));
v___x_1630_ = lean_string_dec_eq(v_str_1623_, v___x_1629_);
lean_dec_ref(v_str_1623_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; 
lean_dec_ref(v_str_1622_);
lean_dec(v_snd_1618_);
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v_r_1586_);
return v___x_1631_;
}
else
{
lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86));
v___x_1633_ = lean_string_dec_eq(v_str_1622_, v___x_1632_);
lean_dec_ref(v_str_1622_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec(v_snd_1618_);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v_r_1586_);
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = lean_array_get_size(v_snd_1618_);
v___x_1636_ = lean_nat_dec_eq(v___x_1635_, v___x_1580_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; 
lean_dec(v_snd_1618_);
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v_r_1586_);
return v___x_1637_;
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1638_ = lean_array_fget(v_snd_1618_, v___x_1559_);
v___x_1639_ = lean_unsigned_to_nat(1u);
v___x_1640_ = lean_array_fget(v_snd_1618_, v___x_1639_);
lean_dec(v_snd_1618_);
v_n_1588_ = v___x_1638_;
v_x_1589_ = v___x_1640_;
goto v___jp_1587_;
}
}
}
}
else
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
lean_dec_ref(v_str_1623_);
v___x_1641_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87));
v___x_1642_ = lean_string_dec_eq(v_str_1622_, v___x_1641_);
lean_dec_ref(v_str_1622_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; 
lean_dec(v_snd_1618_);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v_r_1586_);
return v___x_1643_;
}
else
{
lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = lean_array_get_size(v_snd_1618_);
v___x_1645_ = lean_nat_dec_eq(v___x_1644_, v___x_1580_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
lean_dec(v_snd_1618_);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_r_1586_);
return v___x_1646_;
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = lean_array_fget(v_snd_1618_, v___x_1559_);
v___x_1648_ = lean_unsigned_to_nat(1u);
v___x_1649_ = lean_array_fget(v_snd_1618_, v___x_1648_);
lean_dec(v_snd_1618_);
v_n_1598_ = v___x_1647_;
v_i_1599_ = v___x_1649_;
goto v___jp_1597_;
}
}
}
}
else
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
lean_dec_ref(v_str_1623_);
v___x_1650_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88));
v___x_1651_ = lean_string_dec_eq(v_str_1622_, v___x_1650_);
lean_dec_ref(v_str_1622_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
lean_dec(v_snd_1618_);
lean_del_object(v___x_1230_);
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v_r_1586_);
return v___x_1652_;
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1653_ = lean_array_get_size(v_snd_1618_);
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = lean_nat_dec_eq(v___x_1653_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_dec(v_snd_1618_);
lean_del_object(v___x_1230_);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v_r_1586_);
return v___x_1656_;
}
else
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_array_fget(v_snd_1618_, v___x_1559_);
lean_dec(v_snd_1618_);
v_x_1608_ = v___x_1657_;
goto v___jp_1607_;
}
}
}
}
else
{
lean_object* v___x_1658_; uint8_t v___x_1659_; 
lean_dec_ref(v_str_1623_);
lean_del_object(v___x_1230_);
v___x_1658_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9));
v___x_1659_ = lean_string_dec_eq(v_str_1622_, v___x_1658_);
lean_dec_ref(v_str_1622_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_del_object(v___x_1620_);
lean_dec(v_snd_1618_);
v___x_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1660_, 0, v_r_1586_);
return v___x_1660_;
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1661_ = lean_array_get_size(v_snd_1618_);
v___x_1662_ = lean_unsigned_to_nat(6u);
v___x_1663_ = lean_nat_dec_eq(v___x_1661_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; 
lean_del_object(v___x_1620_);
lean_dec(v_snd_1618_);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v_r_1586_);
return v___x_1664_;
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1665_ = lean_unsigned_to_nat(4u);
v___x_1666_ = lean_array_fget(v_snd_1618_, v___x_1665_);
v___x_1667_ = lean_unsigned_to_nat(5u);
v___x_1668_ = lean_array_fget(v_snd_1618_, v___x_1667_);
lean_dec(v_snd_1618_);
v___x_1669_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90));
v___x_1670_ = l_Lean_Expr_const___override(v___x_1669_, v_us_1563_);
v___x_1671_ = l_Lean_mkAppB(v___x_1670_, v___x_1666_, v___x_1668_);
v___x_1672_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1671_, v_r_1586_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1674_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set_tag(v___x_1620_, 1);
lean_ctor_set(v___x_1620_, 1, v_r_1586_);
lean_ctor_set(v___x_1620_, 0, v___x_1671_);
v___x_1674_ = v___x_1620_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_r_1586_);
v___x_1674_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
else
{
lean_object* v___x_1677_; 
lean_dec_ref(v___x_1671_);
lean_del_object(v___x_1620_);
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_r_1586_);
return v___x_1677_;
}
}
}
}
}
}
else
{
lean_object* v___x_1680_; 
lean_dec_ref_known(v_pre_1616_, 2);
lean_dec_ref_known(v_fst_1615_, 2);
lean_dec_ref(v___x_1614_);
lean_del_object(v___x_1230_);
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v_r_1586_);
return v___x_1680_;
}
}
else
{
lean_object* v___x_1681_; 
lean_dec_ref_known(v_fst_1615_, 2);
lean_dec(v_pre_1616_);
lean_dec_ref(v___x_1614_);
lean_del_object(v___x_1230_);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v_r_1586_);
return v___x_1681_;
}
}
else
{
lean_object* v___x_1682_; 
lean_dec(v_fst_1615_);
lean_dec_ref(v___x_1614_);
lean_del_object(v___x_1230_);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_r_1586_);
return v___x_1682_;
}
}
else
{
lean_object* v___x_1683_; lean_object* v_fst_1684_; 
v___x_1683_ = l_Lean_Expr_getAppFnArgs(v___x_1581_);
v_fst_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_fst_1684_);
if (lean_obj_tag(v_fst_1684_) == 1)
{
lean_object* v_pre_1685_; 
v_pre_1685_ = lean_ctor_get(v_fst_1684_, 0);
lean_inc(v_pre_1685_);
if (lean_obj_tag(v_pre_1685_) == 1)
{
lean_object* v_pre_1686_; 
v_pre_1686_ = lean_ctor_get(v_pre_1685_, 0);
if (lean_obj_tag(v_pre_1686_) == 0)
{
lean_object* v_snd_1687_; lean_object* v_str_1688_; lean_object* v_str_1689_; uint8_t v___x_1690_; 
v_snd_1687_ = lean_ctor_get(v___x_1683_, 1);
lean_inc(v_snd_1687_);
lean_dec_ref(v___x_1683_);
v_str_1688_ = lean_ctor_get(v_fst_1684_, 1);
lean_inc_ref(v_str_1688_);
lean_dec_ref_known(v_fst_1684_, 2);
v_str_1689_ = lean_ctor_get(v_pre_1685_, 1);
lean_inc_ref(v_str_1689_);
lean_dec_ref_known(v_pre_1685_, 2);
v___x_1690_ = lean_string_dec_eq(v_str_1689_, v___x_1565_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; uint8_t v___x_1692_; 
lean_del_object(v___x_1230_);
v___x_1691_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82));
v___x_1692_ = lean_string_dec_eq(v_str_1689_, v___x_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; uint8_t v___x_1694_; 
v___x_1693_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79));
v___x_1694_ = lean_string_dec_eq(v_str_1689_, v___x_1693_);
lean_dec_ref(v_str_1689_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; 
lean_dec_ref(v_str_1688_);
lean_dec(v_snd_1687_);
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v_r_1586_);
return v___x_1695_;
}
else
{
lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1696_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86));
v___x_1697_ = lean_string_dec_eq(v_str_1688_, v___x_1696_);
lean_dec_ref(v_str_1688_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
lean_dec(v_snd_1687_);
v___x_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1698_, 0, v_r_1586_);
return v___x_1698_;
}
else
{
lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1699_ = lean_array_get_size(v_snd_1687_);
v___x_1700_ = lean_nat_dec_eq(v___x_1699_, v___x_1580_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; 
lean_dec(v_snd_1687_);
v___x_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1701_, 0, v_r_1586_);
return v___x_1701_;
}
else
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_array_fget(v_snd_1687_, v___x_1559_);
v___x_1703_ = lean_unsigned_to_nat(1u);
v___x_1704_ = lean_array_fget(v_snd_1687_, v___x_1703_);
lean_dec(v_snd_1687_);
v_n_1588_ = v___x_1702_;
v_x_1589_ = v___x_1704_;
goto v___jp_1587_;
}
}
}
}
else
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
lean_dec_ref(v_str_1689_);
v___x_1705_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87));
v___x_1706_ = lean_string_dec_eq(v_str_1688_, v___x_1705_);
lean_dec_ref(v_str_1688_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; 
lean_dec(v_snd_1687_);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_r_1586_);
return v___x_1707_;
}
else
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = lean_array_get_size(v_snd_1687_);
v___x_1709_ = lean_nat_dec_eq(v___x_1708_, v___x_1580_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; 
lean_dec(v_snd_1687_);
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_r_1586_);
return v___x_1710_;
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = lean_array_fget(v_snd_1687_, v___x_1559_);
v___x_1712_ = lean_unsigned_to_nat(1u);
v___x_1713_ = lean_array_fget(v_snd_1687_, v___x_1712_);
lean_dec(v_snd_1687_);
v_n_1598_ = v___x_1711_;
v_i_1599_ = v___x_1713_;
goto v___jp_1597_;
}
}
}
}
else
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
lean_dec_ref(v_str_1689_);
v___x_1714_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88));
v___x_1715_ = lean_string_dec_eq(v_str_1688_, v___x_1714_);
lean_dec_ref(v_str_1688_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; 
lean_dec(v_snd_1687_);
lean_del_object(v___x_1230_);
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v_r_1586_);
return v___x_1716_;
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1717_ = lean_array_get_size(v_snd_1687_);
v___x_1718_ = lean_unsigned_to_nat(1u);
v___x_1719_ = lean_nat_dec_eq(v___x_1717_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_dec(v_snd_1687_);
lean_del_object(v___x_1230_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_r_1586_);
return v___x_1720_;
}
else
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_array_fget(v_snd_1687_, v___x_1559_);
lean_dec(v_snd_1687_);
v_x_1608_ = v___x_1721_;
goto v___jp_1607_;
}
}
}
}
else
{
lean_object* v___x_1722_; 
lean_dec_ref_known(v_pre_1685_, 2);
lean_dec_ref_known(v_fst_1684_, 2);
lean_dec_ref(v___x_1683_);
lean_del_object(v___x_1230_);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_r_1586_);
return v___x_1722_;
}
}
else
{
lean_object* v___x_1723_; 
lean_dec(v_pre_1685_);
lean_dec_ref_known(v_fst_1684_, 2);
lean_dec_ref(v___x_1683_);
lean_del_object(v___x_1230_);
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v_r_1586_);
return v___x_1723_;
}
}
else
{
lean_object* v___x_1724_; 
lean_dec(v_fst_1684_);
lean_dec_ref(v___x_1683_);
lean_del_object(v___x_1230_);
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_r_1586_);
return v___x_1724_;
}
}
v___jp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1590_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81));
v___x_1591_ = l_Lean_Expr_const___override(v___x_1590_, v_us_1563_);
v___x_1592_ = l_Lean_mkAppB(v___x_1591_, v_n_1588_, v_x_1589_);
v___x_1593_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1592_, v_r_1586_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v_r_1586_);
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
return v___x_1595_;
}
else
{
lean_object* v___x_1596_; 
lean_dec_ref(v___x_1592_);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v_r_1586_);
return v___x_1596_;
}
}
v___jp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83));
v___x_1601_ = l_Lean_Expr_const___override(v___x_1600_, v_us_1563_);
v___x_1602_ = l_Lean_mkAppB(v___x_1601_, v_n_1598_, v_i_1599_);
v___x_1603_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1602_, v_r_1586_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v_r_1586_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; 
lean_dec_ref(v___x_1602_);
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_r_1586_);
return v___x_1606_;
}
}
v___jp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1609_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85));
v___x_1610_ = l_Lean_Expr_const___override(v___x_1609_, v_us_1563_);
lean_inc_ref(v_x_1608_);
v___x_1611_ = l_Lean_Expr_app___override(v___x_1610_, v_x_1608_);
v___x_1612_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1611_, v_r_1586_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v_r_1586_);
v___y_1567_ = v_x_1608_;
v___y_1568_ = v___x_1613_;
goto v___jp_1566_;
}
else
{
lean_dec_ref(v___x_1611_);
v___y_1567_ = v_x_1608_;
v___y_1568_ = v_r_1586_;
goto v___jp_1566_;
}
}
}
else
{
lean_dec(v_us_1563_);
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
}
v___jp_1566_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1569_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76));
v___x_1570_ = l_Lean_Expr_const___override(v___x_1569_, v_us_1563_);
v___x_1571_ = l_Lean_Expr_app___override(v___x_1570_, v___y_1567_);
v___x_1572_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1571_, v___y_1568_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1574_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 1);
lean_ctor_set(v___x_1230_, 1, v___y_1568_);
lean_ctor_set(v___x_1230_, 0, v___x_1571_);
v___x_1574_ = v___x_1230_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v___y_1568_);
v___x_1574_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
}
else
{
lean_object* v___x_1577_; 
lean_dec_ref(v___x_1571_);
lean_del_object(v___x_1230_);
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___y_1568_);
return v___x_1577_;
}
}
}
else
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
}
else
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
}
else
{
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
goto v___jp_1212_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1226_, 2);
lean_dec_ref_known(v_fst_1225_, 2);
lean_dec_ref(v___x_1224_);
goto v___jp_1212_;
}
}
case 0:
{
lean_object* v_snd_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1757_; 
v_snd_1727_ = lean_ctor_get(v___x_1224_, 1);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; 
v_unused_1758_ = lean_ctor_get(v___x_1224_, 0);
lean_dec(v_unused_1758_);
v___x_1729_ = v___x_1224_;
v_isShared_1730_ = v_isSharedCheck_1757_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_snd_1727_);
lean_dec(v___x_1224_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1757_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v_str_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_str_1731_ = lean_ctor_get(v_fst_1225_, 1);
lean_inc_ref(v_str_1731_);
lean_dec_ref_known(v_fst_1225_, 2);
v___x_1732_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91));
v___x_1733_ = lean_string_dec_eq(v_str_1731_, v___x_1732_);
lean_dec_ref(v_str_1731_);
if (v___x_1733_ == 0)
{
lean_del_object(v___x_1729_);
lean_dec(v_snd_1727_);
goto v___jp_1212_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1734_ = lean_array_get_size(v_snd_1727_);
v___x_1735_ = lean_unsigned_to_nat(5u);
v___x_1736_ = lean_nat_dec_eq(v___x_1734_, v___x_1735_);
if (v___x_1736_ == 0)
{
lean_del_object(v___x_1729_);
lean_dec(v_snd_1727_);
goto v___jp_1212_;
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1737_ = lean_unsigned_to_nat(0u);
v___x_1738_ = lean_array_fget(v_snd_1727_, v___x_1737_);
v___x_1739_ = lean_box(0);
v___x_1740_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1741_ = lean_expr_eqv(v___x_1738_, v___x_1740_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; 
lean_dec(v___x_1738_);
lean_del_object(v___x_1729_);
lean_dec(v_snd_1727_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1739_);
return v___x_1742_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1743_ = lean_unsigned_to_nat(1u);
v___x_1744_ = lean_array_fget(v_snd_1727_, v___x_1743_);
v___x_1745_ = lean_unsigned_to_nat(2u);
v___x_1746_ = lean_array_fget(v_snd_1727_, v___x_1745_);
v___x_1747_ = lean_unsigned_to_nat(3u);
v___x_1748_ = lean_array_fget(v_snd_1727_, v___x_1747_);
v___x_1749_ = lean_unsigned_to_nat(4u);
v___x_1750_ = lean_array_fget(v_snd_1727_, v___x_1749_);
lean_dec(v_snd_1727_);
v___x_1751_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94);
v___x_1752_ = l_Lean_mkApp5(v___x_1751_, v___x_1738_, v___x_1744_, v___x_1746_, v___x_1748_, v___x_1750_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set_tag(v___x_1729_, 1);
lean_ctor_set(v___x_1729_, 1, v___x_1739_);
lean_ctor_set(v___x_1729_, 0, v___x_1752_);
v___x_1754_ = v___x_1729_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v___x_1739_);
v___x_1754_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_fst_1225_, 2);
lean_dec_ref(v___x_1224_);
goto v___jp_1212_;
}
}
}
else
{
lean_dec(v_fst_1225_);
lean_dec_ref(v___x_1224_);
goto v___jp_1212_;
}
v___jp_1206_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
v___jp_1209_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_box(0);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
v___jp_1212_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_box(0);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
v___jp_1215_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
v___jp_1218_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_box(0);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
v___jp_1221_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(lean_object* v_e_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_e_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
lean_dec(v_a_1762_);
lean_dec_ref(v_a_1761_);
lean_dec_ref(v_a_1760_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object* v_e_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, uint8_t v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_e_1767_, v_a_1770_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object* v_e_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
uint8_t v_a_boxed_1790_; lean_object* v_res_1791_; 
v_a_boxed_1790_ = lean_unbox(v_a_1783_);
v_res_1791_ = l_Lean_Elab_Tactic_Omega_analyzeAtom(v_e_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_boxed_1790_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec(v_a_1780_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(lean_object* v_m_1792_, lean_object* v_query_1793_, lean_object* v_x_1794_, lean_object* v_x_1795_, lean_object* v_x_1796_){
_start:
{
lean_object* v_zero_1797_; uint8_t v_isZero_1798_; 
v_zero_1797_ = lean_unsigned_to_nat(0u);
v_isZero_1798_ = lean_nat_dec_eq(v_x_1795_, v_zero_1797_);
if (v_isZero_1798_ == 1)
{
lean_dec(v_x_1796_);
lean_dec(v_x_1795_);
if (lean_obj_tag(v_x_1794_) == 0)
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_box(2);
return v___x_1799_;
}
else
{
lean_object* v_val_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
v_val_1800_ = lean_ctor_get(v_x_1794_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_x_1794_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v_x_1794_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_val_1800_);
lean_dec(v_x_1794_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_val_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_object* v_keyArray_1808_; lean_object* v_valueArray_1809_; lean_object* v___x_1810_; uint8_t v_isSome_1811_; 
v_keyArray_1808_ = lean_ctor_get(v_m_1792_, 1);
v_valueArray_1809_ = lean_ctor_get(v_m_1792_, 2);
v___x_1810_ = lean_array_fget_borrowed(v_keyArray_1808_, v_x_1796_);
v_isSome_1811_ = lean_noption_is_some(v___x_1810_);
if (v_isSome_1811_ == 0)
{
lean_dec(v_x_1795_);
if (lean_obj_tag(v_x_1794_) == 0)
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1812_, 0, v_x_1796_);
return v___x_1812_;
}
else
{
lean_object* v_val_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec(v_x_1796_);
v_val_1813_ = lean_ctor_get(v_x_1794_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_x_1794_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v_x_1794_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_val_1813_);
lean_dec(v_x_1794_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_val_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
lean_object* v_one_1821_; lean_object* v_n_1822_; lean_object* v___y_1824_; 
v_one_1821_ = lean_unsigned_to_nat(1u);
v_n_1822_ = lean_nat_sub(v_x_1795_, v_one_1821_);
lean_dec(v_x_1795_);
if (v_isSome_1811_ == 0)
{
goto v___jp_1830_;
}
else
{
lean_object* v___x_1832_; uint8_t v_isSome_1833_; 
v___x_1832_ = lean_array_fget_borrowed(v_valueArray_1809_, v_x_1796_);
v_isSome_1833_ = lean_noption_is_some(v___x_1832_);
if (v_isSome_1833_ == 0)
{
goto v___jp_1830_;
}
else
{
lean_object* v_val_1834_; uint8_t v___x_1835_; 
lean_inc(v___x_1810_);
v_val_1834_ = lean_noption_get(v___x_1810_);
v___x_1835_ = lean_expr_eqv(v_val_1834_, v_query_1793_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
lean_dec(v_val_1834_);
v___x_1836_ = lean_array_get_size(v_keyArray_1808_);
v___x_1837_ = lean_nat_add(v_x_1796_, v_one_1821_);
lean_dec(v_x_1796_);
v___x_1838_ = lean_nat_dec_lt(v___x_1837_, v___x_1836_);
if (v___x_1838_ == 0)
{
lean_dec(v___x_1837_);
v_x_1795_ = v_n_1822_;
v_x_1796_ = v_zero_1797_;
goto _start;
}
else
{
v_x_1795_ = v_n_1822_;
v_x_1796_ = v___x_1837_;
goto _start;
}
}
else
{
lean_object* v_val_1841_; lean_object* v___x_1842_; 
lean_dec(v_n_1822_);
lean_dec(v_x_1794_);
lean_inc(v___x_1832_);
v_val_1841_ = lean_noption_get(v___x_1832_);
v___x_1842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1842_, 0, v_x_1796_);
lean_ctor_set(v___x_1842_, 1, v_val_1834_);
lean_ctor_set(v___x_1842_, 2, v_val_1841_);
return v___x_1842_;
}
}
}
v___jp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1825_ = lean_array_get_size(v_keyArray_1808_);
v___x_1826_ = lean_nat_add(v_x_1796_, v_one_1821_);
lean_dec(v_x_1796_);
v___x_1827_ = lean_nat_dec_lt(v___x_1826_, v___x_1825_);
if (v___x_1827_ == 0)
{
lean_dec(v___x_1826_);
v_x_1794_ = v___y_1824_;
v_x_1795_ = v_n_1822_;
v_x_1796_ = v_zero_1797_;
goto _start;
}
else
{
v_x_1794_ = v___y_1824_;
v_x_1795_ = v_n_1822_;
v_x_1796_ = v___x_1826_;
goto _start;
}
}
v___jp_1830_:
{
if (lean_obj_tag(v_x_1794_) == 0)
{
lean_object* v___x_1831_; 
lean_inc(v_x_1796_);
v___x_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1831_, 0, v_x_1796_);
v___y_1824_ = v___x_1831_;
goto v___jp_1823_;
}
else
{
v___y_1824_ = v_x_1794_;
goto v___jp_1823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg___boxed(lean_object* v_m_1843_, lean_object* v_query_1844_, lean_object* v_x_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_m_1843_, v_query_1844_, v_x_1845_, v_x_1846_, v_x_1847_);
lean_dec_ref(v_query_1844_);
lean_dec_ref(v_m_1843_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object* v_m_1849_, lean_object* v_query_1850_){
_start:
{
lean_object* v_keyArray_1851_; lean_object* v___x_1852_; uint64_t v___x_1853_; uint64_t v___x_1854_; uint64_t v___x_1855_; uint64_t v_fold_1856_; uint64_t v___x_1857_; uint64_t v___x_1858_; uint64_t v___x_1859_; size_t v___x_1860_; size_t v___x_1861_; size_t v___x_1862_; size_t v___x_1863_; size_t v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_keyArray_1851_ = lean_ctor_get(v_m_1849_, 1);
v___x_1852_ = lean_array_get_size(v_keyArray_1851_);
v___x_1853_ = l_Lean_Expr_hash(v_query_1850_);
v___x_1854_ = 32ULL;
v___x_1855_ = lean_uint64_shift_right(v___x_1853_, v___x_1854_);
v_fold_1856_ = lean_uint64_xor(v___x_1853_, v___x_1855_);
v___x_1857_ = 16ULL;
v___x_1858_ = lean_uint64_shift_right(v_fold_1856_, v___x_1857_);
v___x_1859_ = lean_uint64_xor(v_fold_1856_, v___x_1858_);
v___x_1860_ = lean_uint64_to_usize(v___x_1859_);
v___x_1861_ = lean_usize_of_nat(v___x_1852_);
v___x_1862_ = ((size_t)1ULL);
v___x_1863_ = lean_usize_sub(v___x_1861_, v___x_1862_);
v___x_1864_ = lean_usize_land(v___x_1860_, v___x_1863_);
v___x_1865_ = lean_usize_to_nat(v___x_1864_);
v___x_1866_ = lean_box(0);
v___x_1867_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_m_1849_, v_query_1850_, v___x_1866_, v___x_1852_, v___x_1865_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg___boxed(lean_object* v_m_1868_, lean_object* v_query_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v_m_1868_, v_query_1869_);
lean_dec_ref(v_query_1869_);
lean_dec_ref(v_m_1868_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(lean_object* v_m_1871_, lean_object* v_query_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v_m_1871_, v_query_1872_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_index_1874_; lean_object* v_key_1875_; lean_object* v_value_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
v_index_1874_ = lean_ctor_get(v___x_1873_, 0);
v_key_1875_ = lean_ctor_get(v___x_1873_, 1);
v_value_1876_ = lean_ctor_get(v___x_1873_, 2);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1873_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_value_1876_);
lean_inc(v_key_1875_);
lean_inc(v_index_1874_);
lean_dec(v___x_1873_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_index_1874_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_key_1875_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v_value_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
else
{
lean_object* v___x_1884_; 
lean_dec(v___x_1873_);
v___x_1884_ = lean_box(1);
return v___x_1884_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg___boxed(lean_object* v_m_1885_, lean_object* v_query_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_m_1885_, v_query_1886_);
lean_dec_ref(v_query_1886_);
lean_dec_ref(v_m_1885_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object* v_m_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_m_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_value_1891_; lean_object* v___x_1892_; 
v_value_1891_ = lean_ctor_get(v___x_1890_, 2);
lean_inc(v_value_1891_);
lean_dec_ref_known(v___x_1890_, 3);
v___x_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1892_, 0, v_value_1891_);
return v___x_1892_;
}
else
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_box(0);
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(lean_object* v_m_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_1894_, v_a_1895_);
lean_dec_ref(v_a_1895_);
lean_dec_ref(v_m_1894_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg(lean_object* v_x_1897_, lean_object* v_x_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
if (lean_obj_tag(v_x_1897_) == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = l_List_reverse___redArg(v_x_1898_);
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
return v___x_1905_;
}
else
{
lean_object* v_head_1906_; lean_object* v_tail_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1925_; 
v_head_1906_ = lean_ctor_get(v_x_1897_, 0);
v_tail_1907_ = lean_ctor_get(v_x_1897_, 1);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_x_1897_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1909_ = v_x_1897_;
v_isShared_1910_ = v_isSharedCheck_1925_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_tail_1907_);
lean_inc(v_head_1906_);
lean_dec(v_x_1897_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1925_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; 
lean_inc(v___y_1902_);
lean_inc_ref(v___y_1901_);
lean_inc(v___y_1900_);
lean_inc_ref(v___y_1899_);
v___x_1911_ = lean_infer_type(v_head_1906_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 1, v_x_1898_);
lean_ctor_set(v___x_1909_, 0, v_a_1912_);
v___x_1914_ = v___x_1909_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1912_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_x_1898_);
v___x_1914_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
v_x_1897_ = v_tail_1907_;
v_x_1898_ = v___x_1914_;
goto _start;
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_del_object(v___x_1909_);
lean_dec(v_tail_1907_);
lean_dec(v_x_1898_);
v_a_1917_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1911_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1911_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg___boxed(lean_object* v_x_1926_, lean_object* v_x_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg(v_x_1926_, v_x_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4_spec__5___redArg(lean_object* v_b_1934_, lean_object* v_acc_1935_, lean_object* v_i_1936_){
_start:
{
lean_object* v___y_1938_; lean_object* v_keyArray_1946_; lean_object* v_valueArray_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v_keyArray_1946_ = lean_ctor_get(v_b_1934_, 1);
v_valueArray_1947_ = lean_ctor_get(v_b_1934_, 2);
v___x_1948_ = lean_array_get_size(v_keyArray_1946_);
v___x_1949_ = lean_nat_dec_lt(v_i_1936_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_dec(v_i_1936_);
return v_acc_1935_;
}
else
{
lean_object* v___x_1950_; uint8_t v_isSome_1951_; 
v___x_1950_ = lean_array_fget_borrowed(v_keyArray_1946_, v_i_1936_);
v_isSome_1951_ = lean_noption_is_some(v___x_1950_);
if (v_isSome_1951_ == 0)
{
goto v___jp_1942_;
}
else
{
lean_object* v___x_1952_; uint8_t v_isSome_1953_; 
v___x_1952_ = lean_array_fget_borrowed(v_valueArray_1947_, v_i_1936_);
v_isSome_1953_ = lean_noption_is_some(v___x_1952_);
if (v_isSome_1953_ == 0)
{
goto v___jp_1942_;
}
else
{
lean_object* v_val_1954_; lean_object* v_val_1955_; lean_object* v_i_1957_; lean_object* v___x_1962_; 
lean_inc(v___x_1950_);
v_val_1954_ = lean_noption_get(v___x_1950_);
lean_inc(v___x_1952_);
v_val_1955_ = lean_noption_get(v___x_1952_);
v___x_1962_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v_acc_1935_, v_val_1954_);
switch(lean_obj_tag(v___x_1962_))
{
case 0:
{
lean_object* v_index_1963_; lean_object* v_size_1964_; lean_object* v___x_1965_; 
v_index_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_index_1963_);
lean_dec_ref_known(v___x_1962_, 3);
v_size_1964_ = lean_ctor_get(v_acc_1935_, 0);
lean_inc(v_size_1964_);
v___x_1965_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1935_, v_size_1964_, v_index_1963_, v_val_1954_, v_val_1955_);
lean_dec(v_index_1963_);
v___y_1938_ = v___x_1965_;
goto v___jp_1937_;
}
case 1:
{
lean_object* v_index_1966_; 
v_index_1966_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_index_1966_);
lean_dec_ref_known(v___x_1962_, 1);
v_i_1957_ = v_index_1966_;
goto v___jp_1956_;
}
default: 
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1935_, v___x_1967_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_index_1969_; 
v_index_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_index_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v_i_1957_ = v_index_1969_;
goto v___jp_1956_;
}
else
{
lean_dec(v_val_1955_);
lean_dec(v_val_1954_);
v___y_1938_ = v_acc_1935_;
goto v___jp_1937_;
}
}
}
v___jp_1956_:
{
lean_object* v_size_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v_size_1958_ = lean_ctor_get(v_acc_1935_, 0);
v___x_1959_ = lean_unsigned_to_nat(1u);
v___x_1960_ = lean_nat_add(v_size_1958_, v___x_1959_);
v___x_1961_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1935_, v___x_1960_, v_i_1957_, v_val_1954_, v_val_1955_);
lean_dec(v_i_1957_);
v___y_1938_ = v___x_1961_;
goto v___jp_1937_;
}
}
}
}
v___jp_1937_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_unsigned_to_nat(1u);
v___x_1940_ = lean_nat_add(v_i_1936_, v___x_1939_);
lean_dec(v_i_1936_);
v_acc_1935_ = v___y_1938_;
v_i_1936_ = v___x_1940_;
goto _start;
}
v___jp_1942_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = lean_unsigned_to_nat(1u);
v___x_1944_ = lean_nat_add(v_i_1936_, v___x_1943_);
lean_dec(v_i_1936_);
v_i_1936_ = v___x_1944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_1970_, lean_object* v_acc_1971_, lean_object* v_i_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4_spec__5___redArg(v_b_1970_, v_acc_1971_, v_i_1972_);
lean_dec_ref(v_b_1970_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4___redArg(lean_object* v_init_1974_, lean_object* v_b_1975_){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_unsigned_to_nat(0u);
v___x_1977_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4_spec__5___redArg(v_b_1975_, v_init_1974_, v___x_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4___redArg___boxed(lean_object* v_init_1978_, lean_object* v_b_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4___redArg(v_init_1978_, v_b_1979_);
lean_dec_ref(v_b_1979_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object* v_m_1981_){
_start:
{
lean_object* v_keyArray_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v_cellCount_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v_target_1989_; lean_object* v___x_1990_; 
v_keyArray_1982_ = lean_ctor_get(v_m_1981_, 1);
v___x_1983_ = lean_array_get_size(v_keyArray_1982_);
v___x_1984_ = lean_unsigned_to_nat(2u);
v_cellCount_1985_ = lean_nat_mul(v___x_1983_, v___x_1984_);
v___x_1986_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1985_);
v___x_1987_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1985_);
v___x_1988_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1985_);
v_target_1989_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1989_, 0, v___x_1986_);
lean_ctor_set(v_target_1989_, 1, v___x_1987_);
lean_ctor_set(v_target_1989_, 2, v___x_1988_);
v___x_1990_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4___redArg(v_target_1989_, v_m_1981_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(lean_object* v_m_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_m_1991_);
lean_dec_ref(v_m_1991_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
if (lean_obj_tag(v_a_1993_) == 0)
{
lean_object* v___x_1995_; 
v___x_1995_ = l_List_reverse___redArg(v_a_1994_);
return v___x_1995_;
}
else
{
lean_object* v_head_1996_; lean_object* v_tail_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2006_; 
v_head_1996_ = lean_ctor_get(v_a_1993_, 0);
v_tail_1997_ = lean_ctor_get(v_a_1993_, 1);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_a_1993_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1999_ = v_a_1993_;
v_isShared_2000_ = v_isSharedCheck_2006_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_tail_1997_);
lean_inc(v_head_1996_);
lean_dec(v_a_1993_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2006_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; lean_object* v___x_2003_; 
v___x_2001_ = l_Lean_MessageData_ofExpr(v_head_1996_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 1, v_a_1994_);
lean_ctor_set(v___x_1999_, 0, v___x_2001_);
v___x_2003_ = v___x_1999_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_a_1994_);
v___x_2003_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
v_a_1993_ = v_tail_1997_;
v_a_1994_ = v___x_2003_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5_spec__8(lean_object* v_msgData_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; lean_object* v_env_2014_; lean_object* v___x_2015_; lean_object* v_mctx_2016_; lean_object* v_lctx_2017_; lean_object* v_options_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2013_ = lean_st_ref_get(v___y_2011_);
v_env_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc_ref(v_env_2014_);
lean_dec(v___x_2013_);
v___x_2015_ = lean_st_ref_get(v___y_2009_);
v_mctx_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_ref(v_mctx_2016_);
lean_dec(v___x_2015_);
v_lctx_2017_ = lean_ctor_get(v___y_2008_, 2);
v_options_2018_ = lean_ctor_get(v___y_2010_, 2);
lean_inc_ref(v_options_2018_);
lean_inc_ref(v_lctx_2017_);
v___x_2019_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2019_, 0, v_env_2014_);
lean_ctor_set(v___x_2019_, 1, v_mctx_2016_);
lean_ctor_set(v___x_2019_, 2, v_lctx_2017_);
lean_ctor_set(v___x_2019_, 3, v_options_2018_);
v___x_2020_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v_msgData_2007_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5_spec__8___boxed(lean_object* v_msgData_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5_spec__8(v_msgData_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
return v_res_2028_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2029_; double v___x_2030_; 
v___x_2029_ = lean_unsigned_to_nat(0u);
v___x_2030_ = lean_float_of_nat(v___x_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(lean_object* v_cls_2034_, lean_object* v_msg_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_ref_2041_; lean_object* v___x_2042_; lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2087_; 
v_ref_2041_ = lean_ctor_get(v___y_2038_, 5);
v___x_2042_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5_spec__8(v_msg_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2087_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2087_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v_traceState_2048_; lean_object* v_env_2049_; lean_object* v_nextMacroScope_2050_; lean_object* v_ngen_2051_; lean_object* v_auxDeclNGen_2052_; lean_object* v_cache_2053_; lean_object* v_messages_2054_; lean_object* v_infoState_2055_; lean_object* v_snapshotTasks_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2086_; 
v___x_2047_ = lean_st_ref_take(v___y_2039_);
v_traceState_2048_ = lean_ctor_get(v___x_2047_, 4);
v_env_2049_ = lean_ctor_get(v___x_2047_, 0);
v_nextMacroScope_2050_ = lean_ctor_get(v___x_2047_, 1);
v_ngen_2051_ = lean_ctor_get(v___x_2047_, 2);
v_auxDeclNGen_2052_ = lean_ctor_get(v___x_2047_, 3);
v_cache_2053_ = lean_ctor_get(v___x_2047_, 5);
v_messages_2054_ = lean_ctor_get(v___x_2047_, 6);
v_infoState_2055_ = lean_ctor_get(v___x_2047_, 7);
v_snapshotTasks_2056_ = lean_ctor_get(v___x_2047_, 8);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2058_ = v___x_2047_;
v_isShared_2059_ = v_isSharedCheck_2086_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_snapshotTasks_2056_);
lean_inc(v_infoState_2055_);
lean_inc(v_messages_2054_);
lean_inc(v_cache_2053_);
lean_inc(v_traceState_2048_);
lean_inc(v_auxDeclNGen_2052_);
lean_inc(v_ngen_2051_);
lean_inc(v_nextMacroScope_2050_);
lean_inc(v_env_2049_);
lean_dec(v___x_2047_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2086_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
uint64_t v_tid_2060_; lean_object* v_traces_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2085_; 
v_tid_2060_ = lean_ctor_get_uint64(v_traceState_2048_, sizeof(void*)*1);
v_traces_2061_ = lean_ctor_get(v_traceState_2048_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_traceState_2048_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2063_ = v_traceState_2048_;
v_isShared_2064_ = v_isSharedCheck_2085_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_traces_2061_);
lean_dec(v_traceState_2048_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2085_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; double v___x_2066_; uint8_t v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2065_ = lean_box(0);
v___x_2066_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__0);
v___x_2067_ = 0;
v___x_2068_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__1));
v___x_2069_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2069_, 0, v_cls_2034_);
lean_ctor_set(v___x_2069_, 1, v___x_2065_);
lean_ctor_set(v___x_2069_, 2, v___x_2068_);
lean_ctor_set_float(v___x_2069_, sizeof(void*)*3, v___x_2066_);
lean_ctor_set_float(v___x_2069_, sizeof(void*)*3 + 8, v___x_2066_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*3 + 16, v___x_2067_);
v___x_2070_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__2));
v___x_2071_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v_a_2043_);
lean_ctor_set(v___x_2071_, 2, v___x_2070_);
lean_inc(v_ref_2041_);
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v_ref_2041_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = l_Lean_PersistentArray_push___redArg(v_traces_2061_, v___x_2072_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v___x_2073_);
v___x_2075_ = v___x_2063_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2073_);
lean_ctor_set_uint64(v_reuseFailAlloc_2084_, sizeof(void*)*1, v_tid_2060_);
v___x_2075_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2077_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 4, v___x_2075_);
v___x_2077_ = v___x_2058_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_env_2049_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_nextMacroScope_2050_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_ngen_2051_);
lean_ctor_set(v_reuseFailAlloc_2083_, 3, v_auxDeclNGen_2052_);
lean_ctor_set(v_reuseFailAlloc_2083_, 4, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2083_, 5, v_cache_2053_);
lean_ctor_set(v_reuseFailAlloc_2083_, 6, v_messages_2054_);
lean_ctor_set(v_reuseFailAlloc_2083_, 7, v_infoState_2055_);
lean_ctor_set(v_reuseFailAlloc_2083_, 8, v_snapshotTasks_2056_);
v___x_2077_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2078_ = lean_st_ref_put(v___y_2039_, v___x_2077_);
v___x_2079_ = lean_box(0);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2079_);
v___x_2081_ = v___x_2045_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___boxed(lean_object* v_cls_2088_, lean_object* v_msg_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(v_cls_2088_, v_msg_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
return v_res_2095_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__1));
v___x_2103_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__3));
v___x_2104_ = l_Lean_Name_append(v___x_2103_, v___x_2102_);
return v___x_2104_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__5));
v___x_2107_ = l_Lean_stringToMessageData(v___x_2106_);
return v___x_2107_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__7));
v___x_2110_ = l_Lean_stringToMessageData(v___x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object* v_e_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, uint8_t v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_st_ref_get(v_a_2113_);
v___x_2132_ = l_Lean_Meta_Canonicalizer_canon(v_e_2111_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2291_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2291_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2291_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v_i_2142_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v_i_2165_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___x_2215_; 
v___x_2215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v___x_2131_, v_a_2133_);
lean_dec(v___x_2131_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_options_2216_; lean_object* v_inheritedTraceOptions_2217_; uint8_t v_hasTrace_2218_; lean_object* v___x_2219_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; uint8_t v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; 
lean_del_object(v___x_2135_);
v_options_2216_ = lean_ctor_get(v_a_2119_, 2);
v_inheritedTraceOptions_2217_ = lean_ctor_get(v_a_2119_, 13);
v_hasTrace_2218_ = lean_ctor_get_uint8(v_options_2216_, sizeof(void*)*1);
v___x_2219_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__1));
if (v_hasTrace_2218_ == 0)
{
v___y_2221_ = v_a_2112_;
v___y_2222_ = v_a_2113_;
v___y_2223_ = v_a_2114_;
v___y_2224_ = v_a_2115_;
v___y_2225_ = v_a_2116_;
v___y_2226_ = v_a_2117_;
v___y_2227_ = v_a_2118_;
v___y_2228_ = v_a_2119_;
v___y_2229_ = v_a_2120_;
goto v___jp_2220_;
}
else
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__4, &l_Lean_Elab_Tactic_Omega_lookup___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4);
v___x_2272_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2217_, v_options_2216_, v___x_2271_);
if (v___x_2272_ == 0)
{
v___y_2221_ = v_a_2112_;
v___y_2222_ = v_a_2113_;
v___y_2223_ = v_a_2114_;
v___y_2224_ = v_a_2115_;
v___y_2225_ = v_a_2116_;
v___y_2226_ = v_a_2117_;
v___y_2227_ = v_a_2118_;
v___y_2228_ = v_a_2119_;
v___y_2229_ = v_a_2120_;
goto v___jp_2220_;
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2273_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__8, &l_Lean_Elab_Tactic_Omega_lookup___closed__8_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8);
lean_inc(v_a_2133_);
v___x_2274_ = l_Lean_MessageData_ofExpr(v_a_2133_);
v___x_2275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2273_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(v___x_2219_, v___x_2275_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_dec_ref_known(v___x_2276_, 1);
v___y_2221_ = v_a_2112_;
v___y_2222_ = v_a_2113_;
v___y_2223_ = v_a_2114_;
v___y_2224_ = v_a_2115_;
v___y_2225_ = v_a_2116_;
v___y_2226_ = v_a_2117_;
v___y_2227_ = v_a_2118_;
v___y_2228_ = v_a_2119_;
v___y_2229_ = v_a_2120_;
goto v___jp_2220_;
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v_a_2133_);
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
v___jp_2220_:
{
lean_object* v___x_2230_; 
lean_inc(v_a_2133_);
v___x_2230_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_a_2133_, v___y_2223_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_options_2231_; uint8_t v_hasTrace_2232_; 
v_options_2231_ = lean_ctor_get(v___y_2228_, 2);
v_hasTrace_2232_ = lean_ctor_get_uint8(v_options_2231_, sizeof(void*)*1);
if (v_hasTrace_2232_ == 0)
{
lean_object* v_a_2233_; 
v_a_2233_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2230_, 1);
v___y_2185_ = v_a_2233_;
v___y_2186_ = v___y_2222_;
goto v___jp_2184_;
}
else
{
lean_object* v_a_2234_; lean_object* v_inheritedTraceOptions_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; 
v_a_2234_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2230_, 1);
v_inheritedTraceOptions_2235_ = lean_ctor_get(v___y_2228_, 13);
v___x_2236_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__4, &l_Lean_Elab_Tactic_Omega_lookup___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4);
v___x_2237_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2235_, v_options_2231_, v___x_2236_);
if (v___x_2237_ == 0)
{
v___y_2185_ = v_a_2234_;
v___y_2186_ = v___y_2222_;
goto v___jp_2184_;
}
else
{
uint8_t v___x_2238_; 
v___x_2238_ = l_List_isEmpty___redArg(v_a_2234_);
if (v___x_2238_ == 0)
{
if (v___x_2237_ == 0)
{
v___y_2185_ = v_a_2234_;
v___y_2186_ = v___y_2222_;
goto v___jp_2184_;
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_box(0);
lean_inc(v_a_2234_);
v___x_2240_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg(v_a_2234_, v___x_2239_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
v___x_2242_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__6, &l_Lean_Elab_Tactic_Omega_lookup___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6);
v___x_2243_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(v_a_2241_, v___x_2239_);
v___x_2244_ = l_Lean_MessageData_ofList(v___x_2243_);
v___x_2245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2242_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(v___x_2219_, v___x_2245_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_dec_ref_known(v___x_2246_, 1);
v___y_2185_ = v_a_2234_;
v___y_2186_ = v___y_2222_;
goto v___jp_2184_;
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_a_2234_);
lean_dec(v_a_2133_);
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_a_2234_);
lean_dec(v_a_2133_);
v_a_2255_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2240_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2240_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
else
{
v___y_2185_ = v_a_2234_;
v___y_2186_ = v___y_2222_;
goto v___jp_2184_;
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_a_2133_);
v_a_2263_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2230_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2230_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
}
else
{
lean_object* v_val_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
lean_dec(v_a_2133_);
v_val_2285_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_val_2285_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2286_ = lean_box(0);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v_val_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2287_);
v___x_2289_ = v___x_2135_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
v___jp_2137_:
{
lean_object* v_size_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_size_2143_ = lean_ctor_get(v___y_2140_, 0);
v___x_2144_ = lean_unsigned_to_nat(1u);
v___x_2145_ = lean_nat_add(v_size_2143_, v___x_2144_);
lean_inc(v___y_2138_);
v___x_2146_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2140_, v___x_2145_, v_i_2142_, v_a_2133_, v___y_2138_);
lean_dec(v_i_2142_);
v___y_2123_ = v___y_2138_;
v___y_2124_ = v___y_2139_;
v___y_2125_ = v___y_2141_;
v___y_2126_ = v___x_2146_;
goto v___jp_2122_;
}
v___jp_2147_:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v___y_2151_, v_a_2133_);
switch(lean_obj_tag(v___x_2152_))
{
case 0:
{
lean_object* v_index_2153_; lean_object* v_size_2154_; lean_object* v___x_2155_; 
v_index_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_index_2153_);
lean_dec_ref_known(v___x_2152_, 3);
v_size_2154_ = lean_ctor_get(v___y_2151_, 0);
lean_inc(v_size_2154_);
lean_inc(v___y_2148_);
v___x_2155_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2151_, v_size_2154_, v_index_2153_, v_a_2133_, v___y_2148_);
lean_dec(v_index_2153_);
v___y_2123_ = v___y_2148_;
v___y_2124_ = v___y_2149_;
v___y_2125_ = v___y_2150_;
v___y_2126_ = v___x_2155_;
goto v___jp_2122_;
}
case 1:
{
lean_object* v_index_2156_; 
v_index_2156_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_index_2156_);
lean_dec_ref_known(v___x_2152_, 1);
v___y_2138_ = v___y_2148_;
v___y_2139_ = v___y_2149_;
v___y_2140_ = v___y_2151_;
v___y_2141_ = v___y_2150_;
v_i_2142_ = v_index_2156_;
goto v___jp_2137_;
}
default: 
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_unsigned_to_nat(0u);
v___x_2158_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2151_, v___x_2157_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_index_2159_; 
v_index_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_index_2159_);
lean_dec_ref_known(v___x_2158_, 1);
v___y_2138_ = v___y_2148_;
v___y_2139_ = v___y_2149_;
v___y_2140_ = v___y_2151_;
v___y_2141_ = v___y_2150_;
v_i_2142_ = v_index_2159_;
goto v___jp_2137_;
}
else
{
lean_dec(v_a_2133_);
v___y_2123_ = v___y_2148_;
v___y_2124_ = v___y_2149_;
v___y_2125_ = v___y_2150_;
v___y_2126_ = v___y_2151_;
goto v___jp_2122_;
}
}
}
}
v___jp_2160_:
{
lean_object* v_size_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v_size_2166_ = lean_ctor_get(v___y_2162_, 0);
v___x_2167_ = lean_unsigned_to_nat(1u);
v___x_2168_ = lean_nat_add(v_size_2166_, v___x_2167_);
lean_inc(v___y_2161_);
v___x_2169_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2162_, v___x_2168_, v_i_2165_, v_a_2133_, v___y_2161_);
lean_dec(v_i_2165_);
v___y_2123_ = v___y_2161_;
v___y_2124_ = v___y_2163_;
v___y_2125_ = v___y_2164_;
v___y_2126_ = v___x_2169_;
goto v___jp_2122_;
}
v___jp_2170_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v___y_2172_);
lean_dec_ref(v___y_2172_);
v___x_2176_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v___x_2175_, v_a_2133_);
switch(lean_obj_tag(v___x_2176_))
{
case 0:
{
lean_object* v_index_2177_; lean_object* v_size_2178_; lean_object* v___x_2179_; 
v_index_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_index_2177_);
lean_dec_ref_known(v___x_2176_, 3);
v_size_2178_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_size_2178_);
lean_inc(v___y_2171_);
v___x_2179_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2175_, v_size_2178_, v_index_2177_, v_a_2133_, v___y_2171_);
lean_dec(v_index_2177_);
v___y_2123_ = v___y_2171_;
v___y_2124_ = v___y_2173_;
v___y_2125_ = v___y_2174_;
v___y_2126_ = v___x_2179_;
goto v___jp_2122_;
}
case 1:
{
lean_object* v_index_2180_; 
v_index_2180_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_index_2180_);
lean_dec_ref_known(v___x_2176_, 1);
v___y_2161_ = v___y_2171_;
v___y_2162_ = v___x_2175_;
v___y_2163_ = v___y_2173_;
v___y_2164_ = v___y_2174_;
v_i_2165_ = v_index_2180_;
goto v___jp_2160_;
}
default: 
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_unsigned_to_nat(0u);
v___x_2182_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2175_, v___x_2181_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_index_2183_; 
v_index_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_index_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___y_2161_ = v___y_2171_;
v___y_2162_ = v___x_2175_;
v___y_2163_ = v___y_2173_;
v___y_2164_ = v___y_2174_;
v_i_2165_ = v_index_2183_;
goto v___jp_2160_;
}
else
{
lean_dec(v_a_2133_);
v___y_2123_ = v___y_2171_;
v___y_2124_ = v___y_2173_;
v___y_2125_ = v___y_2174_;
v___y_2126_ = v___x_2175_;
goto v___jp_2122_;
}
}
}
}
v___jp_2184_:
{
lean_object* v___x_2187_; lean_object* v_size_2188_; lean_object* v_keyArray_2189_; lean_object* v___x_2190_; 
v___x_2187_ = lean_st_ref_take(v___y_2186_);
v_size_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_size_2188_);
v_keyArray_2189_ = lean_ctor_get(v___x_2187_, 1);
lean_inc_ref(v_keyArray_2189_);
v___x_2190_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v___x_2187_, v_a_2133_);
switch(lean_obj_tag(v___x_2190_))
{
case 0:
{
lean_object* v_index_2191_; lean_object* v___x_2192_; 
lean_dec_ref(v_keyArray_2189_);
v_index_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_index_2191_);
lean_dec_ref_known(v___x_2190_, 3);
lean_inc_n(v_size_2188_, 2);
v___x_2192_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2187_, v_size_2188_, v_index_2191_, v_a_2133_, v_size_2188_);
lean_dec(v_index_2191_);
v___y_2123_ = v_size_2188_;
v___y_2124_ = v___y_2185_;
v___y_2125_ = v___y_2186_;
v___y_2126_ = v___x_2192_;
goto v___jp_2122_;
}
case 1:
{
lean_object* v_index_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v_index_2193_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_index_2193_);
lean_dec_ref_known(v___x_2190_, 1);
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_nat_add(v_size_2188_, v___x_2194_);
v___x_2196_ = lean_array_get_size(v_keyArray_2189_);
lean_dec_ref(v_keyArray_2189_);
v___x_2197_ = lean_nat_dec_lt(v___x_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_dec(v___x_2195_);
lean_dec(v_index_2193_);
v___y_2171_ = v_size_2188_;
v___y_2172_ = v___x_2187_;
v___y_2173_ = v___y_2185_;
v___y_2174_ = v___y_2186_;
goto v___jp_2170_;
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2198_ = lean_unsigned_to_nat(4u);
v___x_2199_ = lean_nat_mul(v___x_2195_, v___x_2198_);
v___x_2200_ = lean_unsigned_to_nat(3u);
v___x_2201_ = lean_nat_mul(v___x_2196_, v___x_2200_);
v___x_2202_ = lean_nat_dec_le(v___x_2199_, v___x_2201_);
lean_dec(v___x_2201_);
lean_dec(v___x_2199_);
if (v___x_2202_ == 0)
{
lean_dec(v___x_2195_);
lean_dec(v_index_2193_);
v___y_2171_ = v_size_2188_;
v___y_2172_ = v___x_2187_;
v___y_2173_ = v___y_2185_;
v___y_2174_ = v___y_2186_;
goto v___jp_2170_;
}
else
{
lean_object* v___x_2203_; 
lean_inc(v_size_2188_);
v___x_2203_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2187_, v___x_2195_, v_index_2193_, v_a_2133_, v_size_2188_);
lean_dec(v_index_2193_);
v___y_2123_ = v_size_2188_;
v___y_2124_ = v___y_2185_;
v___y_2125_ = v___y_2186_;
v___y_2126_ = v___x_2203_;
goto v___jp_2122_;
}
}
}
default: 
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2204_ = lean_unsigned_to_nat(1u);
v___x_2205_ = lean_nat_add(v_size_2188_, v___x_2204_);
v___x_2206_ = lean_array_get_size(v_keyArray_2189_);
lean_dec_ref(v_keyArray_2189_);
v___x_2207_ = lean_nat_dec_lt(v___x_2205_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; 
lean_dec(v___x_2205_);
v___x_2208_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v___x_2187_);
lean_dec(v___x_2187_);
v___y_2148_ = v_size_2188_;
v___y_2149_ = v___y_2185_;
v___y_2150_ = v___y_2186_;
v___y_2151_ = v___x_2208_;
goto v___jp_2147_;
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v___x_2209_ = lean_unsigned_to_nat(4u);
v___x_2210_ = lean_nat_mul(v___x_2205_, v___x_2209_);
lean_dec(v___x_2205_);
v___x_2211_ = lean_unsigned_to_nat(3u);
v___x_2212_ = lean_nat_mul(v___x_2206_, v___x_2211_);
v___x_2213_ = lean_nat_dec_le(v___x_2210_, v___x_2212_);
lean_dec(v___x_2212_);
lean_dec(v___x_2210_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v___x_2187_);
lean_dec(v___x_2187_);
v___y_2148_ = v_size_2188_;
v___y_2149_ = v___y_2185_;
v___y_2150_ = v___y_2186_;
v___y_2151_ = v___x_2214_;
goto v___jp_2147_;
}
else
{
v___y_2148_ = v_size_2188_;
v___y_2149_ = v___y_2185_;
v___y_2150_ = v___y_2186_;
v___y_2151_ = v___x_2187_;
goto v___jp_2147_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v___x_2131_);
v_a_2292_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2132_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2132_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
v___jp_2122_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2127_ = lean_st_ref_put(v___y_2125_, v___y_2126_);
v___x_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___y_2124_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___y_2123_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
return v___x_2130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object* v_e_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
uint8_t v_a_boxed_2311_; lean_object* v_res_2312_; 
v_a_boxed_2311_ = lean_unbox(v_a_2304_);
v_res_2312_ = l_Lean_Elab_Tactic_Omega_lookup(v_e_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_boxed_2311_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2303_);
lean_dec(v_a_2302_);
lean_dec(v_a_2301_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(lean_object* v_00_u03b2_2313_, lean_object* v_m_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_2314_, v_a_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(lean_object* v_00_u03b2_2317_, lean_object* v_m_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(v_00_u03b2_2317_, v_m_2318_, v_a_2319_);
lean_dec_ref(v_a_2319_);
lean_dec_ref(v_m_2318_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object* v_00_u03b2_2321_, lean_object* v_m_2322_, lean_object* v_query_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v_m_2322_, v_query_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___boxed(lean_object* v_00_u03b2_2325_, lean_object* v_m_2326_, lean_object* v_query_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1(v_00_u03b2_2325_, v_m_2326_, v_query_2327_);
lean_dec_ref(v_query_2327_);
lean_dec_ref(v_m_2326_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object* v_00_u03b2_2329_, lean_object* v_m_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_m_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(lean_object* v_00_u03b2_2332_, lean_object* v_m_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(v_00_u03b2_2332_, v_m_2333_);
lean_dec_ref(v_m_2333_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, uint8_t v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg(v_x_2335_, v_x_2336_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___boxed(lean_object* v_x_2348_, lean_object* v_x_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
uint8_t v___y_53943__boxed_2360_; lean_object* v_res_2361_; 
v___y_53943__boxed_2360_ = lean_unbox(v___y_2353_);
v_res_2361_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(v_x_2348_, v_x_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_53943__boxed_2360_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec(v___y_2350_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5(lean_object* v_cls_2362_, lean_object* v_msg_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, uint8_t v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(v_cls_2362_, v_msg_2363_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___boxed(lean_object* v_cls_2375_, lean_object* v_msg_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
uint8_t v___y_53979__boxed_2387_; lean_object* v_res_2388_; 
v___y_53979__boxed_2387_ = lean_unbox(v___y_2380_);
v_res_2388_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5(v_cls_2375_, v_msg_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_53979__boxed_2387_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec(v___y_2377_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(lean_object* v_00_u03b2_2389_, lean_object* v_m_2390_, lean_object* v_query_2391_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_m_2390_, v_query_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2393_, lean_object* v_m_2394_, lean_object* v_query_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(v_00_u03b2_2393_, v_m_2394_, v_query_2395_);
lean_dec_ref(v_query_2395_);
lean_dec_ref(v_m_2394_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(lean_object* v_00_u03b2_2397_, lean_object* v_m_2398_, lean_object* v_query_2399_, lean_object* v_x_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_m_2398_, v_query_2399_, v_x_2400_, v_x_2401_, v_x_2402_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2405_, lean_object* v_m_2406_, lean_object* v_query_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_, lean_object* v_x_2410_, lean_object* v_x_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(v_00_u03b2_2405_, v_m_2406_, v_query_2407_, v_x_2408_, v_x_2409_, v_x_2410_, v_x_2411_);
lean_dec_ref(v_query_2407_);
lean_dec_ref(v_m_2406_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4(lean_object* v_00_u03b2_2413_, lean_object* v_init_2414_, lean_object* v_b_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4___redArg(v_init_2414_, v_b_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2417_, lean_object* v_init_2418_, lean_object* v_b_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4(v_00_u03b2_2417_, v_init_2418_, v_b_2419_);
lean_dec_ref(v_b_2419_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2421_, lean_object* v_b_2422_, lean_object* v_acc_2423_, lean_object* v_i_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4_spec__5___redArg(v_b_2422_, v_acc_2423_, v_i_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2426_, lean_object* v_b_2427_, lean_object* v_acc_2428_, lean_object* v_i_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_spec__4_spec__5(v_00_u03b2_2426_, v_b_2427_, v_acc_2428_, v_i_2429_);
lean_dec_ref(v_b_2427_);
return v_res_2430_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Canonicalizer(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Canonicalizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Omega_OmegaM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Canonicalizer(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Omega_OmegaM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Canonicalizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
}
#ifdef __cplusplus
}
#endif
