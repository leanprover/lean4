// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.OmegaM
// Imports: public import Lean.Meta.AppBuilder public import Lean.Meta.Canonicalizer public import Init.Omega import Lean.OrderLevel
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_nat_x3f(lean_object*);
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "emod_lt_of_pos"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(179, 253, 191, 46, 213, 199, 79, 210)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTNat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(141, 27, 201, 217, 48, 203, 85, 203)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pow_pos"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(8, 188, 92, 81, 98, 125, 214, 195)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ofNat_pos_of_pos"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 141, 7, 147, 89, 24, 200, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value),LEAN_SCALAR_PTR_LITERAL(40, 203, 156, 230, 39, 171, 106, 183)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "emod_nonneg"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value),LEAN_SCALAR_PTR_LITERAL(61, 100, 115, 114, 207, 135, 28, 238)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ne_of_gt"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value),LEAN_SCALAR_PTR_LITERAL(124, 85, 105, 24, 138, 4, 9, 162)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42;
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
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "pos_pow_of_pos"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTInt"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value),LEAN_SCALAR_PTR_LITERAL(174, 212, 102, 196, 69, 170, 149, 126)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mul_ediv_self_le"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_value),LEAN_SCALAR_PTR_LITERAL(252, 253, 214, 154, 97, 254, 157, 214)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "lt_mul_ediv_self_add"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_value),LEAN_SCALAR_PTR_LITERAL(94, 156, 157, 133, 195, 57, 68, 244)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "neg_le_natAbs"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 141, 7, 147, 89, 24, 200, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value),LEAN_SCALAR_PTR_LITERAL(217, 253, 117, 167, 254, 111, 180, 184)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "natCast_nonneg"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_value),LEAN_SCALAR_PTR_LITERAL(78, 189, 5, 123, 91, 219, 85, 246)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "isLt"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_value),LEAN_SCALAR_PTR_LITERAL(196, 26, 231, 251, 226, 55, 19, 117)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_value),LEAN_SCALAR_PTR_LITERAL(222, 150, 50, 101, 25, 222, 136, 68)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "le_natAbs"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value),LEAN_SCALAR_PTR_LITERAL(90, 82, 63, 108, 86, 248, 24, 88)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natAbs"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "ofNat_sub_dichotomy"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 141, 7, 147, 89, 24, 200, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value),LEAN_SCALAR_PTR_LITERAL(132, 176, 7, 204, 155, 0, 78, 60)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ite_disjunction"};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86_value),LEAN_SCALAR_PTR_LITERAL(77, 139, 125, 42, 52, 100, 157, 106)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_4823__boxed_37_; lean_object* v_res_38_; 
v___y_4823__boxed_37_ = lean_unbox(v___y_30_);
v_res_38_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(v___x_26_, v___x_27_, v_m_28_, v_cfg_29_, v___y_4823__boxed_37_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
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
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_box(0);
v___x_40_ = lean_unsigned_to_nat(16u);
v___x_41_ = lean_mk_array(v___x_40_, v___x_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0, &l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0);
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(lean_object* v_m_47_, lean_object* v_cfg_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_54_; lean_object* v___f_55_; uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_54_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1);
v___f_55_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_55_, 0, v___x_54_);
lean_closure_set(v___f_55_, 1, v___x_54_);
lean_closure_set(v___f_55_, 2, v_m_47_);
lean_closure_set(v___f_55_, 3, v_cfg_48_);
v___x_56_ = 3;
v___x_57_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2);
v___x_58_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(v___f_55_, v___x_56_, v___x_57_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___boxed(lean_object* v_m_59_, lean_object* v_cfg_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(v_m_59_, v_cfg_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_object* v_00_u03b1_67_, lean_object* v_m_68_, lean_object* v_cfg_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(v_m_68_, v_cfg_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___boxed(lean_object* v_00_u03b1_76_, lean_object* v_m_77_, lean_object* v_cfg_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Elab_Tactic_Omega_OmegaM_run(v_00_u03b1_76_, v_m_77_, v_cfg_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg(lean_object* v_a_85_){
_start:
{
lean_object* v___x_87_; 
lean_inc_ref(v_a_85_);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v_a_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg___boxed(lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Elab_Tactic_Omega_cfg___redArg(v_a_88_);
lean_dec_ref(v_a_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg(lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, uint8_t v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_101_; 
lean_inc_ref(v_a_93_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v_a_93_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___boxed(lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
uint8_t v_a_boxed_112_; lean_object* v_res_113_; 
v_a_boxed_112_ = lean_unbox(v_a_105_);
v_res_113_ = l_Lean_Elab_Tactic_Omega_cfg(v_a_102_, v_a_103_, v_a_104_, v_a_boxed_112_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec(v_a_102_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(lean_object* v_hi_114_, lean_object* v_pivot_115_, lean_object* v_as_116_, lean_object* v_i_117_, lean_object* v_k_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lean_nat_dec_lt(v_k_118_, v_hi_114_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_k_118_);
v___x_120_ = lean_array_fswap(v_as_116_, v_i_117_, v_hi_114_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_i_117_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; lean_object* v_snd_123_; lean_object* v_snd_124_; uint8_t v___x_125_; 
v___x_122_ = lean_array_fget_borrowed(v_as_116_, v_k_118_);
v_snd_123_ = lean_ctor_get(v___x_122_, 1);
v_snd_124_ = lean_ctor_get(v_pivot_115_, 1);
v___x_125_ = lean_nat_dec_lt(v_snd_123_, v_snd_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_add(v_k_118_, v___x_126_);
lean_dec(v_k_118_);
v_k_118_ = v___x_127_;
goto _start;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = lean_array_fswap(v_as_116_, v_i_117_, v_k_118_);
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_nat_add(v_i_117_, v___x_130_);
lean_dec(v_i_117_);
v___x_132_ = lean_nat_add(v_k_118_, v___x_130_);
lean_dec(v_k_118_);
v_as_116_ = v___x_129_;
v_i_117_ = v___x_131_;
v_k_118_ = v___x_132_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg___boxed(lean_object* v_hi_134_, lean_object* v_pivot_135_, lean_object* v_as_136_, lean_object* v_i_137_, lean_object* v_k_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_134_, v_pivot_135_, v_as_136_, v_i_137_, v_k_138_);
lean_dec_ref(v_pivot_135_);
lean_dec(v_hi_134_);
return v_res_139_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(lean_object* v_x1_140_, lean_object* v_x2_141_){
_start:
{
lean_object* v_snd_142_; lean_object* v_snd_143_; uint8_t v___x_144_; 
v_snd_142_ = lean_ctor_get(v_x1_140_, 1);
v_snd_143_ = lean_ctor_get(v_x2_141_, 1);
v___x_144_ = lean_nat_dec_lt(v_snd_142_, v_snd_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(lean_object* v_x1_145_, lean_object* v_x2_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v_x1_145_, v_x2_146_);
lean_dec_ref(v_x2_146_);
lean_dec_ref(v_x1_145_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(lean_object* v_n_149_, lean_object* v_as_150_, lean_object* v_lo_151_, lean_object* v_hi_152_){
_start:
{
lean_object* v___y_154_; uint8_t v___x_164_; 
v___x_164_ = lean_nat_dec_lt(v_lo_151_, v_hi_152_);
if (v___x_164_ == 0)
{
lean_dec(v_lo_151_);
return v_as_150_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_mid_167_; lean_object* v___y_169_; lean_object* v___y_175_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_165_ = lean_nat_add(v_lo_151_, v_hi_152_);
v___x_166_ = lean_unsigned_to_nat(1u);
v_mid_167_ = lean_nat_shiftr(v___x_165_, v___x_166_);
lean_dec(v___x_165_);
v___x_180_ = lean_array_fget_borrowed(v_as_150_, v_mid_167_);
v___x_181_ = lean_array_fget_borrowed(v_as_150_, v_lo_151_);
v___x_182_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
v___y_175_ = v_as_150_;
goto v___jp_174_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = lean_array_fswap(v_as_150_, v_lo_151_, v_mid_167_);
v___y_175_ = v___x_183_;
goto v___jp_174_;
}
v___jp_168_:
{
lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_170_ = lean_array_fget_borrowed(v___y_169_, v_mid_167_);
v___x_171_ = lean_array_fget_borrowed(v___y_169_, v_hi_152_);
v___x_172_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v___x_170_, v___x_171_);
if (v___x_172_ == 0)
{
lean_dec(v_mid_167_);
v___y_154_ = v___y_169_;
goto v___jp_153_;
}
else
{
lean_object* v___x_173_; 
v___x_173_ = lean_array_fswap(v___y_169_, v_mid_167_, v_hi_152_);
lean_dec(v_mid_167_);
v___y_154_ = v___x_173_;
goto v___jp_153_;
}
}
v___jp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_176_ = lean_array_fget_borrowed(v___y_175_, v_hi_152_);
v___x_177_ = lean_array_fget_borrowed(v___y_175_, v_lo_151_);
v___x_178_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
v___y_169_ = v___y_175_;
goto v___jp_168_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = lean_array_fswap(v___y_175_, v_lo_151_, v_hi_152_);
v___y_169_ = v___x_179_;
goto v___jp_168_;
}
}
}
v___jp_153_:
{
lean_object* v_pivot_155_; lean_object* v___x_156_; lean_object* v_fst_157_; lean_object* v_snd_158_; uint8_t v___x_159_; 
v_pivot_155_ = lean_array_fget(v___y_154_, v_hi_152_);
lean_inc_n(v_lo_151_, 2);
v___x_156_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_152_, v_pivot_155_, v___y_154_, v_lo_151_, v_lo_151_);
lean_dec(v_pivot_155_);
v_fst_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_fst_157_);
v_snd_158_ = lean_ctor_get(v___x_156_, 1);
lean_inc(v_snd_158_);
lean_dec_ref(v___x_156_);
v___x_159_ = lean_nat_dec_le(v_hi_152_, v_fst_157_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_149_, v_snd_158_, v_lo_151_, v_fst_157_);
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_add(v_fst_157_, v___x_161_);
lean_dec(v_fst_157_);
v_as_150_ = v___x_160_;
v_lo_151_ = v___x_162_;
goto _start;
}
else
{
lean_dec(v_fst_157_);
lean_dec(v_lo_151_);
return v_snd_158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___boxed(lean_object* v_n_184_, lean_object* v_as_185_, lean_object* v_lo_186_, lean_object* v_hi_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_184_, v_as_185_, v_lo_186_, v_hi_187_);
lean_dec(v_hi_187_);
lean_dec(v_n_184_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
if (lean_obj_tag(v_x_190_) == 0)
{
return v_x_189_;
}
else
{
lean_object* v_key_191_; lean_object* v_value_192_; lean_object* v_tail_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_key_191_ = lean_ctor_get(v_x_190_, 0);
v_value_192_ = lean_ctor_get(v_x_190_, 1);
v_tail_193_ = lean_ctor_get(v_x_190_, 2);
lean_inc(v_value_192_);
lean_inc(v_key_191_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v_key_191_);
lean_ctor_set(v___x_194_, 1, v_value_192_);
v___x_195_ = lean_array_push(v_x_189_, v___x_194_);
v_x_189_ = v___x_195_;
v_x_190_ = v_tail_193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___boxed(lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(v_x_197_, v_x_198_);
lean_dec(v_x_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(lean_object* v_as_200_, size_t v_i_201_, size_t v_stop_202_, lean_object* v_b_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = lean_usize_dec_eq(v_i_201_, v_stop_202_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; size_t v___x_207_; size_t v___x_208_; 
v___x_205_ = lean_array_uget_borrowed(v_as_200_, v_i_201_);
v___x_206_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(v_b_203_, v___x_205_);
v___x_207_ = ((size_t)1ULL);
v___x_208_ = lean_usize_add(v_i_201_, v___x_207_);
v_i_201_ = v___x_208_;
v_b_203_ = v___x_206_;
goto _start;
}
else
{
return v_b_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3___boxed(lean_object* v_as_210_, lean_object* v_i_211_, lean_object* v_stop_212_, lean_object* v_b_213_){
_start:
{
size_t v_i_boxed_214_; size_t v_stop_boxed_215_; lean_object* v_res_216_; 
v_i_boxed_214_ = lean_unbox_usize(v_i_211_);
lean_dec(v_i_211_);
v_stop_boxed_215_ = lean_unbox_usize(v_stop_212_);
lean_dec(v_stop_212_);
v_res_216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_as_210_, v_i_boxed_214_, v_stop_boxed_215_, v_b_213_);
lean_dec_ref(v_as_210_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(size_t v_sz_217_, size_t v_i_218_, lean_object* v_bs_219_){
_start:
{
uint8_t v___x_220_; 
v___x_220_ = lean_usize_dec_lt(v_i_218_, v_sz_217_);
if (v___x_220_ == 0)
{
return v_bs_219_;
}
else
{
lean_object* v_v_221_; lean_object* v_fst_222_; lean_object* v___x_223_; lean_object* v_bs_x27_224_; size_t v___x_225_; size_t v___x_226_; lean_object* v___x_227_; 
v_v_221_ = lean_array_uget_borrowed(v_bs_219_, v_i_218_);
v_fst_222_ = lean_ctor_get(v_v_221_, 0);
lean_inc(v_fst_222_);
v___x_223_ = lean_unsigned_to_nat(0u);
v_bs_x27_224_ = lean_array_uset(v_bs_219_, v_i_218_, v___x_223_);
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_add(v_i_218_, v___x_225_);
v___x_227_ = lean_array_uset(v_bs_x27_224_, v_i_218_, v_fst_222_);
v_i_218_ = v___x_226_;
v_bs_219_ = v___x_227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(lean_object* v_sz_229_, lean_object* v_i_230_, lean_object* v_bs_231_){
_start:
{
size_t v_sz_boxed_232_; size_t v_i_boxed_233_; lean_object* v_res_234_; 
v_sz_boxed_232_ = lean_unbox_usize(v_sz_229_);
lean_dec(v_sz_229_);
v_i_boxed_233_ = lean_unbox_usize(v_i_230_);
lean_dec(v_i_230_);
v_res_234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_boxed_232_, v_i_boxed_233_, v_bs_231_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg(lean_object* v_a_235_){
_start:
{
lean_object* v___x_237_; lean_object* v___y_239_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_257_; lean_object* v_size_264_; lean_object* v_buckets_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_237_ = lean_st_ref_get(v_a_235_);
v_size_264_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_size_264_);
v_buckets_265_ = lean_ctor_get(v___x_237_, 1);
lean_inc_ref(v_buckets_265_);
lean_dec(v___x_237_);
v___x_266_ = lean_mk_empty_array_with_capacity(v_size_264_);
lean_dec(v_size_264_);
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_array_get_size(v_buckets_265_);
v___x_269_ = lean_nat_dec_lt(v___x_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_dec_ref(v_buckets_265_);
v___y_257_ = v___x_266_;
goto v___jp_256_;
}
else
{
uint8_t v___x_270_; 
v___x_270_ = lean_nat_dec_le(v___x_268_, v___x_268_);
if (v___x_270_ == 0)
{
if (v___x_269_ == 0)
{
lean_dec_ref(v_buckets_265_);
v___y_257_ = v___x_266_;
goto v___jp_256_;
}
else
{
size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; 
v___x_271_ = ((size_t)0ULL);
v___x_272_ = lean_usize_of_nat(v___x_268_);
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_buckets_265_, v___x_271_, v___x_272_, v___x_266_);
lean_dec_ref(v_buckets_265_);
v___y_257_ = v___x_273_;
goto v___jp_256_;
}
}
else
{
size_t v___x_274_; size_t v___x_275_; lean_object* v___x_276_; 
v___x_274_ = ((size_t)0ULL);
v___x_275_ = lean_usize_of_nat(v___x_268_);
v___x_276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_buckets_265_, v___x_274_, v___x_275_, v___x_266_);
lean_dec_ref(v_buckets_265_);
v___y_257_ = v___x_276_;
goto v___jp_256_;
}
}
v___jp_238_:
{
size_t v_sz_240_; size_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_sz_240_ = lean_array_size(v___y_239_);
v___x_241_ = ((size_t)0ULL);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_240_, v___x_241_, v___y_239_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
v___jp_244_:
{
lean_object* v___x_249_; 
v___x_249_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v___y_247_, v___y_246_, v___y_245_, v___y_248_);
lean_dec(v___y_248_);
lean_dec(v___y_247_);
v___y_239_ = v___x_249_;
goto v___jp_238_;
}
v___jp_250_:
{
uint8_t v___x_255_; 
v___x_255_ = lean_nat_dec_le(v___y_254_, v___y_251_);
if (v___x_255_ == 0)
{
lean_dec(v___y_251_);
lean_inc(v___y_254_);
v___y_245_ = v___y_254_;
v___y_246_ = v___y_252_;
v___y_247_ = v___y_253_;
v___y_248_ = v___y_254_;
goto v___jp_244_;
}
else
{
v___y_245_ = v___y_254_;
v___y_246_ = v___y_252_;
v___y_247_ = v___y_253_;
v___y_248_ = v___y_251_;
goto v___jp_244_;
}
}
v___jp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_258_ = lean_array_get_size(v___y_257_);
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_nat_dec_eq(v___x_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_sub(v___x_258_, v___x_261_);
v___x_263_ = lean_nat_dec_le(v___x_259_, v___x_262_);
if (v___x_263_ == 0)
{
lean_inc(v___x_262_);
v___y_251_ = v___x_262_;
v___y_252_ = v___y_257_;
v___y_253_ = v___x_258_;
v___y_254_ = v___x_262_;
goto v___jp_250_;
}
else
{
v___y_251_ = v___x_262_;
v___y_252_ = v___y_257_;
v___y_253_ = v___x_258_;
v___y_254_ = v___x_259_;
goto v___jp_250_;
}
}
else
{
v___y_239_ = v___y_257_;
goto v___jp_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg___boxed(lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_277_);
lean_dec(v_a_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, uint8_t v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_281_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
uint8_t v_a_boxed_301_; lean_object* v_res_302_; 
v_a_boxed_301_ = lean_unbox(v_a_294_);
v_res_302_ = l_Lean_Elab_Tactic_Omega_atoms(v_a_291_, v_a_292_, v_a_293_, v_a_boxed_301_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec(v_a_291_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(lean_object* v_n_303_, lean_object* v_as_304_, lean_object* v_lo_305_, lean_object* v_hi_306_, lean_object* v_w_307_, lean_object* v_hlo_308_, lean_object* v_hhi_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_303_, v_as_304_, v_lo_305_, v_hi_306_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(lean_object* v_n_311_, lean_object* v_as_312_, lean_object* v_lo_313_, lean_object* v_hi_314_, lean_object* v_w_315_, lean_object* v_hlo_316_, lean_object* v_hhi_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(v_n_311_, v_as_312_, v_lo_313_, v_hi_314_, v_w_315_, v_hlo_316_, v_hhi_317_);
lean_dec(v_hi_314_);
lean_dec(v_n_311_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(lean_object* v_n_319_, lean_object* v_lo_320_, lean_object* v_hi_321_, lean_object* v_hhi_322_, lean_object* v_pivot_323_, lean_object* v_as_324_, lean_object* v_i_325_, lean_object* v_k_326_, lean_object* v_ilo_327_, lean_object* v_ik_328_, lean_object* v_w_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_321_, v_pivot_323_, v_as_324_, v_i_325_, v_k_326_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___boxed(lean_object* v_n_331_, lean_object* v_lo_332_, lean_object* v_hi_333_, lean_object* v_hhi_334_, lean_object* v_pivot_335_, lean_object* v_as_336_, lean_object* v_i_337_, lean_object* v_k_338_, lean_object* v_ilo_339_, lean_object* v_ik_340_, lean_object* v_w_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(v_n_331_, v_lo_332_, v_hi_333_, v_hhi_334_, v_pivot_335_, v_as_336_, v_i_337_, v_k_338_, v_ilo_339_, v_ik_340_, v_w_341_);
lean_dec_ref(v_pivot_335_);
lean_dec(v_hi_333_);
lean_dec(v_lo_332_);
lean_dec(v_n_331_);
return v_res_342_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_box(0);
v___x_347_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1));
v___x_348_ = l_Lean_Expr_const___override(v___x_347_, v___x_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg(lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___x_355_; lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_355_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_349_);
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref(v___x_355_);
v___x_357_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_358_ = lean_array_to_list(v_a_356_);
v___x_359_ = l_Lean_Meta_mkListLit(v___x_357_, v___x_358_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___boxed(lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList(lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, uint8_t v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(v_a_368_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___boxed(lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
uint8_t v_a_boxed_388_; lean_object* v_res_389_; 
v_a_boxed_388_ = lean_unbox(v_a_381_);
v_res_389_ = l_Lean_Elab_Tactic_Omega_atomsList(v_a_378_, v_a_379_, v_a_380_, v_a_boxed_388_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec(v_a_378_);
return v_res_389_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_box(0);
v___x_400_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4));
v___x_401_ = l_Lean_Expr_const___override(v___x_400_, v___x_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_418_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_418_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_418_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_418_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_413_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5, &l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5);
v___x_414_ = l_Lean_Expr_app___override(v___x_413_, v_a_409_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_414_);
v___x_416_ = v___x_411_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
else
{
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___boxed(lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs(lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, uint8_t v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_427_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
uint8_t v_a_boxed_447_; lean_object* v_res_448_; 
v_a_boxed_447_ = lean_unbox(v_a_440_);
v_res_448_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs(v_a_437_, v_a_438_, v_a_439_, v_a_boxed_447_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec(v_a_437_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg(lean_object* v_t_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, uint8_t v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_460_ = lean_st_ref_get(v_a_451_);
v___x_461_ = lean_st_ref_get(v_a_450_);
v___x_462_ = lean_box(v_a_453_);
lean_inc(v_a_458_);
lean_inc_ref(v_a_457_);
lean_inc(v_a_456_);
lean_inc_ref(v_a_455_);
lean_inc(v_a_454_);
lean_inc_ref(v_a_452_);
lean_inc(v_a_451_);
lean_inc(v_a_450_);
v___x_463_ = lean_apply_10(v_t_449_, v_a_450_, v_a_451_, v_a_452_, v___x_462_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, lean_box(0));
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_482_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_482_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_482_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_482_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v_snd_468_; uint8_t v___x_469_; 
v_snd_468_ = lean_ctor_get(v_a_464_, 1);
v___x_469_ = lean_unbox(v_snd_468_);
if (v___x_469_ == 0)
{
lean_object* v_fst_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v_fst_470_ = lean_ctor_get(v_a_464_, 0);
lean_inc(v_fst_470_);
lean_dec(v_a_464_);
v___x_471_ = lean_st_ref_take(v_a_451_);
lean_dec(v___x_471_);
v___x_472_ = lean_st_ref_set(v_a_451_, v___x_460_);
v___x_473_ = lean_st_ref_take(v_a_450_);
lean_dec(v___x_473_);
v___x_474_ = lean_st_ref_set(v_a_450_, v___x_461_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v_fst_470_);
v___x_476_ = v___x_466_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_fst_470_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
else
{
lean_object* v_fst_478_; lean_object* v___x_480_; 
lean_dec(v___x_461_);
lean_dec(v___x_460_);
v_fst_478_ = lean_ctor_get(v_a_464_, 0);
lean_inc(v_fst_478_);
lean_dec(v_a_464_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v_fst_478_);
v___x_480_ = v___x_466_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_fst_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec(v___x_461_);
lean_dec(v___x_460_);
v_a_483_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_463_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_463_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg___boxed(lean_object* v_t_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
uint8_t v_a_boxed_502_; lean_object* v_res_503_; 
v_a_boxed_502_ = lean_unbox(v_a_495_);
v_res_503_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(v_t_491_, v_a_492_, v_a_493_, v_a_494_, v_a_boxed_502_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec(v_a_492_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen(lean_object* v_00_u03b1_504_, lean_object* v_t_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, uint8_t v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(v_t_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___boxed(lean_object* v_00_u03b1_517_, lean_object* v_t_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
uint8_t v_a_boxed_529_; lean_object* v_res_530_; 
v_a_boxed_529_ = lean_unbox(v_a_522_);
v_res_530_ = l_Lean_Elab_Tactic_Omega_commitWhen(v_00_u03b1_517_, v_t_518_, v_a_519_, v_a_520_, v_a_521_, v_a_boxed_529_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec(v_a_519_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(lean_object* v_t_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, uint8_t v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_box(v___y_535_);
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
lean_inc(v___y_536_);
lean_inc_ref(v___y_534_);
lean_inc(v___y_533_);
lean_inc(v___y_532_);
v___x_543_ = lean_apply_10(v_t_531_, v___y_532_, v___y_533_, v___y_534_, v___x_542_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, lean_box(0));
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_554_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_554_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_554_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_554_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_548_ = 0;
v___x_549_ = lean_box(v___x_548_);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v_a_544_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_550_);
v___x_552_ = v___x_546_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
v_a_555_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_543_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_543_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed(lean_object* v_t_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
uint8_t v___y_672__boxed_574_; lean_object* v_res_575_; 
v___y_672__boxed_574_ = lean_unbox(v___y_567_);
v_res_575_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(v_t_563_, v___y_564_, v___y_565_, v___y_566_, v___y_672__boxed_574_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec(v___y_564_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(lean_object* v_t_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, uint8_t v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v___f_587_; lean_object* v___x_588_; 
v___f_587_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_587_, 0, v_t_576_);
v___x_588_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(v___f_587_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___boxed(lean_object* v_t_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
uint8_t v_a_boxed_600_; lean_object* v_res_601_; 
v_a_boxed_600_ = lean_unbox(v_a_593_);
v_res_601_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(v_t_589_, v_a_590_, v_a_591_, v_a_592_, v_a_boxed_600_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec(v_a_590_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_object* v_00_u03b1_602_, lean_object* v_t_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, uint8_t v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(v_t_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(lean_object* v_00_u03b1_615_, lean_object* v_t_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
uint8_t v_a_boxed_627_; lean_object* v_res_628_; 
v_a_boxed_627_ = lean_unbox(v_a_620_);
v_res_628_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState(v_00_u03b1_615_, v_t_616_, v_a_617_, v_a_618_, v_a_619_, v_a_boxed_627_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec(v_a_617_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f(lean_object* v_n_631_){
_start:
{
lean_object* v___x_632_; lean_object* v_fst_633_; 
lean_inc_ref(v_n_631_);
v___x_632_ = l_Lean_Expr_getAppFnArgs(v_n_631_);
v_fst_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_fst_633_);
if (lean_obj_tag(v_fst_633_) == 1)
{
lean_object* v_pre_634_; 
v_pre_634_ = lean_ctor_get(v_fst_633_, 0);
lean_inc(v_pre_634_);
if (lean_obj_tag(v_pre_634_) == 1)
{
lean_object* v_pre_635_; 
v_pre_635_ = lean_ctor_get(v_pre_634_, 0);
if (lean_obj_tag(v_pre_635_) == 0)
{
lean_object* v_snd_636_; lean_object* v_str_637_; lean_object* v_str_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_snd_636_ = lean_ctor_get(v___x_632_, 1);
lean_inc(v_snd_636_);
lean_dec_ref(v___x_632_);
v_str_637_ = lean_ctor_get(v_fst_633_, 1);
lean_inc_ref(v_str_637_);
lean_dec_ref_known(v_fst_633_, 2);
v_str_638_ = lean_ctor_get(v_pre_634_, 1);
lean_inc_ref(v_str_638_);
lean_dec_ref_known(v_pre_634_, 2);
v___x_639_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_640_ = lean_string_dec_eq(v_str_638_, v___x_639_);
lean_dec_ref(v_str_638_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec_ref(v_str_637_);
lean_dec(v_snd_636_);
v___x_641_ = l_Lean_Expr_nat_x3f(v_n_631_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_643_ = lean_string_dec_eq(v_str_637_, v___x_642_);
lean_dec_ref(v_str_637_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
lean_dec(v_snd_636_);
v___x_644_ = l_Lean_Expr_nat_x3f(v_n_631_);
return v___x_644_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_645_ = lean_array_get_size(v_snd_636_);
v___x_646_ = lean_unsigned_to_nat(3u);
v___x_647_ = lean_nat_dec_eq(v___x_645_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; 
lean_dec(v_snd_636_);
v___x_648_ = l_Lean_Expr_nat_x3f(v_n_631_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
lean_dec_ref(v_n_631_);
v___x_649_ = lean_unsigned_to_nat(2u);
v___x_650_ = lean_array_fget(v_snd_636_, v___x_649_);
lean_dec(v_snd_636_);
v___x_651_ = l_Lean_Expr_nat_x3f(v___x_650_);
return v___x_651_;
}
}
}
}
else
{
lean_object* v___x_652_; 
lean_dec_ref_known(v_pre_634_, 2);
lean_dec_ref_known(v_fst_633_, 2);
lean_dec_ref(v___x_632_);
v___x_652_ = l_Lean_Expr_nat_x3f(v_n_631_);
return v___x_652_;
}
}
else
{
lean_object* v___x_653_; 
lean_dec_ref_known(v_fst_633_, 2);
lean_dec(v_pre_634_);
lean_dec_ref(v___x_632_);
v___x_653_ = l_Lean_Expr_nat_x3f(v_n_631_);
return v___x_653_;
}
}
else
{
lean_object* v___x_654_; 
lean_dec(v_fst_633_);
lean_dec_ref(v___x_632_);
v___x_654_ = l_Lean_Expr_nat_x3f(v_n_631_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_Tactic_Omega_intCast_x3f_spec__0(lean_object* v_a_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = lean_nat_to_int(v_a_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_intCast_x3f(lean_object* v_n_657_){
_start:
{
lean_object* v___x_658_; lean_object* v_fst_659_; 
lean_inc_ref(v_n_657_);
v___x_658_ = l_Lean_Expr_getAppFnArgs(v_n_657_);
v_fst_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_fst_659_);
if (lean_obj_tag(v_fst_659_) == 1)
{
lean_object* v_pre_660_; 
v_pre_660_ = lean_ctor_get(v_fst_659_, 0);
lean_inc(v_pre_660_);
if (lean_obj_tag(v_pre_660_) == 1)
{
lean_object* v_pre_661_; 
v_pre_661_ = lean_ctor_get(v_pre_660_, 0);
if (lean_obj_tag(v_pre_661_) == 0)
{
lean_object* v_snd_662_; lean_object* v_str_663_; lean_object* v_str_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_snd_662_ = lean_ctor_get(v___x_658_, 1);
lean_inc(v_snd_662_);
lean_dec_ref(v___x_658_);
v_str_663_ = lean_ctor_get(v_fst_659_, 1);
lean_inc_ref(v_str_663_);
lean_dec_ref_known(v_fst_659_, 2);
v_str_664_ = lean_ctor_get(v_pre_660_, 1);
lean_inc_ref(v_str_664_);
lean_dec_ref_known(v_pre_660_, 2);
v___x_665_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_666_ = lean_string_dec_eq(v_str_664_, v___x_665_);
lean_dec_ref(v_str_664_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
lean_dec_ref(v_str_663_);
lean_dec(v_snd_662_);
v___x_667_ = l_Lean_Expr_int_x3f(v_n_657_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_669_ = lean_string_dec_eq(v_str_663_, v___x_668_);
lean_dec_ref(v_str_663_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v_snd_662_);
v___x_670_ = l_Lean_Expr_int_x3f(v_n_657_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = lean_array_get_size(v_snd_662_);
v___x_672_ = lean_unsigned_to_nat(3u);
v___x_673_ = lean_nat_dec_eq(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_dec(v_snd_662_);
v___x_674_ = l_Lean_Expr_int_x3f(v_n_657_);
return v___x_674_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec_ref(v_n_657_);
v___x_675_ = lean_unsigned_to_nat(2u);
v___x_676_ = lean_array_fget(v_snd_662_, v___x_675_);
lean_dec(v_snd_662_);
v___x_677_ = l_Lean_Expr_nat_x3f(v___x_676_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v___x_678_; 
v___x_678_ = lean_box(0);
return v___x_678_;
}
else
{
lean_object* v_val_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_687_; 
v_val_679_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_687_ == 0)
{
v___x_681_ = v___x_677_;
v_isShared_682_ = v_isSharedCheck_687_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_val_679_);
lean_dec(v___x_677_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_687_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = lean_nat_to_int(v_val_679_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_683_);
v___x_685_ = v___x_681_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_688_; 
lean_dec_ref_known(v_pre_660_, 2);
lean_dec_ref_known(v_fst_659_, 2);
lean_dec_ref(v___x_658_);
v___x_688_ = l_Lean_Expr_int_x3f(v_n_657_);
return v___x_688_;
}
}
else
{
lean_object* v___x_689_; 
lean_dec(v_pre_660_);
lean_dec_ref_known(v_fst_659_, 2);
lean_dec_ref(v___x_658_);
v___x_689_ = l_Lean_Expr_int_x3f(v_n_657_);
return v___x_689_;
}
}
else
{
lean_object* v___x_690_; 
lean_dec(v_fst_659_);
lean_dec_ref(v___x_658_);
v___x_690_ = l_Lean_Expr_int_x3f(v_n_657_);
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f(lean_object* v_e_706_){
_start:
{
lean_object* v___x_707_; lean_object* v_fst_708_; 
lean_inc_ref(v_e_706_);
v___x_707_ = l_Lean_Expr_getAppFnArgs(v_e_706_);
v_fst_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_fst_708_);
if (lean_obj_tag(v_fst_708_) == 1)
{
lean_object* v_pre_709_; 
v_pre_709_ = lean_ctor_get(v_fst_708_, 0);
lean_inc(v_pre_709_);
if (lean_obj_tag(v_pre_709_) == 1)
{
lean_object* v_pre_710_; 
v_pre_710_ = lean_ctor_get(v_pre_709_, 0);
if (lean_obj_tag(v_pre_710_) == 0)
{
lean_object* v_snd_711_; lean_object* v_str_712_; lean_object* v_str_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_snd_711_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_snd_711_);
lean_dec_ref(v___x_707_);
v_str_712_ = lean_ctor_get(v_fst_708_, 1);
lean_inc_ref(v_str_712_);
lean_dec_ref_known(v_fst_708_, 2);
v_str_713_ = lean_ctor_get(v_pre_709_, 1);
lean_inc_ref(v_str_713_);
lean_dec_ref_known(v_pre_709_, 2);
v___x_714_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_715_ = lean_string_dec_eq(v_str_713_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0));
v___x_717_ = lean_string_dec_eq(v_str_713_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1));
v___x_719_ = lean_string_dec_eq(v_str_713_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2));
v___x_721_ = lean_string_dec_eq(v_str_713_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3));
v___x_723_ = lean_string_dec_eq(v_str_713_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4));
v___x_725_ = lean_string_dec_eq(v_str_713_, v___x_724_);
lean_dec_ref(v_str_713_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec_ref(v_str_712_);
lean_dec(v_snd_711_);
v___x_726_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_728_ = lean_string_dec_eq(v_str_712_, v___x_727_);
lean_dec_ref(v_str_712_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_dec(v_snd_711_);
v___x_729_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_730_ = lean_array_get_size(v_snd_711_);
v___x_731_ = lean_unsigned_to_nat(6u);
v___x_732_ = lean_nat_dec_eq(v___x_730_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec(v_snd_711_);
v___x_733_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_733_;
}
else
{
lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec_ref(v_e_706_);
v___f_734_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6));
v___x_735_ = lean_unsigned_to_nat(4u);
v___x_736_ = lean_array_fget(v_snd_711_, v___x_735_);
v___x_737_ = lean_unsigned_to_nat(5u);
v___x_738_ = lean_array_fget(v_snd_711_, v___x_737_);
lean_dec(v_snd_711_);
v___x_739_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_734_, v___x_736_, v___x_738_);
return v___x_739_;
}
}
}
}
else
{
lean_object* v___x_740_; uint8_t v___x_741_; 
lean_dec_ref(v_str_713_);
v___x_740_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7));
v___x_741_ = lean_string_dec_eq(v_str_712_, v___x_740_);
lean_dec_ref(v_str_712_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
lean_dec(v_snd_711_);
v___x_742_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_742_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_743_ = lean_array_get_size(v_snd_711_);
v___x_744_ = lean_unsigned_to_nat(6u);
v___x_745_ = lean_nat_dec_eq(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_dec(v_snd_711_);
v___x_746_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_746_;
}
else
{
lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec_ref(v_e_706_);
v___f_747_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8));
v___x_748_ = lean_unsigned_to_nat(4u);
v___x_749_ = lean_array_fget(v_snd_711_, v___x_748_);
v___x_750_ = lean_unsigned_to_nat(5u);
v___x_751_ = lean_array_fget(v_snd_711_, v___x_750_);
lean_dec(v_snd_711_);
v___x_752_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_747_, v___x_749_, v___x_751_);
return v___x_752_;
}
}
}
}
else
{
lean_object* v___x_753_; uint8_t v___x_754_; 
lean_dec_ref(v_str_713_);
v___x_753_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9));
v___x_754_ = lean_string_dec_eq(v_str_712_, v___x_753_);
lean_dec_ref(v_str_712_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
lean_dec(v_snd_711_);
v___x_755_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_755_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_756_ = lean_array_get_size(v_snd_711_);
v___x_757_ = lean_unsigned_to_nat(6u);
v___x_758_ = lean_nat_dec_eq(v___x_756_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
lean_dec(v_snd_711_);
v___x_759_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_759_;
}
else
{
lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
lean_dec_ref(v_e_706_);
v___f_760_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10));
v___x_761_ = lean_unsigned_to_nat(4u);
v___x_762_ = lean_array_fget(v_snd_711_, v___x_761_);
v___x_763_ = lean_unsigned_to_nat(5u);
v___x_764_ = lean_array_fget(v_snd_711_, v___x_763_);
lean_dec(v_snd_711_);
v___x_765_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_760_, v___x_762_, v___x_764_);
return v___x_765_;
}
}
}
}
else
{
lean_object* v___x_766_; uint8_t v___x_767_; 
lean_dec_ref(v_str_713_);
v___x_766_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11));
v___x_767_ = lean_string_dec_eq(v_str_712_, v___x_766_);
lean_dec_ref(v_str_712_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_dec(v_snd_711_);
v___x_768_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_768_;
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_769_ = lean_array_get_size(v_snd_711_);
v___x_770_ = lean_unsigned_to_nat(6u);
v___x_771_ = lean_nat_dec_eq(v___x_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_dec(v_snd_711_);
v___x_772_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_772_;
}
else
{
lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec_ref(v_e_706_);
v___f_773_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12));
v___x_774_ = lean_unsigned_to_nat(4u);
v___x_775_ = lean_array_fget(v_snd_711_, v___x_774_);
v___x_776_ = lean_unsigned_to_nat(5u);
v___x_777_ = lean_array_fget(v_snd_711_, v___x_776_);
lean_dec(v_snd_711_);
v___x_778_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_773_, v___x_775_, v___x_777_);
return v___x_778_;
}
}
}
}
else
{
lean_object* v___x_779_; uint8_t v___x_780_; 
lean_dec_ref(v_str_713_);
v___x_779_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13));
v___x_780_ = lean_string_dec_eq(v_str_712_, v___x_779_);
lean_dec_ref(v_str_712_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_dec(v_snd_711_);
v___x_781_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_781_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_782_ = lean_array_get_size(v_snd_711_);
v___x_783_ = lean_unsigned_to_nat(6u);
v___x_784_ = lean_nat_dec_eq(v___x_782_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec(v_snd_711_);
v___x_785_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_785_;
}
else
{
lean_object* v___f_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_dec_ref(v_e_706_);
v___f_786_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14));
v___x_787_ = lean_unsigned_to_nat(4u);
v___x_788_ = lean_array_fget(v_snd_711_, v___x_787_);
v___x_789_ = lean_unsigned_to_nat(5u);
v___x_790_ = lean_array_fget(v_snd_711_, v___x_789_);
lean_dec(v_snd_711_);
v___x_791_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_786_, v___x_788_, v___x_790_);
return v___x_791_;
}
}
}
}
else
{
lean_object* v___x_792_; uint8_t v___x_793_; 
lean_dec_ref(v_str_713_);
v___x_792_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_793_ = lean_string_dec_eq(v_str_712_, v___x_792_);
lean_dec_ref(v_str_712_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_dec(v_snd_711_);
v___x_794_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_794_;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_795_ = lean_array_get_size(v_snd_711_);
v___x_796_ = lean_unsigned_to_nat(3u);
v___x_797_ = lean_nat_dec_eq(v___x_795_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; 
lean_dec(v_snd_711_);
v___x_798_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_798_;
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec_ref(v_e_706_);
v___x_799_ = lean_unsigned_to_nat(2u);
v___x_800_ = lean_array_fget(v_snd_711_, v___x_799_);
lean_dec(v_snd_711_);
v_e_706_ = v___x_800_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_802_; 
lean_dec_ref_known(v_pre_709_, 2);
lean_dec_ref_known(v_fst_708_, 2);
lean_dec_ref(v___x_707_);
v___x_802_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_802_;
}
}
else
{
lean_object* v___x_803_; 
lean_dec_ref_known(v_fst_708_, 2);
lean_dec(v_pre_709_);
lean_dec_ref(v___x_707_);
v___x_803_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_803_;
}
}
else
{
lean_object* v___x_804_; 
lean_dec(v_fst_708_);
lean_dec_ref(v___x_707_);
v___x_804_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(lean_object* v_f_805_, lean_object* v_x_806_, lean_object* v_y_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_x_806_);
if (lean_obj_tag(v___x_808_) == 1)
{
lean_object* v_val_809_; lean_object* v___x_810_; 
v_val_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_val_809_);
lean_dec_ref_known(v___x_808_, 1);
v___x_810_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_y_807_);
if (lean_obj_tag(v___x_810_) == 1)
{
lean_object* v_val_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_819_; 
v_val_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_819_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_val_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = lean_apply_2(v_f_805_, v_val_809_, v_val_811_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_815_);
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_object* v___x_820_; 
lean_dec(v___x_810_);
lean_dec(v_val_809_);
lean_dec_ref(v_f_805_);
v___x_820_ = lean_box(0);
return v___x_820_;
}
}
else
{
lean_object* v___x_821_; 
lean_dec(v___x_808_);
lean_dec_ref(v_y_807_);
lean_dec_ref(v_f_805_);
v___x_821_ = lean_box(0);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f(lean_object* v_e_826_){
_start:
{
lean_object* v___x_827_; lean_object* v_fst_828_; 
lean_inc_ref(v_e_826_);
v___x_827_ = l_Lean_Expr_getAppFnArgs(v_e_826_);
v_fst_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_fst_828_);
if (lean_obj_tag(v_fst_828_) == 1)
{
lean_object* v_pre_829_; 
v_pre_829_ = lean_ctor_get(v_fst_828_, 0);
lean_inc(v_pre_829_);
if (lean_obj_tag(v_pre_829_) == 1)
{
lean_object* v_pre_830_; 
v_pre_830_ = lean_ctor_get(v_pre_829_, 0);
if (lean_obj_tag(v_pre_830_) == 0)
{
lean_object* v_snd_831_; lean_object* v_str_832_; lean_object* v_str_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_snd_831_ = lean_ctor_get(v___x_827_, 1);
lean_inc(v_snd_831_);
lean_dec_ref(v___x_827_);
v_str_832_ = lean_ctor_get(v_fst_828_, 1);
lean_inc_ref(v_str_832_);
lean_dec_ref_known(v_fst_828_, 2);
v_str_833_ = lean_ctor_get(v_pre_829_, 1);
lean_inc_ref(v_str_833_);
lean_dec_ref_known(v_pre_829_, 2);
v___x_834_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_835_ = lean_string_dec_eq(v_str_833_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0));
v___x_837_ = lean_string_dec_eq(v_str_833_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1));
v___x_839_ = lean_string_dec_eq(v_str_833_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_840_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2));
v___x_841_ = lean_string_dec_eq(v_str_833_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3));
v___x_843_ = lean_string_dec_eq(v_str_833_, v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4));
v___x_845_ = lean_string_dec_eq(v_str_833_, v___x_844_);
lean_dec_ref(v_str_833_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; 
lean_dec_ref(v_str_832_);
lean_dec(v_snd_831_);
v___x_846_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_846_;
}
else
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_848_ = lean_string_dec_eq(v_str_832_, v___x_847_);
lean_dec_ref(v_str_832_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
lean_dec(v_snd_831_);
v___x_849_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_849_;
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_850_ = lean_array_get_size(v_snd_831_);
v___x_851_ = lean_unsigned_to_nat(6u);
v___x_852_ = lean_nat_dec_eq(v___x_850_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
lean_dec(v_snd_831_);
v___x_853_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec_ref(v_e_826_);
v___x_854_ = lean_unsigned_to_nat(4u);
v___x_855_ = lean_array_fget_borrowed(v_snd_831_, v___x_854_);
lean_inc(v___x_855_);
v___x_856_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v___x_855_);
if (lean_obj_tag(v___x_856_) == 1)
{
lean_object* v_val_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_val_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v___x_856_, 1);
v___x_858_ = lean_unsigned_to_nat(5u);
v___x_859_ = lean_array_fget(v_snd_831_, v___x_858_);
lean_dec(v_snd_831_);
v___x_860_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_859_);
if (lean_obj_tag(v___x_860_) == 1)
{
lean_object* v_val_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v_val_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_869_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_val_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = l_Int_pow(v_val_857_, v_val_861_);
lean_dec(v_val_861_);
lean_dec(v_val_857_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
else
{
lean_object* v___x_870_; 
lean_dec(v___x_860_);
lean_dec(v_val_857_);
v___x_870_ = lean_box(0);
return v___x_870_;
}
}
else
{
lean_object* v___x_871_; 
lean_dec(v___x_856_);
lean_dec(v_snd_831_);
v___x_871_ = lean_box(0);
return v___x_871_;
}
}
}
}
}
else
{
lean_object* v___x_872_; uint8_t v___x_873_; 
lean_dec_ref(v_str_833_);
v___x_872_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7));
v___x_873_ = lean_string_dec_eq(v_str_832_, v___x_872_);
lean_dec_ref(v_str_832_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec(v_snd_831_);
v___x_874_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_874_;
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_875_ = lean_array_get_size(v_snd_831_);
v___x_876_ = lean_unsigned_to_nat(6u);
v___x_877_ = lean_nat_dec_eq(v___x_875_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
lean_dec(v_snd_831_);
v___x_878_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_878_;
}
else
{
lean_object* v___f_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec_ref(v_e_826_);
v___f_879_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0));
v___x_880_ = lean_unsigned_to_nat(4u);
v___x_881_ = lean_array_fget(v_snd_831_, v___x_880_);
v___x_882_ = lean_unsigned_to_nat(5u);
v___x_883_ = lean_array_fget(v_snd_831_, v___x_882_);
lean_dec(v_snd_831_);
v___x_884_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_879_, v___x_881_, v___x_883_);
return v___x_884_;
}
}
}
}
else
{
lean_object* v___x_885_; uint8_t v___x_886_; 
lean_dec_ref(v_str_833_);
v___x_885_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9));
v___x_886_ = lean_string_dec_eq(v_str_832_, v___x_885_);
lean_dec_ref(v_str_832_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
lean_dec(v_snd_831_);
v___x_887_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_887_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_888_ = lean_array_get_size(v_snd_831_);
v___x_889_ = lean_unsigned_to_nat(6u);
v___x_890_ = lean_nat_dec_eq(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_dec(v_snd_831_);
v___x_891_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_891_;
}
else
{
lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec_ref(v_e_826_);
v___f_892_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1));
v___x_893_ = lean_unsigned_to_nat(4u);
v___x_894_ = lean_array_fget(v_snd_831_, v___x_893_);
v___x_895_ = lean_unsigned_to_nat(5u);
v___x_896_ = lean_array_fget(v_snd_831_, v___x_895_);
lean_dec(v_snd_831_);
v___x_897_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_892_, v___x_894_, v___x_896_);
return v___x_897_;
}
}
}
}
else
{
lean_object* v___x_898_; uint8_t v___x_899_; 
lean_dec_ref(v_str_833_);
v___x_898_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11));
v___x_899_ = lean_string_dec_eq(v_str_832_, v___x_898_);
lean_dec_ref(v_str_832_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
lean_dec(v_snd_831_);
v___x_900_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_900_;
}
else
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_901_ = lean_array_get_size(v_snd_831_);
v___x_902_ = lean_unsigned_to_nat(6u);
v___x_903_ = lean_nat_dec_eq(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_dec(v_snd_831_);
v___x_904_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_904_;
}
else
{
lean_object* v___f_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec_ref(v_e_826_);
v___f_905_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2));
v___x_906_ = lean_unsigned_to_nat(4u);
v___x_907_ = lean_array_fget(v_snd_831_, v___x_906_);
v___x_908_ = lean_unsigned_to_nat(5u);
v___x_909_ = lean_array_fget(v_snd_831_, v___x_908_);
lean_dec(v_snd_831_);
v___x_910_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_905_, v___x_907_, v___x_909_);
return v___x_910_;
}
}
}
}
else
{
lean_object* v___x_911_; uint8_t v___x_912_; 
lean_dec_ref(v_str_833_);
v___x_911_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13));
v___x_912_ = lean_string_dec_eq(v_str_832_, v___x_911_);
lean_dec_ref(v_str_832_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; 
lean_dec(v_snd_831_);
v___x_913_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_913_;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_914_ = lean_array_get_size(v_snd_831_);
v___x_915_ = lean_unsigned_to_nat(6u);
v___x_916_ = lean_nat_dec_eq(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
lean_dec(v_snd_831_);
v___x_917_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_917_;
}
else
{
lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec_ref(v_e_826_);
v___f_918_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3));
v___x_919_ = lean_unsigned_to_nat(4u);
v___x_920_ = lean_array_fget(v_snd_831_, v___x_919_);
v___x_921_ = lean_unsigned_to_nat(5u);
v___x_922_ = lean_array_fget(v_snd_831_, v___x_921_);
lean_dec(v_snd_831_);
v___x_923_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_918_, v___x_920_, v___x_922_);
return v___x_923_;
}
}
}
}
else
{
lean_object* v___x_924_; uint8_t v___x_925_; 
lean_dec_ref(v_str_833_);
v___x_924_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_925_ = lean_string_dec_eq(v_str_832_, v___x_924_);
lean_dec_ref(v_str_832_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
lean_dec(v_snd_831_);
v___x_926_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_926_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_927_ = lean_array_get_size(v_snd_831_);
v___x_928_ = lean_unsigned_to_nat(3u);
v___x_929_ = lean_nat_dec_eq(v___x_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; 
lean_dec(v_snd_831_);
v___x_930_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref(v_e_826_);
v___x_931_ = lean_unsigned_to_nat(2u);
v___x_932_ = lean_array_fget(v_snd_831_, v___x_931_);
lean_dec(v_snd_831_);
v___x_933_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v___x_934_; 
v___x_934_ = lean_box(0);
return v___x_934_;
}
else
{
lean_object* v_val_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_943_; 
v_val_935_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_943_ == 0)
{
v___x_937_ = v___x_933_;
v_isShared_938_ = v_isSharedCheck_943_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_val_935_);
lean_dec(v___x_933_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_943_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_939_ = lean_nat_to_int(v_val_935_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_939_);
v___x_941_ = v___x_937_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_944_; 
lean_dec_ref_known(v_pre_829_, 2);
lean_dec_ref_known(v_fst_828_, 2);
lean_dec_ref(v___x_827_);
v___x_944_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_944_;
}
}
else
{
lean_object* v___x_945_; 
lean_dec_ref_known(v_fst_828_, 2);
lean_dec(v_pre_829_);
lean_dec_ref(v___x_827_);
v___x_945_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_945_;
}
}
else
{
lean_object* v___x_946_; 
lean_dec(v_fst_828_);
lean_dec_ref(v___x_827_);
v___x_946_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object* v_f_947_, lean_object* v_x_948_, lean_object* v_y_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_x_948_);
if (lean_obj_tag(v___x_950_) == 1)
{
lean_object* v_val_951_; lean_object* v___x_952_; 
v_val_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_val_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_y_949_);
if (lean_obj_tag(v___x_952_) == 1)
{
lean_object* v_val_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_961_; 
v_val_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_961_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_val_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = lean_apply_2(v_f_947_, v_val_951_, v_val_953_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_959_ = v___x_955_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
else
{
lean_object* v___x_962_; 
lean_dec(v___x_952_);
lean_dec(v_val_951_);
lean_dec_ref(v_f_947_);
v___x_962_ = lean_box(0);
return v___x_962_;
}
}
else
{
lean_object* v___x_963_; 
lean_dec(v___x_950_);
lean_dec_ref(v_y_949_);
lean_dec_ref(v_f_947_);
v___x_963_ = lean_box(0);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object* v_a_964_, lean_object* v_b_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v___x_971_; 
lean_inc_ref(v_a_964_);
v___x_971_ = l_Lean_Meta_mkEqRefl(v_a_964_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = l_Lean_Meta_mkEq(v_a_964_, v_b_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_982_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_982_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = l_Lean_Meta_mkExpectedPropHint(v_a_972_, v_a_974_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
else
{
lean_dec(v_a_972_);
return v___x_973_;
}
}
else
{
lean_dec_ref(v_b_965_);
lean_dec_ref(v_a_964_);
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType___boxed(lean_object* v_a_983_, lean_object* v_b_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v_a_983_, v_b_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
return v_res_990_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(lean_object* v_a_991_, lean_object* v_x_992_){
_start:
{
if (lean_obj_tag(v_x_992_) == 0)
{
uint8_t v___x_993_; 
v___x_993_ = 0;
return v___x_993_;
}
else
{
lean_object* v_head_994_; lean_object* v_tail_995_; uint8_t v___x_996_; 
v_head_994_ = lean_ctor_get(v_x_992_, 0);
v_tail_995_ = lean_ctor_get(v_x_992_, 1);
v___x_996_ = lean_expr_eqv(v_a_991_, v_head_994_);
if (v___x_996_ == 0)
{
v_x_992_ = v_tail_995_;
goto _start;
}
else
{
return v___x_996_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0___boxed(lean_object* v_a_998_, lean_object* v_x_999_){
_start:
{
uint8_t v_res_1000_; lean_object* v_r_1001_; 
v_res_1000_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v_a_998_, v_x_999_);
lean_dec(v_x_999_);
lean_dec_ref(v_a_998_);
v_r_1001_ = lean_box(v_res_1000_);
return v_r_1001_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_box(0);
v___x_1011_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5));
v___x_1012_ = l_Lean_Expr_const___override(v___x_1011_, v___x_1010_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_box(0);
v___x_1018_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8));
v___x_1019_ = l_Lean_Expr_const___override(v___x_1018_, v___x_1017_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12));
v___x_1027_ = l_Lean_Expr_const___override(v___x_1026_, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15));
v___x_1034_ = l_Lean_Expr_const___override(v___x_1033_, v___x_1032_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = l_Lean_mkNatLit(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = lean_nat_to_int(v___x_1076_);
return v___x_1077_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38(void){
_start:
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37);
v___x_1079_ = lean_int_dec_le(v___x_1078_, v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1086_ = l_Lean_Level_ofNat(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37);
v___x_1092_ = lean_int_neg(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45);
v___x_1094_ = l_Int_toNat(v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46);
v___x_1096_ = l_Lean_instToExprInt_mkNat(v___x_1095_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37);
v___x_1098_ = l_Int_toNat(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48);
v___x_1100_ = l_Lean_instToExprInt_mkNat(v___x_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_unsigned_to_nat(1u);
v___x_1102_ = l_Lean_Level_ofNat(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = lean_box(0);
v___x_1109_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53));
v___x_1110_ = l_Lean_Expr_const___override(v___x_1109_, v___x_1108_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42);
v___x_1113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v___x_1111_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55);
v___x_1115_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41));
v___x_1116_ = l_Lean_Expr_const___override(v___x_1115_, v___x_1114_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_box(0);
v___x_1118_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44));
v___x_1119_ = l_Lean_Expr_const___override(v___x_1118_, v___x_1117_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1120_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47);
v___x_1121_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57);
v___x_1122_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1123_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56);
v___x_1124_ = l_Lean_mkApp3(v___x_1123_, v___x_1122_, v___x_1121_, v___x_1120_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
lean_ctor_set(v___x_1130_, 1, v___x_1128_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61);
v___x_1132_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60));
v___x_1133_ = l_Lean_Expr_const___override(v___x_1132_, v___x_1131_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = lean_box(0);
v___x_1139_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64));
v___x_1140_ = l_Lean_Expr_const___override(v___x_1139_, v___x_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = lean_box(0);
v___x_1146_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67));
v___x_1147_ = l_Lean_Expr_const___override(v___x_1146_, v___x_1145_);
return v___x_1147_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1186_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55);
v___x_1187_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87));
v___x_1188_ = l_Lean_Expr_const___override(v___x_1187_, v___x_1186_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(lean_object* v_e_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1214_; lean_object* v_fst_1215_; 
v___x_1214_ = l_Lean_Expr_getAppFnArgs(v_e_1189_);
v_fst_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_fst_1215_);
if (lean_obj_tag(v_fst_1215_) == 1)
{
lean_object* v_pre_1216_; 
v_pre_1216_ = lean_ctor_get(v_fst_1215_, 0);
switch(lean_obj_tag(v_pre_1216_))
{
case 1:
{
lean_object* v_pre_1217_; 
lean_inc_ref(v_pre_1216_);
v_pre_1217_ = lean_ctor_get(v_pre_1216_, 0);
if (lean_obj_tag(v_pre_1217_) == 0)
{
lean_object* v_snd_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1797_; 
v_snd_1218_ = lean_ctor_get(v___x_1214_, 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; 
v_unused_1798_ = lean_ctor_get(v___x_1214_, 0);
lean_dec(v_unused_1798_);
v___x_1220_ = v___x_1214_;
v_isShared_1221_ = v_isSharedCheck_1797_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_snd_1218_);
lean_dec(v___x_1214_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1797_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_str_1222_; lean_object* v_str_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v_str_1222_ = lean_ctor_get(v_fst_1215_, 1);
lean_inc_ref(v_str_1222_);
lean_dec_ref_known(v_fst_1215_, 2);
v_str_1223_ = lean_ctor_get(v_pre_1216_, 1);
lean_inc_ref(v_str_1223_);
lean_dec_ref_known(v_pre_1216_, 2);
v___x_1224_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_1225_ = lean_string_dec_eq(v_str_1223_, v___x_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3));
v___x_1227_ = lean_string_dec_eq(v_str_1223_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0));
v___x_1229_ = lean_string_dec_eq(v_str_1223_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1));
v___x_1231_ = lean_string_dec_eq(v_str_1223_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2));
v___x_1233_ = lean_string_dec_eq(v_str_1223_, v___x_1232_);
lean_dec_ref(v_str_1223_);
if (v___x_1233_ == 0)
{
lean_dec_ref(v_str_1222_);
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3));
v___x_1235_ = lean_string_dec_eq(v_str_1222_, v___x_1234_);
lean_dec_ref(v_str_1222_);
if (v___x_1235_ == 0)
{
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1236_ = lean_array_get_size(v_snd_1218_);
v___x_1237_ = lean_unsigned_to_nat(4u);
v___x_1238_ = lean_nat_dec_eq(v___x_1236_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1239_ = lean_unsigned_to_nat(2u);
v___x_1240_ = lean_array_fget(v_snd_1218_, v___x_1239_);
v___x_1241_ = lean_unsigned_to_nat(3u);
v___x_1242_ = lean_array_fget(v_snd_1218_, v___x_1241_);
lean_dec(v_snd_1218_);
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6);
lean_inc(v___x_1242_);
lean_inc(v___x_1240_);
v___x_1245_ = l_Lean_mkAppB(v___x_1244_, v___x_1240_, v___x_1242_);
v___x_1246_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9);
v___x_1247_ = l_Lean_mkAppB(v___x_1246_, v___x_1240_, v___x_1242_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 1);
lean_ctor_set(v___x_1220_, 1, v___x_1243_);
lean_ctor_set(v___x_1220_, 0, v___x_1247_);
v___x_1249_ = v___x_1220_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v___x_1243_);
v___x_1249_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1245_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
}
}
}
else
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
lean_dec_ref(v_str_1223_);
v___x_1253_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10));
v___x_1254_ = lean_string_dec_eq(v_str_1222_, v___x_1253_);
lean_dec_ref(v_str_1222_);
if (v___x_1254_ == 0)
{
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v___x_1255_ = lean_array_get_size(v_snd_1218_);
v___x_1256_ = lean_unsigned_to_nat(4u);
v___x_1257_ = lean_nat_dec_eq(v___x_1255_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1258_ = lean_unsigned_to_nat(2u);
v___x_1259_ = lean_array_fget(v_snd_1218_, v___x_1258_);
v___x_1260_ = lean_unsigned_to_nat(3u);
v___x_1261_ = lean_array_fget(v_snd_1218_, v___x_1260_);
lean_dec(v_snd_1218_);
v___x_1262_ = lean_box(0);
v___x_1263_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13);
lean_inc(v___x_1261_);
lean_inc(v___x_1259_);
v___x_1264_ = l_Lean_mkAppB(v___x_1263_, v___x_1259_, v___x_1261_);
v___x_1265_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16);
v___x_1266_ = l_Lean_mkAppB(v___x_1265_, v___x_1259_, v___x_1261_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 1);
lean_ctor_set(v___x_1220_, 1, v___x_1262_);
lean_ctor_set(v___x_1220_, 0, v___x_1266_);
v___x_1268_ = v___x_1220_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1262_);
v___x_1268_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1264_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
return v___x_1270_;
}
}
}
}
}
else
{
lean_object* v___x_1272_; uint8_t v___x_1273_; 
lean_dec_ref(v_str_1223_);
v___x_1272_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17));
v___x_1273_ = lean_string_dec_eq(v_str_1222_, v___x_1272_);
lean_dec_ref(v_str_1222_);
if (v___x_1273_ == 0)
{
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1274_ = lean_array_get_size(v_snd_1218_);
v___x_1275_ = lean_unsigned_to_nat(6u);
v___x_1276_ = lean_nat_dec_eq(v___x_1274_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v_fst_1280_; 
v___x_1277_ = lean_unsigned_to_nat(5u);
v___x_1278_ = lean_array_fget(v_snd_1218_, v___x_1277_);
lean_inc(v___x_1278_);
v___x_1279_ = l_Lean_Expr_getAppFnArgs(v___x_1278_);
v_fst_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_fst_1280_);
if (lean_obj_tag(v_fst_1280_) == 1)
{
lean_object* v_pre_1281_; 
v_pre_1281_ = lean_ctor_get(v_fst_1280_, 0);
lean_inc(v_pre_1281_);
if (lean_obj_tag(v_pre_1281_) == 1)
{
lean_object* v_pre_1282_; 
v_pre_1282_ = lean_ctor_get(v_pre_1281_, 0);
if (lean_obj_tag(v_pre_1282_) == 0)
{
lean_object* v_snd_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1541_; 
v_snd_1283_ = lean_ctor_get(v___x_1279_, 1);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; 
v_unused_1542_ = lean_ctor_get(v___x_1279_, 0);
lean_dec(v_unused_1542_);
v___x_1285_ = v___x_1279_;
v_isShared_1286_ = v_isSharedCheck_1541_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_snd_1283_);
lean_dec(v___x_1279_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1541_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_str_1287_; lean_object* v_str_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v_str_1287_ = lean_ctor_get(v_fst_1280_, 1);
lean_inc_ref(v_str_1287_);
lean_dec_ref_known(v_fst_1280_, 2);
v_str_1288_ = lean_ctor_get(v_pre_1281_, 1);
lean_inc_ref(v_str_1288_);
lean_dec_ref_known(v_pre_1281_, 2);
v___x_1289_ = lean_unsigned_to_nat(4u);
v___x_1290_ = lean_array_fget(v_snd_1218_, v___x_1289_);
lean_dec(v_snd_1218_);
v___x_1328_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4));
v___x_1329_ = lean_string_dec_eq(v_str_1288_, v___x_1328_);
if (v___x_1329_ == 0)
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_string_dec_eq(v_str_1288_, v___x_1224_);
lean_dec_ref(v_str_1288_);
if (v___x_1330_ == 0)
{
lean_dec(v___x_1290_);
lean_dec_ref(v_str_1287_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1202_;
}
else
{
lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1331_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1332_ = lean_string_dec_eq(v_str_1287_, v___x_1331_);
lean_dec_ref(v_str_1287_);
if (v___x_1332_ == 0)
{
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1202_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1333_ = lean_array_get_size(v_snd_1283_);
v___x_1334_ = lean_unsigned_to_nat(3u);
v___x_1335_ = lean_nat_dec_eq(v___x_1333_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1202_;
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = lean_array_fget_borrowed(v_snd_1283_, v___x_1336_);
if (lean_obj_tag(v___x_1337_) == 4)
{
lean_object* v_declName_1338_; 
v_declName_1338_ = lean_ctor_get(v___x_1337_, 0);
if (lean_obj_tag(v_declName_1338_) == 1)
{
lean_object* v_pre_1339_; 
v_pre_1339_ = lean_ctor_get(v_declName_1338_, 0);
if (lean_obj_tag(v_pre_1339_) == 0)
{
lean_object* v_us_1340_; lean_object* v_str_1341_; lean_object* v___x_1342_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; uint8_t v___x_1361_; 
v_us_1340_ = lean_ctor_get(v___x_1337_, 1);
lean_inc(v_us_1340_);
v_str_1341_ = lean_ctor_get(v_declName_1338_, 1);
v___x_1342_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1361_ = lean_string_dec_eq(v_str_1341_, v___x_1342_);
if (v___x_1361_ == 0)
{
lean_dec(v_us_1340_);
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1202_;
}
else
{
if (lean_obj_tag(v_us_1340_) == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_fst_1365_; 
v___x_1362_ = lean_unsigned_to_nat(2u);
v___x_1363_ = lean_array_fget(v_snd_1283_, v___x_1362_);
lean_dec(v_snd_1283_);
lean_inc(v___x_1363_);
v___x_1364_ = l_Lean_Expr_getAppFnArgs(v___x_1363_);
v_fst_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_fst_1365_);
if (lean_obj_tag(v_fst_1365_) == 1)
{
lean_object* v_pre_1366_; 
v_pre_1366_ = lean_ctor_get(v_fst_1365_, 0);
lean_inc(v_pre_1366_);
if (lean_obj_tag(v_pre_1366_) == 1)
{
lean_object* v_pre_1367_; 
v_pre_1367_ = lean_ctor_get(v_pre_1366_, 0);
if (lean_obj_tag(v_pre_1367_) == 0)
{
lean_object* v_snd_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1446_; 
v_snd_1368_ = lean_ctor_get(v___x_1364_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; 
v_unused_1447_ = lean_ctor_get(v___x_1364_, 0);
lean_dec(v_unused_1447_);
v___x_1370_ = v___x_1364_;
v_isShared_1371_ = v_isSharedCheck_1446_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_snd_1368_);
lean_dec(v___x_1364_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1446_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v_str_1372_; lean_object* v_str_1373_; uint8_t v___x_1374_; 
v_str_1372_ = lean_ctor_get(v_fst_1365_, 1);
lean_inc_ref(v_str_1372_);
lean_dec_ref_known(v_fst_1365_, 2);
v_str_1373_ = lean_ctor_get(v_pre_1366_, 1);
lean_inc_ref(v_str_1373_);
lean_dec_ref_known(v_pre_1366_, 2);
v___x_1374_ = lean_string_dec_eq(v_str_1373_, v___x_1328_);
lean_dec_ref(v_str_1373_);
if (v___x_1374_ == 0)
{
lean_dec_ref(v_str_1372_);
lean_del_object(v___x_1370_);
lean_dec(v_snd_1368_);
lean_dec(v___x_1363_);
lean_del_object(v___x_1285_);
lean_del_object(v___x_1220_);
goto v___jp_1291_;
}
else
{
lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_1376_ = lean_string_dec_eq(v_str_1372_, v___x_1375_);
lean_dec_ref(v_str_1372_);
if (v___x_1376_ == 0)
{
lean_del_object(v___x_1370_);
lean_dec(v_snd_1368_);
lean_dec(v___x_1363_);
lean_del_object(v___x_1285_);
lean_del_object(v___x_1220_);
goto v___jp_1291_;
}
else
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = lean_array_get_size(v_snd_1368_);
v___x_1378_ = lean_nat_dec_eq(v___x_1377_, v___x_1275_);
if (v___x_1378_ == 0)
{
lean_del_object(v___x_1370_);
lean_dec(v_snd_1368_);
lean_dec(v___x_1363_);
lean_del_object(v___x_1285_);
lean_del_object(v___x_1220_);
goto v___jp_1291_;
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_array_fget(v_snd_1368_, v___x_1289_);
lean_inc(v___x_1379_);
v___x_1380_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1379_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_dec(v___x_1379_);
lean_del_object(v___x_1370_);
lean_dec(v_snd_1368_);
lean_dec(v___x_1363_);
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1208_;
}
else
{
lean_object* v_val_1381_; uint8_t v___x_1382_; 
v_val_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_val_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v___x_1382_ = lean_nat_dec_eq(v_val_1381_, v___x_1336_);
lean_dec(v_val_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_leCarrierIsSort(v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; lean_object* v_____do__lift_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; uint8_t v___x_1435_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = lean_array_fget(v_snd_1368_, v___x_1277_);
lean_dec(v_snd_1368_);
v___x_1435_ = lean_unbox(v_a_1384_);
lean_dec(v_a_1384_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42);
v_____do__lift_1387_ = v___x_1436_;
v___y_1388_ = v_a_1191_;
v___y_1389_ = v_a_1192_;
v___y_1390_ = v_a_1193_;
v___y_1391_ = v_a_1194_;
goto v___jp_1386_;
}
else
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v_____do__lift_1387_ = v___x_1437_;
v___y_1388_ = v_a_1191_;
v___y_1389_ = v_a_1192_;
v___y_1390_ = v_a_1193_;
v___y_1391_ = v_a_1194_;
goto v___jp_1386_;
}
v___jp_1386_:
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1392_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24));
lean_inc(v_____do__lift_1387_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 1);
lean_ctor_set(v___x_1370_, 1, v_us_1340_);
lean_ctor_set(v___x_1370_, 0, v_____do__lift_1387_);
v___x_1394_ = v___x_1370_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_____do__lift_1387_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_us_1340_);
v___x_1394_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1395_ = l_Lean_Expr_const___override(v___x_1392_, v___x_1394_);
v___x_1396_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25));
v___x_1397_ = l_Lean_Expr_const___override(v___x_1396_, v_us_1340_);
v___x_1398_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27));
v___x_1399_ = l_Lean_Expr_const___override(v___x_1398_, v_us_1340_);
v___x_1400_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28);
lean_inc(v___x_1379_);
v___x_1401_ = l_Lean_mkApp4(v___x_1395_, v___x_1397_, v___x_1399_, v___x_1400_, v___x_1379_);
v___x_1402_ = l_Lean_Meta_mkDecideProof(v___x_1401_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
v___x_1404_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30));
v___x_1405_ = l_Lean_Expr_const___override(v___x_1404_, v_us_1340_);
v___x_1406_ = l_Lean_mkApp3(v___x_1405_, v___x_1379_, v___x_1385_, v_a_1403_);
v___x_1407_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32));
v___x_1408_ = l_Lean_Expr_const___override(v___x_1407_, v_us_1340_);
v___x_1409_ = l_Lean_mkAppB(v___x_1408_, v___x_1363_, v___x_1406_);
v___x_1410_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34));
v___x_1411_ = l_Lean_Expr_const___override(v___x_1410_, v_us_1340_);
v___x_1412_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36));
v___x_1413_ = l_Lean_Expr_const___override(v___x_1412_, v_us_1340_);
v___x_1414_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1415_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41));
v___x_1416_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42);
v___x_1417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
lean_ctor_set(v___x_1417_, 1, v_us_1340_);
v___x_1418_ = l_Lean_Expr_const___override(v___x_1415_, v___x_1417_);
v___x_1419_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1));
v___x_1420_ = l_Lean_Expr_const___override(v___x_1419_, v_us_1340_);
v___x_1421_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44));
v___x_1422_ = l_Lean_Expr_const___override(v___x_1421_, v_us_1340_);
v___x_1423_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47);
v___x_1424_ = l_Lean_mkApp3(v___x_1418_, v___x_1420_, v___x_1422_, v___x_1423_);
v___y_1344_ = v___x_1411_;
v___y_1345_ = v___x_1413_;
v___y_1346_ = v___x_1409_;
v___y_1347_ = v___x_1424_;
goto v___jp_1343_;
}
else
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1344_ = v___x_1411_;
v___y_1345_ = v___x_1413_;
v___y_1346_ = v___x_1409_;
v___y_1347_ = v___x_1425_;
goto v___jp_1343_;
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v___x_1385_);
lean_dec(v___x_1379_);
lean_dec(v___x_1363_);
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
v_a_1426_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1402_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1402_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v___x_1379_);
lean_del_object(v___x_1370_);
lean_dec(v_snd_1368_);
lean_dec(v___x_1363_);
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
v_a_1438_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1383_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1383_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_dec(v___x_1379_);
lean_del_object(v___x_1370_);
lean_dec(v_snd_1368_);
lean_dec(v___x_1363_);
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1208_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1366_, 2);
lean_dec_ref_known(v_fst_1365_, 2);
lean_dec_ref(v___x_1364_);
lean_dec(v___x_1363_);
lean_del_object(v___x_1285_);
lean_del_object(v___x_1220_);
goto v___jp_1291_;
}
}
else
{
lean_dec(v_pre_1366_);
lean_dec_ref_known(v_fst_1365_, 2);
lean_dec_ref(v___x_1364_);
lean_dec(v___x_1363_);
lean_del_object(v___x_1285_);
lean_del_object(v___x_1220_);
goto v___jp_1291_;
}
}
else
{
lean_dec(v_fst_1365_);
lean_dec_ref(v___x_1364_);
lean_dec(v___x_1363_);
lean_del_object(v___x_1285_);
lean_del_object(v___x_1220_);
goto v___jp_1291_;
}
}
else
{
lean_dec(v_us_1340_);
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1202_;
}
}
v___jp_1343_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
lean_inc_ref(v___y_1346_);
lean_inc_n(v___x_1278_, 2);
v___x_1348_ = l_Lean_mkApp3(v___y_1345_, v___x_1278_, v___y_1347_, v___y_1346_);
lean_inc(v___x_1290_);
v___x_1349_ = l_Lean_mkApp3(v___y_1344_, v___x_1290_, v___x_1278_, v___x_1348_);
v___x_1350_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21));
v___x_1351_ = l_Lean_Expr_const___override(v___x_1350_, v_us_1340_);
v___x_1352_ = l_Lean_mkApp3(v___x_1351_, v___x_1290_, v___x_1278_, v___y_1346_);
v___x_1353_ = lean_box(0);
if (v_isShared_1286_ == 0)
{
lean_ctor_set_tag(v___x_1285_, 1);
lean_ctor_set(v___x_1285_, 1, v___x_1353_);
lean_ctor_set(v___x_1285_, 0, v___x_1352_);
v___x_1355_ = v___x_1285_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1357_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 1);
lean_ctor_set(v___x_1220_, 1, v___x_1355_);
lean_ctor_set(v___x_1220_, 0, v___x_1349_);
v___x_1357_ = v___x_1220_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
}
}
}
else
{
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1202_;
}
}
else
{
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1202_;
}
}
else
{
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1202_;
}
}
}
}
}
else
{
lean_object* v___x_1448_; uint8_t v___x_1449_; 
lean_dec_ref(v_str_1288_);
v___x_1448_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_1449_ = lean_string_dec_eq(v_str_1287_, v___x_1448_);
lean_dec_ref(v_str_1287_);
if (v___x_1449_ == 0)
{
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1202_;
}
else
{
lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1450_ = lean_array_get_size(v_snd_1283_);
v___x_1451_ = lean_nat_dec_eq(v___x_1450_, v___x_1275_);
if (v___x_1451_ == 0)
{
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1202_;
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_array_fget(v_snd_1283_, v___x_1289_);
lean_inc(v___x_1452_);
v___x_1453_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1452_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_dec(v___x_1452_);
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1211_;
}
else
{
lean_object* v_val_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_val_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_val_1454_);
lean_dec_ref_known(v___x_1453_, 1);
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = lean_nat_dec_eq(v_val_1454_, v___x_1455_);
lean_dec(v_val_1454_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_leCarrierIsSort(v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v_____do__lift_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; uint8_t v___x_1530_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = lean_array_fget(v_snd_1283_, v___x_1277_);
lean_dec(v_snd_1283_);
v___x_1530_ = lean_unbox(v_a_1458_);
lean_dec(v_a_1458_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42);
v_____do__lift_1515_ = v___x_1531_;
v___y_1516_ = v_a_1191_;
v___y_1517_ = v_a_1192_;
v___y_1518_ = v_a_1193_;
v___y_1519_ = v_a_1194_;
goto v___jp_1514_;
}
else
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v_____do__lift_1515_ = v___x_1532_;
v___y_1516_ = v_a_1191_;
v___y_1517_ = v_a_1192_;
v___y_1518_ = v_a_1193_;
v___y_1519_ = v_a_1194_;
goto v___jp_1514_;
}
v___jp_1460_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_inc(v___x_1452_);
lean_inc_ref(v___y_1470_);
lean_inc_ref(v___y_1465_);
lean_inc_ref(v___y_1468_);
v___x_1471_ = l_Lean_mkApp4(v___y_1463_, v___y_1468_, v___y_1465_, v___y_1470_, v___x_1452_);
v___x_1472_ = l_Lean_Meta_mkDecideProof(v___x_1471_, v___y_1462_, v___y_1464_, v___y_1467_, v___y_1469_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1505_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1505_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1505_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1477_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0));
v___x_1478_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1));
v___x_1479_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51));
lean_inc_ref_n(v___y_1466_, 4);
v___x_1480_ = l_Lean_Name_mkStr4(v___x_1477_, v___x_1478_, v___y_1466_, v___x_1479_);
lean_inc_n(v___y_1461_, 4);
v___x_1481_ = l_Lean_Expr_const___override(v___x_1480_, v___y_1461_);
v___x_1482_ = l_Lean_mkApp3(v___x_1481_, v___x_1452_, v___x_1459_, v_a_1473_);
v___x_1483_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33));
v___x_1484_ = l_Lean_Name_mkStr2(v___y_1466_, v___x_1483_);
v___x_1485_ = l_Lean_Expr_const___override(v___x_1484_, v___y_1461_);
v___x_1486_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35));
v___x_1487_ = l_Lean_Name_mkStr2(v___y_1466_, v___x_1486_);
v___x_1488_ = l_Lean_Expr_const___override(v___x_1487_, v___y_1461_);
lean_inc_ref(v___x_1482_);
lean_inc_ref(v___y_1470_);
lean_inc_n(v___x_1278_, 2);
v___x_1489_ = l_Lean_mkApp3(v___x_1488_, v___x_1278_, v___y_1470_, v___x_1482_);
lean_inc(v___x_1290_);
v___x_1490_ = l_Lean_mkApp3(v___x_1485_, v___x_1290_, v___x_1278_, v___x_1489_);
v___x_1491_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20));
v___x_1492_ = l_Lean_Name_mkStr2(v___y_1466_, v___x_1491_);
v___x_1493_ = l_Lean_Expr_const___override(v___x_1492_, v___y_1461_);
v___x_1494_ = l_Lean_mkApp3(v___x_1493_, v___x_1290_, v___x_1278_, v___x_1482_);
v___x_1495_ = lean_box(0);
if (v_isShared_1286_ == 0)
{
lean_ctor_set_tag(v___x_1285_, 1);
lean_ctor_set(v___x_1285_, 1, v___x_1495_);
lean_ctor_set(v___x_1285_, 0, v___x_1494_);
v___x_1497_ = v___x_1285_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 1);
lean_ctor_set(v___x_1220_, 1, v___x_1497_);
lean_ctor_set(v___x_1220_, 0, v___x_1490_);
v___x_1499_ = v___x_1220_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1499_);
v___x_1501_ = v___x_1475_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec(v___x_1459_);
lean_dec(v___x_1452_);
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
v_a_1506_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1472_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1472_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
v___jp_1514_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1520_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24));
v___x_1521_ = lean_box(0);
lean_inc(v_____do__lift_1515_);
v___x_1522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1522_, 0, v_____do__lift_1515_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = l_Lean_Expr_const___override(v___x_1520_, v___x_1522_);
v___x_1524_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1525_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1526_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
v___x_1527_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58);
v___y_1461_ = v___x_1521_;
v___y_1462_ = v___y_1516_;
v___y_1463_ = v___x_1523_;
v___y_1464_ = v___y_1517_;
v___y_1465_ = v___x_1526_;
v___y_1466_ = v___x_1524_;
v___y_1467_ = v___y_1518_;
v___y_1468_ = v___x_1525_;
v___y_1469_ = v___y_1519_;
v___y_1470_ = v___x_1528_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1461_ = v___x_1521_;
v___y_1462_ = v___y_1516_;
v___y_1463_ = v___x_1523_;
v___y_1464_ = v___y_1517_;
v___y_1465_ = v___x_1526_;
v___y_1466_ = v___x_1524_;
v___y_1467_ = v___y_1518_;
v___y_1468_ = v___x_1525_;
v___y_1469_ = v___y_1519_;
v___y_1470_ = v___x_1529_;
goto v___jp_1460_;
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v___x_1452_);
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
v_a_1533_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1457_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1457_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_dec(v___x_1452_);
lean_dec(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
goto v___jp_1211_;
}
}
}
}
}
v___jp_1291_:
{
lean_object* v___x_1292_; lean_object* v_fst_1293_; 
v___x_1292_ = l_Lean_Expr_getAppFnArgs(v___x_1290_);
v_fst_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_fst_1293_);
if (lean_obj_tag(v_fst_1293_) == 1)
{
lean_object* v_pre_1294_; 
v_pre_1294_ = lean_ctor_get(v_fst_1293_, 0);
lean_inc(v_pre_1294_);
if (lean_obj_tag(v_pre_1294_) == 1)
{
lean_object* v_pre_1295_; 
v_pre_1295_ = lean_ctor_get(v_pre_1294_, 0);
if (lean_obj_tag(v_pre_1295_) == 0)
{
lean_object* v_snd_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1326_; 
v_snd_1296_ = lean_ctor_get(v___x_1292_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v___x_1292_, 0);
lean_dec(v_unused_1327_);
v___x_1298_ = v___x_1292_;
v_isShared_1299_ = v_isSharedCheck_1326_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_snd_1296_);
lean_dec(v___x_1292_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1326_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v_str_1300_; lean_object* v_str_1301_; uint8_t v___x_1302_; 
v_str_1300_ = lean_ctor_get(v_fst_1293_, 1);
lean_inc_ref(v_str_1300_);
lean_dec_ref_known(v_fst_1293_, 2);
v_str_1301_ = lean_ctor_get(v_pre_1294_, 1);
lean_inc_ref(v_str_1301_);
lean_dec_ref_known(v_pre_1294_, 2);
v___x_1302_ = lean_string_dec_eq(v_str_1301_, v___x_1224_);
lean_dec_ref(v_str_1301_);
if (v___x_1302_ == 0)
{
lean_dec_ref(v_str_1300_);
lean_del_object(v___x_1298_);
lean_dec(v_snd_1296_);
lean_dec(v___x_1278_);
goto v___jp_1205_;
}
else
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1304_ = lean_string_dec_eq(v_str_1300_, v___x_1303_);
lean_dec_ref(v_str_1300_);
if (v___x_1304_ == 0)
{
lean_del_object(v___x_1298_);
lean_dec(v_snd_1296_);
lean_dec(v___x_1278_);
goto v___jp_1205_;
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1305_ = lean_array_get_size(v_snd_1296_);
v___x_1306_ = lean_unsigned_to_nat(3u);
v___x_1307_ = lean_nat_dec_eq(v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_del_object(v___x_1298_);
lean_dec(v_snd_1296_);
lean_dec(v___x_1278_);
goto v___jp_1205_;
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_array_fget_borrowed(v_snd_1296_, v___x_1308_);
if (lean_obj_tag(v___x_1309_) == 4)
{
lean_object* v_declName_1310_; 
v_declName_1310_ = lean_ctor_get(v___x_1309_, 0);
if (lean_obj_tag(v_declName_1310_) == 1)
{
lean_object* v_pre_1311_; 
v_pre_1311_ = lean_ctor_get(v_declName_1310_, 0);
if (lean_obj_tag(v_pre_1311_) == 0)
{
lean_object* v_us_1312_; lean_object* v_str_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v_us_1312_ = lean_ctor_get(v___x_1309_, 1);
lean_inc(v_us_1312_);
v_str_1313_ = lean_ctor_get(v_declName_1310_, 1);
v___x_1314_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1315_ = lean_string_dec_eq(v_str_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_dec(v_us_1312_);
lean_del_object(v___x_1298_);
lean_dec(v_snd_1296_);
lean_dec(v___x_1278_);
goto v___jp_1205_;
}
else
{
if (lean_obj_tag(v_us_1312_) == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1316_ = lean_unsigned_to_nat(2u);
v___x_1317_ = lean_array_fget(v_snd_1296_, v___x_1316_);
lean_dec(v_snd_1296_);
v___x_1318_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19));
v___x_1319_ = l_Lean_Expr_const___override(v___x_1318_, v_us_1312_);
v___x_1320_ = l_Lean_mkAppB(v___x_1319_, v___x_1317_, v___x_1278_);
v___x_1321_ = lean_box(0);
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 1);
lean_ctor_set(v___x_1298_, 1, v___x_1321_);
lean_ctor_set(v___x_1298_, 0, v___x_1320_);
v___x_1323_ = v___x_1298_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
}
else
{
lean_dec(v_us_1312_);
lean_del_object(v___x_1298_);
lean_dec(v_snd_1296_);
lean_dec(v___x_1278_);
goto v___jp_1205_;
}
}
}
else
{
lean_del_object(v___x_1298_);
lean_dec(v_snd_1296_);
lean_dec(v___x_1278_);
goto v___jp_1205_;
}
}
else
{
lean_del_object(v___x_1298_);
lean_dec(v_snd_1296_);
lean_dec(v___x_1278_);
goto v___jp_1205_;
}
}
else
{
lean_del_object(v___x_1298_);
lean_dec(v_snd_1296_);
lean_dec(v___x_1278_);
goto v___jp_1205_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1294_, 2);
lean_dec_ref_known(v_fst_1293_, 2);
lean_dec_ref(v___x_1292_);
lean_dec(v___x_1278_);
goto v___jp_1205_;
}
}
else
{
lean_dec(v_pre_1294_);
lean_dec_ref_known(v_fst_1293_, 2);
lean_dec_ref(v___x_1292_);
lean_dec(v___x_1278_);
goto v___jp_1205_;
}
}
else
{
lean_dec(v_fst_1293_);
lean_dec_ref(v___x_1292_);
lean_dec(v___x_1278_);
goto v___jp_1205_;
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1281_, 2);
lean_dec_ref_known(v_fst_1280_, 2);
lean_dec_ref(v___x_1279_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1202_;
}
}
else
{
lean_dec_ref_known(v_fst_1280_, 2);
lean_dec(v_pre_1281_);
lean_dec_ref(v___x_1279_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1202_;
}
}
else
{
lean_dec(v_fst_1280_);
lean_dec_ref(v___x_1279_);
lean_dec(v___x_1278_);
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1202_;
}
}
}
}
}
else
{
lean_object* v___x_1543_; uint8_t v___x_1544_; 
lean_dec_ref(v_str_1223_);
v___x_1543_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7));
v___x_1544_ = lean_string_dec_eq(v_str_1222_, v___x_1543_);
lean_dec_ref(v_str_1222_);
if (v___x_1544_ == 0)
{
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1545_ = lean_array_get_size(v_snd_1218_);
v___x_1546_ = lean_unsigned_to_nat(6u);
v___x_1547_ = lean_nat_dec_eq(v___x_1545_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = lean_unsigned_to_nat(5u);
v___x_1549_ = lean_array_fget(v_snd_1218_, v___x_1548_);
lean_inc(v___x_1549_);
v___x_1550_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1549_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_dec(v___x_1549_);
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1196_;
}
else
{
lean_object* v_val_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v_val_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = lean_nat_dec_eq(v_val_1551_, v___x_1552_);
lean_dec(v_val_1551_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v_____do__lift_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1609_; uint8_t v___x_1623_; 
v___x_1554_ = lean_unsigned_to_nat(4u);
v___x_1555_ = lean_array_fget(v_snd_1218_, v___x_1554_);
lean_dec(v_snd_1218_);
v___x_1556_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62);
v___x_1559_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1623_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58);
v___y_1609_ = v___x_1624_;
goto v___jp_1608_;
}
else
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1609_ = v___x_1625_;
goto v___jp_1608_;
}
v___jp_1560_:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Meta_mkDecideProof(v___y_1562_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
lean_inc(v_____do__lift_1563_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 1);
lean_ctor_set(v___x_1220_, 1, v___x_1557_);
lean_ctor_set(v___x_1220_, 0, v_____do__lift_1563_);
v___x_1571_ = v___x_1220_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_____do__lift_1563_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___x_1557_);
v___x_1571_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1572_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24));
v___x_1573_ = l_Lean_Expr_const___override(v___x_1572_, v___x_1571_);
v___x_1574_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
lean_inc(v___x_1549_);
lean_inc_ref(v___y_1561_);
v___x_1575_ = l_Lean_mkApp4(v___x_1573_, v___x_1559_, v___x_1574_, v___y_1561_, v___x_1549_);
v___x_1576_ = l_Lean_Meta_mkDecideProof(v___x_1575_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1590_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1581_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65);
lean_inc(v___x_1549_);
lean_inc(v___x_1555_);
v___x_1582_ = l_Lean_mkApp3(v___x_1581_, v___x_1555_, v___x_1549_, v_a_1569_);
v___x_1583_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68);
v___x_1584_ = l_Lean_mkApp3(v___x_1583_, v___x_1555_, v___x_1549_, v_a_1577_);
v___x_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v___x_1557_);
v___x_1586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1582_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1586_);
v___x_1588_ = v___x_1579_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_a_1569_);
lean_dec(v___x_1555_);
lean_dec(v___x_1549_);
v_a_1591_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1576_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1576_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v___x_1555_);
lean_dec(v___x_1549_);
lean_del_object(v___x_1220_);
v_a_1600_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1568_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1568_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
v___jp_1608_:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_leCarrierIsSort(v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v_ne__zero_1612_; uint8_t v___x_1613_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
lean_inc_ref(v___y_1609_);
lean_inc(v___x_1549_);
v_ne__zero_1612_ = l_Lean_mkApp3(v___x_1558_, v___x_1559_, v___x_1549_, v___y_1609_);
v___x_1613_ = lean_unbox(v_a_1611_);
lean_dec(v_a_1611_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42);
v___y_1561_ = v___y_1609_;
v___y_1562_ = v_ne__zero_1612_;
v_____do__lift_1563_ = v___x_1614_;
v___y_1564_ = v_a_1191_;
v___y_1565_ = v_a_1192_;
v___y_1566_ = v_a_1193_;
v___y_1567_ = v_a_1194_;
goto v___jp_1560_;
}
else
{
v___y_1561_ = v___y_1609_;
v___y_1562_ = v_ne__zero_1612_;
v_____do__lift_1563_ = v___x_1556_;
v___y_1564_ = v_a_1191_;
v___y_1565_ = v_a_1192_;
v___y_1566_ = v_a_1193_;
v___y_1567_ = v_a_1194_;
goto v___jp_1560_;
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v___x_1555_);
lean_dec(v___x_1549_);
lean_del_object(v___x_1220_);
v_a_1615_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1610_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1610_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
else
{
lean_dec(v___x_1549_);
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1196_;
}
}
}
}
}
}
else
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
lean_dec_ref(v_str_1223_);
v___x_1626_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1627_ = lean_string_dec_eq(v_str_1222_, v___x_1626_);
lean_dec_ref(v_str_1222_);
if (v___x_1627_ == 0)
{
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1628_ = lean_array_get_size(v_snd_1218_);
v___x_1629_ = lean_unsigned_to_nat(3u);
v___x_1630_ = lean_nat_dec_eq(v___x_1628_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = lean_array_fget_borrowed(v_snd_1218_, v___x_1631_);
if (lean_obj_tag(v___x_1632_) == 4)
{
lean_object* v_declName_1633_; 
v_declName_1633_ = lean_ctor_get(v___x_1632_, 0);
if (lean_obj_tag(v_declName_1633_) == 1)
{
lean_object* v_pre_1634_; 
v_pre_1634_ = lean_ctor_get(v_declName_1633_, 0);
if (lean_obj_tag(v_pre_1634_) == 0)
{
lean_object* v_us_1635_; lean_object* v_str_1636_; lean_object* v___x_1637_; lean_object* v___y_1639_; lean_object* v___y_1640_; uint8_t v___x_1650_; 
v_us_1635_ = lean_ctor_get(v___x_1632_, 1);
lean_inc(v_us_1635_);
v_str_1636_ = lean_ctor_get(v_declName_1633_, 1);
v___x_1637_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1650_ = lean_string_dec_eq(v_str_1636_, v___x_1637_);
if (v___x_1650_ == 0)
{
lean_dec(v_us_1635_);
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
else
{
if (lean_obj_tag(v_us_1635_) == 0)
{
uint8_t v_splitNatSub_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v_r_1658_; lean_object* v_n_1660_; lean_object* v_x_1661_; lean_object* v_n_1670_; lean_object* v_i_1671_; lean_object* v_x_1680_; 
v_splitNatSub_1651_ = lean_ctor_get_uint8(v_a_1190_, 1);
v___x_1652_ = lean_unsigned_to_nat(2u);
v___x_1653_ = lean_array_fget(v_snd_1218_, v___x_1652_);
lean_dec(v_snd_1218_);
v___x_1654_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72));
v___x_1655_ = l_Lean_Expr_const___override(v___x_1654_, v_us_1635_);
lean_inc(v___x_1653_);
v___x_1656_ = l_Lean_Expr_app___override(v___x_1655_, v___x_1653_);
v___x_1657_ = lean_box(0);
v_r_1658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_r_1658_, 0, v___x_1656_);
lean_ctor_set(v_r_1658_, 1, v___x_1657_);
if (v_splitNatSub_1651_ == 1)
{
lean_object* v___x_1686_; lean_object* v_fst_1687_; 
v___x_1686_ = l_Lean_Expr_getAppFnArgs(v___x_1653_);
v_fst_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_fst_1687_);
if (lean_obj_tag(v_fst_1687_) == 1)
{
lean_object* v_pre_1688_; 
v_pre_1688_ = lean_ctor_get(v_fst_1687_, 0);
lean_inc(v_pre_1688_);
if (lean_obj_tag(v_pre_1688_) == 1)
{
lean_object* v_pre_1689_; 
v_pre_1689_ = lean_ctor_get(v_pre_1688_, 0);
if (lean_obj_tag(v_pre_1689_) == 0)
{
lean_object* v_snd_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1750_; 
v_snd_1690_ = lean_ctor_get(v___x_1686_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v___x_1686_, 0);
lean_dec(v_unused_1751_);
v___x_1692_ = v___x_1686_;
v_isShared_1693_ = v_isSharedCheck_1750_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_snd_1690_);
lean_dec(v___x_1686_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1750_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v_str_1694_; lean_object* v_str_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v_str_1694_ = lean_ctor_get(v_fst_1687_, 1);
lean_inc_ref(v_str_1694_);
lean_dec_ref_known(v_fst_1687_, 2);
v_str_1695_ = lean_ctor_get(v_pre_1688_, 1);
lean_inc_ref(v_str_1695_);
lean_dec_ref_known(v_pre_1688_, 2);
v___x_1696_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2));
v___x_1697_ = lean_string_dec_eq(v_str_1695_, v___x_1696_);
if (v___x_1697_ == 0)
{
uint8_t v___x_1698_; 
lean_del_object(v___x_1692_);
v___x_1698_ = lean_string_dec_eq(v_str_1695_, v___x_1637_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; uint8_t v___x_1700_; 
lean_del_object(v___x_1220_);
v___x_1699_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76));
v___x_1700_ = lean_string_dec_eq(v_str_1695_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; uint8_t v___x_1702_; 
v___x_1701_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73));
v___x_1702_ = lean_string_dec_eq(v_str_1695_, v___x_1701_);
lean_dec_ref(v_str_1695_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; 
lean_dec_ref(v_str_1694_);
lean_dec(v_snd_1690_);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_r_1658_);
return v___x_1703_;
}
else
{
lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1704_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80));
v___x_1705_ = lean_string_dec_eq(v_str_1694_, v___x_1704_);
lean_dec_ref(v_str_1694_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
lean_dec(v_snd_1690_);
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_r_1658_);
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1707_ = lean_array_get_size(v_snd_1690_);
v___x_1708_ = lean_nat_dec_eq(v___x_1707_, v___x_1652_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; 
lean_dec(v_snd_1690_);
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_r_1658_);
return v___x_1709_;
}
else
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = lean_array_fget(v_snd_1690_, v___x_1631_);
v___x_1711_ = lean_unsigned_to_nat(1u);
v___x_1712_ = lean_array_fget(v_snd_1690_, v___x_1711_);
lean_dec(v_snd_1690_);
v_n_1660_ = v___x_1710_;
v_x_1661_ = v___x_1712_;
goto v___jp_1659_;
}
}
}
}
else
{
lean_object* v___x_1713_; uint8_t v___x_1714_; 
lean_dec_ref(v_str_1695_);
v___x_1713_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81));
v___x_1714_ = lean_string_dec_eq(v_str_1694_, v___x_1713_);
lean_dec_ref(v_str_1694_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_dec(v_snd_1690_);
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v_r_1658_);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = lean_array_get_size(v_snd_1690_);
v___x_1717_ = lean_nat_dec_eq(v___x_1716_, v___x_1652_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
lean_dec(v_snd_1690_);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_r_1658_);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_array_fget(v_snd_1690_, v___x_1631_);
v___x_1720_ = lean_unsigned_to_nat(1u);
v___x_1721_ = lean_array_fget(v_snd_1690_, v___x_1720_);
lean_dec(v_snd_1690_);
v_n_1670_ = v___x_1719_;
v_i_1671_ = v___x_1721_;
goto v___jp_1669_;
}
}
}
}
else
{
lean_object* v___x_1722_; uint8_t v___x_1723_; 
lean_dec_ref(v_str_1695_);
v___x_1722_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82));
v___x_1723_ = lean_string_dec_eq(v_str_1694_, v___x_1722_);
lean_dec_ref(v_str_1694_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
lean_dec(v_snd_1690_);
lean_del_object(v___x_1220_);
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_r_1658_);
return v___x_1724_;
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1725_ = lean_array_get_size(v_snd_1690_);
v___x_1726_ = lean_unsigned_to_nat(1u);
v___x_1727_ = lean_nat_dec_eq(v___x_1725_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; 
lean_dec(v_snd_1690_);
lean_del_object(v___x_1220_);
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_r_1658_);
return v___x_1728_;
}
else
{
lean_object* v___x_1729_; 
v___x_1729_ = lean_array_fget(v_snd_1690_, v___x_1631_);
lean_dec(v_snd_1690_);
v_x_1680_ = v___x_1729_;
goto v___jp_1679_;
}
}
}
}
else
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
lean_dec_ref(v_str_1695_);
lean_del_object(v___x_1220_);
v___x_1730_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9));
v___x_1731_ = lean_string_dec_eq(v_str_1694_, v___x_1730_);
lean_dec_ref(v_str_1694_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; 
lean_del_object(v___x_1692_);
lean_dec(v_snd_1690_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_r_1658_);
return v___x_1732_;
}
else
{
lean_object* v___x_1733_; lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1733_ = lean_array_get_size(v_snd_1690_);
v___x_1734_ = lean_unsigned_to_nat(6u);
v___x_1735_ = lean_nat_dec_eq(v___x_1733_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
lean_del_object(v___x_1692_);
lean_dec(v_snd_1690_);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v_r_1658_);
return v___x_1736_;
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1737_ = lean_unsigned_to_nat(4u);
v___x_1738_ = lean_array_fget(v_snd_1690_, v___x_1737_);
v___x_1739_ = lean_unsigned_to_nat(5u);
v___x_1740_ = lean_array_fget(v_snd_1690_, v___x_1739_);
lean_dec(v_snd_1690_);
v___x_1741_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84));
v___x_1742_ = l_Lean_Expr_const___override(v___x_1741_, v_us_1635_);
v___x_1743_ = l_Lean_mkAppB(v___x_1742_, v___x_1738_, v___x_1740_);
v___x_1744_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1743_, v_r_1658_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1746_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set_tag(v___x_1692_, 1);
lean_ctor_set(v___x_1692_, 1, v_r_1658_);
lean_ctor_set(v___x_1692_, 0, v___x_1743_);
v___x_1746_ = v___x_1692_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_r_1658_);
v___x_1746_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
return v___x_1747_;
}
}
else
{
lean_object* v___x_1749_; 
lean_dec_ref(v___x_1743_);
lean_del_object(v___x_1692_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v_r_1658_);
return v___x_1749_;
}
}
}
}
}
}
else
{
lean_object* v___x_1752_; 
lean_dec_ref_known(v_pre_1688_, 2);
lean_dec_ref_known(v_fst_1687_, 2);
lean_dec_ref(v___x_1686_);
lean_del_object(v___x_1220_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_r_1658_);
return v___x_1752_;
}
}
else
{
lean_object* v___x_1753_; 
lean_dec_ref_known(v_fst_1687_, 2);
lean_dec(v_pre_1688_);
lean_dec_ref(v___x_1686_);
lean_del_object(v___x_1220_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_r_1658_);
return v___x_1753_;
}
}
else
{
lean_object* v___x_1754_; 
lean_dec(v_fst_1687_);
lean_dec_ref(v___x_1686_);
lean_del_object(v___x_1220_);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_r_1658_);
return v___x_1754_;
}
}
else
{
lean_object* v___x_1755_; lean_object* v_fst_1756_; 
v___x_1755_ = l_Lean_Expr_getAppFnArgs(v___x_1653_);
v_fst_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_fst_1756_);
if (lean_obj_tag(v_fst_1756_) == 1)
{
lean_object* v_pre_1757_; 
v_pre_1757_ = lean_ctor_get(v_fst_1756_, 0);
lean_inc(v_pre_1757_);
if (lean_obj_tag(v_pre_1757_) == 1)
{
lean_object* v_pre_1758_; 
v_pre_1758_ = lean_ctor_get(v_pre_1757_, 0);
if (lean_obj_tag(v_pre_1758_) == 0)
{
lean_object* v_snd_1759_; lean_object* v_str_1760_; lean_object* v_str_1761_; uint8_t v___x_1762_; 
v_snd_1759_ = lean_ctor_get(v___x_1755_, 1);
lean_inc(v_snd_1759_);
lean_dec_ref(v___x_1755_);
v_str_1760_ = lean_ctor_get(v_fst_1756_, 1);
lean_inc_ref(v_str_1760_);
lean_dec_ref_known(v_fst_1756_, 2);
v_str_1761_ = lean_ctor_get(v_pre_1757_, 1);
lean_inc_ref(v_str_1761_);
lean_dec_ref_known(v_pre_1757_, 2);
v___x_1762_ = lean_string_dec_eq(v_str_1761_, v___x_1637_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
lean_del_object(v___x_1220_);
v___x_1763_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76));
v___x_1764_ = lean_string_dec_eq(v_str_1761_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73));
v___x_1766_ = lean_string_dec_eq(v_str_1761_, v___x_1765_);
lean_dec_ref(v_str_1761_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; 
lean_dec_ref(v_str_1760_);
lean_dec(v_snd_1759_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v_r_1658_);
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80));
v___x_1769_ = lean_string_dec_eq(v_str_1760_, v___x_1768_);
lean_dec_ref(v_str_1760_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; 
lean_dec(v_snd_1759_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_r_1658_);
return v___x_1770_;
}
else
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = lean_array_get_size(v_snd_1759_);
v___x_1772_ = lean_nat_dec_eq(v___x_1771_, v___x_1652_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; 
lean_dec(v_snd_1759_);
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v_r_1658_);
return v___x_1773_;
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_array_fget(v_snd_1759_, v___x_1631_);
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1776_ = lean_array_fget(v_snd_1759_, v___x_1775_);
lean_dec(v_snd_1759_);
v_n_1660_ = v___x_1774_;
v_x_1661_ = v___x_1776_;
goto v___jp_1659_;
}
}
}
}
else
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
lean_dec_ref(v_str_1761_);
v___x_1777_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81));
v___x_1778_ = lean_string_dec_eq(v_str_1760_, v___x_1777_);
lean_dec_ref(v_str_1760_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; 
lean_dec(v_snd_1759_);
v___x_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1779_, 0, v_r_1658_);
return v___x_1779_;
}
else
{
lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = lean_array_get_size(v_snd_1759_);
v___x_1781_ = lean_nat_dec_eq(v___x_1780_, v___x_1652_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; 
lean_dec(v_snd_1759_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_r_1658_);
return v___x_1782_;
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = lean_array_fget(v_snd_1759_, v___x_1631_);
v___x_1784_ = lean_unsigned_to_nat(1u);
v___x_1785_ = lean_array_fget(v_snd_1759_, v___x_1784_);
lean_dec(v_snd_1759_);
v_n_1670_ = v___x_1783_;
v_i_1671_ = v___x_1785_;
goto v___jp_1669_;
}
}
}
}
else
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
lean_dec_ref(v_str_1761_);
v___x_1786_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82));
v___x_1787_ = lean_string_dec_eq(v_str_1760_, v___x_1786_);
lean_dec_ref(v_str_1760_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; 
lean_dec(v_snd_1759_);
lean_del_object(v___x_1220_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v_r_1658_);
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1789_ = lean_array_get_size(v_snd_1759_);
v___x_1790_ = lean_unsigned_to_nat(1u);
v___x_1791_ = lean_nat_dec_eq(v___x_1789_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; 
lean_dec(v_snd_1759_);
lean_del_object(v___x_1220_);
v___x_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1792_, 0, v_r_1658_);
return v___x_1792_;
}
else
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_array_fget(v_snd_1759_, v___x_1631_);
lean_dec(v_snd_1759_);
v_x_1680_ = v___x_1793_;
goto v___jp_1679_;
}
}
}
}
else
{
lean_object* v___x_1794_; 
lean_dec_ref_known(v_pre_1757_, 2);
lean_dec_ref_known(v_fst_1756_, 2);
lean_dec_ref(v___x_1755_);
lean_del_object(v___x_1220_);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v_r_1658_);
return v___x_1794_;
}
}
else
{
lean_object* v___x_1795_; 
lean_dec_ref_known(v_fst_1756_, 2);
lean_dec(v_pre_1757_);
lean_dec_ref(v___x_1755_);
lean_del_object(v___x_1220_);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v_r_1658_);
return v___x_1795_;
}
}
else
{
lean_object* v___x_1796_; 
lean_dec(v_fst_1756_);
lean_dec_ref(v___x_1755_);
lean_del_object(v___x_1220_);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v_r_1658_);
return v___x_1796_;
}
}
v___jp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1662_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75));
v___x_1663_ = l_Lean_Expr_const___override(v___x_1662_, v_us_1635_);
v___x_1664_ = l_Lean_mkAppB(v___x_1663_, v_n_1660_, v_x_1661_);
v___x_1665_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1664_, v_r_1658_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v_r_1658_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
return v___x_1667_;
}
else
{
lean_object* v___x_1668_; 
lean_dec_ref(v___x_1664_);
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v_r_1658_);
return v___x_1668_;
}
}
v___jp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1672_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77));
v___x_1673_ = l_Lean_Expr_const___override(v___x_1672_, v_us_1635_);
v___x_1674_ = l_Lean_mkAppB(v___x_1673_, v_n_1670_, v_i_1671_);
v___x_1675_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1674_, v_r_1658_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v_r_1658_);
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
return v___x_1677_;
}
else
{
lean_object* v___x_1678_; 
lean_dec_ref(v___x_1674_);
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v_r_1658_);
return v___x_1678_;
}
}
v___jp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1681_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79));
v___x_1682_ = l_Lean_Expr_const___override(v___x_1681_, v_us_1635_);
lean_inc_ref(v_x_1680_);
v___x_1683_ = l_Lean_Expr_app___override(v___x_1682_, v_x_1680_);
v___x_1684_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1683_, v_r_1658_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v_r_1658_);
v___y_1639_ = v_x_1680_;
v___y_1640_ = v___x_1685_;
goto v___jp_1638_;
}
else
{
lean_dec_ref(v___x_1683_);
v___y_1639_ = v_x_1680_;
v___y_1640_ = v_r_1658_;
goto v___jp_1638_;
}
}
}
else
{
lean_dec(v_us_1635_);
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
}
v___jp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1641_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70));
v___x_1642_ = l_Lean_Expr_const___override(v___x_1641_, v_us_1635_);
v___x_1643_ = l_Lean_Expr_app___override(v___x_1642_, v___y_1639_);
v___x_1644_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1643_, v___y_1640_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1646_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 1);
lean_ctor_set(v___x_1220_, 1, v___y_1640_);
lean_ctor_set(v___x_1220_, 0, v___x_1643_);
v___x_1646_ = v___x_1220_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v___y_1640_);
v___x_1646_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
}
else
{
lean_object* v___x_1649_; 
lean_dec_ref(v___x_1643_);
lean_del_object(v___x_1220_);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___y_1640_);
return v___x_1649_;
}
}
}
else
{
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
}
else
{
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
}
else
{
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
goto v___jp_1199_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1216_, 2);
lean_dec_ref_known(v_fst_1215_, 2);
lean_dec_ref(v___x_1214_);
goto v___jp_1199_;
}
}
case 0:
{
lean_object* v_snd_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1829_; 
v_snd_1799_ = lean_ctor_get(v___x_1214_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v___x_1214_, 0);
lean_dec(v_unused_1830_);
v___x_1801_ = v___x_1214_;
v_isShared_1802_ = v_isSharedCheck_1829_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_snd_1799_);
lean_dec(v___x_1214_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1829_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_str_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v_str_1803_ = lean_ctor_get(v_fst_1215_, 1);
lean_inc_ref(v_str_1803_);
lean_dec_ref_known(v_fst_1215_, 2);
v___x_1804_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85));
v___x_1805_ = lean_string_dec_eq(v_str_1803_, v___x_1804_);
lean_dec_ref(v_str_1803_);
if (v___x_1805_ == 0)
{
lean_del_object(v___x_1801_);
lean_dec(v_snd_1799_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1806_ = lean_array_get_size(v_snd_1799_);
v___x_1807_ = lean_unsigned_to_nat(5u);
v___x_1808_ = lean_nat_dec_eq(v___x_1806_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_del_object(v___x_1801_);
lean_dec(v_snd_1799_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1809_ = lean_unsigned_to_nat(0u);
v___x_1810_ = lean_array_fget(v_snd_1799_, v___x_1809_);
v___x_1811_ = lean_box(0);
v___x_1812_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1813_ = lean_expr_eqv(v___x_1810_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; 
lean_dec(v___x_1810_);
lean_del_object(v___x_1801_);
lean_dec(v_snd_1799_);
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1811_);
return v___x_1814_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1815_ = lean_unsigned_to_nat(1u);
v___x_1816_ = lean_array_fget(v_snd_1799_, v___x_1815_);
v___x_1817_ = lean_unsigned_to_nat(2u);
v___x_1818_ = lean_array_fget(v_snd_1799_, v___x_1817_);
v___x_1819_ = lean_unsigned_to_nat(3u);
v___x_1820_ = lean_array_fget(v_snd_1799_, v___x_1819_);
v___x_1821_ = lean_unsigned_to_nat(4u);
v___x_1822_ = lean_array_fget(v_snd_1799_, v___x_1821_);
lean_dec(v_snd_1799_);
v___x_1823_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88);
v___x_1824_ = l_Lean_mkApp5(v___x_1823_, v___x_1810_, v___x_1816_, v___x_1818_, v___x_1820_, v___x_1822_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set_tag(v___x_1801_, 1);
lean_ctor_set(v___x_1801_, 1, v___x_1811_);
lean_ctor_set(v___x_1801_, 0, v___x_1824_);
v___x_1826_ = v___x_1801_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v___x_1811_);
v___x_1826_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; 
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_fst_1215_, 2);
lean_dec_ref(v___x_1214_);
goto v___jp_1199_;
}
}
}
else
{
lean_dec(v_fst_1215_);
lean_dec_ref(v___x_1214_);
goto v___jp_1199_;
}
v___jp_1196_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_box(0);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
v___jp_1199_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
v___jp_1202_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_box(0);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
v___jp_1205_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_box(0);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
v___jp_1208_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_box(0);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
return v___x_1210_;
}
v___jp_1211_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(lean_object* v_e_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_e_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec_ref(v_a_1832_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object* v_e_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, uint8_t v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_e_1839_, v_a_1842_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object* v_e_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
uint8_t v_a_boxed_1862_; lean_object* v_res_1863_; 
v_a_boxed_1862_ = lean_unbox(v_a_1855_);
v_res_1863_ = l_Lean_Elab_Tactic_Omega_analyzeAtom(v_e_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_boxed_1862_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1854_);
lean_dec(v_a_1853_);
lean_dec(v_a_1852_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(lean_object* v_a_1864_, lean_object* v_x_1865_){
_start:
{
if (lean_obj_tag(v_x_1865_) == 0)
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_box(0);
return v___x_1866_;
}
else
{
lean_object* v_key_1867_; lean_object* v_value_1868_; lean_object* v_tail_1869_; uint8_t v___x_1870_; 
v_key_1867_ = lean_ctor_get(v_x_1865_, 0);
v_value_1868_ = lean_ctor_get(v_x_1865_, 1);
v_tail_1869_ = lean_ctor_get(v_x_1865_, 2);
v___x_1870_ = lean_expr_eqv(v_key_1867_, v_a_1864_);
if (v___x_1870_ == 0)
{
v_x_1865_ = v_tail_1869_;
goto _start;
}
else
{
lean_object* v___x_1872_; 
lean_inc(v_value_1868_);
v___x_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_value_1868_);
return v___x_1872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg___boxed(lean_object* v_a_1873_, lean_object* v_x_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_1873_, v_x_1874_);
lean_dec(v_x_1874_);
lean_dec_ref(v_a_1873_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object* v_m_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v_buckets_1878_; lean_object* v___x_1879_; uint64_t v___x_1880_; uint64_t v___x_1881_; uint64_t v___x_1882_; uint64_t v_fold_1883_; uint64_t v___x_1884_; uint64_t v___x_1885_; uint64_t v___x_1886_; size_t v___x_1887_; size_t v___x_1888_; size_t v___x_1889_; size_t v___x_1890_; size_t v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v_buckets_1878_ = lean_ctor_get(v_m_1876_, 1);
v___x_1879_ = lean_array_get_size(v_buckets_1878_);
v___x_1880_ = l_Lean_Expr_hash(v_a_1877_);
v___x_1881_ = 32ULL;
v___x_1882_ = lean_uint64_shift_right(v___x_1880_, v___x_1881_);
v_fold_1883_ = lean_uint64_xor(v___x_1880_, v___x_1882_);
v___x_1884_ = 16ULL;
v___x_1885_ = lean_uint64_shift_right(v_fold_1883_, v___x_1884_);
v___x_1886_ = lean_uint64_xor(v_fold_1883_, v___x_1885_);
v___x_1887_ = lean_uint64_to_usize(v___x_1886_);
v___x_1888_ = lean_usize_of_nat(v___x_1879_);
v___x_1889_ = ((size_t)1ULL);
v___x_1890_ = lean_usize_sub(v___x_1888_, v___x_1889_);
v___x_1891_ = lean_usize_land(v___x_1887_, v___x_1890_);
v___x_1892_ = lean_array_uget_borrowed(v_buckets_1878_, v___x_1891_);
v___x_1893_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_1877_, v___x_1892_);
return v___x_1893_;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(lean_object* v_a_1897_, lean_object* v_x_1898_){
_start:
{
if (lean_obj_tag(v_x_1898_) == 0)
{
uint8_t v___x_1899_; 
v___x_1899_ = 0;
return v___x_1899_;
}
else
{
lean_object* v_key_1900_; lean_object* v_tail_1901_; uint8_t v___x_1902_; 
v_key_1900_ = lean_ctor_get(v_x_1898_, 0);
v_tail_1901_ = lean_ctor_get(v_x_1898_, 2);
v___x_1902_ = lean_expr_eqv(v_key_1900_, v_a_1897_);
if (v___x_1902_ == 0)
{
v_x_1898_ = v_tail_1901_;
goto _start;
}
else
{
return v___x_1902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg___boxed(lean_object* v_a_1904_, lean_object* v_x_1905_){
_start:
{
uint8_t v_res_1906_; lean_object* v_r_1907_; 
v_res_1906_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_1904_, v_x_1905_);
lean_dec(v_x_1905_);
lean_dec_ref(v_a_1904_);
v_r_1907_ = lean_box(v_res_1906_);
return v_r_1907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(lean_object* v_x_1908_, lean_object* v_x_1909_){
_start:
{
if (lean_obj_tag(v_x_1909_) == 0)
{
return v_x_1908_;
}
else
{
lean_object* v_key_1910_; lean_object* v_value_1911_; lean_object* v_tail_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1935_; 
v_key_1910_ = lean_ctor_get(v_x_1909_, 0);
v_value_1911_ = lean_ctor_get(v_x_1909_, 1);
v_tail_1912_ = lean_ctor_get(v_x_1909_, 2);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_x_1909_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1914_ = v_x_1909_;
v_isShared_1915_ = v_isSharedCheck_1935_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_tail_1912_);
lean_inc(v_value_1911_);
lean_inc(v_key_1910_);
lean_dec(v_x_1909_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1935_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; uint64_t v___x_1917_; uint64_t v___x_1918_; uint64_t v___x_1919_; uint64_t v_fold_1920_; uint64_t v___x_1921_; uint64_t v___x_1922_; uint64_t v___x_1923_; size_t v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; size_t v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1916_ = lean_array_get_size(v_x_1908_);
v___x_1917_ = l_Lean_Expr_hash(v_key_1910_);
v___x_1918_ = 32ULL;
v___x_1919_ = lean_uint64_shift_right(v___x_1917_, v___x_1918_);
v_fold_1920_ = lean_uint64_xor(v___x_1917_, v___x_1919_);
v___x_1921_ = 16ULL;
v___x_1922_ = lean_uint64_shift_right(v_fold_1920_, v___x_1921_);
v___x_1923_ = lean_uint64_xor(v_fold_1920_, v___x_1922_);
v___x_1924_ = lean_uint64_to_usize(v___x_1923_);
v___x_1925_ = lean_usize_of_nat(v___x_1916_);
v___x_1926_ = ((size_t)1ULL);
v___x_1927_ = lean_usize_sub(v___x_1925_, v___x_1926_);
v___x_1928_ = lean_usize_land(v___x_1924_, v___x_1927_);
v___x_1929_ = lean_array_uget_borrowed(v_x_1908_, v___x_1928_);
lean_inc(v___x_1929_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 2, v___x_1929_);
v___x_1931_ = v___x_1914_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_key_1910_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_value_1911_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_array_uset(v_x_1908_, v___x_1928_, v___x_1931_);
v_x_1908_ = v___x_1932_;
v_x_1909_ = v_tail_1912_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1936_, lean_object* v_source_1937_, lean_object* v_target_1938_){
_start:
{
lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1939_ = lean_array_get_size(v_source_1937_);
v___x_1940_ = lean_nat_dec_lt(v_i_1936_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_dec_ref(v_source_1937_);
lean_dec(v_i_1936_);
return v_target_1938_;
}
else
{
lean_object* v_es_1941_; lean_object* v___x_1942_; lean_object* v_source_1943_; lean_object* v_target_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_es_1941_ = lean_array_fget(v_source_1937_, v_i_1936_);
v___x_1942_ = lean_box(0);
v_source_1943_ = lean_array_fset(v_source_1937_, v_i_1936_, v___x_1942_);
v_target_1944_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(v_target_1938_, v_es_1941_);
v___x_1945_ = lean_unsigned_to_nat(1u);
v___x_1946_ = lean_nat_add(v_i_1936_, v___x_1945_);
lean_dec(v_i_1936_);
v_i_1936_ = v___x_1946_;
v_source_1937_ = v_source_1943_;
v_target_1938_ = v_target_1944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(lean_object* v_data_1948_){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v_nbuckets_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1949_ = lean_array_get_size(v_data_1948_);
v___x_1950_ = lean_unsigned_to_nat(2u);
v_nbuckets_1951_ = lean_nat_mul(v___x_1949_, v___x_1950_);
v___x_1952_ = lean_unsigned_to_nat(0u);
v___x_1953_ = lean_box(0);
v___x_1954_ = lean_mk_array(v_nbuckets_1951_, v___x_1953_);
v___x_1955_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(v___x_1952_, v_data_1948_, v___x_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(lean_object* v_a_1956_, lean_object* v_b_1957_, lean_object* v_x_1958_){
_start:
{
if (lean_obj_tag(v_x_1958_) == 0)
{
lean_dec(v_b_1957_);
lean_dec_ref(v_a_1956_);
return v_x_1958_;
}
else
{
lean_object* v_key_1959_; lean_object* v_value_1960_; lean_object* v_tail_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1973_; 
v_key_1959_ = lean_ctor_get(v_x_1958_, 0);
v_value_1960_ = lean_ctor_get(v_x_1958_, 1);
v_tail_1961_ = lean_ctor_get(v_x_1958_, 2);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_x_1958_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1963_ = v_x_1958_;
v_isShared_1964_ = v_isSharedCheck_1973_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_tail_1961_);
lean_inc(v_value_1960_);
lean_inc(v_key_1959_);
lean_dec(v_x_1958_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1973_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
uint8_t v___x_1965_; 
v___x_1965_ = lean_expr_eqv(v_key_1959_, v_a_1956_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1966_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_1956_, v_b_1957_, v_tail_1961_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 2, v___x_1966_);
v___x_1968_ = v___x_1963_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_key_1959_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_value_1960_);
lean_ctor_set(v_reuseFailAlloc_1969_, 2, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
else
{
lean_object* v___x_1971_; 
lean_dec(v_value_1960_);
lean_dec(v_key_1959_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v_b_1957_);
lean_ctor_set(v___x_1963_, 0, v_a_1956_);
v___x_1971_ = v___x_1963_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1956_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_b_1957_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_tail_1961_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object* v_m_1974_, lean_object* v_a_1975_, lean_object* v_b_1976_){
_start:
{
lean_object* v_size_1977_; lean_object* v_buckets_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2021_; 
v_size_1977_ = lean_ctor_get(v_m_1974_, 0);
v_buckets_1978_ = lean_ctor_get(v_m_1974_, 1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_m_1974_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1980_ = v_m_1974_;
v_isShared_1981_ = v_isSharedCheck_2021_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_buckets_1978_);
lean_inc(v_size_1977_);
lean_dec(v_m_1974_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2021_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; uint64_t v___x_1983_; uint64_t v___x_1984_; uint64_t v___x_1985_; uint64_t v_fold_1986_; uint64_t v___x_1987_; uint64_t v___x_1988_; uint64_t v___x_1989_; size_t v___x_1990_; size_t v___x_1991_; size_t v___x_1992_; size_t v___x_1993_; size_t v___x_1994_; lean_object* v_bkt_1995_; uint8_t v___x_1996_; 
v___x_1982_ = lean_array_get_size(v_buckets_1978_);
v___x_1983_ = l_Lean_Expr_hash(v_a_1975_);
v___x_1984_ = 32ULL;
v___x_1985_ = lean_uint64_shift_right(v___x_1983_, v___x_1984_);
v_fold_1986_ = lean_uint64_xor(v___x_1983_, v___x_1985_);
v___x_1987_ = 16ULL;
v___x_1988_ = lean_uint64_shift_right(v_fold_1986_, v___x_1987_);
v___x_1989_ = lean_uint64_xor(v_fold_1986_, v___x_1988_);
v___x_1990_ = lean_uint64_to_usize(v___x_1989_);
v___x_1991_ = lean_usize_of_nat(v___x_1982_);
v___x_1992_ = ((size_t)1ULL);
v___x_1993_ = lean_usize_sub(v___x_1991_, v___x_1992_);
v___x_1994_ = lean_usize_land(v___x_1990_, v___x_1993_);
v_bkt_1995_ = lean_array_uget_borrowed(v_buckets_1978_, v___x_1994_);
v___x_1996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_1975_, v_bkt_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v_size_x27_1998_; lean_object* v___x_1999_; lean_object* v_buckets_x27_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v___x_1997_ = lean_unsigned_to_nat(1u);
v_size_x27_1998_ = lean_nat_add(v_size_1977_, v___x_1997_);
lean_dec(v_size_1977_);
lean_inc(v_bkt_1995_);
v___x_1999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1999_, 0, v_a_1975_);
lean_ctor_set(v___x_1999_, 1, v_b_1976_);
lean_ctor_set(v___x_1999_, 2, v_bkt_1995_);
v_buckets_x27_2000_ = lean_array_uset(v_buckets_1978_, v___x_1994_, v___x_1999_);
v___x_2001_ = lean_unsigned_to_nat(4u);
v___x_2002_ = lean_nat_mul(v_size_x27_1998_, v___x_2001_);
v___x_2003_ = lean_unsigned_to_nat(3u);
v___x_2004_ = lean_nat_div(v___x_2002_, v___x_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_array_get_size(v_buckets_x27_2000_);
v___x_2006_ = lean_nat_dec_le(v___x_2004_, v___x_2005_);
lean_dec(v___x_2004_);
if (v___x_2006_ == 0)
{
lean_object* v_val_2007_; lean_object* v___x_2009_; 
v_val_2007_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_buckets_x27_2000_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 1, v_val_2007_);
lean_ctor_set(v___x_1980_, 0, v_size_x27_1998_);
v___x_2009_ = v___x_1980_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_size_x27_1998_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_val_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
else
{
lean_object* v___x_2012_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 1, v_buckets_x27_2000_);
lean_ctor_set(v___x_1980_, 0, v_size_x27_1998_);
v___x_2012_ = v___x_1980_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_size_x27_1998_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_buckets_x27_2000_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
else
{
lean_object* v___x_2014_; lean_object* v_buckets_x27_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
lean_inc(v_bkt_1995_);
v___x_2014_ = lean_box(0);
v_buckets_x27_2015_ = lean_array_uset(v_buckets_1978_, v___x_1994_, v___x_2014_);
v___x_2016_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_1975_, v_b_1976_, v_bkt_1995_);
v___x_2017_ = lean_array_uset(v_buckets_x27_2015_, v___x_1994_, v___x_2016_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 1, v___x_2017_);
v___x_2019_ = v___x_1980_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_size_1977_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(lean_object* v_msgData_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v___x_2028_; lean_object* v_env_2029_; lean_object* v___x_2030_; lean_object* v_mctx_2031_; lean_object* v_lctx_2032_; lean_object* v_options_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2028_ = lean_st_ref_get(v___y_2026_);
v_env_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc_ref(v_env_2029_);
lean_dec(v___x_2028_);
v___x_2030_ = lean_st_ref_get(v___y_2024_);
v_mctx_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc_ref(v_mctx_2031_);
lean_dec(v___x_2030_);
v_lctx_2032_ = lean_ctor_get(v___y_2023_, 2);
v_options_2033_ = lean_ctor_get(v___y_2025_, 2);
lean_inc_ref(v_options_2033_);
lean_inc_ref(v_lctx_2032_);
v___x_2034_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2034_, 0, v_env_2029_);
lean_ctor_set(v___x_2034_, 1, v_mctx_2031_);
lean_ctor_set(v___x_2034_, 2, v_lctx_2032_);
lean_ctor_set(v___x_2034_, 3, v_options_2033_);
v___x_2035_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
lean_ctor_set(v___x_2035_, 1, v_msgData_2022_);
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8___boxed(lean_object* v_msgData_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(v_msgData_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
return v_res_2043_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2044_; double v___x_2045_; 
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = lean_float_of_nat(v___x_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(lean_object* v_cls_2049_, lean_object* v_msg_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_ref_2056_; lean_object* v___x_2057_; lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2102_; 
v_ref_2056_ = lean_ctor_get(v___y_2053_, 5);
v___x_2057_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(v_msg_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2102_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2102_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v_traceState_2063_; lean_object* v_env_2064_; lean_object* v_nextMacroScope_2065_; lean_object* v_ngen_2066_; lean_object* v_auxDeclNGen_2067_; lean_object* v_cache_2068_; lean_object* v_messages_2069_; lean_object* v_infoState_2070_; lean_object* v_snapshotTasks_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2101_; 
v___x_2062_ = lean_st_ref_take(v___y_2054_);
v_traceState_2063_ = lean_ctor_get(v___x_2062_, 4);
v_env_2064_ = lean_ctor_get(v___x_2062_, 0);
v_nextMacroScope_2065_ = lean_ctor_get(v___x_2062_, 1);
v_ngen_2066_ = lean_ctor_get(v___x_2062_, 2);
v_auxDeclNGen_2067_ = lean_ctor_get(v___x_2062_, 3);
v_cache_2068_ = lean_ctor_get(v___x_2062_, 5);
v_messages_2069_ = lean_ctor_get(v___x_2062_, 6);
v_infoState_2070_ = lean_ctor_get(v___x_2062_, 7);
v_snapshotTasks_2071_ = lean_ctor_get(v___x_2062_, 8);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2073_ = v___x_2062_;
v_isShared_2074_ = v_isSharedCheck_2101_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_snapshotTasks_2071_);
lean_inc(v_infoState_2070_);
lean_inc(v_messages_2069_);
lean_inc(v_cache_2068_);
lean_inc(v_traceState_2063_);
lean_inc(v_auxDeclNGen_2067_);
lean_inc(v_ngen_2066_);
lean_inc(v_nextMacroScope_2065_);
lean_inc(v_env_2064_);
lean_dec(v___x_2062_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2101_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
uint64_t v_tid_2075_; lean_object* v_traces_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2100_; 
v_tid_2075_ = lean_ctor_get_uint64(v_traceState_2063_, sizeof(void*)*1);
v_traces_2076_ = lean_ctor_get(v_traceState_2063_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_traceState_2063_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2078_ = v_traceState_2063_;
v_isShared_2079_ = v_isSharedCheck_2100_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_traces_2076_);
lean_dec(v_traceState_2063_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2100_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; double v___x_2081_; uint8_t v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2080_ = lean_box(0);
v___x_2081_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0);
v___x_2082_ = 0;
v___x_2083_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1));
v___x_2084_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2084_, 0, v_cls_2049_);
lean_ctor_set(v___x_2084_, 1, v___x_2080_);
lean_ctor_set(v___x_2084_, 2, v___x_2083_);
lean_ctor_set_float(v___x_2084_, sizeof(void*)*3, v___x_2081_);
lean_ctor_set_float(v___x_2084_, sizeof(void*)*3 + 8, v___x_2081_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*3 + 16, v___x_2082_);
v___x_2085_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2));
v___x_2086_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2084_);
lean_ctor_set(v___x_2086_, 1, v_a_2058_);
lean_ctor_set(v___x_2086_, 2, v___x_2085_);
lean_inc(v_ref_2056_);
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v_ref_2056_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = l_Lean_PersistentArray_push___redArg(v_traces_2076_, v___x_2087_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2088_);
v___x_2090_ = v___x_2078_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2088_);
lean_ctor_set_uint64(v_reuseFailAlloc_2099_, sizeof(void*)*1, v_tid_2075_);
v___x_2090_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2092_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v___x_2090_);
v___x_2092_ = v___x_2073_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_env_2064_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_nextMacroScope_2065_);
lean_ctor_set(v_reuseFailAlloc_2098_, 2, v_ngen_2066_);
lean_ctor_set(v_reuseFailAlloc_2098_, 3, v_auxDeclNGen_2067_);
lean_ctor_set(v_reuseFailAlloc_2098_, 4, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2098_, 5, v_cache_2068_);
lean_ctor_set(v_reuseFailAlloc_2098_, 6, v_messages_2069_);
lean_ctor_set(v_reuseFailAlloc_2098_, 7, v_infoState_2070_);
lean_ctor_set(v_reuseFailAlloc_2098_, 8, v_snapshotTasks_2071_);
v___x_2092_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2093_ = lean_st_ref_set(v___y_2054_, v___x_2092_);
v___x_2094_ = lean_box(0);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2094_);
v___x_2096_ = v___x_2060_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___boxed(lean_object* v_cls_2103_, lean_object* v_msg_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v_cls_2103_, v_msg_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object* v_x_2111_, lean_object* v_x_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
if (lean_obj_tag(v_x_2111_) == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = l_List_reverse___redArg(v_x_2112_);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
else
{
lean_object* v_head_2120_; lean_object* v_tail_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2139_; 
v_head_2120_ = lean_ctor_get(v_x_2111_, 0);
v_tail_2121_ = lean_ctor_get(v_x_2111_, 1);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_x_2111_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2123_ = v_x_2111_;
v_isShared_2124_ = v_isSharedCheck_2139_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_tail_2121_);
lean_inc(v_head_2120_);
lean_dec(v_x_2111_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2139_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; 
lean_inc(v___y_2116_);
lean_inc_ref(v___y_2115_);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
v___x_2125_ = lean_infer_type(v_head_2120_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 1, v_x_2112_);
lean_ctor_set(v___x_2123_, 0, v_a_2126_);
v___x_2128_ = v___x_2123_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2126_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_x_2112_);
v___x_2128_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
v_x_2111_ = v_tail_2121_;
v_x_2112_ = v___x_2128_;
goto _start;
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_del_object(v___x_2123_);
lean_dec(v_tail_2121_);
lean_dec(v_x_2112_);
v_a_2131_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2125_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2125_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(lean_object* v_x_2140_, lean_object* v_x_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_x_2140_, v_x_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
if (lean_obj_tag(v_a_2148_) == 0)
{
lean_object* v___x_2150_; 
v___x_2150_ = l_List_reverse___redArg(v_a_2149_);
return v___x_2150_;
}
else
{
lean_object* v_head_2151_; lean_object* v_tail_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2161_; 
v_head_2151_ = lean_ctor_get(v_a_2148_, 0);
v_tail_2152_ = lean_ctor_get(v_a_2148_, 1);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_a_2148_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2154_ = v_a_2148_;
v_isShared_2155_ = v_isSharedCheck_2161_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_tail_2152_);
lean_inc(v_head_2151_);
lean_dec(v_a_2148_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2161_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = l_Lean_MessageData_ofExpr(v_head_2151_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v_a_2149_);
lean_ctor_set(v___x_2154_, 0, v___x_2156_);
v___x_2158_ = v___x_2154_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_a_2149_);
v___x_2158_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
v_a_2148_ = v_tail_2152_;
v_a_2149_ = v___x_2158_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4(void){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__1));
v___x_2169_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__3));
v___x_2170_ = l_Lean_Name_append(v___x_2169_, v___x_2168_);
return v___x_2170_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__5));
v___x_2173_ = l_Lean_stringToMessageData(v___x_2172_);
return v___x_2173_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__7));
v___x_2176_ = l_Lean_stringToMessageData(v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object* v_e_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, uint8_t v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_st_ref_get(v_a_2179_);
v___x_2189_ = l_Lean_Meta_Canonicalizer_canon(v_e_2177_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2286_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2286_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2286_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___x_2206_; 
v___x_2206_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v___x_2188_, v_a_2190_);
lean_dec(v___x_2188_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_options_2207_; lean_object* v_inheritedTraceOptions_2208_; uint8_t v_hasTrace_2209_; lean_object* v___x_2210_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; uint8_t v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; 
v_options_2207_ = lean_ctor_get(v_a_2185_, 2);
v_inheritedTraceOptions_2208_ = lean_ctor_get(v_a_2185_, 13);
v_hasTrace_2209_ = lean_ctor_get_uint8(v_options_2207_, sizeof(void*)*1);
v___x_2210_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__1));
if (v_hasTrace_2209_ == 0)
{
v___y_2212_ = v_a_2178_;
v___y_2213_ = v_a_2179_;
v___y_2214_ = v_a_2180_;
v___y_2215_ = v_a_2181_;
v___y_2216_ = v_a_2182_;
v___y_2217_ = v_a_2183_;
v___y_2218_ = v_a_2184_;
v___y_2219_ = v_a_2185_;
v___y_2220_ = v_a_2186_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__4, &l_Lean_Elab_Tactic_Omega_lookup___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4);
v___x_2263_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2208_, v_options_2207_, v___x_2262_);
if (v___x_2263_ == 0)
{
v___y_2212_ = v_a_2178_;
v___y_2213_ = v_a_2179_;
v___y_2214_ = v_a_2180_;
v___y_2215_ = v_a_2181_;
v___y_2216_ = v_a_2182_;
v___y_2217_ = v_a_2183_;
v___y_2218_ = v_a_2184_;
v___y_2219_ = v_a_2185_;
v___y_2220_ = v_a_2186_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2264_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__8, &l_Lean_Elab_Tactic_Omega_lookup___closed__8_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8);
lean_inc(v_a_2190_);
v___x_2265_ = l_Lean_MessageData_ofExpr(v_a_2190_);
v___x_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v___x_2210_, v___x_2266_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_dec_ref_known(v___x_2267_, 1);
v___y_2212_ = v_a_2178_;
v___y_2213_ = v_a_2179_;
v___y_2214_ = v_a_2180_;
v___y_2215_ = v_a_2181_;
v___y_2216_ = v_a_2182_;
v___y_2217_ = v_a_2183_;
v___y_2218_ = v_a_2184_;
v___y_2219_ = v_a_2185_;
v___y_2220_ = v_a_2186_;
goto v___jp_2211_;
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_del_object(v___x_2192_);
lean_dec(v_a_2190_);
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2267_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2267_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
v___jp_2211_:
{
lean_object* v___x_2221_; 
lean_inc(v_a_2190_);
v___x_2221_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_a_2190_, v___y_2214_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_options_2222_; uint8_t v_hasTrace_2223_; 
v_options_2222_ = lean_ctor_get(v___y_2219_, 2);
v_hasTrace_2223_ = lean_ctor_get_uint8(v_options_2222_, sizeof(void*)*1);
if (v_hasTrace_2223_ == 0)
{
lean_object* v_a_2224_; 
v_a_2224_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2221_, 1);
v___y_2195_ = v_a_2224_;
v___y_2196_ = v___y_2213_;
goto v___jp_2194_;
}
else
{
lean_object* v_a_2225_; lean_object* v_inheritedTraceOptions_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v_a_2225_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2221_, 1);
v_inheritedTraceOptions_2226_ = lean_ctor_get(v___y_2219_, 13);
v___x_2227_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__4, &l_Lean_Elab_Tactic_Omega_lookup___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4);
v___x_2228_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2226_, v_options_2222_, v___x_2227_);
if (v___x_2228_ == 0)
{
v___y_2195_ = v_a_2225_;
v___y_2196_ = v___y_2213_;
goto v___jp_2194_;
}
else
{
uint8_t v___x_2229_; 
v___x_2229_ = l_List_isEmpty___redArg(v_a_2225_);
if (v___x_2229_ == 0)
{
if (v___x_2228_ == 0)
{
v___y_2195_ = v_a_2225_;
v___y_2196_ = v___y_2213_;
goto v___jp_2194_;
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_box(0);
lean_inc(v_a_2225_);
v___x_2231_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_a_2225_, v___x_2230_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2231_, 1);
v___x_2233_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__6, &l_Lean_Elab_Tactic_Omega_lookup___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6);
v___x_2234_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(v_a_2232_, v___x_2230_);
v___x_2235_ = l_Lean_MessageData_ofList(v___x_2234_);
v___x_2236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2233_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
v___x_2237_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v___x_2210_, v___x_2236_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_dec_ref_known(v___x_2237_, 1);
v___y_2195_ = v_a_2225_;
v___y_2196_ = v___y_2213_;
goto v___jp_2194_;
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v_a_2225_);
lean_del_object(v___x_2192_);
lean_dec(v_a_2190_);
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v_a_2225_);
lean_del_object(v___x_2192_);
lean_dec(v_a_2190_);
v_a_2246_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2231_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2231_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
else
{
v___y_2195_ = v_a_2225_;
v___y_2196_ = v___y_2213_;
goto v___jp_2194_;
}
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_del_object(v___x_2192_);
lean_dec(v_a_2190_);
v_a_2254_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2221_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2221_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
else
{
lean_object* v_val_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2285_; 
lean_del_object(v___x_2192_);
lean_dec(v_a_2190_);
v_val_2276_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2278_ = v___x_2206_;
v_isShared_2279_ = v_isSharedCheck_2285_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_val_2276_);
lean_dec(v___x_2206_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2285_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2280_ = lean_box(0);
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v_val_2276_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set_tag(v___x_2278_, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2281_);
v___x_2283_ = v___x_2278_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
v___jp_2194_:
{
lean_object* v___x_2197_; lean_object* v_size_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2197_ = lean_st_ref_take(v___y_2196_);
v_size_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc_n(v_size_2198_, 2);
v___x_2199_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v___x_2197_, v_a_2190_, v_size_2198_);
v___x_2200_ = lean_st_ref_set(v___y_2196_, v___x_2199_);
v___x_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___y_2195_);
v___x_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2202_, 0, v_size_2198_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2202_);
v___x_2204_ = v___x_2192_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2202_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec(v___x_2188_);
v_a_2287_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2189_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2189_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object* v_e_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_){
_start:
{
uint8_t v_a_boxed_2306_; lean_object* v_res_2307_; 
v_a_boxed_2306_ = lean_unbox(v_a_2299_);
v_res_2307_ = l_Lean_Elab_Tactic_Omega_lookup(v_e_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_boxed_2306_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
lean_dec(v_a_2304_);
lean_dec_ref(v_a_2303_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec(v_a_2296_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(lean_object* v_00_u03b2_2308_, lean_object* v_m_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_2309_, v_a_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(lean_object* v_00_u03b2_2312_, lean_object* v_m_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(v_00_u03b2_2312_, v_m_2313_, v_a_2314_);
lean_dec_ref(v_a_2314_);
lean_dec_ref(v_m_2313_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object* v_00_u03b2_2316_, lean_object* v_m_2317_, lean_object* v_a_2318_, lean_object* v_b_2319_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v_m_2317_, v_a_2318_, v_b_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object* v_x_2321_, lean_object* v_x_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, uint8_t v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_x_2321_, v_x_2322_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(lean_object* v_x_2334_, lean_object* v_x_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
uint8_t v___y_42962__boxed_2346_; lean_object* v_res_2347_; 
v___y_42962__boxed_2346_ = lean_unbox(v___y_2339_);
v_res_2347_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(v_x_2334_, v_x_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_42962__boxed_2346_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec(v___y_2336_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(lean_object* v_cls_2348_, lean_object* v_msg_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, uint8_t v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v_cls_2348_, v_msg_2349_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___boxed(lean_object* v_cls_2361_, lean_object* v_msg_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
uint8_t v___y_42998__boxed_2373_; lean_object* v_res_2374_; 
v___y_42998__boxed_2373_ = lean_unbox(v___y_2366_);
v_res_2374_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(v_cls_2361_, v_msg_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_42998__boxed_2373_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec(v___y_2363_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(lean_object* v_00_u03b2_2375_, lean_object* v_a_2376_, lean_object* v_x_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_2376_, v_x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2379_, lean_object* v_a_2380_, lean_object* v_x_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(v_00_u03b2_2379_, v_a_2380_, v_x_2381_);
lean_dec(v_x_2381_);
lean_dec_ref(v_a_2380_);
return v_res_2382_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(lean_object* v_00_u03b2_2383_, lean_object* v_a_2384_, lean_object* v_x_2385_){
_start:
{
uint8_t v___x_2386_; 
v___x_2386_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_2384_, v_x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2387_, lean_object* v_a_2388_, lean_object* v_x_2389_){
_start:
{
uint8_t v_res_2390_; lean_object* v_r_2391_; 
v_res_2390_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(v_00_u03b2_2387_, v_a_2388_, v_x_2389_);
lean_dec(v_x_2389_);
lean_dec_ref(v_a_2388_);
v_r_2391_ = lean_box(v_res_2390_);
return v_r_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3(lean_object* v_00_u03b2_2392_, lean_object* v_data_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_data_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4(lean_object* v_00_u03b2_2395_, lean_object* v_a_2396_, lean_object* v_b_2397_, lean_object* v_x_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_2396_, v_b_2397_, v_x_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2400_, lean_object* v_i_2401_, lean_object* v_source_2402_, lean_object* v_target_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(v_i_2401_, v_source_2402_, v_target_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(v_x_2406_, v_x_2407_);
return v___x_2408_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Canonicalizer(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Lean_OrderLevel(uint8_t builtin);
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
res = runtime_initialize_Lean_OrderLevel(builtin);
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
lean_object* initialize_Lean_OrderLevel(uint8_t builtin);
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
res = initialize_Lean_OrderLevel(builtin);
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
