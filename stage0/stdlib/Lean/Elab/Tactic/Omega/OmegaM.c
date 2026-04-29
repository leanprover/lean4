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
v___y_246_ = v___y_253_;
v___y_247_ = v___y_252_;
v___y_248_ = v___y_254_;
goto v___jp_244_;
}
else
{
v___y_245_ = v___y_254_;
v___y_246_ = v___y_253_;
v___y_247_ = v___y_252_;
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
v___y_252_ = v___x_258_;
v___y_253_ = v___y_257_;
v___y_254_ = v___x_262_;
goto v___jp_250_;
}
else
{
v___y_251_ = v___x_262_;
v___y_252_ = v___x_258_;
v___y_253_ = v___y_257_;
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
uint8_t v___y_657__boxed_574_; lean_object* v_res_575_; 
v___y_657__boxed_574_ = lean_unbox(v___y_567_);
v_res_575_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(v_t_563_, v___y_564_, v___y_565_, v___y_566_, v___y_657__boxed_574_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
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
lean_dec_ref(v_fst_633_);
v_str_638_ = lean_ctor_get(v_pre_634_, 1);
lean_inc_ref(v_str_638_);
lean_dec_ref(v_pre_634_);
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
lean_dec_ref(v_pre_634_);
lean_dec_ref(v_fst_633_);
lean_dec_ref(v___x_632_);
v___x_652_ = l_Lean_Expr_nat_x3f(v_n_631_);
return v___x_652_;
}
}
else
{
lean_object* v___x_653_; 
lean_dec_ref(v_fst_633_);
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
lean_dec_ref(v_fst_659_);
v_str_664_ = lean_ctor_get(v_pre_660_, 1);
lean_inc_ref(v_str_664_);
lean_dec_ref(v_pre_660_);
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
lean_dec_ref(v_pre_660_);
lean_dec_ref(v_fst_659_);
lean_dec_ref(v___x_658_);
v___x_688_ = l_Lean_Expr_int_x3f(v_n_657_);
return v___x_688_;
}
}
else
{
lean_object* v___x_689_; 
lean_dec_ref(v_fst_659_);
lean_dec(v_pre_660_);
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
lean_dec_ref(v_fst_708_);
v_str_713_ = lean_ctor_get(v_pre_709_, 1);
lean_inc_ref(v_str_713_);
lean_dec_ref(v_pre_709_);
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
lean_dec_ref(v_pre_709_);
lean_dec_ref(v_fst_708_);
lean_dec_ref(v___x_707_);
v___x_802_ = l_Lean_Expr_nat_x3f(v_e_706_);
return v___x_802_;
}
}
else
{
lean_object* v___x_803_; 
lean_dec(v_pre_709_);
lean_dec_ref(v_fst_708_);
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
lean_dec_ref(v___x_808_);
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
lean_dec_ref(v_fst_828_);
v_str_833_ = lean_ctor_get(v_pre_829_, 1);
lean_inc_ref(v_str_833_);
lean_dec_ref(v_pre_829_);
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
lean_dec_ref(v___x_856_);
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
lean_dec_ref(v_pre_829_);
lean_dec_ref(v_fst_828_);
lean_dec_ref(v___x_827_);
v___x_944_ = l_Lean_Expr_int_x3f(v_e_826_);
return v___x_944_;
}
}
else
{
lean_object* v___x_945_; 
lean_dec_ref(v_fst_828_);
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
lean_dec_ref(v___x_950_);
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
lean_dec_ref(v___x_971_);
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
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = l_Lean_Level_ofNat(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_unsigned_to_nat(0u);
v___x_1055_ = l_Lean_mkNatLit(v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = lean_nat_to_int(v___x_1078_);
return v___x_1079_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39(void){
_start:
{
lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
v___x_1081_ = lean_int_dec_le(v___x_1080_, v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
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
v___x_1097_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
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
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23);
v___x_1103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v___x_1101_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1105_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22));
v___x_1106_ = l_Lean_Expr_const___override(v___x_1105_, v___x_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53));
v___x_1113_ = l_Lean_Expr_const___override(v___x_1112_, v___x_1111_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = lean_box(0);
v___x_1121_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56));
v___x_1122_ = l_Lean_Expr_const___override(v___x_1121_, v___x_1120_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = lean_box(0);
v___x_1124_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33));
v___x_1125_ = l_Lean_Expr_const___override(v___x_1124_, v___x_1123_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35));
v___x_1128_ = l_Lean_Expr_const___override(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = lean_box(0);
v___x_1130_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37));
v___x_1131_ = l_Lean_Expr_const___override(v___x_1130_, v___x_1129_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1133_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42));
v___x_1134_ = l_Lean_Expr_const___override(v___x_1133_, v___x_1132_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = lean_box(0);
v___x_1136_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44));
v___x_1137_ = l_Lean_Expr_const___override(v___x_1136_, v___x_1135_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1138_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47);
v___x_1139_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62);
v___x_1140_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1141_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61);
v___x_1142_ = l_Lean_mkApp3(v___x_1141_, v___x_1140_, v___x_1139_, v___x_1138_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_unsigned_to_nat(1u);
v___x_1147_ = l_Lean_Level_ofNat(v___x_1146_);
return v___x_1147_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = lean_box(0);
v___x_1149_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66);
v___x_1150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v___x_1148_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67);
v___x_1152_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65));
v___x_1153_ = l_Lean_Expr_const___override(v___x_1152_, v___x_1151_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_box(0);
v___x_1159_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70));
v___x_1160_ = l_Lean_Expr_const___override(v___x_1159_, v___x_1158_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_box(0);
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73));
v___x_1167_ = l_Lean_Expr_const___override(v___x_1166_, v___x_1165_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1207_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93));
v___x_1208_ = l_Lean_Expr_const___override(v___x_1207_, v___x_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(lean_object* v_e_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___x_1234_; lean_object* v_fst_1235_; 
v___x_1234_ = l_Lean_Expr_getAppFnArgs(v_e_1209_);
v_fst_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_fst_1235_);
if (lean_obj_tag(v_fst_1235_) == 1)
{
lean_object* v_pre_1236_; 
v_pre_1236_ = lean_ctor_get(v_fst_1235_, 0);
switch(lean_obj_tag(v_pre_1236_))
{
case 1:
{
lean_object* v_pre_1237_; 
lean_inc_ref(v_pre_1236_);
v_pre_1237_ = lean_ctor_get(v_pre_1236_, 0);
if (lean_obj_tag(v_pre_1237_) == 0)
{
lean_object* v_snd_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1735_; 
v_snd_1238_ = lean_ctor_get(v___x_1234_, 1);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; 
v_unused_1736_ = lean_ctor_get(v___x_1234_, 0);
lean_dec(v_unused_1736_);
v___x_1240_ = v___x_1234_;
v_isShared_1241_ = v_isSharedCheck_1735_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_snd_1238_);
lean_dec(v___x_1234_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1735_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v_str_1242_; lean_object* v_str_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v_str_1242_ = lean_ctor_get(v_fst_1235_, 1);
lean_inc_ref(v_str_1242_);
lean_dec_ref(v_fst_1235_);
v_str_1243_ = lean_ctor_get(v_pre_1236_, 1);
lean_inc_ref(v_str_1243_);
lean_dec_ref(v_pre_1236_);
v___x_1244_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_1245_ = lean_string_dec_eq(v_str_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3));
v___x_1247_ = lean_string_dec_eq(v_str_1243_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1248_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0));
v___x_1249_ = lean_string_dec_eq(v_str_1243_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1));
v___x_1251_ = lean_string_dec_eq(v_str_1243_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2));
v___x_1253_ = lean_string_dec_eq(v_str_1243_, v___x_1252_);
lean_dec_ref(v_str_1243_);
if (v___x_1253_ == 0)
{
lean_dec_ref(v_str_1242_);
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3));
v___x_1255_ = lean_string_dec_eq(v_str_1242_, v___x_1254_);
lean_dec_ref(v_str_1242_);
if (v___x_1255_ == 0)
{
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1256_ = lean_array_get_size(v_snd_1238_);
v___x_1257_ = lean_unsigned_to_nat(4u);
v___x_1258_ = lean_nat_dec_eq(v___x_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1259_ = lean_unsigned_to_nat(2u);
v___x_1260_ = lean_array_fget(v_snd_1238_, v___x_1259_);
v___x_1261_ = lean_unsigned_to_nat(3u);
v___x_1262_ = lean_array_fget(v_snd_1238_, v___x_1261_);
lean_dec(v_snd_1238_);
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6);
lean_inc(v___x_1262_);
lean_inc(v___x_1260_);
v___x_1265_ = l_Lean_mkAppB(v___x_1264_, v___x_1260_, v___x_1262_);
v___x_1266_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9);
v___x_1267_ = l_Lean_mkAppB(v___x_1266_, v___x_1260_, v___x_1262_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 1);
lean_ctor_set(v___x_1240_, 1, v___x_1263_);
lean_ctor_set(v___x_1240_, 0, v___x_1267_);
v___x_1269_ = v___x_1240_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1263_);
v___x_1269_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1265_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
return v___x_1271_;
}
}
}
}
}
else
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
lean_dec_ref(v_str_1243_);
v___x_1273_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10));
v___x_1274_ = lean_string_dec_eq(v_str_1242_, v___x_1273_);
lean_dec_ref(v_str_1242_);
if (v___x_1274_ == 0)
{
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1275_ = lean_array_get_size(v_snd_1238_);
v___x_1276_ = lean_unsigned_to_nat(4u);
v___x_1277_ = lean_nat_dec_eq(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1278_ = lean_unsigned_to_nat(2u);
v___x_1279_ = lean_array_fget(v_snd_1238_, v___x_1278_);
v___x_1280_ = lean_unsigned_to_nat(3u);
v___x_1281_ = lean_array_fget(v_snd_1238_, v___x_1280_);
lean_dec(v_snd_1238_);
v___x_1282_ = lean_box(0);
v___x_1283_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13);
lean_inc(v___x_1281_);
lean_inc(v___x_1279_);
v___x_1284_ = l_Lean_mkAppB(v___x_1283_, v___x_1279_, v___x_1281_);
v___x_1285_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16);
v___x_1286_ = l_Lean_mkAppB(v___x_1285_, v___x_1279_, v___x_1281_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 1);
lean_ctor_set(v___x_1240_, 1, v___x_1282_);
lean_ctor_set(v___x_1240_, 0, v___x_1286_);
v___x_1288_ = v___x_1240_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1282_);
v___x_1288_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1284_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
return v___x_1290_;
}
}
}
}
}
else
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
lean_dec_ref(v_str_1243_);
v___x_1292_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17));
v___x_1293_ = lean_string_dec_eq(v_str_1242_, v___x_1292_);
lean_dec_ref(v_str_1242_);
if (v___x_1293_ == 0)
{
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1294_ = lean_array_get_size(v_snd_1238_);
v___x_1295_ = lean_unsigned_to_nat(6u);
v___x_1296_ = lean_nat_dec_eq(v___x_1294_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_fst_1300_; 
v___x_1297_ = lean_unsigned_to_nat(5u);
v___x_1298_ = lean_array_fget(v_snd_1238_, v___x_1297_);
lean_inc(v___x_1298_);
v___x_1299_ = l_Lean_Expr_getAppFnArgs(v___x_1298_);
v_fst_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_fst_1300_);
if (lean_obj_tag(v_fst_1300_) == 1)
{
lean_object* v_pre_1301_; 
v_pre_1301_ = lean_ctor_get(v_fst_1300_, 0);
lean_inc(v_pre_1301_);
if (lean_obj_tag(v_pre_1301_) == 1)
{
lean_object* v_pre_1302_; 
v_pre_1302_ = lean_ctor_get(v_pre_1301_, 0);
if (lean_obj_tag(v_pre_1302_) == 0)
{
lean_object* v_snd_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1502_; 
v_snd_1303_ = lean_ctor_get(v___x_1299_, 1);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; 
v_unused_1503_ = lean_ctor_get(v___x_1299_, 0);
lean_dec(v_unused_1503_);
v___x_1305_ = v___x_1299_;
v_isShared_1306_ = v_isSharedCheck_1502_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_snd_1303_);
lean_dec(v___x_1299_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1502_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v_str_1307_; lean_object* v_str_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_str_1307_ = lean_ctor_get(v_fst_1300_, 1);
lean_inc_ref(v_str_1307_);
lean_dec_ref(v_fst_1300_);
v_str_1308_ = lean_ctor_get(v_pre_1301_, 1);
lean_inc_ref(v_str_1308_);
lean_dec_ref(v_pre_1301_);
v___x_1309_ = lean_unsigned_to_nat(4u);
v___x_1310_ = lean_array_fget(v_snd_1238_, v___x_1309_);
lean_dec(v_snd_1238_);
v___x_1348_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4));
v___x_1349_ = lean_string_dec_eq(v_str_1308_, v___x_1348_);
if (v___x_1349_ == 0)
{
uint8_t v___x_1350_; 
v___x_1350_ = lean_string_dec_eq(v_str_1308_, v___x_1244_);
lean_dec_ref(v_str_1308_);
if (v___x_1350_ == 0)
{
lean_dec(v___x_1310_);
lean_dec_ref(v_str_1307_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1225_;
}
else
{
lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1351_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1352_ = lean_string_dec_eq(v_str_1307_, v___x_1351_);
lean_dec_ref(v_str_1307_);
if (v___x_1352_ == 0)
{
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1225_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1353_ = lean_array_get_size(v_snd_1303_);
v___x_1354_ = lean_unsigned_to_nat(3u);
v___x_1355_ = lean_nat_dec_eq(v___x_1353_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1225_;
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = lean_array_fget_borrowed(v_snd_1303_, v___x_1356_);
if (lean_obj_tag(v___x_1357_) == 4)
{
lean_object* v_declName_1358_; 
v_declName_1358_ = lean_ctor_get(v___x_1357_, 0);
if (lean_obj_tag(v_declName_1358_) == 1)
{
lean_object* v_pre_1359_; 
v_pre_1359_ = lean_ctor_get(v_declName_1358_, 0);
if (lean_obj_tag(v_pre_1359_) == 0)
{
lean_object* v_us_1360_; lean_object* v_str_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v_us_1360_ = lean_ctor_get(v___x_1357_, 1);
lean_inc(v_us_1360_);
v_str_1361_ = lean_ctor_get(v_declName_1358_, 1);
v___x_1362_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1363_ = lean_string_dec_eq(v_str_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_dec(v_us_1360_);
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1225_;
}
else
{
if (lean_obj_tag(v_us_1360_) == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v_fst_1367_; 
v___x_1364_ = lean_unsigned_to_nat(2u);
v___x_1365_ = lean_array_fget(v_snd_1303_, v___x_1364_);
lean_dec(v_snd_1303_);
lean_inc(v___x_1365_);
v___x_1366_ = l_Lean_Expr_getAppFnArgs(v___x_1365_);
v_fst_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_fst_1367_);
if (lean_obj_tag(v_fst_1367_) == 1)
{
lean_object* v_pre_1368_; 
v_pre_1368_ = lean_ctor_get(v_fst_1367_, 0);
lean_inc(v_pre_1368_);
if (lean_obj_tag(v_pre_1368_) == 1)
{
lean_object* v_pre_1369_; 
v_pre_1369_ = lean_ctor_get(v_pre_1368_, 0);
if (lean_obj_tag(v_pre_1369_) == 0)
{
lean_object* v_snd_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1449_; 
v_snd_1370_ = lean_ctor_get(v___x_1366_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; 
v_unused_1450_ = lean_ctor_get(v___x_1366_, 0);
lean_dec(v_unused_1450_);
v___x_1372_ = v___x_1366_;
v_isShared_1373_ = v_isSharedCheck_1449_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_snd_1370_);
lean_dec(v___x_1366_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1449_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v_str_1374_; lean_object* v_str_1375_; uint8_t v___x_1376_; 
v_str_1374_ = lean_ctor_get(v_fst_1367_, 1);
lean_inc_ref(v_str_1374_);
lean_dec_ref(v_fst_1367_);
v_str_1375_ = lean_ctor_get(v_pre_1368_, 1);
lean_inc_ref(v_str_1375_);
lean_dec_ref(v_pre_1368_);
v___x_1376_ = lean_string_dec_eq(v_str_1375_, v___x_1348_);
lean_dec_ref(v_str_1375_);
if (v___x_1376_ == 0)
{
lean_dec_ref(v_str_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_snd_1370_);
lean_dec(v___x_1365_);
lean_del_object(v___x_1305_);
lean_del_object(v___x_1240_);
goto v___jp_1311_;
}
else
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_1378_ = lean_string_dec_eq(v_str_1374_, v___x_1377_);
lean_dec_ref(v_str_1374_);
if (v___x_1378_ == 0)
{
lean_del_object(v___x_1372_);
lean_dec(v_snd_1370_);
lean_dec(v___x_1365_);
lean_del_object(v___x_1305_);
lean_del_object(v___x_1240_);
goto v___jp_1311_;
}
else
{
lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1379_ = lean_array_get_size(v_snd_1370_);
v___x_1380_ = lean_nat_dec_eq(v___x_1379_, v___x_1295_);
if (v___x_1380_ == 0)
{
lean_del_object(v___x_1372_);
lean_dec(v_snd_1370_);
lean_dec(v___x_1365_);
lean_del_object(v___x_1305_);
lean_del_object(v___x_1240_);
goto v___jp_1311_;
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_array_fget(v_snd_1370_, v___x_1309_);
lean_inc(v___x_1381_);
v___x_1382_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1381_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_dec(v___x_1381_);
lean_del_object(v___x_1372_);
lean_dec(v_snd_1370_);
lean_dec(v___x_1365_);
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1231_;
}
else
{
lean_object* v_val_1383_; uint8_t v___x_1384_; 
v_val_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_val_1383_);
lean_dec_ref(v___x_1382_);
v___x_1384_ = lean_nat_dec_eq(v_val_1383_, v___x_1356_);
lean_dec(v_val_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1385_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22));
v___x_1386_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23);
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 1);
lean_ctor_set(v___x_1372_, 1, v_us_1360_);
lean_ctor_set(v___x_1372_, 0, v___x_1386_);
v___x_1388_ = v___x_1372_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_us_1360_);
v___x_1388_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v_b__pos_1395_; lean_object* v___x_1396_; 
lean_inc_ref(v___x_1388_);
v___x_1389_ = l_Lean_Expr_const___override(v___x_1385_, v___x_1388_);
v___x_1390_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24));
v___x_1391_ = l_Lean_Expr_const___override(v___x_1390_, v_us_1360_);
v___x_1392_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26));
v___x_1393_ = l_Lean_Expr_const___override(v___x_1392_, v_us_1360_);
v___x_1394_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27);
lean_inc(v___x_1381_);
v_b__pos_1395_ = l_Lean_mkApp4(v___x_1389_, v___x_1391_, v___x_1393_, v___x_1394_, v___x_1381_);
v___x_1396_ = l_Lean_Meta_mkDecideProof(v_b__pos_1395_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1439_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1439_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1439_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___y_1413_; uint8_t v___x_1429_; 
v___x_1401_ = lean_array_fget(v_snd_1370_, v___x_1297_);
lean_dec(v_snd_1370_);
v___x_1402_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29));
v___x_1403_ = l_Lean_Expr_const___override(v___x_1402_, v_us_1360_);
v___x_1404_ = l_Lean_mkApp3(v___x_1403_, v___x_1381_, v___x_1401_, v_a_1397_);
v___x_1405_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31));
v___x_1406_ = l_Lean_Expr_const___override(v___x_1405_, v_us_1360_);
v___x_1407_ = l_Lean_mkAppB(v___x_1406_, v___x_1365_, v___x_1404_);
v___x_1408_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33));
v___x_1409_ = l_Lean_Expr_const___override(v___x_1408_, v_us_1360_);
v___x_1410_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35));
v___x_1411_ = l_Lean_Expr_const___override(v___x_1410_, v_us_1360_);
v___x_1429_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1430_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42));
v___x_1431_ = l_Lean_Expr_const___override(v___x_1430_, v___x_1388_);
v___x_1432_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1));
v___x_1433_ = l_Lean_Expr_const___override(v___x_1432_, v_us_1360_);
v___x_1434_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44));
v___x_1435_ = l_Lean_Expr_const___override(v___x_1434_, v_us_1360_);
v___x_1436_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47);
v___x_1437_ = l_Lean_mkApp3(v___x_1431_, v___x_1433_, v___x_1435_, v___x_1436_);
v___y_1413_ = v___x_1437_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1438_; 
lean_dec_ref(v___x_1388_);
v___x_1438_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1413_ = v___x_1438_;
goto v___jp_1412_;
}
v___jp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
lean_inc_ref(v___x_1407_);
lean_inc_n(v___x_1298_, 2);
v___x_1414_ = l_Lean_mkApp3(v___x_1411_, v___x_1298_, v___y_1413_, v___x_1407_);
lean_inc(v___x_1310_);
v___x_1415_ = l_Lean_mkApp3(v___x_1409_, v___x_1310_, v___x_1298_, v___x_1414_);
v___x_1416_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37));
v___x_1417_ = l_Lean_Expr_const___override(v___x_1416_, v_us_1360_);
v___x_1418_ = l_Lean_mkApp3(v___x_1417_, v___x_1310_, v___x_1298_, v___x_1407_);
v___x_1419_ = lean_box(0);
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 1);
lean_ctor_set(v___x_1305_, 1, v___x_1419_);
lean_ctor_set(v___x_1305_, 0, v___x_1418_);
v___x_1421_ = v___x_1305_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 1);
lean_ctor_set(v___x_1240_, 1, v___x_1421_);
lean_ctor_set(v___x_1240_, 0, v___x_1415_);
v___x_1423_ = v___x_1240_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1425_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1423_);
v___x_1425_ = v___x_1399_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec_ref(v___x_1388_);
lean_dec(v___x_1381_);
lean_dec(v_snd_1370_);
lean_dec(v___x_1365_);
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
v_a_1440_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1396_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1396_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
else
{
lean_dec(v___x_1381_);
lean_del_object(v___x_1372_);
lean_dec(v_snd_1370_);
lean_dec(v___x_1365_);
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1231_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_1368_);
lean_dec_ref(v_fst_1367_);
lean_dec_ref(v___x_1366_);
lean_dec(v___x_1365_);
lean_del_object(v___x_1305_);
lean_del_object(v___x_1240_);
goto v___jp_1311_;
}
}
else
{
lean_dec(v_pre_1368_);
lean_dec_ref(v_fst_1367_);
lean_dec_ref(v___x_1366_);
lean_dec(v___x_1365_);
lean_del_object(v___x_1305_);
lean_del_object(v___x_1240_);
goto v___jp_1311_;
}
}
else
{
lean_dec(v_fst_1367_);
lean_dec_ref(v___x_1366_);
lean_dec(v___x_1365_);
lean_del_object(v___x_1305_);
lean_del_object(v___x_1240_);
goto v___jp_1311_;
}
}
else
{
lean_dec(v_us_1360_);
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1225_;
}
}
}
else
{
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1225_;
}
}
else
{
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1225_;
}
}
else
{
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1225_;
}
}
}
}
}
else
{
lean_object* v___x_1451_; uint8_t v___x_1452_; 
lean_dec_ref(v_str_1308_);
v___x_1451_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_1452_ = lean_string_dec_eq(v_str_1307_, v___x_1451_);
lean_dec_ref(v_str_1307_);
if (v___x_1452_ == 0)
{
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1225_;
}
else
{
lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1453_ = lean_array_get_size(v_snd_1303_);
v___x_1454_ = lean_nat_dec_eq(v___x_1453_, v___x_1295_);
if (v___x_1454_ == 0)
{
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1225_;
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_array_fget(v_snd_1303_, v___x_1309_);
lean_inc(v___x_1455_);
v___x_1456_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1455_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_dec(v___x_1455_);
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1219_;
}
else
{
lean_object* v_val_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_val_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_val_1457_);
lean_dec_ref(v___x_1456_);
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = lean_nat_dec_eq(v_val_1457_, v___x_1458_);
lean_dec(v_val_1457_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___y_1466_; uint8_t v___x_1499_; 
v___x_1460_ = lean_array_fget(v_snd_1303_, v___x_1297_);
lean_dec(v_snd_1303_);
v___x_1461_ = lean_box(0);
v___x_1462_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51);
v___x_1463_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1464_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
v___x_1499_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
v___y_1466_ = v___x_1500_;
goto v___jp_1465_;
}
else
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1466_ = v___x_1501_;
goto v___jp_1465_;
}
v___jp_1465_:
{
lean_object* v_b__pos_1467_; lean_object* v___x_1468_; 
lean_inc(v___x_1455_);
lean_inc_ref(v___y_1466_);
v_b__pos_1467_ = l_Lean_mkApp4(v___x_1462_, v___x_1463_, v___x_1464_, v___y_1466_, v___x_1455_);
v___x_1468_ = l_Lean_Meta_mkDecideProof(v_b__pos_1467_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1490_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1490_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1490_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1473_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57);
v___x_1474_ = l_Lean_mkApp3(v___x_1473_, v___x_1455_, v___x_1460_, v_a_1469_);
v___x_1475_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58);
v___x_1476_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59);
lean_inc_ref(v___x_1474_);
lean_inc_ref(v___y_1466_);
lean_inc_n(v___x_1298_, 2);
v___x_1477_ = l_Lean_mkApp3(v___x_1476_, v___x_1298_, v___y_1466_, v___x_1474_);
lean_inc(v___x_1310_);
v___x_1478_ = l_Lean_mkApp3(v___x_1475_, v___x_1310_, v___x_1298_, v___x_1477_);
v___x_1479_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60);
v___x_1480_ = l_Lean_mkApp3(v___x_1479_, v___x_1310_, v___x_1298_, v___x_1474_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 1);
lean_ctor_set(v___x_1305_, 1, v___x_1461_);
lean_ctor_set(v___x_1305_, 0, v___x_1480_);
v___x_1482_ = v___x_1305_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v___x_1461_);
v___x_1482_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 1);
lean_ctor_set(v___x_1240_, 1, v___x_1482_);
lean_ctor_set(v___x_1240_, 0, v___x_1478_);
v___x_1484_ = v___x_1240_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1484_);
v___x_1486_ = v___x_1471_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
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
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v___x_1460_);
lean_dec(v___x_1455_);
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
v_a_1491_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1468_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1468_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
else
{
lean_dec(v___x_1455_);
lean_dec(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
goto v___jp_1219_;
}
}
}
}
}
v___jp_1311_:
{
lean_object* v___x_1312_; lean_object* v_fst_1313_; 
v___x_1312_ = l_Lean_Expr_getAppFnArgs(v___x_1310_);
v_fst_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_fst_1313_);
if (lean_obj_tag(v_fst_1313_) == 1)
{
lean_object* v_pre_1314_; 
v_pre_1314_ = lean_ctor_get(v_fst_1313_, 0);
lean_inc(v_pre_1314_);
if (lean_obj_tag(v_pre_1314_) == 1)
{
lean_object* v_pre_1315_; 
v_pre_1315_ = lean_ctor_get(v_pre_1314_, 0);
if (lean_obj_tag(v_pre_1315_) == 0)
{
lean_object* v_snd_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1346_; 
v_snd_1316_ = lean_ctor_get(v___x_1312_, 1);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v___x_1312_, 0);
lean_dec(v_unused_1347_);
v___x_1318_ = v___x_1312_;
v_isShared_1319_ = v_isSharedCheck_1346_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_snd_1316_);
lean_dec(v___x_1312_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1346_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v_str_1320_; lean_object* v_str_1321_; uint8_t v___x_1322_; 
v_str_1320_ = lean_ctor_get(v_fst_1313_, 1);
lean_inc_ref(v_str_1320_);
lean_dec_ref(v_fst_1313_);
v_str_1321_ = lean_ctor_get(v_pre_1314_, 1);
lean_inc_ref(v_str_1321_);
lean_dec_ref(v_pre_1314_);
v___x_1322_ = lean_string_dec_eq(v_str_1321_, v___x_1244_);
lean_dec_ref(v_str_1321_);
if (v___x_1322_ == 0)
{
lean_dec_ref(v_str_1320_);
lean_del_object(v___x_1318_);
lean_dec(v_snd_1316_);
lean_dec(v___x_1298_);
goto v___jp_1228_;
}
else
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1324_ = lean_string_dec_eq(v_str_1320_, v___x_1323_);
lean_dec_ref(v_str_1320_);
if (v___x_1324_ == 0)
{
lean_del_object(v___x_1318_);
lean_dec(v_snd_1316_);
lean_dec(v___x_1298_);
goto v___jp_1228_;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1325_ = lean_array_get_size(v_snd_1316_);
v___x_1326_ = lean_unsigned_to_nat(3u);
v___x_1327_ = lean_nat_dec_eq(v___x_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_del_object(v___x_1318_);
lean_dec(v_snd_1316_);
lean_dec(v___x_1298_);
goto v___jp_1228_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = lean_array_fget_borrowed(v_snd_1316_, v___x_1328_);
if (lean_obj_tag(v___x_1329_) == 4)
{
lean_object* v_declName_1330_; 
v_declName_1330_ = lean_ctor_get(v___x_1329_, 0);
if (lean_obj_tag(v_declName_1330_) == 1)
{
lean_object* v_pre_1331_; 
v_pre_1331_ = lean_ctor_get(v_declName_1330_, 0);
if (lean_obj_tag(v_pre_1331_) == 0)
{
lean_object* v_us_1332_; lean_object* v_str_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v_us_1332_ = lean_ctor_get(v___x_1329_, 1);
lean_inc(v_us_1332_);
v_str_1333_ = lean_ctor_get(v_declName_1330_, 1);
v___x_1334_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1335_ = lean_string_dec_eq(v_str_1333_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_dec(v_us_1332_);
lean_del_object(v___x_1318_);
lean_dec(v_snd_1316_);
lean_dec(v___x_1298_);
goto v___jp_1228_;
}
else
{
if (lean_obj_tag(v_us_1332_) == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1336_ = lean_unsigned_to_nat(2u);
v___x_1337_ = lean_array_fget(v_snd_1316_, v___x_1336_);
lean_dec(v_snd_1316_);
v___x_1338_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19));
v___x_1339_ = l_Lean_Expr_const___override(v___x_1338_, v_us_1332_);
v___x_1340_ = l_Lean_mkAppB(v___x_1339_, v___x_1337_, v___x_1298_);
v___x_1341_ = lean_box(0);
if (v_isShared_1319_ == 0)
{
lean_ctor_set_tag(v___x_1318_, 1);
lean_ctor_set(v___x_1318_, 1, v___x_1341_);
lean_ctor_set(v___x_1318_, 0, v___x_1340_);
v___x_1343_ = v___x_1318_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
return v___x_1344_;
}
}
else
{
lean_dec(v_us_1332_);
lean_del_object(v___x_1318_);
lean_dec(v_snd_1316_);
lean_dec(v___x_1298_);
goto v___jp_1228_;
}
}
}
else
{
lean_del_object(v___x_1318_);
lean_dec(v_snd_1316_);
lean_dec(v___x_1298_);
goto v___jp_1228_;
}
}
else
{
lean_del_object(v___x_1318_);
lean_dec(v_snd_1316_);
lean_dec(v___x_1298_);
goto v___jp_1228_;
}
}
else
{
lean_del_object(v___x_1318_);
lean_dec(v_snd_1316_);
lean_dec(v___x_1298_);
goto v___jp_1228_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_1314_);
lean_dec_ref(v_fst_1313_);
lean_dec_ref(v___x_1312_);
lean_dec(v___x_1298_);
goto v___jp_1228_;
}
}
else
{
lean_dec(v_pre_1314_);
lean_dec_ref(v_fst_1313_);
lean_dec_ref(v___x_1312_);
lean_dec(v___x_1298_);
goto v___jp_1228_;
}
}
else
{
lean_dec(v_fst_1313_);
lean_dec_ref(v___x_1312_);
lean_dec(v___x_1298_);
goto v___jp_1228_;
}
}
}
}
else
{
lean_dec_ref(v_pre_1301_);
lean_dec_ref(v_fst_1300_);
lean_dec_ref(v___x_1299_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1225_;
}
}
else
{
lean_dec_ref(v_fst_1300_);
lean_dec(v_pre_1301_);
lean_dec_ref(v___x_1299_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1225_;
}
}
else
{
lean_dec(v_fst_1300_);
lean_dec_ref(v___x_1299_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1225_;
}
}
}
}
}
else
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
lean_dec_ref(v_str_1243_);
v___x_1504_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7));
v___x_1505_ = lean_string_dec_eq(v_str_1242_, v___x_1504_);
lean_dec_ref(v_str_1242_);
if (v___x_1505_ == 0)
{
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1506_ = lean_array_get_size(v_snd_1238_);
v___x_1507_ = lean_unsigned_to_nat(6u);
v___x_1508_ = lean_nat_dec_eq(v___x_1506_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_unsigned_to_nat(5u);
v___x_1510_ = lean_array_fget(v_snd_1238_, v___x_1509_);
lean_inc(v___x_1510_);
v___x_1511_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1510_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_dec(v___x_1510_);
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1216_;
}
else
{
lean_object* v_val_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_val_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_val_1512_);
lean_dec_ref(v___x_1511_);
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = lean_nat_dec_eq(v_val_1512_, v___x_1513_);
lean_dec(v_val_1512_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___y_1521_; uint8_t v___x_1561_; 
v___x_1515_ = lean_unsigned_to_nat(4u);
v___x_1516_ = lean_array_fget(v_snd_1238_, v___x_1515_);
lean_dec(v_snd_1238_);
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68);
v___x_1519_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1561_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
v___y_1521_ = v___x_1562_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1521_ = v___x_1563_;
goto v___jp_1520_;
}
v___jp_1520_:
{
lean_object* v_ne__zero_1522_; lean_object* v___x_1523_; 
lean_inc_ref(v___y_1521_);
lean_inc(v___x_1510_);
v_ne__zero_1522_ = l_Lean_mkApp3(v___x_1518_, v___x_1519_, v___x_1510_, v___y_1521_);
v___x_1523_ = l_Lean_Meta_mkDecideProof(v_ne__zero_1522_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v_pos_1527_; lean_object* v___x_1528_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref(v___x_1523_);
v___x_1525_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51);
v___x_1526_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
lean_inc(v___x_1510_);
lean_inc_ref(v___y_1521_);
v_pos_1527_ = l_Lean_mkApp4(v___x_1525_, v___x_1519_, v___x_1526_, v___y_1521_, v___x_1510_);
v___x_1528_ = l_Lean_Meta_mkDecideProof(v_pos_1527_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1544_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1544_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1544_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1533_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71);
lean_inc(v___x_1510_);
lean_inc(v___x_1516_);
v___x_1534_ = l_Lean_mkApp3(v___x_1533_, v___x_1516_, v___x_1510_, v_a_1524_);
v___x_1535_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74);
v___x_1536_ = l_Lean_mkApp3(v___x_1535_, v___x_1516_, v___x_1510_, v_a_1529_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 1);
lean_ctor_set(v___x_1240_, 1, v___x_1517_);
lean_ctor_set(v___x_1240_, 0, v___x_1536_);
v___x_1538_ = v___x_1240_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___x_1517_);
v___x_1538_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1534_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1539_);
v___x_1541_ = v___x_1531_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_a_1524_);
lean_dec(v___x_1516_);
lean_dec(v___x_1510_);
lean_del_object(v___x_1240_);
v_a_1545_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1528_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1528_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v___x_1516_);
lean_dec(v___x_1510_);
lean_del_object(v___x_1240_);
v_a_1553_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1523_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1523_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
else
{
lean_dec(v___x_1510_);
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1216_;
}
}
}
}
}
}
else
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
lean_dec_ref(v_str_1243_);
v___x_1564_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1565_ = lean_string_dec_eq(v_str_1242_, v___x_1564_);
lean_dec_ref(v_str_1242_);
if (v___x_1565_ == 0)
{
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1566_ = lean_array_get_size(v_snd_1238_);
v___x_1567_ = lean_unsigned_to_nat(3u);
v___x_1568_ = lean_nat_dec_eq(v___x_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = lean_array_fget_borrowed(v_snd_1238_, v___x_1569_);
if (lean_obj_tag(v___x_1570_) == 4)
{
lean_object* v_declName_1571_; 
v_declName_1571_ = lean_ctor_get(v___x_1570_, 0);
if (lean_obj_tag(v_declName_1571_) == 1)
{
lean_object* v_pre_1572_; 
v_pre_1572_ = lean_ctor_get(v_declName_1571_, 0);
if (lean_obj_tag(v_pre_1572_) == 0)
{
lean_object* v_us_1573_; lean_object* v_str_1574_; lean_object* v___x_1575_; lean_object* v___y_1577_; lean_object* v___y_1578_; uint8_t v___x_1588_; 
v_us_1573_ = lean_ctor_get(v___x_1570_, 1);
lean_inc(v_us_1573_);
v_str_1574_ = lean_ctor_get(v_declName_1571_, 1);
v___x_1575_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1588_ = lean_string_dec_eq(v_str_1574_, v___x_1575_);
if (v___x_1588_ == 0)
{
lean_dec(v_us_1573_);
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
else
{
if (lean_obj_tag(v_us_1573_) == 0)
{
uint8_t v_splitNatSub_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v_r_1596_; lean_object* v_n_1598_; lean_object* v_x_1599_; lean_object* v_n_1608_; lean_object* v_i_1609_; lean_object* v_x_1618_; 
v_splitNatSub_1589_ = lean_ctor_get_uint8(v_a_1210_, 1);
v___x_1590_ = lean_unsigned_to_nat(2u);
v___x_1591_ = lean_array_fget(v_snd_1238_, v___x_1590_);
lean_dec(v_snd_1238_);
v___x_1592_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78));
v___x_1593_ = l_Lean_Expr_const___override(v___x_1592_, v_us_1573_);
lean_inc(v___x_1591_);
v___x_1594_ = l_Lean_Expr_app___override(v___x_1593_, v___x_1591_);
v___x_1595_ = lean_box(0);
v_r_1596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_r_1596_, 0, v___x_1594_);
lean_ctor_set(v_r_1596_, 1, v___x_1595_);
if (v_splitNatSub_1589_ == 1)
{
lean_object* v___x_1624_; lean_object* v_fst_1625_; 
v___x_1624_ = l_Lean_Expr_getAppFnArgs(v___x_1591_);
v_fst_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_fst_1625_);
if (lean_obj_tag(v_fst_1625_) == 1)
{
lean_object* v_pre_1626_; 
v_pre_1626_ = lean_ctor_get(v_fst_1625_, 0);
lean_inc(v_pre_1626_);
if (lean_obj_tag(v_pre_1626_) == 1)
{
lean_object* v_pre_1627_; 
v_pre_1627_ = lean_ctor_get(v_pre_1626_, 0);
if (lean_obj_tag(v_pre_1627_) == 0)
{
lean_object* v_snd_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1688_; 
v_snd_1628_ = lean_ctor_get(v___x_1624_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v___x_1624_, 0);
lean_dec(v_unused_1689_);
v___x_1630_ = v___x_1624_;
v_isShared_1631_ = v_isSharedCheck_1688_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_snd_1628_);
lean_dec(v___x_1624_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1688_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_str_1632_; lean_object* v_str_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v_str_1632_ = lean_ctor_get(v_fst_1625_, 1);
lean_inc_ref(v_str_1632_);
lean_dec_ref(v_fst_1625_);
v_str_1633_ = lean_ctor_get(v_pre_1626_, 1);
lean_inc_ref(v_str_1633_);
lean_dec_ref(v_pre_1626_);
v___x_1634_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2));
v___x_1635_ = lean_string_dec_eq(v_str_1633_, v___x_1634_);
if (v___x_1635_ == 0)
{
uint8_t v___x_1636_; 
lean_del_object(v___x_1630_);
v___x_1636_ = lean_string_dec_eq(v_str_1633_, v___x_1575_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
lean_del_object(v___x_1240_);
v___x_1637_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82));
v___x_1638_ = lean_string_dec_eq(v_str_1633_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79));
v___x_1640_ = lean_string_dec_eq(v_str_1633_, v___x_1639_);
lean_dec_ref(v_str_1633_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; 
lean_dec_ref(v_str_1632_);
lean_dec(v_snd_1628_);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v_r_1596_);
return v___x_1641_;
}
else
{
lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1642_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86));
v___x_1643_ = lean_string_dec_eq(v_str_1632_, v___x_1642_);
lean_dec_ref(v_str_1632_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; 
lean_dec(v_snd_1628_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v_r_1596_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = lean_array_get_size(v_snd_1628_);
v___x_1646_ = lean_nat_dec_eq(v___x_1645_, v___x_1590_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
lean_dec(v_snd_1628_);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_r_1596_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = lean_array_fget(v_snd_1628_, v___x_1569_);
v___x_1649_ = lean_unsigned_to_nat(1u);
v___x_1650_ = lean_array_fget(v_snd_1628_, v___x_1649_);
lean_dec(v_snd_1628_);
v_n_1598_ = v___x_1648_;
v_x_1599_ = v___x_1650_;
goto v___jp_1597_;
}
}
}
}
else
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
lean_dec_ref(v_str_1633_);
v___x_1651_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87));
v___x_1652_ = lean_string_dec_eq(v_str_1632_, v___x_1651_);
lean_dec_ref(v_str_1632_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
lean_dec(v_snd_1628_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v_r_1596_);
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = lean_array_get_size(v_snd_1628_);
v___x_1655_ = lean_nat_dec_eq(v___x_1654_, v___x_1590_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_dec(v_snd_1628_);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v_r_1596_);
return v___x_1656_;
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = lean_array_fget(v_snd_1628_, v___x_1569_);
v___x_1658_ = lean_unsigned_to_nat(1u);
v___x_1659_ = lean_array_fget(v_snd_1628_, v___x_1658_);
lean_dec(v_snd_1628_);
v_n_1608_ = v___x_1657_;
v_i_1609_ = v___x_1659_;
goto v___jp_1607_;
}
}
}
}
else
{
lean_object* v___x_1660_; uint8_t v___x_1661_; 
lean_dec_ref(v_str_1633_);
v___x_1660_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88));
v___x_1661_ = lean_string_dec_eq(v_str_1632_, v___x_1660_);
lean_dec_ref(v_str_1632_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; 
lean_dec(v_snd_1628_);
lean_del_object(v___x_1240_);
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v_r_1596_);
return v___x_1662_;
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1663_ = lean_array_get_size(v_snd_1628_);
v___x_1664_ = lean_unsigned_to_nat(1u);
v___x_1665_ = lean_nat_dec_eq(v___x_1663_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; 
lean_dec(v_snd_1628_);
lean_del_object(v___x_1240_);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v_r_1596_);
return v___x_1666_;
}
else
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_array_fget(v_snd_1628_, v___x_1569_);
lean_dec(v_snd_1628_);
v_x_1618_ = v___x_1667_;
goto v___jp_1617_;
}
}
}
}
else
{
lean_object* v___x_1668_; uint8_t v___x_1669_; 
lean_dec_ref(v_str_1633_);
lean_del_object(v___x_1240_);
v___x_1668_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9));
v___x_1669_ = lean_string_dec_eq(v_str_1632_, v___x_1668_);
lean_dec_ref(v_str_1632_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
lean_del_object(v___x_1630_);
lean_dec(v_snd_1628_);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_r_1596_);
return v___x_1670_;
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1671_ = lean_array_get_size(v_snd_1628_);
v___x_1672_ = lean_unsigned_to_nat(6u);
v___x_1673_ = lean_nat_dec_eq(v___x_1671_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; 
lean_del_object(v___x_1630_);
lean_dec(v_snd_1628_);
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_r_1596_);
return v___x_1674_;
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1675_ = lean_unsigned_to_nat(4u);
v___x_1676_ = lean_array_fget(v_snd_1628_, v___x_1675_);
v___x_1677_ = lean_unsigned_to_nat(5u);
v___x_1678_ = lean_array_fget(v_snd_1628_, v___x_1677_);
lean_dec(v_snd_1628_);
v___x_1679_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90));
v___x_1680_ = l_Lean_Expr_const___override(v___x_1679_, v_us_1573_);
v___x_1681_ = l_Lean_mkAppB(v___x_1680_, v___x_1676_, v___x_1678_);
v___x_1682_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1681_, v_r_1596_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1684_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set_tag(v___x_1630_, 1);
lean_ctor_set(v___x_1630_, 1, v_r_1596_);
lean_ctor_set(v___x_1630_, 0, v___x_1681_);
v___x_1684_ = v___x_1630_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_r_1596_);
v___x_1684_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
return v___x_1685_;
}
}
else
{
lean_object* v___x_1687_; 
lean_dec_ref(v___x_1681_);
lean_del_object(v___x_1630_);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v_r_1596_);
return v___x_1687_;
}
}
}
}
}
}
else
{
lean_object* v___x_1690_; 
lean_dec_ref(v_pre_1626_);
lean_dec_ref(v_fst_1625_);
lean_dec_ref(v___x_1624_);
lean_del_object(v___x_1240_);
v___x_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1690_, 0, v_r_1596_);
return v___x_1690_;
}
}
else
{
lean_object* v___x_1691_; 
lean_dec_ref(v_fst_1625_);
lean_dec(v_pre_1626_);
lean_dec_ref(v___x_1624_);
lean_del_object(v___x_1240_);
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_r_1596_);
return v___x_1691_;
}
}
else
{
lean_object* v___x_1692_; 
lean_dec(v_fst_1625_);
lean_dec_ref(v___x_1624_);
lean_del_object(v___x_1240_);
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_r_1596_);
return v___x_1692_;
}
}
else
{
lean_object* v___x_1693_; lean_object* v_fst_1694_; 
v___x_1693_ = l_Lean_Expr_getAppFnArgs(v___x_1591_);
v_fst_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_fst_1694_);
if (lean_obj_tag(v_fst_1694_) == 1)
{
lean_object* v_pre_1695_; 
v_pre_1695_ = lean_ctor_get(v_fst_1694_, 0);
lean_inc(v_pre_1695_);
if (lean_obj_tag(v_pre_1695_) == 1)
{
lean_object* v_pre_1696_; 
v_pre_1696_ = lean_ctor_get(v_pre_1695_, 0);
if (lean_obj_tag(v_pre_1696_) == 0)
{
lean_object* v_snd_1697_; lean_object* v_str_1698_; lean_object* v_str_1699_; uint8_t v___x_1700_; 
v_snd_1697_ = lean_ctor_get(v___x_1693_, 1);
lean_inc(v_snd_1697_);
lean_dec_ref(v___x_1693_);
v_str_1698_ = lean_ctor_get(v_fst_1694_, 1);
lean_inc_ref(v_str_1698_);
lean_dec_ref(v_fst_1694_);
v_str_1699_ = lean_ctor_get(v_pre_1695_, 1);
lean_inc_ref(v_str_1699_);
lean_dec_ref(v_pre_1695_);
v___x_1700_ = lean_string_dec_eq(v_str_1699_, v___x_1575_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; uint8_t v___x_1702_; 
lean_del_object(v___x_1240_);
v___x_1701_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82));
v___x_1702_ = lean_string_dec_eq(v_str_1699_, v___x_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1703_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79));
v___x_1704_ = lean_string_dec_eq(v_str_1699_, v___x_1703_);
lean_dec_ref(v_str_1699_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
lean_dec_ref(v_str_1698_);
lean_dec(v_snd_1697_);
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_r_1596_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86));
v___x_1707_ = lean_string_dec_eq(v_str_1698_, v___x_1706_);
lean_dec_ref(v_str_1698_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; 
lean_dec(v_snd_1697_);
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v_r_1596_);
return v___x_1708_;
}
else
{
lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1709_ = lean_array_get_size(v_snd_1697_);
v___x_1710_ = lean_nat_dec_eq(v___x_1709_, v___x_1590_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_dec(v_snd_1697_);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_r_1596_);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_array_fget(v_snd_1697_, v___x_1569_);
v___x_1713_ = lean_unsigned_to_nat(1u);
v___x_1714_ = lean_array_fget(v_snd_1697_, v___x_1713_);
lean_dec(v_snd_1697_);
v_n_1598_ = v___x_1712_;
v_x_1599_ = v___x_1714_;
goto v___jp_1597_;
}
}
}
}
else
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
lean_dec_ref(v_str_1699_);
v___x_1715_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87));
v___x_1716_ = lean_string_dec_eq(v_str_1698_, v___x_1715_);
lean_dec_ref(v_str_1698_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec(v_snd_1697_);
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_r_1596_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = lean_array_get_size(v_snd_1697_);
v___x_1719_ = lean_nat_dec_eq(v___x_1718_, v___x_1590_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_dec(v_snd_1697_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_r_1596_);
return v___x_1720_;
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_array_fget(v_snd_1697_, v___x_1569_);
v___x_1722_ = lean_unsigned_to_nat(1u);
v___x_1723_ = lean_array_fget(v_snd_1697_, v___x_1722_);
lean_dec(v_snd_1697_);
v_n_1608_ = v___x_1721_;
v_i_1609_ = v___x_1723_;
goto v___jp_1607_;
}
}
}
}
else
{
lean_object* v___x_1724_; uint8_t v___x_1725_; 
lean_dec_ref(v_str_1699_);
v___x_1724_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88));
v___x_1725_ = lean_string_dec_eq(v_str_1698_, v___x_1724_);
lean_dec_ref(v_str_1698_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; 
lean_dec(v_snd_1697_);
lean_del_object(v___x_1240_);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v_r_1596_);
return v___x_1726_;
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1727_ = lean_array_get_size(v_snd_1697_);
v___x_1728_ = lean_unsigned_to_nat(1u);
v___x_1729_ = lean_nat_dec_eq(v___x_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; 
lean_dec(v_snd_1697_);
lean_del_object(v___x_1240_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_r_1596_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_array_fget(v_snd_1697_, v___x_1569_);
lean_dec(v_snd_1697_);
v_x_1618_ = v___x_1731_;
goto v___jp_1617_;
}
}
}
}
else
{
lean_object* v___x_1732_; 
lean_dec_ref(v_pre_1695_);
lean_dec_ref(v_fst_1694_);
lean_dec_ref(v___x_1693_);
lean_del_object(v___x_1240_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_r_1596_);
return v___x_1732_;
}
}
else
{
lean_object* v___x_1733_; 
lean_dec(v_pre_1695_);
lean_dec_ref(v_fst_1694_);
lean_dec_ref(v___x_1693_);
lean_del_object(v___x_1240_);
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_r_1596_);
return v___x_1733_;
}
}
else
{
lean_object* v___x_1734_; 
lean_dec(v_fst_1694_);
lean_dec_ref(v___x_1693_);
lean_del_object(v___x_1240_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_r_1596_);
return v___x_1734_;
}
}
v___jp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81));
v___x_1601_ = l_Lean_Expr_const___override(v___x_1600_, v_us_1573_);
v___x_1602_ = l_Lean_mkAppB(v___x_1601_, v_n_1598_, v_x_1599_);
v___x_1603_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1602_, v_r_1596_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v_r_1596_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; 
lean_dec_ref(v___x_1602_);
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_r_1596_);
return v___x_1606_;
}
}
v___jp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1610_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83));
v___x_1611_ = l_Lean_Expr_const___override(v___x_1610_, v_us_1573_);
v___x_1612_ = l_Lean_mkAppB(v___x_1611_, v_n_1608_, v_i_1609_);
v___x_1613_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1612_, v_r_1596_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v_r_1596_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
else
{
lean_object* v___x_1616_; 
lean_dec_ref(v___x_1612_);
v___x_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1616_, 0, v_r_1596_);
return v___x_1616_;
}
}
v___jp_1617_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1619_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85));
v___x_1620_ = l_Lean_Expr_const___override(v___x_1619_, v_us_1573_);
lean_inc_ref(v_x_1618_);
v___x_1621_ = l_Lean_Expr_app___override(v___x_1620_, v_x_1618_);
v___x_1622_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1621_, v_r_1596_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v_r_1596_);
v___y_1577_ = v_x_1618_;
v___y_1578_ = v___x_1623_;
goto v___jp_1576_;
}
else
{
lean_dec_ref(v___x_1621_);
v___y_1577_ = v_x_1618_;
v___y_1578_ = v_r_1596_;
goto v___jp_1576_;
}
}
}
else
{
lean_dec(v_us_1573_);
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
}
v___jp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1579_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76));
v___x_1580_ = l_Lean_Expr_const___override(v___x_1579_, v_us_1573_);
v___x_1581_ = l_Lean_Expr_app___override(v___x_1580_, v___y_1577_);
v___x_1582_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1581_, v___y_1578_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1584_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 1);
lean_ctor_set(v___x_1240_, 1, v___y_1578_);
lean_ctor_set(v___x_1240_, 0, v___x_1581_);
v___x_1584_ = v___x_1240_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v___y_1578_);
v___x_1584_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
}
else
{
lean_object* v___x_1587_; 
lean_dec_ref(v___x_1581_);
lean_del_object(v___x_1240_);
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___y_1578_);
return v___x_1587_;
}
}
}
else
{
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
}
else
{
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
}
else
{
lean_del_object(v___x_1240_);
lean_dec(v_snd_1238_);
goto v___jp_1222_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_1236_);
lean_dec_ref(v_fst_1235_);
lean_dec_ref(v___x_1234_);
goto v___jp_1222_;
}
}
case 0:
{
lean_object* v_snd_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1767_; 
v_snd_1737_ = lean_ctor_get(v___x_1234_, 1);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; 
v_unused_1768_ = lean_ctor_get(v___x_1234_, 0);
lean_dec(v_unused_1768_);
v___x_1739_ = v___x_1234_;
v_isShared_1740_ = v_isSharedCheck_1767_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_snd_1737_);
lean_dec(v___x_1234_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1767_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v_str_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v_str_1741_ = lean_ctor_get(v_fst_1235_, 1);
lean_inc_ref(v_str_1741_);
lean_dec_ref(v_fst_1235_);
v___x_1742_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91));
v___x_1743_ = lean_string_dec_eq(v_str_1741_, v___x_1742_);
lean_dec_ref(v_str_1741_);
if (v___x_1743_ == 0)
{
lean_del_object(v___x_1739_);
lean_dec(v_snd_1737_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1744_ = lean_array_get_size(v_snd_1737_);
v___x_1745_ = lean_unsigned_to_nat(5u);
v___x_1746_ = lean_nat_dec_eq(v___x_1744_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_del_object(v___x_1739_);
lean_dec(v_snd_1737_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = lean_array_fget(v_snd_1737_, v___x_1747_);
v___x_1749_ = lean_box(0);
v___x_1750_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1751_ = lean_expr_eqv(v___x_1748_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
lean_dec(v___x_1748_);
lean_del_object(v___x_1739_);
lean_dec(v_snd_1737_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1749_);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1754_ = lean_array_fget(v_snd_1737_, v___x_1753_);
v___x_1755_ = lean_unsigned_to_nat(2u);
v___x_1756_ = lean_array_fget(v_snd_1737_, v___x_1755_);
v___x_1757_ = lean_unsigned_to_nat(3u);
v___x_1758_ = lean_array_fget(v_snd_1737_, v___x_1757_);
v___x_1759_ = lean_unsigned_to_nat(4u);
v___x_1760_ = lean_array_fget(v_snd_1737_, v___x_1759_);
lean_dec(v_snd_1737_);
v___x_1761_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94);
v___x_1762_ = l_Lean_mkApp5(v___x_1761_, v___x_1748_, v___x_1754_, v___x_1756_, v___x_1758_, v___x_1760_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set_tag(v___x_1739_, 1);
lean_ctor_set(v___x_1739_, 1, v___x_1749_);
lean_ctor_set(v___x_1739_, 0, v___x_1762_);
v___x_1764_ = v___x_1739_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___x_1749_);
v___x_1764_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_fst_1235_);
lean_dec_ref(v___x_1234_);
goto v___jp_1222_;
}
}
}
else
{
lean_dec(v_fst_1235_);
lean_dec_ref(v___x_1234_);
goto v___jp_1222_;
}
v___jp_1216_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_box(0);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
v___jp_1219_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
v___jp_1222_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
v___jp_1225_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
v___jp_1228_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_box(0);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
return v___x_1230_;
}
v___jp_1231_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_box(0);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(lean_object* v_e_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_e_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec_ref(v_a_1770_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object* v_e_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, uint8_t v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_e_1777_, v_a_1780_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object* v_e_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
uint8_t v_a_boxed_1800_; lean_object* v_res_1801_; 
v_a_boxed_1800_ = lean_unbox(v_a_1793_);
v_res_1801_ = l_Lean_Elab_Tactic_Omega_analyzeAtom(v_e_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_boxed_1800_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec(v_a_1790_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(lean_object* v_a_1802_, lean_object* v_x_1803_){
_start:
{
if (lean_obj_tag(v_x_1803_) == 0)
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_box(0);
return v___x_1804_;
}
else
{
lean_object* v_key_1805_; lean_object* v_value_1806_; lean_object* v_tail_1807_; uint8_t v___x_1808_; 
v_key_1805_ = lean_ctor_get(v_x_1803_, 0);
v_value_1806_ = lean_ctor_get(v_x_1803_, 1);
v_tail_1807_ = lean_ctor_get(v_x_1803_, 2);
v___x_1808_ = lean_expr_eqv(v_key_1805_, v_a_1802_);
if (v___x_1808_ == 0)
{
v_x_1803_ = v_tail_1807_;
goto _start;
}
else
{
lean_object* v___x_1810_; 
lean_inc(v_value_1806_);
v___x_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_value_1806_);
return v___x_1810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg___boxed(lean_object* v_a_1811_, lean_object* v_x_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_1811_, v_x_1812_);
lean_dec(v_x_1812_);
lean_dec_ref(v_a_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object* v_m_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_buckets_1816_; lean_object* v___x_1817_; uint64_t v___x_1818_; uint64_t v___x_1819_; uint64_t v___x_1820_; uint64_t v_fold_1821_; uint64_t v___x_1822_; uint64_t v___x_1823_; uint64_t v___x_1824_; size_t v___x_1825_; size_t v___x_1826_; size_t v___x_1827_; size_t v___x_1828_; size_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_buckets_1816_ = lean_ctor_get(v_m_1814_, 1);
v___x_1817_ = lean_array_get_size(v_buckets_1816_);
v___x_1818_ = l_Lean_Expr_hash(v_a_1815_);
v___x_1819_ = 32ULL;
v___x_1820_ = lean_uint64_shift_right(v___x_1818_, v___x_1819_);
v_fold_1821_ = lean_uint64_xor(v___x_1818_, v___x_1820_);
v___x_1822_ = 16ULL;
v___x_1823_ = lean_uint64_shift_right(v_fold_1821_, v___x_1822_);
v___x_1824_ = lean_uint64_xor(v_fold_1821_, v___x_1823_);
v___x_1825_ = lean_uint64_to_usize(v___x_1824_);
v___x_1826_ = lean_usize_of_nat(v___x_1817_);
v___x_1827_ = ((size_t)1ULL);
v___x_1828_ = lean_usize_sub(v___x_1826_, v___x_1827_);
v___x_1829_ = lean_usize_land(v___x_1825_, v___x_1828_);
v___x_1830_ = lean_array_uget_borrowed(v_buckets_1816_, v___x_1829_);
v___x_1831_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_1815_, v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(lean_object* v_m_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_1832_, v_a_1833_);
lean_dec_ref(v_a_1833_);
lean_dec_ref(v_m_1832_);
return v_res_1834_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(lean_object* v_a_1835_, lean_object* v_x_1836_){
_start:
{
if (lean_obj_tag(v_x_1836_) == 0)
{
uint8_t v___x_1837_; 
v___x_1837_ = 0;
return v___x_1837_;
}
else
{
lean_object* v_key_1838_; lean_object* v_tail_1839_; uint8_t v___x_1840_; 
v_key_1838_ = lean_ctor_get(v_x_1836_, 0);
v_tail_1839_ = lean_ctor_get(v_x_1836_, 2);
v___x_1840_ = lean_expr_eqv(v_key_1838_, v_a_1835_);
if (v___x_1840_ == 0)
{
v_x_1836_ = v_tail_1839_;
goto _start;
}
else
{
return v___x_1840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg___boxed(lean_object* v_a_1842_, lean_object* v_x_1843_){
_start:
{
uint8_t v_res_1844_; lean_object* v_r_1845_; 
v_res_1844_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_1842_, v_x_1843_);
lean_dec(v_x_1843_);
lean_dec_ref(v_a_1842_);
v_r_1845_ = lean_box(v_res_1844_);
return v_r_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
if (lean_obj_tag(v_x_1847_) == 0)
{
return v_x_1846_;
}
else
{
lean_object* v_key_1848_; lean_object* v_value_1849_; lean_object* v_tail_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1873_; 
v_key_1848_ = lean_ctor_get(v_x_1847_, 0);
v_value_1849_ = lean_ctor_get(v_x_1847_, 1);
v_tail_1850_ = lean_ctor_get(v_x_1847_, 2);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_x_1847_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1852_ = v_x_1847_;
v_isShared_1853_ = v_isSharedCheck_1873_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_tail_1850_);
lean_inc(v_value_1849_);
lean_inc(v_key_1848_);
lean_dec(v_x_1847_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1873_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; uint64_t v___x_1855_; uint64_t v___x_1856_; uint64_t v___x_1857_; uint64_t v_fold_1858_; uint64_t v___x_1859_; uint64_t v___x_1860_; uint64_t v___x_1861_; size_t v___x_1862_; size_t v___x_1863_; size_t v___x_1864_; size_t v___x_1865_; size_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1854_ = lean_array_get_size(v_x_1846_);
v___x_1855_ = l_Lean_Expr_hash(v_key_1848_);
v___x_1856_ = 32ULL;
v___x_1857_ = lean_uint64_shift_right(v___x_1855_, v___x_1856_);
v_fold_1858_ = lean_uint64_xor(v___x_1855_, v___x_1857_);
v___x_1859_ = 16ULL;
v___x_1860_ = lean_uint64_shift_right(v_fold_1858_, v___x_1859_);
v___x_1861_ = lean_uint64_xor(v_fold_1858_, v___x_1860_);
v___x_1862_ = lean_uint64_to_usize(v___x_1861_);
v___x_1863_ = lean_usize_of_nat(v___x_1854_);
v___x_1864_ = ((size_t)1ULL);
v___x_1865_ = lean_usize_sub(v___x_1863_, v___x_1864_);
v___x_1866_ = lean_usize_land(v___x_1862_, v___x_1865_);
v___x_1867_ = lean_array_uget_borrowed(v_x_1846_, v___x_1866_);
lean_inc(v___x_1867_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 2, v___x_1867_);
v___x_1869_ = v___x_1852_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_key_1848_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_value_1849_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_array_uset(v_x_1846_, v___x_1866_, v___x_1869_);
v_x_1846_ = v___x_1870_;
v_x_1847_ = v_tail_1850_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1874_, lean_object* v_source_1875_, lean_object* v_target_1876_){
_start:
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = lean_array_get_size(v_source_1875_);
v___x_1878_ = lean_nat_dec_lt(v_i_1874_, v___x_1877_);
if (v___x_1878_ == 0)
{
lean_dec_ref(v_source_1875_);
lean_dec(v_i_1874_);
return v_target_1876_;
}
else
{
lean_object* v_es_1879_; lean_object* v___x_1880_; lean_object* v_source_1881_; lean_object* v_target_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_es_1879_ = lean_array_fget(v_source_1875_, v_i_1874_);
v___x_1880_ = lean_box(0);
v_source_1881_ = lean_array_fset(v_source_1875_, v_i_1874_, v___x_1880_);
v_target_1882_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(v_target_1876_, v_es_1879_);
v___x_1883_ = lean_unsigned_to_nat(1u);
v___x_1884_ = lean_nat_add(v_i_1874_, v___x_1883_);
lean_dec(v_i_1874_);
v_i_1874_ = v___x_1884_;
v_source_1875_ = v_source_1881_;
v_target_1876_ = v_target_1882_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(lean_object* v_data_1886_){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v_nbuckets_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1887_ = lean_array_get_size(v_data_1886_);
v___x_1888_ = lean_unsigned_to_nat(2u);
v_nbuckets_1889_ = lean_nat_mul(v___x_1887_, v___x_1888_);
v___x_1890_ = lean_unsigned_to_nat(0u);
v___x_1891_ = lean_box(0);
v___x_1892_ = lean_mk_array(v_nbuckets_1889_, v___x_1891_);
v___x_1893_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(v___x_1890_, v_data_1886_, v___x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(lean_object* v_a_1894_, lean_object* v_b_1895_, lean_object* v_x_1896_){
_start:
{
if (lean_obj_tag(v_x_1896_) == 0)
{
lean_dec(v_b_1895_);
lean_dec_ref(v_a_1894_);
return v_x_1896_;
}
else
{
lean_object* v_key_1897_; lean_object* v_value_1898_; lean_object* v_tail_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1911_; 
v_key_1897_ = lean_ctor_get(v_x_1896_, 0);
v_value_1898_ = lean_ctor_get(v_x_1896_, 1);
v_tail_1899_ = lean_ctor_get(v_x_1896_, 2);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_x_1896_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1901_ = v_x_1896_;
v_isShared_1902_ = v_isSharedCheck_1911_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_tail_1899_);
lean_inc(v_value_1898_);
lean_inc(v_key_1897_);
lean_dec(v_x_1896_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1911_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
uint8_t v___x_1903_; 
v___x_1903_ = lean_expr_eqv(v_key_1897_, v_a_1894_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1904_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_1894_, v_b_1895_, v_tail_1899_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 2, v___x_1904_);
v___x_1906_ = v___x_1901_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_key_1897_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_value_1898_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
else
{
lean_object* v___x_1909_; 
lean_dec(v_value_1898_);
lean_dec(v_key_1897_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 1, v_b_1895_);
lean_ctor_set(v___x_1901_, 0, v_a_1894_);
v___x_1909_ = v___x_1901_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1894_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_b_1895_);
lean_ctor_set(v_reuseFailAlloc_1910_, 2, v_tail_1899_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object* v_m_1912_, lean_object* v_a_1913_, lean_object* v_b_1914_){
_start:
{
lean_object* v_size_1915_; lean_object* v_buckets_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1959_; 
v_size_1915_ = lean_ctor_get(v_m_1912_, 0);
v_buckets_1916_ = lean_ctor_get(v_m_1912_, 1);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_m_1912_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1918_ = v_m_1912_;
v_isShared_1919_ = v_isSharedCheck_1959_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_buckets_1916_);
lean_inc(v_size_1915_);
lean_dec(v_m_1912_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1959_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; uint64_t v___x_1921_; uint64_t v___x_1922_; uint64_t v___x_1923_; uint64_t v_fold_1924_; uint64_t v___x_1925_; uint64_t v___x_1926_; uint64_t v___x_1927_; size_t v___x_1928_; size_t v___x_1929_; size_t v___x_1930_; size_t v___x_1931_; size_t v___x_1932_; lean_object* v_bkt_1933_; uint8_t v___x_1934_; 
v___x_1920_ = lean_array_get_size(v_buckets_1916_);
v___x_1921_ = l_Lean_Expr_hash(v_a_1913_);
v___x_1922_ = 32ULL;
v___x_1923_ = lean_uint64_shift_right(v___x_1921_, v___x_1922_);
v_fold_1924_ = lean_uint64_xor(v___x_1921_, v___x_1923_);
v___x_1925_ = 16ULL;
v___x_1926_ = lean_uint64_shift_right(v_fold_1924_, v___x_1925_);
v___x_1927_ = lean_uint64_xor(v_fold_1924_, v___x_1926_);
v___x_1928_ = lean_uint64_to_usize(v___x_1927_);
v___x_1929_ = lean_usize_of_nat(v___x_1920_);
v___x_1930_ = ((size_t)1ULL);
v___x_1931_ = lean_usize_sub(v___x_1929_, v___x_1930_);
v___x_1932_ = lean_usize_land(v___x_1928_, v___x_1931_);
v_bkt_1933_ = lean_array_uget_borrowed(v_buckets_1916_, v___x_1932_);
v___x_1934_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_1913_, v_bkt_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; lean_object* v_size_x27_1936_; lean_object* v___x_1937_; lean_object* v_buckets_x27_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1935_ = lean_unsigned_to_nat(1u);
v_size_x27_1936_ = lean_nat_add(v_size_1915_, v___x_1935_);
lean_dec(v_size_1915_);
lean_inc(v_bkt_1933_);
v___x_1937_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1937_, 0, v_a_1913_);
lean_ctor_set(v___x_1937_, 1, v_b_1914_);
lean_ctor_set(v___x_1937_, 2, v_bkt_1933_);
v_buckets_x27_1938_ = lean_array_uset(v_buckets_1916_, v___x_1932_, v___x_1937_);
v___x_1939_ = lean_unsigned_to_nat(4u);
v___x_1940_ = lean_nat_mul(v_size_x27_1936_, v___x_1939_);
v___x_1941_ = lean_unsigned_to_nat(3u);
v___x_1942_ = lean_nat_div(v___x_1940_, v___x_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_array_get_size(v_buckets_x27_1938_);
v___x_1944_ = lean_nat_dec_le(v___x_1942_, v___x_1943_);
lean_dec(v___x_1942_);
if (v___x_1944_ == 0)
{
lean_object* v_val_1945_; lean_object* v___x_1947_; 
v_val_1945_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_buckets_x27_1938_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v_val_1945_);
lean_ctor_set(v___x_1918_, 0, v_size_x27_1936_);
v___x_1947_ = v___x_1918_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_size_x27_1936_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_val_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
else
{
lean_object* v___x_1950_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v_buckets_x27_1938_);
lean_ctor_set(v___x_1918_, 0, v_size_x27_1936_);
v___x_1950_ = v___x_1918_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_size_x27_1936_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_buckets_x27_1938_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
else
{
lean_object* v___x_1952_; lean_object* v_buckets_x27_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
lean_inc(v_bkt_1933_);
v___x_1952_ = lean_box(0);
v_buckets_x27_1953_ = lean_array_uset(v_buckets_1916_, v___x_1932_, v___x_1952_);
v___x_1954_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_1913_, v_b_1914_, v_bkt_1933_);
v___x_1955_ = lean_array_uset(v_buckets_x27_1953_, v___x_1932_, v___x_1954_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_1955_);
v___x_1957_ = v___x_1918_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_size_1915_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(lean_object* v_msgData_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; lean_object* v_env_1967_; lean_object* v___x_1968_; lean_object* v_mctx_1969_; lean_object* v_lctx_1970_; lean_object* v_options_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1966_ = lean_st_ref_get(v___y_1964_);
v_env_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc_ref(v_env_1967_);
lean_dec(v___x_1966_);
v___x_1968_ = lean_st_ref_get(v___y_1962_);
v_mctx_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc_ref(v_mctx_1969_);
lean_dec(v___x_1968_);
v_lctx_1970_ = lean_ctor_get(v___y_1961_, 2);
v_options_1971_ = lean_ctor_get(v___y_1963_, 2);
lean_inc_ref(v_options_1971_);
lean_inc_ref(v_lctx_1970_);
v___x_1972_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1972_, 0, v_env_1967_);
lean_ctor_set(v___x_1972_, 1, v_mctx_1969_);
lean_ctor_set(v___x_1972_, 2, v_lctx_1970_);
lean_ctor_set(v___x_1972_, 3, v_options_1971_);
v___x_1973_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
lean_ctor_set(v___x_1973_, 1, v_msgData_1960_);
v___x_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8___boxed(lean_object* v_msgData_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(v_msgData_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
return v_res_1981_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1982_; double v___x_1983_; 
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1983_ = lean_float_of_nat(v___x_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(lean_object* v_cls_1987_, lean_object* v_msg_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_ref_1994_; lean_object* v___x_1995_; lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2040_; 
v_ref_1994_ = lean_ctor_get(v___y_1991_, 5);
v___x_1995_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(v_msg_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2040_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2040_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v_traceState_2001_; lean_object* v_env_2002_; lean_object* v_nextMacroScope_2003_; lean_object* v_ngen_2004_; lean_object* v_auxDeclNGen_2005_; lean_object* v_cache_2006_; lean_object* v_messages_2007_; lean_object* v_infoState_2008_; lean_object* v_snapshotTasks_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2039_; 
v___x_2000_ = lean_st_ref_take(v___y_1992_);
v_traceState_2001_ = lean_ctor_get(v___x_2000_, 4);
v_env_2002_ = lean_ctor_get(v___x_2000_, 0);
v_nextMacroScope_2003_ = lean_ctor_get(v___x_2000_, 1);
v_ngen_2004_ = lean_ctor_get(v___x_2000_, 2);
v_auxDeclNGen_2005_ = lean_ctor_get(v___x_2000_, 3);
v_cache_2006_ = lean_ctor_get(v___x_2000_, 5);
v_messages_2007_ = lean_ctor_get(v___x_2000_, 6);
v_infoState_2008_ = lean_ctor_get(v___x_2000_, 7);
v_snapshotTasks_2009_ = lean_ctor_get(v___x_2000_, 8);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2011_ = v___x_2000_;
v_isShared_2012_ = v_isSharedCheck_2039_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_snapshotTasks_2009_);
lean_inc(v_infoState_2008_);
lean_inc(v_messages_2007_);
lean_inc(v_cache_2006_);
lean_inc(v_traceState_2001_);
lean_inc(v_auxDeclNGen_2005_);
lean_inc(v_ngen_2004_);
lean_inc(v_nextMacroScope_2003_);
lean_inc(v_env_2002_);
lean_dec(v___x_2000_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2039_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
uint64_t v_tid_2013_; lean_object* v_traces_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2038_; 
v_tid_2013_ = lean_ctor_get_uint64(v_traceState_2001_, sizeof(void*)*1);
v_traces_2014_ = lean_ctor_get(v_traceState_2001_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_traceState_2001_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2016_ = v_traceState_2001_;
v_isShared_2017_ = v_isSharedCheck_2038_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_traces_2014_);
lean_dec(v_traceState_2001_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2038_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; double v___x_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2018_ = lean_box(0);
v___x_2019_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0);
v___x_2020_ = 0;
v___x_2021_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1));
v___x_2022_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2022_, 0, v_cls_1987_);
lean_ctor_set(v___x_2022_, 1, v___x_2018_);
lean_ctor_set(v___x_2022_, 2, v___x_2021_);
lean_ctor_set_float(v___x_2022_, sizeof(void*)*3, v___x_2019_);
lean_ctor_set_float(v___x_2022_, sizeof(void*)*3 + 8, v___x_2019_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*3 + 16, v___x_2020_);
v___x_2023_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2));
v___x_2024_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2022_);
lean_ctor_set(v___x_2024_, 1, v_a_1996_);
lean_ctor_set(v___x_2024_, 2, v___x_2023_);
lean_inc(v_ref_1994_);
v___x_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2025_, 0, v_ref_1994_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = l_Lean_PersistentArray_push___redArg(v_traces_2014_, v___x_2025_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2026_);
v___x_2028_ = v___x_2016_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2026_);
lean_ctor_set_uint64(v_reuseFailAlloc_2037_, sizeof(void*)*1, v_tid_2013_);
v___x_2028_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2030_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 4, v___x_2028_);
v___x_2030_ = v___x_2011_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_env_2002_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_nextMacroScope_2003_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_ngen_2004_);
lean_ctor_set(v_reuseFailAlloc_2036_, 3, v_auxDeclNGen_2005_);
lean_ctor_set(v_reuseFailAlloc_2036_, 4, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2036_, 5, v_cache_2006_);
lean_ctor_set(v_reuseFailAlloc_2036_, 6, v_messages_2007_);
lean_ctor_set(v_reuseFailAlloc_2036_, 7, v_infoState_2008_);
lean_ctor_set(v_reuseFailAlloc_2036_, 8, v_snapshotTasks_2009_);
v___x_2030_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2031_ = lean_st_ref_set(v___y_1992_, v___x_2030_);
v___x_2032_ = lean_box(0);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2032_);
v___x_2034_ = v___x_1998_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___boxed(lean_object* v_cls_2041_, lean_object* v_msg_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v_cls_2041_, v_msg_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
if (lean_obj_tag(v_x_2049_) == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = l_List_reverse___redArg(v_x_2050_);
v___x_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
return v___x_2057_;
}
else
{
lean_object* v_head_2058_; lean_object* v_tail_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2077_; 
v_head_2058_ = lean_ctor_get(v_x_2049_, 0);
v_tail_2059_ = lean_ctor_get(v_x_2049_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_x_2049_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2061_ = v_x_2049_;
v_isShared_2062_ = v_isSharedCheck_2077_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_tail_2059_);
lean_inc(v_head_2058_);
lean_dec(v_x_2049_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2077_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; 
lean_inc(v___y_2054_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc_ref(v___y_2051_);
v___x_2063_ = lean_infer_type(v_head_2058_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2066_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v___x_2063_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v_x_2050_);
lean_ctor_set(v___x_2061_, 0, v_a_2064_);
v___x_2066_ = v___x_2061_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2064_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_x_2050_);
v___x_2066_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
v_x_2049_ = v_tail_2059_;
v_x_2050_ = v___x_2066_;
goto _start;
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_del_object(v___x_2061_);
lean_dec(v_tail_2059_);
lean_dec(v_x_2050_);
v_a_2069_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2063_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2063_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(lean_object* v_x_2078_, lean_object* v_x_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_x_2078_, v_x_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
if (lean_obj_tag(v_a_2086_) == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = l_List_reverse___redArg(v_a_2087_);
return v___x_2088_;
}
else
{
lean_object* v_head_2089_; lean_object* v_tail_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2099_; 
v_head_2089_ = lean_ctor_get(v_a_2086_, 0);
v_tail_2090_ = lean_ctor_get(v_a_2086_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_a_2086_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2092_ = v_a_2086_;
v_isShared_2093_ = v_isSharedCheck_2099_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_tail_2090_);
lean_inc(v_head_2089_);
lean_dec(v_a_2086_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2099_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2094_ = l_Lean_MessageData_ofExpr(v_head_2089_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v_a_2087_);
lean_ctor_set(v___x_2092_, 0, v___x_2094_);
v___x_2096_ = v___x_2092_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_a_2087_);
v___x_2096_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
v_a_2086_ = v_tail_2090_;
v_a_2087_ = v___x_2096_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__1));
v___x_2107_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__3));
v___x_2108_ = l_Lean_Name_append(v___x_2107_, v___x_2106_);
return v___x_2108_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__5));
v___x_2111_ = l_Lean_stringToMessageData(v___x_2110_);
return v___x_2111_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__7));
v___x_2114_ = l_Lean_stringToMessageData(v___x_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object* v_e_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, uint8_t v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_st_ref_get(v_a_2117_);
v___x_2127_ = l_Lean_Meta_Canonicalizer_canon(v_e_2115_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2224_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2224_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2224_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___x_2144_; 
v___x_2144_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v___x_2126_, v_a_2128_);
lean_dec(v___x_2126_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_options_2145_; lean_object* v_inheritedTraceOptions_2146_; uint8_t v_hasTrace_2147_; lean_object* v___x_2148_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; uint8_t v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; 
v_options_2145_ = lean_ctor_get(v_a_2123_, 2);
v_inheritedTraceOptions_2146_ = lean_ctor_get(v_a_2123_, 13);
v_hasTrace_2147_ = lean_ctor_get_uint8(v_options_2145_, sizeof(void*)*1);
v___x_2148_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__1));
if (v_hasTrace_2147_ == 0)
{
v___y_2150_ = v_a_2116_;
v___y_2151_ = v_a_2117_;
v___y_2152_ = v_a_2118_;
v___y_2153_ = v_a_2119_;
v___y_2154_ = v_a_2120_;
v___y_2155_ = v_a_2121_;
v___y_2156_ = v_a_2122_;
v___y_2157_ = v_a_2123_;
v___y_2158_ = v_a_2124_;
goto v___jp_2149_;
}
else
{
lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2200_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__4, &l_Lean_Elab_Tactic_Omega_lookup___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4);
v___x_2201_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2146_, v_options_2145_, v___x_2200_);
if (v___x_2201_ == 0)
{
v___y_2150_ = v_a_2116_;
v___y_2151_ = v_a_2117_;
v___y_2152_ = v_a_2118_;
v___y_2153_ = v_a_2119_;
v___y_2154_ = v_a_2120_;
v___y_2155_ = v_a_2121_;
v___y_2156_ = v_a_2122_;
v___y_2157_ = v_a_2123_;
v___y_2158_ = v_a_2124_;
goto v___jp_2149_;
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2202_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__8, &l_Lean_Elab_Tactic_Omega_lookup___closed__8_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8);
lean_inc(v_a_2128_);
v___x_2203_ = l_Lean_MessageData_ofExpr(v_a_2128_);
v___x_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v___x_2148_, v___x_2204_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_dec_ref(v___x_2205_);
v___y_2150_ = v_a_2116_;
v___y_2151_ = v_a_2117_;
v___y_2152_ = v_a_2118_;
v___y_2153_ = v_a_2119_;
v___y_2154_ = v_a_2120_;
v___y_2155_ = v_a_2121_;
v___y_2156_ = v_a_2122_;
v___y_2157_ = v_a_2123_;
v___y_2158_ = v_a_2124_;
goto v___jp_2149_;
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_del_object(v___x_2130_);
lean_dec(v_a_2128_);
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
v___jp_2149_:
{
lean_object* v___x_2159_; 
lean_inc(v_a_2128_);
v___x_2159_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_a_2128_, v___y_2152_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_options_2160_; uint8_t v_hasTrace_2161_; 
v_options_2160_ = lean_ctor_get(v___y_2157_, 2);
v_hasTrace_2161_ = lean_ctor_get_uint8(v_options_2160_, sizeof(void*)*1);
if (v_hasTrace_2161_ == 0)
{
lean_object* v_a_2162_; 
v_a_2162_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2162_);
lean_dec_ref(v___x_2159_);
v___y_2133_ = v_a_2162_;
v___y_2134_ = v___y_2151_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2163_; lean_object* v_inheritedTraceOptions_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v_a_2163_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2163_);
lean_dec_ref(v___x_2159_);
v_inheritedTraceOptions_2164_ = lean_ctor_get(v___y_2157_, 13);
v___x_2165_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__4, &l_Lean_Elab_Tactic_Omega_lookup___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4);
v___x_2166_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2164_, v_options_2160_, v___x_2165_);
if (v___x_2166_ == 0)
{
v___y_2133_ = v_a_2163_;
v___y_2134_ = v___y_2151_;
goto v___jp_2132_;
}
else
{
uint8_t v___x_2167_; 
v___x_2167_ = l_List_isEmpty___redArg(v_a_2163_);
if (v___x_2167_ == 0)
{
if (v___x_2166_ == 0)
{
v___y_2133_ = v_a_2163_;
v___y_2134_ = v___y_2151_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = lean_box(0);
lean_inc(v_a_2163_);
v___x_2169_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_a_2163_, v___x_2168_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref(v___x_2169_);
v___x_2171_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__6, &l_Lean_Elab_Tactic_Omega_lookup___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6);
v___x_2172_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(v_a_2170_, v___x_2168_);
v___x_2173_ = l_Lean_MessageData_ofList(v___x_2172_);
v___x_2174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2171_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v___x_2148_, v___x_2174_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_dec_ref(v___x_2175_);
v___y_2133_ = v_a_2163_;
v___y_2134_ = v___y_2151_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_a_2163_);
lean_del_object(v___x_2130_);
lean_dec(v_a_2128_);
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_a_2163_);
lean_del_object(v___x_2130_);
lean_dec(v_a_2128_);
v_a_2184_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2169_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2169_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
else
{
v___y_2133_ = v_a_2163_;
v___y_2134_ = v___y_2151_;
goto v___jp_2132_;
}
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_del_object(v___x_2130_);
lean_dec(v_a_2128_);
v_a_2192_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2159_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2159_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
else
{
lean_object* v_val_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2223_; 
lean_del_object(v___x_2130_);
lean_dec(v_a_2128_);
v_val_2214_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2216_ = v___x_2144_;
v_isShared_2217_ = v_isSharedCheck_2223_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_val_2214_);
lean_dec(v___x_2144_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2223_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2218_ = lean_box(0);
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v_val_2214_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set_tag(v___x_2216_, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2219_);
v___x_2221_ = v___x_2216_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
v___jp_2132_:
{
lean_object* v___x_2135_; lean_object* v_size_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2135_ = lean_st_ref_take(v___y_2134_);
v_size_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc_n(v_size_2136_, 2);
v___x_2137_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v___x_2135_, v_a_2128_, v_size_2136_);
v___x_2138_ = lean_st_ref_set(v___y_2134_, v___x_2137_);
v___x_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___y_2133_);
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v_size_2136_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2140_);
v___x_2142_ = v___x_2130_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v___x_2126_);
v_a_2225_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2127_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2127_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object* v_e_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
uint8_t v_a_boxed_2244_; lean_object* v_res_2245_; 
v_a_boxed_2244_ = lean_unbox(v_a_2237_);
v_res_2245_ = l_Lean_Elab_Tactic_Omega_lookup(v_e_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_boxed_2244_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec(v_a_2234_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(lean_object* v_00_u03b2_2246_, lean_object* v_m_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_2247_, v_a_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(lean_object* v_00_u03b2_2250_, lean_object* v_m_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(v_00_u03b2_2250_, v_m_2251_, v_a_2252_);
lean_dec_ref(v_a_2252_);
lean_dec_ref(v_m_2251_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object* v_00_u03b2_2254_, lean_object* v_m_2255_, lean_object* v_a_2256_, lean_object* v_b_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v_m_2255_, v_a_2256_, v_b_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object* v_x_2259_, lean_object* v_x_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, uint8_t v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_x_2259_, v_x_2260_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(lean_object* v_x_2272_, lean_object* v_x_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
uint8_t v___y_42932__boxed_2284_; lean_object* v_res_2285_; 
v___y_42932__boxed_2284_ = lean_unbox(v___y_2277_);
v_res_2285_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(v_x_2272_, v_x_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_42932__boxed_2284_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec(v___y_2274_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(lean_object* v_cls_2286_, lean_object* v_msg_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, uint8_t v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v_cls_2286_, v_msg_2287_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___boxed(lean_object* v_cls_2299_, lean_object* v_msg_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
uint8_t v___y_42968__boxed_2311_; lean_object* v_res_2312_; 
v___y_42968__boxed_2311_ = lean_unbox(v___y_2304_);
v_res_2312_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(v_cls_2299_, v_msg_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_42968__boxed_2311_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec(v___y_2301_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(lean_object* v_00_u03b2_2313_, lean_object* v_a_2314_, lean_object* v_x_2315_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_2314_, v_x_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2317_, lean_object* v_a_2318_, lean_object* v_x_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(v_00_u03b2_2317_, v_a_2318_, v_x_2319_);
lean_dec(v_x_2319_);
lean_dec_ref(v_a_2318_);
return v_res_2320_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(lean_object* v_00_u03b2_2321_, lean_object* v_a_2322_, lean_object* v_x_2323_){
_start:
{
uint8_t v___x_2324_; 
v___x_2324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_2322_, v_x_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2325_, lean_object* v_a_2326_, lean_object* v_x_2327_){
_start:
{
uint8_t v_res_2328_; lean_object* v_r_2329_; 
v_res_2328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(v_00_u03b2_2325_, v_a_2326_, v_x_2327_);
lean_dec(v_x_2327_);
lean_dec_ref(v_a_2326_);
v_r_2329_ = lean_box(v_res_2328_);
return v_r_2329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3(lean_object* v_00_u03b2_2330_, lean_object* v_data_2331_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_data_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4(lean_object* v_00_u03b2_2333_, lean_object* v_a_2334_, lean_object* v_b_2335_, lean_object* v_x_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_2334_, v_b_2335_, v_x_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2338_, lean_object* v_i_2339_, lean_object* v_source_2340_, lean_object* v_target_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(v_i_2339_, v_source_2340_, v_target_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_2343_, lean_object* v_x_2344_, lean_object* v_x_2345_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(v_x_2344_, v_x_2345_);
return v___x_2346_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Canonicalizer(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
