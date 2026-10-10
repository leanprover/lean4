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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v_m_3_, lean_object* v_cfg_4_, uint8_t v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
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
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1_ = stack[0].m_obj;
lean_object* v___x_2_ = stack[1].m_obj;
lean_object* v_m_3_ = stack[2].m_obj;
lean_object* v_cfg_4_ = stack[3].m_obj;
uint8_t v___y_5_ = stack[4].m_num;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v___y_10_ = stack[9].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(v___x_1_, v___x_2_, v_m_3_, v_cfg_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed(lean_object* v___x_27_, lean_object* v___x_28_, lean_object* v_m_29_, lean_object* v_cfg_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
uint8_t v___y_4824__boxed_38_; lean_object* v_res_39_; 
v___y_4824__boxed_38_ = lean_unbox(v___y_31_);
v_res_39_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(v___x_27_, v___x_28_, v_m_29_, v_cfg_30_, v___y_4824__boxed_38_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
lean_dec(v___y_32_);
return v_res_39_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_box(0);
v___x_41_ = lean_unsigned_to_nat(16u);
v___x_42_ = lean_mk_array(v___x_41_, v___x_40_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0, &l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0);
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
return v___x_47_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(lean_object* v_m_48_, lean_object* v_cfg_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_55_; lean_object* v___f_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_55_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1);
v___f_56_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_56_, 0, v___x_55_);
lean_closure_set(v___f_56_, 1, v___x_55_);
lean_closure_set(v___f_56_, 2, v_m_48_);
lean_closure_set(v___f_56_, 3, v_cfg_49_);
v___x_57_ = 3;
v___x_58_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2);
v___x_59_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(v___f_56_, v___x_57_, v___x_58_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
return v___x_59_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_48_ = stack[0].m_obj;
lean_object* v_cfg_49_ = stack[1].m_obj;
lean_object* v_a_50_ = stack[2].m_obj;
lean_object* v_a_51_ = stack[3].m_obj;
lean_object* v_a_52_ = stack[4].m_obj;
lean_object* v_a_53_ = stack[5].m_obj;
lean_object* v_res_60_;
v_res_60_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(v_m_48_, v_cfg_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
stack->m_obj
 = v_res_60_;
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
lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_object* v_00_u03b1_69_, lean_object* v_m_70_, lean_object* v_cfg_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(v_m_70_, v_cfg_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
return v___x_77_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_OmegaM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_70_ = stack[1].m_obj;
lean_object* v_cfg_71_ = stack[2].m_obj;
lean_object* v_a_72_ = stack[3].m_obj;
lean_object* v_a_73_ = stack[4].m_obj;
lean_object* v_a_74_ = stack[5].m_obj;
lean_object* v_a_75_ = stack[6].m_obj;
lean_object* v_res_78_;
v_res_78_ = l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_box(0), v_m_70_, v_cfg_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___boxed(lean_object* v_00_u03b1_79_, lean_object* v_m_80_, lean_object* v_cfg_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Elab_Tactic_Omega_OmegaM_run(v_00_u03b1_79_, v_m_80_, v_cfg_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
return v_res_87_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg(lean_object* v_a_88_){
_start:
{
lean_object* v___x_90_; 
lean_inc_ref(v_a_88_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v_a_88_);
return v___x_90_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_cfg___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_88_ = stack[0].m_obj;
lean_object* v_res_91_;
v_res_91_ = l_Lean_Elab_Tactic_Omega_cfg___redArg(v_a_88_);
stack->m_obj
 = v_res_91_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg___boxed(lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Elab_Tactic_Omega_cfg___redArg(v_a_92_);
lean_dec_ref(v_a_92_);
return v_res_94_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_cfg(lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, uint8_t v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_105_; 
lean_inc_ref(v_a_97_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v_a_97_);
return v___x_105_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_cfg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_95_ = stack[0].m_obj;
lean_object* v_a_96_ = stack[1].m_obj;
lean_object* v_a_97_ = stack[2].m_obj;
uint8_t v_a_98_ = stack[3].m_num;
lean_object* v_a_99_ = stack[4].m_obj;
lean_object* v_a_100_ = stack[5].m_obj;
lean_object* v_a_101_ = stack[6].m_obj;
lean_object* v_a_102_ = stack[7].m_obj;
lean_object* v_a_103_ = stack[8].m_obj;
lean_object* v_res_106_;
v_res_106_ = l_Lean_Elab_Tactic_Omega_cfg(v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___boxed(lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
uint8_t v_a_boxed_117_; lean_object* v_res_118_; 
v_a_boxed_117_ = lean_unbox(v_a_110_);
v_res_118_ = l_Lean_Elab_Tactic_Omega_cfg(v_a_107_, v_a_108_, v_a_109_, v_a_boxed_117_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec(v_a_107_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(lean_object* v_hi_119_, lean_object* v_pivot_120_, lean_object* v_as_121_, lean_object* v_i_122_, lean_object* v_k_123_){
_start:
{
uint8_t v___x_124_; 
v___x_124_ = lean_nat_dec_lt(v_k_123_, v_hi_119_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec(v_k_123_);
v___x_125_ = lean_array_fswap(v_as_121_, v_i_122_, v_hi_119_);
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v_i_122_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
return v___x_126_;
}
else
{
lean_object* v___x_127_; lean_object* v_snd_128_; lean_object* v_snd_129_; uint8_t v___x_130_; 
v___x_127_ = lean_array_fget_borrowed(v_as_121_, v_k_123_);
v_snd_128_ = lean_ctor_get(v___x_127_, 1);
v_snd_129_ = lean_ctor_get(v_pivot_120_, 1);
v___x_130_ = lean_nat_dec_lt(v_snd_128_, v_snd_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1u);
v___x_132_ = lean_nat_add(v_k_123_, v___x_131_);
lean_dec(v_k_123_);
v_k_123_ = v___x_132_;
goto _start;
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_134_ = lean_array_fswap(v_as_121_, v_i_122_, v_k_123_);
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = lean_nat_add(v_i_122_, v___x_135_);
lean_dec(v_i_122_);
v___x_137_ = lean_nat_add(v_k_123_, v___x_135_);
lean_dec(v_k_123_);
v_as_121_ = v___x_134_;
v_i_122_ = v___x_136_;
v_k_123_ = v___x_137_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg___boxed(lean_object* v_hi_139_, lean_object* v_pivot_140_, lean_object* v_as_141_, lean_object* v_i_142_, lean_object* v_k_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_139_, v_pivot_140_, v_as_141_, v_i_142_, v_k_143_);
lean_dec_ref(v_pivot_140_);
lean_dec(v_hi_139_);
return v_res_144_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(lean_object* v_x1_145_, lean_object* v_x2_146_){
_start:
{
lean_object* v_snd_147_; lean_object* v_snd_148_; uint8_t v___x_149_; 
v_snd_147_ = lean_ctor_get(v_x1_145_, 1);
v_snd_148_ = lean_ctor_get(v_x2_146_, 1);
v___x_149_ = lean_nat_dec_lt(v_snd_147_, v_snd_148_);
return v___x_149_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_145_ = stack[0].m_obj;
lean_object* v_x2_146_ = stack[1].m_obj;
uint8_t v_res_150_;
v_res_150_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v_x1_145_, v_x2_146_);
stack->m_num = v_res_150_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(lean_object* v_x1_151_, lean_object* v_x2_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v_x1_151_, v_x2_152_);
lean_dec_ref(v_x2_152_);
lean_dec_ref(v_x1_151_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(lean_object* v_n_155_, lean_object* v_as_156_, lean_object* v_lo_157_, lean_object* v_hi_158_){
_start:
{
lean_object* v___y_160_; uint8_t v___x_170_; 
v___x_170_ = lean_nat_dec_lt(v_lo_157_, v_hi_158_);
if (v___x_170_ == 0)
{
lean_dec(v_lo_157_);
return v_as_156_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v_mid_173_; lean_object* v___y_175_; lean_object* v___y_181_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_171_ = lean_nat_add(v_lo_157_, v_hi_158_);
v___x_172_ = lean_unsigned_to_nat(1u);
v_mid_173_ = lean_nat_shiftr(v___x_171_, v___x_172_);
lean_dec(v___x_171_);
v___x_186_ = lean_array_fget_borrowed(v_as_156_, v_mid_173_);
v___x_187_ = lean_array_fget_borrowed(v_as_156_, v_lo_157_);
v___x_188_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v___x_186_, v___x_187_);
if (v___x_188_ == 0)
{
v___y_181_ = v_as_156_;
goto v___jp_180_;
}
else
{
lean_object* v___x_189_; 
v___x_189_ = lean_array_fswap(v_as_156_, v_lo_157_, v_mid_173_);
v___y_181_ = v___x_189_;
goto v___jp_180_;
}
v___jp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_176_ = lean_array_fget_borrowed(v___y_175_, v_mid_173_);
v___x_177_ = lean_array_fget_borrowed(v___y_175_, v_hi_158_);
v___x_178_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
lean_dec(v_mid_173_);
v___y_160_ = v___y_175_;
goto v___jp_159_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = lean_array_fswap(v___y_175_, v_mid_173_, v_hi_158_);
lean_dec(v_mid_173_);
v___y_160_ = v___x_179_;
goto v___jp_159_;
}
}
v___jp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_182_ = lean_array_fget_borrowed(v___y_181_, v_hi_158_);
v___x_183_ = lean_array_fget_borrowed(v___y_181_, v_lo_157_);
v___x_184_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v___x_182_, v___x_183_);
if (v___x_184_ == 0)
{
v___y_175_ = v___y_181_;
goto v___jp_174_;
}
else
{
lean_object* v___x_185_; 
v___x_185_ = lean_array_fswap(v___y_181_, v_lo_157_, v_hi_158_);
v___y_175_ = v___x_185_;
goto v___jp_174_;
}
}
}
v___jp_159_:
{
lean_object* v_pivot_161_; lean_object* v___x_162_; lean_object* v_fst_163_; lean_object* v_snd_164_; uint8_t v___x_165_; 
v_pivot_161_ = lean_array_fget(v___y_160_, v_hi_158_);
lean_inc_n(v_lo_157_, 2);
v___x_162_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_158_, v_pivot_161_, v___y_160_, v_lo_157_, v_lo_157_);
lean_dec(v_pivot_161_);
v_fst_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_fst_163_);
v_snd_164_ = lean_ctor_get(v___x_162_, 1);
lean_inc(v_snd_164_);
lean_dec_ref(v___x_162_);
v___x_165_ = lean_nat_dec_le(v_hi_158_, v_fst_163_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_155_, v_snd_164_, v_lo_157_, v_fst_163_);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_add(v_fst_163_, v___x_167_);
lean_dec(v_fst_163_);
v_as_156_ = v___x_166_;
v_lo_157_ = v___x_168_;
goto _start;
}
else
{
lean_dec(v_fst_163_);
lean_dec(v_lo_157_);
return v_snd_164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___boxed(lean_object* v_n_190_, lean_object* v_as_191_, lean_object* v_lo_192_, lean_object* v_hi_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_190_, v_as_191_, v_lo_192_, v_hi_193_);
lean_dec(v_hi_193_);
lean_dec(v_n_190_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
return v_x_195_;
}
else
{
lean_object* v_key_197_; lean_object* v_value_198_; lean_object* v_tail_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_key_197_ = lean_ctor_get(v_x_196_, 0);
v_value_198_ = lean_ctor_get(v_x_196_, 1);
v_tail_199_ = lean_ctor_get(v_x_196_, 2);
lean_inc(v_value_198_);
lean_inc(v_key_197_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v_key_197_);
lean_ctor_set(v___x_200_, 1, v_value_198_);
v___x_201_ = lean_array_push(v_x_195_, v___x_200_);
v_x_195_ = v___x_201_;
v_x_196_ = v_tail_199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___boxed(lean_object* v_x_203_, lean_object* v_x_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(v_x_203_, v_x_204_);
lean_dec(v_x_204_);
return v_res_205_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(lean_object* v_as_206_, size_t v_i_207_, size_t v_stop_208_, lean_object* v_b_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = lean_usize_dec_eq(v_i_207_, v_stop_208_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; size_t v___x_213_; size_t v___x_214_; 
v___x_211_ = lean_array_uget_borrowed(v_as_206_, v_i_207_);
v___x_212_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(v_b_209_, v___x_211_);
v___x_213_ = ((size_t)1ULL);
v___x_214_ = lean_usize_add(v_i_207_, v___x_213_);
v_i_207_ = v___x_214_;
v_b_209_ = v___x_212_;
goto _start;
}
else
{
return v_b_209_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_206_ = stack[0].m_obj;
size_t v_i_207_ = stack[1].m_num;
size_t v_stop_208_ = stack[2].m_num;
lean_object* v_b_209_ = stack[3].m_obj;
lean_object* v_res_216_;
v_res_216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_as_206_, v_i_207_, v_stop_208_, v_b_209_);
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3___boxed(lean_object* v_as_217_, lean_object* v_i_218_, lean_object* v_stop_219_, lean_object* v_b_220_){
_start:
{
size_t v_i_boxed_221_; size_t v_stop_boxed_222_; lean_object* v_res_223_; 
v_i_boxed_221_ = lean_unbox_usize(v_i_218_);
lean_dec(v_i_218_);
v_stop_boxed_222_ = lean_unbox_usize(v_stop_219_);
lean_dec(v_stop_219_);
v_res_223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_as_217_, v_i_boxed_221_, v_stop_boxed_222_, v_b_220_);
lean_dec_ref(v_as_217_);
return v_res_223_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(size_t v_sz_224_, size_t v_i_225_, lean_object* v_bs_226_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_224_ = stack[0].m_num;
size_t v_i_225_ = stack[1].m_num;
lean_object* v_bs_226_ = stack[2].m_obj;
lean_object* v_res_236_;
v_res_236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_224_, v_i_225_, v_bs_226_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(lean_object* v_sz_237_, lean_object* v_i_238_, lean_object* v_bs_239_){
_start:
{
size_t v_sz_boxed_240_; size_t v_i_boxed_241_; lean_object* v_res_242_; 
v_sz_boxed_240_ = lean_unbox_usize(v_sz_237_);
lean_dec(v_sz_237_);
v_i_boxed_241_ = lean_unbox_usize(v_i_238_);
lean_dec(v_i_238_);
v_res_242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_boxed_240_, v_i_boxed_241_, v_bs_239_);
return v_res_242_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg(lean_object* v_a_243_){
_start:
{
lean_object* v___x_245_; lean_object* v___y_247_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_265_; lean_object* v_size_272_; lean_object* v_buckets_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_245_ = lean_st_ref_get(v_a_243_);
v_size_272_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_size_272_);
v_buckets_273_ = lean_ctor_get(v___x_245_, 1);
lean_inc_ref(v_buckets_273_);
lean_dec(v___x_245_);
v___x_274_ = lean_mk_empty_array_with_capacity(v_size_272_);
lean_dec(v_size_272_);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_array_get_size(v_buckets_273_);
v___x_277_ = lean_nat_dec_lt(v___x_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_dec_ref(v_buckets_273_);
v___y_265_ = v___x_274_;
goto v___jp_264_;
}
else
{
size_t v___x_278_; size_t v___x_279_; lean_object* v___x_280_; 
v___x_278_ = ((size_t)0ULL);
v___x_279_ = lean_usize_of_nat(v___x_276_);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_buckets_273_, v___x_278_, v___x_279_, v___x_274_);
lean_dec_ref(v_buckets_273_);
v___y_265_ = v___x_280_;
goto v___jp_264_;
}
v___jp_246_:
{
size_t v_sz_248_; size_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_sz_248_ = lean_array_size(v___y_247_);
v___x_249_ = ((size_t)0ULL);
v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_248_, v___x_249_, v___y_247_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
v___jp_252_:
{
lean_object* v___x_257_; 
v___x_257_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v___y_254_, v___y_253_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec(v___y_254_);
v___y_247_ = v___x_257_;
goto v___jp_246_;
}
v___jp_258_:
{
uint8_t v___x_263_; 
v___x_263_ = lean_nat_dec_le(v___y_262_, v___y_260_);
if (v___x_263_ == 0)
{
lean_dec(v___y_260_);
lean_inc(v___y_262_);
v___y_253_ = v___y_259_;
v___y_254_ = v___y_261_;
v___y_255_ = v___y_262_;
v___y_256_ = v___y_262_;
goto v___jp_252_;
}
else
{
v___y_253_ = v___y_259_;
v___y_254_ = v___y_261_;
v___y_255_ = v___y_262_;
v___y_256_ = v___y_260_;
goto v___jp_252_;
}
}
v___jp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_266_ = lean_array_get_size(v___y_265_);
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_nat_dec_eq(v___x_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_sub(v___x_266_, v___x_269_);
v___x_271_ = lean_nat_dec_le(v___x_267_, v___x_270_);
if (v___x_271_ == 0)
{
lean_inc(v___x_270_);
v___y_259_ = v___y_265_;
v___y_260_ = v___x_270_;
v___y_261_ = v___x_266_;
v___y_262_ = v___x_270_;
goto v___jp_258_;
}
else
{
v___y_259_ = v___y_265_;
v___y_260_ = v___x_270_;
v___y_261_ = v___x_266_;
v___y_262_ = v___x_267_;
goto v___jp_258_;
}
}
else
{
v___y_247_ = v___y_265_;
goto v___jp_246_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_atoms___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_243_ = stack[0].m_obj;
lean_object* v_res_281_;
v_res_281_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_243_);
stack->m_obj
 = v_res_281_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg___boxed(lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_282_);
lean_dec(v_a_282_);
return v_res_284_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, uint8_t v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_286_);
return v___x_295_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_atoms_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_285_ = stack[0].m_obj;
lean_object* v_a_286_ = stack[1].m_obj;
lean_object* v_a_287_ = stack[2].m_obj;
uint8_t v_a_288_ = stack[3].m_num;
lean_object* v_a_289_ = stack[4].m_obj;
lean_object* v_a_290_ = stack[5].m_obj;
lean_object* v_a_291_ = stack[6].m_obj;
lean_object* v_a_292_ = stack[7].m_obj;
lean_object* v_a_293_ = stack[8].m_obj;
lean_object* v_res_296_;
v_res_296_ = l_Lean_Elab_Tactic_Omega_atoms(v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
uint8_t v_a_boxed_307_; lean_object* v_res_308_; 
v_a_boxed_307_ = lean_unbox(v_a_300_);
v_res_308_ = l_Lean_Elab_Tactic_Omega_atoms(v_a_297_, v_a_298_, v_a_299_, v_a_boxed_307_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec(v_a_297_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(lean_object* v_n_309_, lean_object* v_as_310_, lean_object* v_lo_311_, lean_object* v_hi_312_, lean_object* v_w_313_, lean_object* v_hlo_314_, lean_object* v_hhi_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_309_, v_as_310_, v_lo_311_, v_hi_312_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(lean_object* v_n_317_, lean_object* v_as_318_, lean_object* v_lo_319_, lean_object* v_hi_320_, lean_object* v_w_321_, lean_object* v_hlo_322_, lean_object* v_hhi_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(v_n_317_, v_as_318_, v_lo_319_, v_hi_320_, v_w_321_, v_hlo_322_, v_hhi_323_);
lean_dec(v_hi_320_);
lean_dec(v_n_317_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(lean_object* v_n_325_, lean_object* v_lo_326_, lean_object* v_hi_327_, lean_object* v_hhi_328_, lean_object* v_pivot_329_, lean_object* v_as_330_, lean_object* v_i_331_, lean_object* v_k_332_, lean_object* v_ilo_333_, lean_object* v_ik_334_, lean_object* v_w_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_327_, v_pivot_329_, v_as_330_, v_i_331_, v_k_332_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___boxed(lean_object* v_n_337_, lean_object* v_lo_338_, lean_object* v_hi_339_, lean_object* v_hhi_340_, lean_object* v_pivot_341_, lean_object* v_as_342_, lean_object* v_i_343_, lean_object* v_k_344_, lean_object* v_ilo_345_, lean_object* v_ik_346_, lean_object* v_w_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(v_n_337_, v_lo_338_, v_hi_339_, v_hhi_340_, v_pivot_341_, v_as_342_, v_i_343_, v_k_344_, v_ilo_345_, v_ik_346_, v_w_347_);
lean_dec_ref(v_pivot_341_);
lean_dec(v_hi_339_);
lean_dec(v_lo_338_);
lean_dec(v_n_337_);
return v_res_348_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_box(0);
v___x_353_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1));
v___x_354_ = l_Lean_Expr_const___override(v___x_353_, v___x_352_);
return v___x_354_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg(lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_361_; lean_object* v_a_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_361_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_355_);
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref(v___x_361_);
v___x_363_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_364_ = lean_array_to_list(v_a_362_);
v___x_365_ = l_Lean_Meta_mkListLit(v___x_363_, v___x_364_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
return v___x_365_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_atomsList___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_355_ = stack[0].m_obj;
lean_object* v_a_356_ = stack[1].m_obj;
lean_object* v_a_357_ = stack[2].m_obj;
lean_object* v_a_358_ = stack[3].m_obj;
lean_object* v_a_359_ = stack[4].m_obj;
lean_object* v_res_366_;
v_res_366_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
stack->m_obj
 = v_res_366_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___boxed(lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
return v_res_373_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_atomsList(lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, uint8_t v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(v_a_375_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_384_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_atomsList_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_374_ = stack[0].m_obj;
lean_object* v_a_375_ = stack[1].m_obj;
lean_object* v_a_376_ = stack[2].m_obj;
uint8_t v_a_377_ = stack[3].m_num;
lean_object* v_a_378_ = stack[4].m_obj;
lean_object* v_a_379_ = stack[5].m_obj;
lean_object* v_a_380_ = stack[6].m_obj;
lean_object* v_a_381_ = stack[7].m_obj;
lean_object* v_a_382_ = stack[8].m_obj;
lean_object* v_res_385_;
v_res_385_ = l_Lean_Elab_Tactic_Omega_atomsList(v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
stack->m_obj
 = v_res_385_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___boxed(lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
uint8_t v_a_boxed_396_; lean_object* v_res_397_; 
v_a_boxed_396_ = lean_unbox(v_a_389_);
v_res_397_ = l_Lean_Elab_Tactic_Omega_atomsList(v_a_386_, v_a_387_, v_a_388_, v_a_boxed_396_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec(v_a_386_);
return v_res_397_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_box(0);
v___x_408_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4));
v___x_409_ = l_Lean_Expr_const___override(v___x_408_, v___x_407_);
return v___x_409_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_426_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_426_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_426_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_426_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_421_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5, &l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5);
v___x_422_ = l_Lean_Expr_app___override(v___x_421_, v_a_417_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_422_);
v___x_424_ = v___x_419_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
else
{
return v___x_416_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_410_ = stack[0].m_obj;
lean_object* v_a_411_ = stack[1].m_obj;
lean_object* v_a_412_ = stack[2].m_obj;
lean_object* v_a_413_ = stack[3].m_obj;
lean_object* v_a_414_ = stack[4].m_obj;
lean_object* v_res_427_;
v_res_427_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
stack->m_obj
 = v_res_427_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___boxed(lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
return v_res_434_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs(lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, uint8_t v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_436_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
return v___x_445_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_atomsCoeffs_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_435_ = stack[0].m_obj;
lean_object* v_a_436_ = stack[1].m_obj;
lean_object* v_a_437_ = stack[2].m_obj;
uint8_t v_a_438_ = stack[3].m_num;
lean_object* v_a_439_ = stack[4].m_obj;
lean_object* v_a_440_ = stack[5].m_obj;
lean_object* v_a_441_ = stack[6].m_obj;
lean_object* v_a_442_ = stack[7].m_obj;
lean_object* v_a_443_ = stack[8].m_obj;
lean_object* v_res_446_;
v_res_446_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs(v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
uint8_t v_a_boxed_457_; lean_object* v_res_458_; 
v_a_boxed_457_ = lean_unbox(v_a_450_);
v_res_458_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs(v_a_447_, v_a_448_, v_a_449_, v_a_boxed_457_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec(v_a_447_);
return v_res_458_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg(lean_object* v_t_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, uint8_t v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_470_ = lean_st_ref_get(v_a_461_);
v___x_471_ = lean_st_ref_get(v_a_460_);
v___x_472_ = lean_box(v_a_463_);
lean_inc(v_a_468_);
lean_inc_ref(v_a_467_);
lean_inc(v_a_466_);
lean_inc_ref(v_a_465_);
lean_inc(v_a_464_);
lean_inc_ref(v_a_462_);
lean_inc(v_a_461_);
lean_inc(v_a_460_);
v___x_473_ = lean_apply_10(v_t_459_, v_a_460_, v_a_461_, v_a_462_, v___x_472_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, lean_box(0));
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_492_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_492_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_492_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_492_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_snd_478_; uint8_t v___x_479_; 
v_snd_478_ = lean_ctor_get(v_a_474_, 1);
v___x_479_ = lean_unbox(v_snd_478_);
if (v___x_479_ == 0)
{
lean_object* v_fst_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v_fst_480_ = lean_ctor_get(v_a_474_, 0);
lean_inc(v_fst_480_);
lean_dec(v_a_474_);
v___x_481_ = lean_st_ref_take(v_a_461_);
lean_dec(v___x_481_);
v___x_482_ = lean_st_ref_put(v_a_461_, v___x_470_);
v___x_483_ = lean_st_ref_take(v_a_460_);
lean_dec(v___x_483_);
v___x_484_ = lean_st_ref_put(v_a_460_, v___x_471_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v_fst_480_);
v___x_486_ = v___x_476_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_fst_480_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
else
{
lean_object* v_fst_488_; lean_object* v___x_490_; 
lean_dec(v___x_471_);
lean_dec(v___x_470_);
v_fst_488_ = lean_ctor_get(v_a_474_, 0);
lean_inc(v_fst_488_);
lean_dec(v_a_474_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v_fst_488_);
v___x_490_ = v___x_476_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_fst_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v___x_471_);
lean_dec(v___x_470_);
v_a_493_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_473_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_473_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_commitWhen___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_459_ = stack[0].m_obj;
lean_object* v_a_460_ = stack[1].m_obj;
lean_object* v_a_461_ = stack[2].m_obj;
lean_object* v_a_462_ = stack[3].m_obj;
uint8_t v_a_463_ = stack[4].m_num;
lean_object* v_a_464_ = stack[5].m_obj;
lean_object* v_a_465_ = stack[6].m_obj;
lean_object* v_a_466_ = stack[7].m_obj;
lean_object* v_a_467_ = stack[8].m_obj;
lean_object* v_a_468_ = stack[9].m_obj;
lean_object* v_res_501_;
v_res_501_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(v_t_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
stack->m_obj
 = v_res_501_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg___boxed(lean_object* v_t_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
uint8_t v_a_boxed_513_; lean_object* v_res_514_; 
v_a_boxed_513_ = lean_unbox(v_a_506_);
v_res_514_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(v_t_502_, v_a_503_, v_a_504_, v_a_505_, v_a_boxed_513_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec(v_a_503_);
return v_res_514_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_commitWhen(lean_object* v_00_u03b1_515_, lean_object* v_t_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, uint8_t v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(v_t_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
return v___x_527_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_commitWhen_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_516_ = stack[1].m_obj;
lean_object* v_a_517_ = stack[2].m_obj;
lean_object* v_a_518_ = stack[3].m_obj;
lean_object* v_a_519_ = stack[4].m_obj;
uint8_t v_a_520_ = stack[5].m_num;
lean_object* v_a_521_ = stack[6].m_obj;
lean_object* v_a_522_ = stack[7].m_obj;
lean_object* v_a_523_ = stack[8].m_obj;
lean_object* v_a_524_ = stack[9].m_obj;
lean_object* v_a_525_ = stack[10].m_obj;
lean_object* v_res_528_;
v_res_528_ = l_Lean_Elab_Tactic_Omega_commitWhen(lean_box(0), v_t_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
stack->m_obj
 = v_res_528_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___boxed(lean_object* v_00_u03b1_529_, lean_object* v_t_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
uint8_t v_a_boxed_541_; lean_object* v_res_542_; 
v_a_boxed_541_ = lean_unbox(v_a_534_);
v_res_542_ = l_Lean_Elab_Tactic_Omega_commitWhen(v_00_u03b1_529_, v_t_530_, v_a_531_, v_a_532_, v_a_533_, v_a_boxed_541_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec(v_a_531_);
return v_res_542_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(lean_object* v_t_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, uint8_t v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_box(v___y_547_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_546_);
lean_inc(v___y_545_);
lean_inc(v___y_544_);
v___x_555_ = lean_apply_10(v_t_543_, v___y_544_, v___y_545_, v___y_546_, v___x_554_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, lean_box(0));
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_566_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_566_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_566_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_566_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
uint8_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_560_ = 0;
v___x_561_ = lean_box(v___x_560_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v_a_556_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_562_);
v___x_564_ = v___x_558_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
v_a_567_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_555_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_555_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_543_ = stack[0].m_obj;
lean_object* v___y_544_ = stack[1].m_obj;
lean_object* v___y_545_ = stack[2].m_obj;
lean_object* v___y_546_ = stack[3].m_obj;
uint8_t v___y_547_ = stack[4].m_num;
lean_object* v___y_548_ = stack[5].m_obj;
lean_object* v___y_549_ = stack[6].m_obj;
lean_object* v___y_550_ = stack[7].m_obj;
lean_object* v___y_551_ = stack[8].m_obj;
lean_object* v___y_552_ = stack[9].m_obj;
lean_object* v_res_575_;
v_res_575_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(v_t_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
stack->m_obj
 = v_res_575_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed(lean_object* v_t_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
uint8_t v___y_673__boxed_587_; lean_object* v_res_588_; 
v___y_673__boxed_587_ = lean_unbox(v___y_580_);
v_res_588_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(v_t_576_, v___y_577_, v___y_578_, v___y_579_, v___y_673__boxed_587_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec(v___y_577_);
return v_res_588_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(lean_object* v_t_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, uint8_t v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___f_600_; lean_object* v___x_601_; 
v___f_600_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_600_, 0, v_t_589_);
v___x_601_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(v___f_600_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
return v___x_601_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_589_ = stack[0].m_obj;
lean_object* v_a_590_ = stack[1].m_obj;
lean_object* v_a_591_ = stack[2].m_obj;
lean_object* v_a_592_ = stack[3].m_obj;
uint8_t v_a_593_ = stack[4].m_num;
lean_object* v_a_594_ = stack[5].m_obj;
lean_object* v_a_595_ = stack[6].m_obj;
lean_object* v_a_596_ = stack[7].m_obj;
lean_object* v_a_597_ = stack[8].m_obj;
lean_object* v_a_598_ = stack[9].m_obj;
lean_object* v_res_602_;
v_res_602_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(v_t_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
stack->m_obj
 = v_res_602_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___boxed(lean_object* v_t_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
uint8_t v_a_boxed_614_; lean_object* v_res_615_; 
v_a_boxed_614_ = lean_unbox(v_a_607_);
v_res_615_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(v_t_603_, v_a_604_, v_a_605_, v_a_606_, v_a_boxed_614_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec(v_a_604_);
return v_res_615_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_object* v_00_u03b1_616_, lean_object* v_t_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, uint8_t v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(v_t_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
return v___x_628_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_withoutModifyingState_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_617_ = stack[1].m_obj;
lean_object* v_a_618_ = stack[2].m_obj;
lean_object* v_a_619_ = stack[3].m_obj;
lean_object* v_a_620_ = stack[4].m_obj;
uint8_t v_a_621_ = stack[5].m_num;
lean_object* v_a_622_ = stack[6].m_obj;
lean_object* v_a_623_ = stack[7].m_obj;
lean_object* v_a_624_ = stack[8].m_obj;
lean_object* v_a_625_ = stack[9].m_obj;
lean_object* v_a_626_ = stack[10].m_obj;
lean_object* v_res_629_;
v_res_629_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_box(0), v_t_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
stack->m_obj
 = v_res_629_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(lean_object* v_00_u03b1_630_, lean_object* v_t_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
uint8_t v_a_boxed_642_; lean_object* v_res_643_; 
v_a_boxed_642_ = lean_unbox(v_a_635_);
v_res_643_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState(v_00_u03b1_630_, v_t_631_, v_a_632_, v_a_633_, v_a_634_, v_a_boxed_642_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec(v_a_632_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f(lean_object* v_n_646_){
_start:
{
lean_object* v___x_647_; lean_object* v_fst_648_; 
lean_inc_ref(v_n_646_);
v___x_647_ = l_Lean_Expr_getAppFnArgs(v_n_646_);
v_fst_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_fst_648_);
if (lean_obj_tag(v_fst_648_) == 1)
{
lean_object* v_pre_649_; 
v_pre_649_ = lean_ctor_get(v_fst_648_, 0);
lean_inc(v_pre_649_);
if (lean_obj_tag(v_pre_649_) == 1)
{
lean_object* v_pre_650_; 
v_pre_650_ = lean_ctor_get(v_pre_649_, 0);
if (lean_obj_tag(v_pre_650_) == 0)
{
lean_object* v_snd_651_; lean_object* v_str_652_; lean_object* v_str_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_snd_651_ = lean_ctor_get(v___x_647_, 1);
lean_inc(v_snd_651_);
lean_dec_ref(v___x_647_);
v_str_652_ = lean_ctor_get(v_fst_648_, 1);
lean_inc_ref(v_str_652_);
lean_dec_ref_known(v_fst_648_, 2);
v_str_653_ = lean_ctor_get(v_pre_649_, 1);
lean_inc_ref(v_str_653_);
lean_dec_ref_known(v_pre_649_, 2);
v___x_654_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_655_ = lean_string_dec_eq(v_str_653_, v___x_654_);
lean_dec_ref(v_str_653_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec_ref(v_str_652_);
lean_dec(v_snd_651_);
v___x_656_ = l_Lean_Expr_nat_x3f(v_n_646_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_658_ = lean_string_dec_eq(v_str_652_, v___x_657_);
lean_dec_ref(v_str_652_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
lean_dec(v_snd_651_);
v___x_659_ = l_Lean_Expr_nat_x3f(v_n_646_);
return v___x_659_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_660_ = lean_array_get_size(v_snd_651_);
v___x_661_ = lean_unsigned_to_nat(3u);
v___x_662_ = lean_nat_dec_eq(v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_dec(v_snd_651_);
v___x_663_ = l_Lean_Expr_nat_x3f(v_n_646_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec_ref(v_n_646_);
v___x_664_ = lean_unsigned_to_nat(2u);
v___x_665_ = lean_array_fget(v_snd_651_, v___x_664_);
lean_dec(v_snd_651_);
v___x_666_ = l_Lean_Expr_nat_x3f(v___x_665_);
return v___x_666_;
}
}
}
}
else
{
lean_object* v___x_667_; 
lean_dec_ref_known(v_pre_649_, 2);
lean_dec_ref_known(v_fst_648_, 2);
lean_dec_ref(v___x_647_);
v___x_667_ = l_Lean_Expr_nat_x3f(v_n_646_);
return v___x_667_;
}
}
else
{
lean_object* v___x_668_; 
lean_dec_ref_known(v_fst_648_, 2);
lean_dec(v_pre_649_);
lean_dec_ref(v___x_647_);
v___x_668_ = l_Lean_Expr_nat_x3f(v_n_646_);
return v___x_668_;
}
}
else
{
lean_object* v___x_669_; 
lean_dec(v_fst_648_);
lean_dec_ref(v___x_647_);
v___x_669_ = l_Lean_Expr_nat_x3f(v_n_646_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_Tactic_Omega_intCast_x3f_spec__0(lean_object* v_a_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = lean_nat_to_int(v_a_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_intCast_x3f(lean_object* v_n_672_){
_start:
{
lean_object* v___x_673_; lean_object* v_fst_674_; 
lean_inc_ref(v_n_672_);
v___x_673_ = l_Lean_Expr_getAppFnArgs(v_n_672_);
v_fst_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_fst_674_);
if (lean_obj_tag(v_fst_674_) == 1)
{
lean_object* v_pre_675_; 
v_pre_675_ = lean_ctor_get(v_fst_674_, 0);
lean_inc(v_pre_675_);
if (lean_obj_tag(v_pre_675_) == 1)
{
lean_object* v_pre_676_; 
v_pre_676_ = lean_ctor_get(v_pre_675_, 0);
if (lean_obj_tag(v_pre_676_) == 0)
{
lean_object* v_snd_677_; lean_object* v_str_678_; lean_object* v_str_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_snd_677_ = lean_ctor_get(v___x_673_, 1);
lean_inc(v_snd_677_);
lean_dec_ref(v___x_673_);
v_str_678_ = lean_ctor_get(v_fst_674_, 1);
lean_inc_ref(v_str_678_);
lean_dec_ref_known(v_fst_674_, 2);
v_str_679_ = lean_ctor_get(v_pre_675_, 1);
lean_inc_ref(v_str_679_);
lean_dec_ref_known(v_pre_675_, 2);
v___x_680_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_681_ = lean_string_dec_eq(v_str_679_, v___x_680_);
lean_dec_ref(v_str_679_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
lean_dec_ref(v_str_678_);
lean_dec(v_snd_677_);
v___x_682_ = l_Lean_Expr_int_x3f(v_n_672_);
return v___x_682_;
}
else
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_684_ = lean_string_dec_eq(v_str_678_, v___x_683_);
lean_dec_ref(v_str_678_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
lean_dec(v_snd_677_);
v___x_685_ = l_Lean_Expr_int_x3f(v_n_672_);
return v___x_685_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_array_get_size(v_snd_677_);
v___x_687_ = lean_unsigned_to_nat(3u);
v___x_688_ = lean_nat_dec_eq(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
lean_dec(v_snd_677_);
v___x_689_ = l_Lean_Expr_int_x3f(v_n_672_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec_ref(v_n_672_);
v___x_690_ = lean_unsigned_to_nat(2u);
v___x_691_ = lean_array_fget(v_snd_677_, v___x_690_);
lean_dec(v_snd_677_);
v___x_692_ = l_Lean_Expr_nat_x3f(v___x_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_box(0);
return v___x_693_;
}
else
{
lean_object* v_val_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_702_; 
v_val_694_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_702_ == 0)
{
v___x_696_ = v___x_692_;
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_val_694_);
lean_dec(v___x_692_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = lean_nat_to_int(v_val_694_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_698_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_703_; 
lean_dec_ref_known(v_pre_675_, 2);
lean_dec_ref_known(v_fst_674_, 2);
lean_dec_ref(v___x_673_);
v___x_703_ = l_Lean_Expr_int_x3f(v_n_672_);
return v___x_703_;
}
}
else
{
lean_object* v___x_704_; 
lean_dec(v_pre_675_);
lean_dec_ref_known(v_fst_674_, 2);
lean_dec_ref(v___x_673_);
v___x_704_ = l_Lean_Expr_int_x3f(v_n_672_);
return v___x_704_;
}
}
else
{
lean_object* v___x_705_; 
lean_dec(v_fst_674_);
lean_dec_ref(v___x_673_);
v___x_705_ = l_Lean_Expr_int_x3f(v_n_672_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f(lean_object* v_e_721_){
_start:
{
lean_object* v___x_722_; lean_object* v_fst_723_; 
lean_inc_ref(v_e_721_);
v___x_722_ = l_Lean_Expr_getAppFnArgs(v_e_721_);
v_fst_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_fst_723_);
if (lean_obj_tag(v_fst_723_) == 1)
{
lean_object* v_pre_724_; 
v_pre_724_ = lean_ctor_get(v_fst_723_, 0);
lean_inc(v_pre_724_);
if (lean_obj_tag(v_pre_724_) == 1)
{
lean_object* v_pre_725_; 
v_pre_725_ = lean_ctor_get(v_pre_724_, 0);
if (lean_obj_tag(v_pre_725_) == 0)
{
lean_object* v_snd_726_; lean_object* v_str_727_; lean_object* v_str_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_snd_726_ = lean_ctor_get(v___x_722_, 1);
lean_inc(v_snd_726_);
lean_dec_ref(v___x_722_);
v_str_727_ = lean_ctor_get(v_fst_723_, 1);
lean_inc_ref(v_str_727_);
lean_dec_ref_known(v_fst_723_, 2);
v_str_728_ = lean_ctor_get(v_pre_724_, 1);
lean_inc_ref(v_str_728_);
lean_dec_ref_known(v_pre_724_, 2);
v___x_729_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_730_ = lean_string_dec_eq(v_str_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0));
v___x_732_ = lean_string_dec_eq(v_str_728_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1));
v___x_734_ = lean_string_dec_eq(v_str_728_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2));
v___x_736_ = lean_string_dec_eq(v_str_728_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3));
v___x_738_ = lean_string_dec_eq(v_str_728_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4));
v___x_740_ = lean_string_dec_eq(v_str_728_, v___x_739_);
lean_dec_ref(v_str_728_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_dec_ref(v_str_727_);
lean_dec(v_snd_726_);
v___x_741_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_741_;
}
else
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_743_ = lean_string_dec_eq(v_str_727_, v___x_742_);
lean_dec_ref(v_str_727_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_dec(v_snd_726_);
v___x_744_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_744_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_745_ = lean_array_get_size(v_snd_726_);
v___x_746_ = lean_unsigned_to_nat(6u);
v___x_747_ = lean_nat_dec_eq(v___x_745_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
lean_dec(v_snd_726_);
v___x_748_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_748_;
}
else
{
lean_object* v___f_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref(v_e_721_);
v___f_749_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6));
v___x_750_ = lean_unsigned_to_nat(4u);
v___x_751_ = lean_array_fget(v_snd_726_, v___x_750_);
v___x_752_ = lean_unsigned_to_nat(5u);
v___x_753_ = lean_array_fget(v_snd_726_, v___x_752_);
lean_dec(v_snd_726_);
v___x_754_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_749_, v___x_751_, v___x_753_);
return v___x_754_;
}
}
}
}
else
{
lean_object* v___x_755_; uint8_t v___x_756_; 
lean_dec_ref(v_str_728_);
v___x_755_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7));
v___x_756_ = lean_string_dec_eq(v_str_727_, v___x_755_);
lean_dec_ref(v_str_727_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
lean_dec(v_snd_726_);
v___x_757_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_757_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_758_ = lean_array_get_size(v_snd_726_);
v___x_759_ = lean_unsigned_to_nat(6u);
v___x_760_ = lean_nat_dec_eq(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
lean_dec(v_snd_726_);
v___x_761_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_761_;
}
else
{
lean_object* v___f_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec_ref(v_e_721_);
v___f_762_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8));
v___x_763_ = lean_unsigned_to_nat(4u);
v___x_764_ = lean_array_fget(v_snd_726_, v___x_763_);
v___x_765_ = lean_unsigned_to_nat(5u);
v___x_766_ = lean_array_fget(v_snd_726_, v___x_765_);
lean_dec(v_snd_726_);
v___x_767_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_762_, v___x_764_, v___x_766_);
return v___x_767_;
}
}
}
}
else
{
lean_object* v___x_768_; uint8_t v___x_769_; 
lean_dec_ref(v_str_728_);
v___x_768_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9));
v___x_769_ = lean_string_dec_eq(v_str_727_, v___x_768_);
lean_dec_ref(v_str_727_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_dec(v_snd_726_);
v___x_770_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_770_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_array_get_size(v_snd_726_);
v___x_772_ = lean_unsigned_to_nat(6u);
v___x_773_ = lean_nat_dec_eq(v___x_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; 
lean_dec(v_snd_726_);
v___x_774_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_774_;
}
else
{
lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec_ref(v_e_721_);
v___f_775_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10));
v___x_776_ = lean_unsigned_to_nat(4u);
v___x_777_ = lean_array_fget(v_snd_726_, v___x_776_);
v___x_778_ = lean_unsigned_to_nat(5u);
v___x_779_ = lean_array_fget(v_snd_726_, v___x_778_);
lean_dec(v_snd_726_);
v___x_780_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_775_, v___x_777_, v___x_779_);
return v___x_780_;
}
}
}
}
else
{
lean_object* v___x_781_; uint8_t v___x_782_; 
lean_dec_ref(v_str_728_);
v___x_781_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11));
v___x_782_ = lean_string_dec_eq(v_str_727_, v___x_781_);
lean_dec_ref(v_str_727_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; 
lean_dec(v_snd_726_);
v___x_783_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_783_;
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_784_ = lean_array_get_size(v_snd_726_);
v___x_785_ = lean_unsigned_to_nat(6u);
v___x_786_ = lean_nat_dec_eq(v___x_784_, v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
lean_dec(v_snd_726_);
v___x_787_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_787_;
}
else
{
lean_object* v___f_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v_e_721_);
v___f_788_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12));
v___x_789_ = lean_unsigned_to_nat(4u);
v___x_790_ = lean_array_fget(v_snd_726_, v___x_789_);
v___x_791_ = lean_unsigned_to_nat(5u);
v___x_792_ = lean_array_fget(v_snd_726_, v___x_791_);
lean_dec(v_snd_726_);
v___x_793_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_788_, v___x_790_, v___x_792_);
return v___x_793_;
}
}
}
}
else
{
lean_object* v___x_794_; uint8_t v___x_795_; 
lean_dec_ref(v_str_728_);
v___x_794_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13));
v___x_795_ = lean_string_dec_eq(v_str_727_, v___x_794_);
lean_dec_ref(v_str_727_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
lean_dec(v_snd_726_);
v___x_796_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_796_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_797_ = lean_array_get_size(v_snd_726_);
v___x_798_ = lean_unsigned_to_nat(6u);
v___x_799_ = lean_nat_dec_eq(v___x_797_, v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; 
lean_dec(v_snd_726_);
v___x_800_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_800_;
}
else
{
lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref(v_e_721_);
v___f_801_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14));
v___x_802_ = lean_unsigned_to_nat(4u);
v___x_803_ = lean_array_fget(v_snd_726_, v___x_802_);
v___x_804_ = lean_unsigned_to_nat(5u);
v___x_805_ = lean_array_fget(v_snd_726_, v___x_804_);
lean_dec(v_snd_726_);
v___x_806_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_801_, v___x_803_, v___x_805_);
return v___x_806_;
}
}
}
}
else
{
lean_object* v___x_807_; uint8_t v___x_808_; 
lean_dec_ref(v_str_728_);
v___x_807_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_808_ = lean_string_dec_eq(v_str_727_, v___x_807_);
lean_dec_ref(v_str_727_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec(v_snd_726_);
v___x_809_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_809_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_810_ = lean_array_get_size(v_snd_726_);
v___x_811_ = lean_unsigned_to_nat(3u);
v___x_812_ = lean_nat_dec_eq(v___x_810_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
lean_dec(v_snd_726_);
v___x_813_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_813_;
}
else
{
lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec_ref(v_e_721_);
v___x_814_ = lean_unsigned_to_nat(2u);
v___x_815_ = lean_array_fget(v_snd_726_, v___x_814_);
lean_dec(v_snd_726_);
v_e_721_ = v___x_815_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_817_; 
lean_dec_ref_known(v_pre_724_, 2);
lean_dec_ref_known(v_fst_723_, 2);
lean_dec_ref(v___x_722_);
v___x_817_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_817_;
}
}
else
{
lean_object* v___x_818_; 
lean_dec_ref_known(v_fst_723_, 2);
lean_dec(v_pre_724_);
lean_dec_ref(v___x_722_);
v___x_818_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_818_;
}
}
else
{
lean_object* v___x_819_; 
lean_dec(v_fst_723_);
lean_dec_ref(v___x_722_);
v___x_819_ = l_Lean_Expr_nat_x3f(v_e_721_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(lean_object* v_f_820_, lean_object* v_x_821_, lean_object* v_y_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_x_821_);
if (lean_obj_tag(v___x_823_) == 1)
{
lean_object* v_val_824_; lean_object* v___x_825_; 
v_val_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_val_824_);
lean_dec_ref_known(v___x_823_, 1);
v___x_825_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_y_822_);
if (lean_obj_tag(v___x_825_) == 1)
{
lean_object* v_val_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_834_; 
v_val_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_834_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_val_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_830_ = lean_apply_2(v_f_820_, v_val_824_, v_val_826_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_830_);
v___x_832_ = v___x_828_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
else
{
lean_object* v___x_835_; 
lean_dec(v___x_825_);
lean_dec(v_val_824_);
lean_dec_ref(v_f_820_);
v___x_835_ = lean_box(0);
return v___x_835_;
}
}
else
{
lean_object* v___x_836_; 
lean_dec(v___x_823_);
lean_dec_ref(v_y_822_);
lean_dec_ref(v_f_820_);
v___x_836_ = lean_box(0);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f(lean_object* v_e_841_){
_start:
{
lean_object* v___x_842_; lean_object* v_fst_843_; 
lean_inc_ref(v_e_841_);
v___x_842_ = l_Lean_Expr_getAppFnArgs(v_e_841_);
v_fst_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_fst_843_);
if (lean_obj_tag(v_fst_843_) == 1)
{
lean_object* v_pre_844_; 
v_pre_844_ = lean_ctor_get(v_fst_843_, 0);
lean_inc(v_pre_844_);
if (lean_obj_tag(v_pre_844_) == 1)
{
lean_object* v_pre_845_; 
v_pre_845_ = lean_ctor_get(v_pre_844_, 0);
if (lean_obj_tag(v_pre_845_) == 0)
{
lean_object* v_snd_846_; lean_object* v_str_847_; lean_object* v_str_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_snd_846_ = lean_ctor_get(v___x_842_, 1);
lean_inc(v_snd_846_);
lean_dec_ref(v___x_842_);
v_str_847_ = lean_ctor_get(v_fst_843_, 1);
lean_inc_ref(v_str_847_);
lean_dec_ref_known(v_fst_843_, 2);
v_str_848_ = lean_ctor_get(v_pre_844_, 1);
lean_inc_ref(v_str_848_);
lean_dec_ref_known(v_pre_844_, 2);
v___x_849_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_850_ = lean_string_dec_eq(v_str_848_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0));
v___x_852_ = lean_string_dec_eq(v_str_848_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1));
v___x_854_ = lean_string_dec_eq(v_str_848_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_855_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2));
v___x_856_ = lean_string_dec_eq(v_str_848_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3));
v___x_858_ = lean_string_dec_eq(v_str_848_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4));
v___x_860_ = lean_string_dec_eq(v_str_848_, v___x_859_);
lean_dec_ref(v_str_848_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
lean_dec_ref(v_str_847_);
lean_dec(v_snd_846_);
v___x_861_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_862_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_863_ = lean_string_dec_eq(v_str_847_, v___x_862_);
lean_dec_ref(v_str_847_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; 
lean_dec(v_snd_846_);
v___x_864_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_864_;
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_865_ = lean_array_get_size(v_snd_846_);
v___x_866_ = lean_unsigned_to_nat(6u);
v___x_867_ = lean_nat_dec_eq(v___x_865_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
lean_dec(v_snd_846_);
v___x_868_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec_ref(v_e_841_);
v___x_869_ = lean_unsigned_to_nat(4u);
v___x_870_ = lean_array_fget_borrowed(v_snd_846_, v___x_869_);
lean_inc(v___x_870_);
v___x_871_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v___x_870_);
if (lean_obj_tag(v___x_871_) == 1)
{
lean_object* v_val_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_val_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_val_872_);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = lean_unsigned_to_nat(5u);
v___x_874_ = lean_array_fget(v_snd_846_, v___x_873_);
lean_dec(v_snd_846_);
v___x_875_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_874_);
if (lean_obj_tag(v___x_875_) == 1)
{
lean_object* v_val_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_884_; 
v_val_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_884_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_val_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = l_Int_pow(v_val_872_, v_val_876_);
lean_dec(v_val_876_);
lean_dec(v_val_872_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_880_);
v___x_882_ = v___x_878_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
else
{
lean_object* v___x_885_; 
lean_dec(v___x_875_);
lean_dec(v_val_872_);
v___x_885_ = lean_box(0);
return v___x_885_;
}
}
else
{
lean_object* v___x_886_; 
lean_dec(v___x_871_);
lean_dec(v_snd_846_);
v___x_886_ = lean_box(0);
return v___x_886_;
}
}
}
}
}
else
{
lean_object* v___x_887_; uint8_t v___x_888_; 
lean_dec_ref(v_str_848_);
v___x_887_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7));
v___x_888_ = lean_string_dec_eq(v_str_847_, v___x_887_);
lean_dec_ref(v_str_847_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
lean_dec(v_snd_846_);
v___x_889_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_889_;
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_890_ = lean_array_get_size(v_snd_846_);
v___x_891_ = lean_unsigned_to_nat(6u);
v___x_892_ = lean_nat_dec_eq(v___x_890_, v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
lean_dec(v_snd_846_);
v___x_893_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_893_;
}
else
{
lean_object* v___f_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec_ref(v_e_841_);
v___f_894_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0));
v___x_895_ = lean_unsigned_to_nat(4u);
v___x_896_ = lean_array_fget(v_snd_846_, v___x_895_);
v___x_897_ = lean_unsigned_to_nat(5u);
v___x_898_ = lean_array_fget(v_snd_846_, v___x_897_);
lean_dec(v_snd_846_);
v___x_899_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_894_, v___x_896_, v___x_898_);
return v___x_899_;
}
}
}
}
else
{
lean_object* v___x_900_; uint8_t v___x_901_; 
lean_dec_ref(v_str_848_);
v___x_900_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9));
v___x_901_ = lean_string_dec_eq(v_str_847_, v___x_900_);
lean_dec_ref(v_str_847_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_dec(v_snd_846_);
v___x_902_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_902_;
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_903_ = lean_array_get_size(v_snd_846_);
v___x_904_ = lean_unsigned_to_nat(6u);
v___x_905_ = lean_nat_dec_eq(v___x_903_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec(v_snd_846_);
v___x_906_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_906_;
}
else
{
lean_object* v___f_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec_ref(v_e_841_);
v___f_907_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1));
v___x_908_ = lean_unsigned_to_nat(4u);
v___x_909_ = lean_array_fget(v_snd_846_, v___x_908_);
v___x_910_ = lean_unsigned_to_nat(5u);
v___x_911_ = lean_array_fget(v_snd_846_, v___x_910_);
lean_dec(v_snd_846_);
v___x_912_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_907_, v___x_909_, v___x_911_);
return v___x_912_;
}
}
}
}
else
{
lean_object* v___x_913_; uint8_t v___x_914_; 
lean_dec_ref(v_str_848_);
v___x_913_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11));
v___x_914_ = lean_string_dec_eq(v_str_847_, v___x_913_);
lean_dec_ref(v_str_847_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
lean_dec(v_snd_846_);
v___x_915_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_915_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_916_ = lean_array_get_size(v_snd_846_);
v___x_917_ = lean_unsigned_to_nat(6u);
v___x_918_ = lean_nat_dec_eq(v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
lean_dec(v_snd_846_);
v___x_919_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_919_;
}
else
{
lean_object* v___f_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec_ref(v_e_841_);
v___f_920_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2));
v___x_921_ = lean_unsigned_to_nat(4u);
v___x_922_ = lean_array_fget(v_snd_846_, v___x_921_);
v___x_923_ = lean_unsigned_to_nat(5u);
v___x_924_ = lean_array_fget(v_snd_846_, v___x_923_);
lean_dec(v_snd_846_);
v___x_925_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_920_, v___x_922_, v___x_924_);
return v___x_925_;
}
}
}
}
else
{
lean_object* v___x_926_; uint8_t v___x_927_; 
lean_dec_ref(v_str_848_);
v___x_926_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13));
v___x_927_ = lean_string_dec_eq(v_str_847_, v___x_926_);
lean_dec_ref(v_str_847_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
lean_dec(v_snd_846_);
v___x_928_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_928_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_929_ = lean_array_get_size(v_snd_846_);
v___x_930_ = lean_unsigned_to_nat(6u);
v___x_931_ = lean_nat_dec_eq(v___x_929_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec(v_snd_846_);
v___x_932_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_932_;
}
else
{
lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec_ref(v_e_841_);
v___f_933_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3));
v___x_934_ = lean_unsigned_to_nat(4u);
v___x_935_ = lean_array_fget(v_snd_846_, v___x_934_);
v___x_936_ = lean_unsigned_to_nat(5u);
v___x_937_ = lean_array_fget(v_snd_846_, v___x_936_);
lean_dec(v_snd_846_);
v___x_938_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_933_, v___x_935_, v___x_937_);
return v___x_938_;
}
}
}
}
else
{
lean_object* v___x_939_; uint8_t v___x_940_; 
lean_dec_ref(v_str_848_);
v___x_939_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_940_ = lean_string_dec_eq(v_str_847_, v___x_939_);
lean_dec_ref(v_str_847_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
lean_dec(v_snd_846_);
v___x_941_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_941_;
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_942_ = lean_array_get_size(v_snd_846_);
v___x_943_ = lean_unsigned_to_nat(3u);
v___x_944_ = lean_nat_dec_eq(v___x_942_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
lean_dec(v_snd_846_);
v___x_945_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec_ref(v_e_841_);
v___x_946_ = lean_unsigned_to_nat(2u);
v___x_947_ = lean_array_fget(v_snd_846_, v___x_946_);
lean_dec(v_snd_846_);
v___x_948_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_947_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v___x_949_; 
v___x_949_ = lean_box(0);
return v___x_949_;
}
else
{
lean_object* v_val_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_958_; 
v_val_950_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_958_ == 0)
{
v___x_952_ = v___x_948_;
v_isShared_953_ = v_isSharedCheck_958_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_val_950_);
lean_dec(v___x_948_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_958_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = lean_nat_to_int(v_val_950_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_954_);
v___x_956_ = v___x_952_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_959_; 
lean_dec_ref_known(v_pre_844_, 2);
lean_dec_ref_known(v_fst_843_, 2);
lean_dec_ref(v___x_842_);
v___x_959_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_959_;
}
}
else
{
lean_object* v___x_960_; 
lean_dec(v_pre_844_);
lean_dec_ref_known(v_fst_843_, 2);
lean_dec_ref(v___x_842_);
v___x_960_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_960_;
}
}
else
{
lean_object* v___x_961_; 
lean_dec(v_fst_843_);
lean_dec_ref(v___x_842_);
v___x_961_ = l_Lean_Expr_int_x3f(v_e_841_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object* v_f_962_, lean_object* v_x_963_, lean_object* v_y_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_x_963_);
if (lean_obj_tag(v___x_965_) == 1)
{
lean_object* v_val_966_; lean_object* v___x_967_; 
v_val_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_val_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_y_964_);
if (lean_obj_tag(v___x_967_) == 1)
{
lean_object* v_val_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_976_; 
v_val_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_976_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_val_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = lean_apply_2(v_f_962_, v_val_966_, v_val_968_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
else
{
lean_object* v___x_977_; 
lean_dec(v___x_967_);
lean_dec(v_val_966_);
lean_dec_ref(v_f_962_);
v___x_977_ = lean_box(0);
return v___x_977_;
}
}
else
{
lean_object* v___x_978_; 
lean_dec(v___x_965_);
lean_dec_ref(v_y_964_);
lean_dec_ref(v_f_962_);
v___x_978_ = lean_box(0);
return v___x_978_;
}
}
}
lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object* v_a_979_, lean_object* v_b_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_986_; 
lean_inc_ref(v_a_979_);
v___x_986_ = l_Lean_Meta_mkEqRefl(v_a_979_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_988_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v___x_988_ = l_Lean_Meta_mkEq(v_a_979_, v_b_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_997_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_997_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = l_Lean_Meta_mkExpectedPropHint(v_a_987_, v_a_989_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_993_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
else
{
lean_dec(v_a_987_);
return v___x_988_;
}
}
else
{
lean_dec_ref(v_b_980_);
lean_dec_ref(v_a_979_);
return v___x_986_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_979_ = stack[0].m_obj;
lean_object* v_b_980_ = stack[1].m_obj;
lean_object* v_a_981_ = stack[2].m_obj;
lean_object* v_a_982_ = stack[3].m_obj;
lean_object* v_a_983_ = stack[4].m_obj;
lean_object* v_a_984_ = stack[5].m_obj;
lean_object* v_res_998_;
v_res_998_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v_a_979_, v_b_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
stack->m_obj
 = v_res_998_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType___boxed(lean_object* v_a_999_, lean_object* v_b_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v_a_999_, v_b_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
return v_res_1006_;
}
}
uint8_t l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(lean_object* v_a_1007_, lean_object* v_x_1008_){
_start:
{
if (lean_obj_tag(v_x_1008_) == 0)
{
uint8_t v___x_1009_; 
v___x_1009_ = 0;
return v___x_1009_;
}
else
{
lean_object* v_head_1010_; lean_object* v_tail_1011_; uint8_t v___x_1012_; 
v_head_1010_ = lean_ctor_get(v_x_1008_, 0);
v_tail_1011_ = lean_ctor_get(v_x_1008_, 1);
v___x_1012_ = lean_expr_eqv(v_a_1007_, v_head_1010_);
if (v___x_1012_ == 0)
{
v_x_1008_ = v_tail_1011_;
goto _start;
}
else
{
return v___x_1012_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1007_ = stack[0].m_obj;
lean_object* v_x_1008_ = stack[1].m_obj;
uint8_t v_res_1014_;
v_res_1014_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v_a_1007_, v_x_1008_);
stack->m_num = v_res_1014_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0___boxed(lean_object* v_a_1015_, lean_object* v_x_1016_){
_start:
{
uint8_t v_res_1017_; lean_object* v_r_1018_; 
v_res_1017_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v_a_1015_, v_x_1016_);
lean_dec(v_x_1016_);
lean_dec_ref(v_a_1015_);
v_r_1018_ = lean_box(v_res_1017_);
return v_r_1018_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_box(0);
v___x_1028_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5));
v___x_1029_ = l_Lean_Expr_const___override(v___x_1028_, v___x_1027_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_box(0);
v___x_1035_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8));
v___x_1036_ = l_Lean_Expr_const___override(v___x_1035_, v___x_1034_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12));
v___x_1044_ = l_Lean_Expr_const___override(v___x_1043_, v___x_1042_);
return v___x_1044_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15));
v___x_1051_ = l_Lean_Expr_const___override(v___x_1050_, v___x_1049_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = l_Lean_Level_ofNat(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1072_ = l_Lean_mkNatLit(v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = lean_nat_to_int(v___x_1095_);
return v___x_1096_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39(void){
_start:
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
v___x_1098_ = lean_int_dec_le(v___x_1097_, v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
v___x_1109_ = lean_int_neg(v___x_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45);
v___x_1111_ = l_Int_toNat(v___x_1110_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46);
v___x_1113_ = l_Lean_instToExprInt_mkNat(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
v___x_1115_ = l_Int_toNat(v___x_1114_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48);
v___x_1117_ = l_Lean_instToExprInt_mkNat(v___x_1116_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_box(0);
v___x_1119_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23);
v___x_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___x_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1122_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22));
v___x_1123_ = l_Lean_Expr_const___override(v___x_1122_, v___x_1121_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = lean_box(0);
v___x_1129_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53));
v___x_1130_ = l_Lean_Expr_const___override(v___x_1129_, v___x_1128_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = lean_box(0);
v___x_1138_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56));
v___x_1139_ = l_Lean_Expr_const___override(v___x_1138_, v___x_1137_);
return v___x_1139_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_box(0);
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33));
v___x_1142_ = l_Lean_Expr_const___override(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = lean_box(0);
v___x_1144_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35));
v___x_1145_ = l_Lean_Expr_const___override(v___x_1144_, v___x_1143_);
return v___x_1145_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = lean_box(0);
v___x_1147_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37));
v___x_1148_ = l_Lean_Expr_const___override(v___x_1147_, v___x_1146_);
return v___x_1148_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1150_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42));
v___x_1151_ = l_Lean_Expr_const___override(v___x_1150_, v___x_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_box(0);
v___x_1153_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44));
v___x_1154_ = l_Lean_Expr_const___override(v___x_1153_, v___x_1152_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1155_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47);
v___x_1156_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62);
v___x_1157_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1158_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61);
v___x_1159_ = l_Lean_mkApp3(v___x_1158_, v___x_1157_, v___x_1156_, v___x_1155_);
return v___x_1159_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = l_Lean_Level_ofNat(v___x_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66);
v___x_1167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v___x_1165_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67);
v___x_1169_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65));
v___x_1170_ = l_Lean_Expr_const___override(v___x_1169_, v___x_1168_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1175_ = lean_box(0);
v___x_1176_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70));
v___x_1177_ = l_Lean_Expr_const___override(v___x_1176_, v___x_1175_);
return v___x_1177_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_box(0);
v___x_1183_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73));
v___x_1184_ = l_Lean_Expr_const___override(v___x_1183_, v___x_1182_);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1224_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93));
v___x_1225_ = l_Lean_Expr_const___override(v___x_1224_, v___x_1223_);
return v___x_1225_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(lean_object* v_e_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v___x_1251_; lean_object* v_fst_1252_; 
v___x_1251_ = l_Lean_Expr_getAppFnArgs(v_e_1226_);
v_fst_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_fst_1252_);
if (lean_obj_tag(v_fst_1252_) == 1)
{
lean_object* v_pre_1253_; 
v_pre_1253_ = lean_ctor_get(v_fst_1252_, 0);
switch(lean_obj_tag(v_pre_1253_))
{
case 1:
{
lean_object* v_pre_1254_; 
lean_inc_ref(v_pre_1253_);
v_pre_1254_ = lean_ctor_get(v_pre_1253_, 0);
if (lean_obj_tag(v_pre_1254_) == 0)
{
lean_object* v_snd_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1752_; 
v_snd_1255_ = lean_ctor_get(v___x_1251_, 1);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; 
v_unused_1753_ = lean_ctor_get(v___x_1251_, 0);
lean_dec(v_unused_1753_);
v___x_1257_ = v___x_1251_;
v_isShared_1258_ = v_isSharedCheck_1752_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_snd_1255_);
lean_dec(v___x_1251_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1752_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_str_1259_; lean_object* v_str_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_str_1259_ = lean_ctor_get(v_fst_1252_, 1);
lean_inc_ref(v_str_1259_);
lean_dec_ref_known(v_fst_1252_, 2);
v_str_1260_ = lean_ctor_get(v_pre_1253_, 1);
lean_inc_ref(v_str_1260_);
lean_dec_ref_known(v_pre_1253_, 2);
v___x_1261_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_1262_ = lean_string_dec_eq(v_str_1260_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3));
v___x_1264_ = lean_string_dec_eq(v_str_1260_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1265_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0));
v___x_1266_ = lean_string_dec_eq(v_str_1260_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1267_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1));
v___x_1268_ = lean_string_dec_eq(v_str_1260_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2));
v___x_1270_ = lean_string_dec_eq(v_str_1260_, v___x_1269_);
lean_dec_ref(v_str_1260_);
if (v___x_1270_ == 0)
{
lean_dec_ref(v_str_1259_);
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3));
v___x_1272_ = lean_string_dec_eq(v_str_1259_, v___x_1271_);
lean_dec_ref(v_str_1259_);
if (v___x_1272_ == 0)
{
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1273_ = lean_array_get_size(v_snd_1255_);
v___x_1274_ = lean_unsigned_to_nat(4u);
v___x_1275_ = lean_nat_dec_eq(v___x_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1276_ = lean_unsigned_to_nat(2u);
v___x_1277_ = lean_array_fget(v_snd_1255_, v___x_1276_);
v___x_1278_ = lean_unsigned_to_nat(3u);
v___x_1279_ = lean_array_fget(v_snd_1255_, v___x_1278_);
lean_dec(v_snd_1255_);
v___x_1280_ = lean_box(0);
v___x_1281_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6);
lean_inc(v___x_1279_);
lean_inc(v___x_1277_);
v___x_1282_ = l_Lean_mkAppB(v___x_1281_, v___x_1277_, v___x_1279_);
v___x_1283_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9);
v___x_1284_ = l_Lean_mkAppB(v___x_1283_, v___x_1277_, v___x_1279_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 1);
lean_ctor_set(v___x_1257_, 1, v___x_1280_);
lean_ctor_set(v___x_1257_, 0, v___x_1284_);
v___x_1286_ = v___x_1257_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v___x_1280_);
v___x_1286_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1282_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
return v___x_1288_;
}
}
}
}
}
else
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
lean_dec_ref(v_str_1260_);
v___x_1290_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10));
v___x_1291_ = lean_string_dec_eq(v_str_1259_, v___x_1290_);
lean_dec_ref(v_str_1259_);
if (v___x_1291_ == 0)
{
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1292_ = lean_array_get_size(v_snd_1255_);
v___x_1293_ = lean_unsigned_to_nat(4u);
v___x_1294_ = lean_nat_dec_eq(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1295_ = lean_unsigned_to_nat(2u);
v___x_1296_ = lean_array_fget(v_snd_1255_, v___x_1295_);
v___x_1297_ = lean_unsigned_to_nat(3u);
v___x_1298_ = lean_array_fget(v_snd_1255_, v___x_1297_);
lean_dec(v_snd_1255_);
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13);
lean_inc(v___x_1298_);
lean_inc(v___x_1296_);
v___x_1301_ = l_Lean_mkAppB(v___x_1300_, v___x_1296_, v___x_1298_);
v___x_1302_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16);
v___x_1303_ = l_Lean_mkAppB(v___x_1302_, v___x_1296_, v___x_1298_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 1);
lean_ctor_set(v___x_1257_, 1, v___x_1299_);
lean_ctor_set(v___x_1257_, 0, v___x_1303_);
v___x_1305_ = v___x_1257_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v___x_1299_);
v___x_1305_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1301_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
return v___x_1307_;
}
}
}
}
}
else
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
lean_dec_ref(v_str_1260_);
v___x_1309_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17));
v___x_1310_ = lean_string_dec_eq(v_str_1259_, v___x_1309_);
lean_dec_ref(v_str_1259_);
if (v___x_1310_ == 0)
{
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1311_ = lean_array_get_size(v_snd_1255_);
v___x_1312_ = lean_unsigned_to_nat(6u);
v___x_1313_ = lean_nat_dec_eq(v___x_1311_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v_fst_1317_; 
v___x_1314_ = lean_unsigned_to_nat(5u);
v___x_1315_ = lean_array_fget(v_snd_1255_, v___x_1314_);
lean_inc(v___x_1315_);
v___x_1316_ = l_Lean_Expr_getAppFnArgs(v___x_1315_);
v_fst_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_fst_1317_);
if (lean_obj_tag(v_fst_1317_) == 1)
{
lean_object* v_pre_1318_; 
v_pre_1318_ = lean_ctor_get(v_fst_1317_, 0);
lean_inc(v_pre_1318_);
if (lean_obj_tag(v_pre_1318_) == 1)
{
lean_object* v_pre_1319_; 
v_pre_1319_ = lean_ctor_get(v_pre_1318_, 0);
if (lean_obj_tag(v_pre_1319_) == 0)
{
lean_object* v_snd_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1519_; 
v_snd_1320_ = lean_ctor_get(v___x_1316_, 1);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v___x_1316_, 0);
lean_dec(v_unused_1520_);
v___x_1322_ = v___x_1316_;
v_isShared_1323_ = v_isSharedCheck_1519_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_snd_1320_);
lean_dec(v___x_1316_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1519_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v_str_1324_; lean_object* v_str_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_str_1324_ = lean_ctor_get(v_fst_1317_, 1);
lean_inc_ref(v_str_1324_);
lean_dec_ref_known(v_fst_1317_, 2);
v_str_1325_ = lean_ctor_get(v_pre_1318_, 1);
lean_inc_ref(v_str_1325_);
lean_dec_ref_known(v_pre_1318_, 2);
v___x_1326_ = lean_unsigned_to_nat(4u);
v___x_1327_ = lean_array_fget(v_snd_1255_, v___x_1326_);
lean_dec(v_snd_1255_);
v___x_1365_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4));
v___x_1366_ = lean_string_dec_eq(v_str_1325_, v___x_1365_);
if (v___x_1366_ == 0)
{
uint8_t v___x_1367_; 
v___x_1367_ = lean_string_dec_eq(v_str_1325_, v___x_1261_);
lean_dec_ref(v_str_1325_);
if (v___x_1367_ == 0)
{
lean_dec(v___x_1327_);
lean_dec_ref(v_str_1324_);
lean_del_object(v___x_1322_);
lean_dec(v_snd_1320_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1242_;
}
else
{
lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1369_ = lean_string_dec_eq(v_str_1324_, v___x_1368_);
lean_dec_ref(v_str_1324_);
if (v___x_1369_ == 0)
{
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v_snd_1320_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1242_;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1370_ = lean_array_get_size(v_snd_1320_);
v___x_1371_ = lean_unsigned_to_nat(3u);
v___x_1372_ = lean_nat_dec_eq(v___x_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v_snd_1320_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1242_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = lean_array_fget_borrowed(v_snd_1320_, v___x_1373_);
if (lean_obj_tag(v___x_1374_) == 4)
{
lean_object* v_declName_1375_; 
v_declName_1375_ = lean_ctor_get(v___x_1374_, 0);
if (lean_obj_tag(v_declName_1375_) == 1)
{
lean_object* v_pre_1376_; 
v_pre_1376_ = lean_ctor_get(v_declName_1375_, 0);
if (lean_obj_tag(v_pre_1376_) == 0)
{
lean_object* v_us_1377_; lean_object* v_str_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v_us_1377_ = lean_ctor_get(v___x_1374_, 1);
lean_inc(v_us_1377_);
v_str_1378_ = lean_ctor_get(v_declName_1375_, 1);
v___x_1379_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1380_ = lean_string_dec_eq(v_str_1378_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_dec(v_us_1377_);
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v_snd_1320_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1242_;
}
else
{
if (lean_obj_tag(v_us_1377_) == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v_fst_1384_; 
v___x_1381_ = lean_unsigned_to_nat(2u);
v___x_1382_ = lean_array_fget(v_snd_1320_, v___x_1381_);
lean_dec(v_snd_1320_);
lean_inc(v___x_1382_);
v___x_1383_ = l_Lean_Expr_getAppFnArgs(v___x_1382_);
v_fst_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_fst_1384_);
if (lean_obj_tag(v_fst_1384_) == 1)
{
lean_object* v_pre_1385_; 
v_pre_1385_ = lean_ctor_get(v_fst_1384_, 0);
lean_inc(v_pre_1385_);
if (lean_obj_tag(v_pre_1385_) == 1)
{
lean_object* v_pre_1386_; 
v_pre_1386_ = lean_ctor_get(v_pre_1385_, 0);
if (lean_obj_tag(v_pre_1386_) == 0)
{
lean_object* v_snd_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1466_; 
v_snd_1387_ = lean_ctor_get(v___x_1383_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v___x_1383_, 0);
lean_dec(v_unused_1467_);
v___x_1389_ = v___x_1383_;
v_isShared_1390_ = v_isSharedCheck_1466_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_snd_1387_);
lean_dec(v___x_1383_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1466_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_str_1391_; lean_object* v_str_1392_; uint8_t v___x_1393_; 
v_str_1391_ = lean_ctor_get(v_fst_1384_, 1);
lean_inc_ref(v_str_1391_);
lean_dec_ref_known(v_fst_1384_, 2);
v_str_1392_ = lean_ctor_get(v_pre_1385_, 1);
lean_inc_ref(v_str_1392_);
lean_dec_ref_known(v_pre_1385_, 2);
v___x_1393_ = lean_string_dec_eq(v_str_1392_, v___x_1365_);
lean_dec_ref(v_str_1392_);
if (v___x_1393_ == 0)
{
lean_dec_ref(v_str_1391_);
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec(v___x_1382_);
lean_del_object(v___x_1322_);
lean_del_object(v___x_1257_);
goto v___jp_1328_;
}
else
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_1395_ = lean_string_dec_eq(v_str_1391_, v___x_1394_);
lean_dec_ref(v_str_1391_);
if (v___x_1395_ == 0)
{
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec(v___x_1382_);
lean_del_object(v___x_1322_);
lean_del_object(v___x_1257_);
goto v___jp_1328_;
}
else
{
lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1396_ = lean_array_get_size(v_snd_1387_);
v___x_1397_ = lean_nat_dec_eq(v___x_1396_, v___x_1312_);
if (v___x_1397_ == 0)
{
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec(v___x_1382_);
lean_del_object(v___x_1322_);
lean_del_object(v___x_1257_);
goto v___jp_1328_;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_array_fget(v_snd_1387_, v___x_1326_);
lean_inc(v___x_1398_);
v___x_1399_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1398_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_dec(v___x_1398_);
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec(v___x_1382_);
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1248_;
}
else
{
lean_object* v_val_1400_; uint8_t v___x_1401_; 
v_val_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_val_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___x_1401_ = lean_nat_dec_eq(v_val_1400_, v___x_1373_);
lean_dec(v_val_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1402_ = lean_array_fget(v_snd_1387_, v___x_1314_);
lean_dec(v_snd_1387_);
v___x_1403_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22));
v___x_1404_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23);
if (v_isShared_1390_ == 0)
{
lean_ctor_set_tag(v___x_1389_, 1);
lean_ctor_set(v___x_1389_, 1, v_us_1377_);
lean_ctor_set(v___x_1389_, 0, v___x_1404_);
v___x_1406_ = v___x_1389_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_us_1377_);
v___x_1406_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_b__pos_1413_; lean_object* v___x_1414_; 
lean_inc_ref(v___x_1406_);
v___x_1407_ = l_Lean_Expr_const___override(v___x_1403_, v___x_1406_);
v___x_1408_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24));
v___x_1409_ = l_Lean_Expr_const___override(v___x_1408_, v_us_1377_);
v___x_1410_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26));
v___x_1411_ = l_Lean_Expr_const___override(v___x_1410_, v_us_1377_);
v___x_1412_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27);
lean_inc(v___x_1398_);
v_b__pos_1413_ = l_Lean_mkApp4(v___x_1407_, v___x_1409_, v___x_1411_, v___x_1412_, v___x_1398_);
v___x_1414_ = l_Lean_Meta_mkDecideProof(v_b__pos_1413_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1456_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1456_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1456_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___y_1430_; uint8_t v___x_1446_; 
v___x_1419_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29));
v___x_1420_ = l_Lean_Expr_const___override(v___x_1419_, v_us_1377_);
v___x_1421_ = l_Lean_mkApp3(v___x_1420_, v___x_1398_, v___x_1402_, v_a_1415_);
v___x_1422_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31));
v___x_1423_ = l_Lean_Expr_const___override(v___x_1422_, v_us_1377_);
v___x_1424_ = l_Lean_mkAppB(v___x_1423_, v___x_1382_, v___x_1421_);
v___x_1425_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33));
v___x_1426_ = l_Lean_Expr_const___override(v___x_1425_, v_us_1377_);
v___x_1427_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35));
v___x_1428_ = l_Lean_Expr_const___override(v___x_1427_, v_us_1377_);
v___x_1446_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1447_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42));
v___x_1448_ = l_Lean_Expr_const___override(v___x_1447_, v___x_1406_);
v___x_1449_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1));
v___x_1450_ = l_Lean_Expr_const___override(v___x_1449_, v_us_1377_);
v___x_1451_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44));
v___x_1452_ = l_Lean_Expr_const___override(v___x_1451_, v_us_1377_);
v___x_1453_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47);
v___x_1454_ = l_Lean_mkApp3(v___x_1448_, v___x_1450_, v___x_1452_, v___x_1453_);
v___y_1430_ = v___x_1454_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1455_; 
lean_dec_ref(v___x_1406_);
v___x_1455_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1430_ = v___x_1455_;
goto v___jp_1429_;
}
v___jp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
lean_inc_ref(v___x_1424_);
lean_inc_n(v___x_1315_, 2);
v___x_1431_ = l_Lean_mkApp3(v___x_1428_, v___x_1315_, v___y_1430_, v___x_1424_);
lean_inc(v___x_1327_);
v___x_1432_ = l_Lean_mkApp3(v___x_1426_, v___x_1327_, v___x_1315_, v___x_1431_);
v___x_1433_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37));
v___x_1434_ = l_Lean_Expr_const___override(v___x_1433_, v_us_1377_);
v___x_1435_ = l_Lean_mkApp3(v___x_1434_, v___x_1327_, v___x_1315_, v___x_1424_);
v___x_1436_ = lean_box(0);
if (v_isShared_1323_ == 0)
{
lean_ctor_set_tag(v___x_1322_, 1);
lean_ctor_set(v___x_1322_, 1, v___x_1436_);
lean_ctor_set(v___x_1322_, 0, v___x_1435_);
v___x_1438_ = v___x_1322_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1440_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 1);
lean_ctor_set(v___x_1257_, 1, v___x_1438_);
lean_ctor_set(v___x_1257_, 0, v___x_1432_);
v___x_1440_ = v___x_1257_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1440_);
v___x_1442_ = v___x_1417_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v___x_1406_);
lean_dec(v___x_1402_);
lean_dec(v___x_1398_);
lean_dec(v___x_1382_);
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
v_a_1457_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1414_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1414_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
else
{
lean_dec(v___x_1398_);
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec(v___x_1382_);
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1248_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1385_, 2);
lean_dec_ref_known(v_fst_1384_, 2);
lean_dec_ref(v___x_1383_);
lean_dec(v___x_1382_);
lean_del_object(v___x_1322_);
lean_del_object(v___x_1257_);
goto v___jp_1328_;
}
}
else
{
lean_dec(v_pre_1385_);
lean_dec_ref_known(v_fst_1384_, 2);
lean_dec_ref(v___x_1383_);
lean_dec(v___x_1382_);
lean_del_object(v___x_1322_);
lean_del_object(v___x_1257_);
goto v___jp_1328_;
}
}
else
{
lean_dec(v_fst_1384_);
lean_dec_ref(v___x_1383_);
lean_dec(v___x_1382_);
lean_del_object(v___x_1322_);
lean_del_object(v___x_1257_);
goto v___jp_1328_;
}
}
else
{
lean_dec(v_us_1377_);
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v_snd_1320_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1242_;
}
}
}
else
{
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v_snd_1320_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1242_;
}
}
else
{
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v_snd_1320_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1242_;
}
}
else
{
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v_snd_1320_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1242_;
}
}
}
}
}
else
{
lean_object* v___x_1468_; uint8_t v___x_1469_; 
lean_dec_ref(v_str_1325_);
v___x_1468_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_1469_ = lean_string_dec_eq(v_str_1324_, v___x_1468_);
lean_dec_ref(v_str_1324_);
if (v___x_1469_ == 0)
{
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v_snd_1320_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1242_;
}
else
{
lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = lean_array_get_size(v_snd_1320_);
v___x_1471_ = lean_nat_dec_eq(v___x_1470_, v___x_1312_);
if (v___x_1471_ == 0)
{
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v_snd_1320_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1242_;
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_array_fget(v_snd_1320_, v___x_1326_);
lean_inc(v___x_1472_);
v___x_1473_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1472_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_dec(v___x_1472_);
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v_snd_1320_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1236_;
}
else
{
lean_object* v_val_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v_val_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_val_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = lean_nat_dec_eq(v_val_1474_, v___x_1475_);
lean_dec(v_val_1474_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___y_1483_; uint8_t v___x_1516_; 
v___x_1477_ = lean_array_fget(v_snd_1320_, v___x_1314_);
lean_dec(v_snd_1320_);
v___x_1478_ = lean_box(0);
v___x_1479_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51);
v___x_1480_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1481_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
v___x_1516_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
v___y_1483_ = v___x_1517_;
goto v___jp_1482_;
}
else
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1483_ = v___x_1518_;
goto v___jp_1482_;
}
v___jp_1482_:
{
lean_object* v_b__pos_1484_; lean_object* v___x_1485_; 
lean_inc(v___x_1472_);
lean_inc_ref(v___y_1483_);
v_b__pos_1484_ = l_Lean_mkApp4(v___x_1479_, v___x_1480_, v___x_1481_, v___y_1483_, v___x_1472_);
v___x_1485_ = l_Lean_Meta_mkDecideProof(v_b__pos_1484_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1507_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1507_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1507_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1490_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57);
v___x_1491_ = l_Lean_mkApp3(v___x_1490_, v___x_1472_, v___x_1477_, v_a_1486_);
v___x_1492_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58);
v___x_1493_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59);
lean_inc_ref(v___x_1491_);
lean_inc_ref(v___y_1483_);
lean_inc_n(v___x_1315_, 2);
v___x_1494_ = l_Lean_mkApp3(v___x_1493_, v___x_1315_, v___y_1483_, v___x_1491_);
lean_inc(v___x_1327_);
v___x_1495_ = l_Lean_mkApp3(v___x_1492_, v___x_1327_, v___x_1315_, v___x_1494_);
v___x_1496_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60);
v___x_1497_ = l_Lean_mkApp3(v___x_1496_, v___x_1327_, v___x_1315_, v___x_1491_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set_tag(v___x_1322_, 1);
lean_ctor_set(v___x_1322_, 1, v___x_1478_);
lean_ctor_set(v___x_1322_, 0, v___x_1497_);
v___x_1499_ = v___x_1322_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v___x_1478_);
v___x_1499_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 1);
lean_ctor_set(v___x_1257_, 1, v___x_1499_);
lean_ctor_set(v___x_1257_, 0, v___x_1495_);
v___x_1501_ = v___x_1257_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1503_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1501_);
v___x_1503_ = v___x_1488_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v___x_1477_);
lean_dec(v___x_1472_);
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
v_a_1508_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1485_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1485_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
else
{
lean_dec(v___x_1472_);
lean_dec(v___x_1327_);
lean_del_object(v___x_1322_);
lean_dec(v_snd_1320_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
goto v___jp_1236_;
}
}
}
}
}
v___jp_1328_:
{
lean_object* v___x_1329_; lean_object* v_fst_1330_; 
v___x_1329_ = l_Lean_Expr_getAppFnArgs(v___x_1327_);
v_fst_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_fst_1330_);
if (lean_obj_tag(v_fst_1330_) == 1)
{
lean_object* v_pre_1331_; 
v_pre_1331_ = lean_ctor_get(v_fst_1330_, 0);
lean_inc(v_pre_1331_);
if (lean_obj_tag(v_pre_1331_) == 1)
{
lean_object* v_pre_1332_; 
v_pre_1332_ = lean_ctor_get(v_pre_1331_, 0);
if (lean_obj_tag(v_pre_1332_) == 0)
{
lean_object* v_snd_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1363_; 
v_snd_1333_ = lean_ctor_get(v___x_1329_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1363_ == 0)
{
lean_object* v_unused_1364_; 
v_unused_1364_ = lean_ctor_get(v___x_1329_, 0);
lean_dec(v_unused_1364_);
v___x_1335_ = v___x_1329_;
v_isShared_1336_ = v_isSharedCheck_1363_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_snd_1333_);
lean_dec(v___x_1329_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1363_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_str_1337_; lean_object* v_str_1338_; uint8_t v___x_1339_; 
v_str_1337_ = lean_ctor_get(v_fst_1330_, 1);
lean_inc_ref(v_str_1337_);
lean_dec_ref_known(v_fst_1330_, 2);
v_str_1338_ = lean_ctor_get(v_pre_1331_, 1);
lean_inc_ref(v_str_1338_);
lean_dec_ref_known(v_pre_1331_, 2);
v___x_1339_ = lean_string_dec_eq(v_str_1338_, v___x_1261_);
lean_dec_ref(v_str_1338_);
if (v___x_1339_ == 0)
{
lean_dec_ref(v_str_1337_);
lean_del_object(v___x_1335_);
lean_dec(v_snd_1333_);
lean_dec(v___x_1315_);
goto v___jp_1245_;
}
else
{
lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1341_ = lean_string_dec_eq(v_str_1337_, v___x_1340_);
lean_dec_ref(v_str_1337_);
if (v___x_1341_ == 0)
{
lean_del_object(v___x_1335_);
lean_dec(v_snd_1333_);
lean_dec(v___x_1315_);
goto v___jp_1245_;
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1342_ = lean_array_get_size(v_snd_1333_);
v___x_1343_ = lean_unsigned_to_nat(3u);
v___x_1344_ = lean_nat_dec_eq(v___x_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_del_object(v___x_1335_);
lean_dec(v_snd_1333_);
lean_dec(v___x_1315_);
goto v___jp_1245_;
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_array_fget_borrowed(v_snd_1333_, v___x_1345_);
if (lean_obj_tag(v___x_1346_) == 4)
{
lean_object* v_declName_1347_; 
v_declName_1347_ = lean_ctor_get(v___x_1346_, 0);
if (lean_obj_tag(v_declName_1347_) == 1)
{
lean_object* v_pre_1348_; 
v_pre_1348_ = lean_ctor_get(v_declName_1347_, 0);
if (lean_obj_tag(v_pre_1348_) == 0)
{
lean_object* v_us_1349_; lean_object* v_str_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_us_1349_ = lean_ctor_get(v___x_1346_, 1);
lean_inc(v_us_1349_);
v_str_1350_ = lean_ctor_get(v_declName_1347_, 1);
v___x_1351_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1352_ = lean_string_dec_eq(v_str_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_dec(v_us_1349_);
lean_del_object(v___x_1335_);
lean_dec(v_snd_1333_);
lean_dec(v___x_1315_);
goto v___jp_1245_;
}
else
{
if (lean_obj_tag(v_us_1349_) == 0)
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1353_ = lean_unsigned_to_nat(2u);
v___x_1354_ = lean_array_fget(v_snd_1333_, v___x_1353_);
lean_dec(v_snd_1333_);
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19));
v___x_1356_ = l_Lean_Expr_const___override(v___x_1355_, v_us_1349_);
v___x_1357_ = l_Lean_mkAppB(v___x_1356_, v___x_1354_, v___x_1315_);
v___x_1358_ = lean_box(0);
if (v_isShared_1336_ == 0)
{
lean_ctor_set_tag(v___x_1335_, 1);
lean_ctor_set(v___x_1335_, 1, v___x_1358_);
lean_ctor_set(v___x_1335_, 0, v___x_1357_);
v___x_1360_ = v___x_1335_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
}
else
{
lean_dec(v_us_1349_);
lean_del_object(v___x_1335_);
lean_dec(v_snd_1333_);
lean_dec(v___x_1315_);
goto v___jp_1245_;
}
}
}
else
{
lean_del_object(v___x_1335_);
lean_dec(v_snd_1333_);
lean_dec(v___x_1315_);
goto v___jp_1245_;
}
}
else
{
lean_del_object(v___x_1335_);
lean_dec(v_snd_1333_);
lean_dec(v___x_1315_);
goto v___jp_1245_;
}
}
else
{
lean_del_object(v___x_1335_);
lean_dec(v_snd_1333_);
lean_dec(v___x_1315_);
goto v___jp_1245_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1331_, 2);
lean_dec_ref_known(v_fst_1330_, 2);
lean_dec_ref(v___x_1329_);
lean_dec(v___x_1315_);
goto v___jp_1245_;
}
}
else
{
lean_dec(v_pre_1331_);
lean_dec_ref_known(v_fst_1330_, 2);
lean_dec_ref(v___x_1329_);
lean_dec(v___x_1315_);
goto v___jp_1245_;
}
}
else
{
lean_dec(v_fst_1330_);
lean_dec_ref(v___x_1329_);
lean_dec(v___x_1315_);
goto v___jp_1245_;
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1318_, 2);
lean_dec_ref_known(v_fst_1317_, 2);
lean_dec_ref(v___x_1316_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1242_;
}
}
else
{
lean_dec(v_pre_1318_);
lean_dec_ref_known(v_fst_1317_, 2);
lean_dec_ref(v___x_1316_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1242_;
}
}
else
{
lean_dec(v_fst_1317_);
lean_dec_ref(v___x_1316_);
lean_dec(v___x_1315_);
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1242_;
}
}
}
}
}
else
{
lean_object* v___x_1521_; uint8_t v___x_1522_; 
lean_dec_ref(v_str_1260_);
v___x_1521_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7));
v___x_1522_ = lean_string_dec_eq(v_str_1259_, v___x_1521_);
lean_dec_ref(v_str_1259_);
if (v___x_1522_ == 0)
{
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1523_ = lean_array_get_size(v_snd_1255_);
v___x_1524_ = lean_unsigned_to_nat(6u);
v___x_1525_ = lean_nat_dec_eq(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1526_ = lean_unsigned_to_nat(5u);
v___x_1527_ = lean_array_fget(v_snd_1255_, v___x_1526_);
lean_inc(v___x_1527_);
v___x_1528_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1527_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_dec(v___x_1527_);
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1233_;
}
else
{
lean_object* v_val_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v_val_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_val_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v___x_1530_ = lean_unsigned_to_nat(0u);
v___x_1531_ = lean_nat_dec_eq(v_val_1529_, v___x_1530_);
lean_dec(v_val_1529_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___y_1538_; uint8_t v___x_1578_; 
v___x_1532_ = lean_unsigned_to_nat(4u);
v___x_1533_ = lean_array_fget(v_snd_1255_, v___x_1532_);
lean_dec(v_snd_1255_);
v___x_1534_ = lean_box(0);
v___x_1535_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68);
v___x_1536_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1578_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
v___y_1538_ = v___x_1579_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1538_ = v___x_1580_;
goto v___jp_1537_;
}
v___jp_1537_:
{
lean_object* v_ne__zero_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v_pos_1542_; lean_object* v___x_1543_; 
lean_inc_ref_n(v___y_1538_, 2);
lean_inc_n(v___x_1527_, 2);
v_ne__zero_1539_ = l_Lean_mkApp3(v___x_1535_, v___x_1536_, v___x_1527_, v___y_1538_);
v___x_1540_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51);
v___x_1541_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
v_pos_1542_ = l_Lean_mkApp4(v___x_1540_, v___x_1536_, v___x_1541_, v___y_1538_, v___x_1527_);
v___x_1543_ = l_Lean_Meta_mkDecideProof(v_ne__zero_1539_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1545_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1545_ = l_Lean_Meta_mkDecideProof(v_pos_1542_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1561_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1561_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1561_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1550_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71);
lean_inc(v___x_1527_);
lean_inc(v___x_1533_);
v___x_1551_ = l_Lean_mkApp3(v___x_1550_, v___x_1533_, v___x_1527_, v_a_1544_);
v___x_1552_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74);
v___x_1553_ = l_Lean_mkApp3(v___x_1552_, v___x_1533_, v___x_1527_, v_a_1546_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 1);
lean_ctor_set(v___x_1257_, 1, v___x_1534_);
lean_ctor_set(v___x_1257_, 0, v___x_1553_);
v___x_1555_ = v___x_1257_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v___x_1534_);
v___x_1555_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1551_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1556_);
v___x_1558_ = v___x_1548_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1556_);
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
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec(v_a_1544_);
lean_dec(v___x_1533_);
lean_dec(v___x_1527_);
lean_del_object(v___x_1257_);
v_a_1562_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1545_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1545_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec_ref(v_pos_1542_);
lean_dec(v___x_1533_);
lean_dec(v___x_1527_);
lean_del_object(v___x_1257_);
v_a_1570_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1543_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1543_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
else
{
lean_dec(v___x_1527_);
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1233_;
}
}
}
}
}
}
else
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
lean_dec_ref(v_str_1260_);
v___x_1581_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1582_ = lean_string_dec_eq(v_str_1259_, v___x_1581_);
lean_dec_ref(v_str_1259_);
if (v___x_1582_ == 0)
{
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1583_ = lean_array_get_size(v_snd_1255_);
v___x_1584_ = lean_unsigned_to_nat(3u);
v___x_1585_ = lean_nat_dec_eq(v___x_1583_, v___x_1584_);
if (v___x_1585_ == 0)
{
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_unsigned_to_nat(0u);
v___x_1587_ = lean_array_fget_borrowed(v_snd_1255_, v___x_1586_);
if (lean_obj_tag(v___x_1587_) == 4)
{
lean_object* v_declName_1588_; 
v_declName_1588_ = lean_ctor_get(v___x_1587_, 0);
if (lean_obj_tag(v_declName_1588_) == 1)
{
lean_object* v_pre_1589_; 
v_pre_1589_ = lean_ctor_get(v_declName_1588_, 0);
if (lean_obj_tag(v_pre_1589_) == 0)
{
lean_object* v_us_1590_; lean_object* v_str_1591_; lean_object* v___x_1592_; lean_object* v___y_1594_; lean_object* v___y_1595_; uint8_t v___x_1605_; 
v_us_1590_ = lean_ctor_get(v___x_1587_, 1);
lean_inc(v_us_1590_);
v_str_1591_ = lean_ctor_get(v_declName_1588_, 1);
v___x_1592_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1605_ = lean_string_dec_eq(v_str_1591_, v___x_1592_);
if (v___x_1605_ == 0)
{
lean_dec(v_us_1590_);
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
else
{
if (lean_obj_tag(v_us_1590_) == 0)
{
uint8_t v_splitNatSub_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v_r_1613_; lean_object* v_n_1615_; lean_object* v_x_1616_; lean_object* v_n_1625_; lean_object* v_i_1626_; lean_object* v_x_1635_; 
v_splitNatSub_1606_ = lean_ctor_get_uint8(v_a_1227_, 1);
v___x_1607_ = lean_unsigned_to_nat(2u);
v___x_1608_ = lean_array_fget(v_snd_1255_, v___x_1607_);
lean_dec(v_snd_1255_);
v___x_1609_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78));
v___x_1610_ = l_Lean_Expr_const___override(v___x_1609_, v_us_1590_);
lean_inc(v___x_1608_);
v___x_1611_ = l_Lean_Expr_app___override(v___x_1610_, v___x_1608_);
v___x_1612_ = lean_box(0);
v_r_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_r_1613_, 0, v___x_1611_);
lean_ctor_set(v_r_1613_, 1, v___x_1612_);
if (v_splitNatSub_1606_ == 1)
{
lean_object* v___x_1641_; lean_object* v_fst_1642_; 
v___x_1641_ = l_Lean_Expr_getAppFnArgs(v___x_1608_);
v_fst_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_fst_1642_);
if (lean_obj_tag(v_fst_1642_) == 1)
{
lean_object* v_pre_1643_; 
v_pre_1643_ = lean_ctor_get(v_fst_1642_, 0);
lean_inc(v_pre_1643_);
if (lean_obj_tag(v_pre_1643_) == 1)
{
lean_object* v_pre_1644_; 
v_pre_1644_ = lean_ctor_get(v_pre_1643_, 0);
if (lean_obj_tag(v_pre_1644_) == 0)
{
lean_object* v_snd_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1705_; 
v_snd_1645_ = lean_ctor_get(v___x_1641_, 1);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; 
v_unused_1706_ = lean_ctor_get(v___x_1641_, 0);
lean_dec(v_unused_1706_);
v___x_1647_ = v___x_1641_;
v_isShared_1648_ = v_isSharedCheck_1705_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_snd_1645_);
lean_dec(v___x_1641_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1705_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v_str_1649_; lean_object* v_str_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v_str_1649_ = lean_ctor_get(v_fst_1642_, 1);
lean_inc_ref(v_str_1649_);
lean_dec_ref_known(v_fst_1642_, 2);
v_str_1650_ = lean_ctor_get(v_pre_1643_, 1);
lean_inc_ref(v_str_1650_);
lean_dec_ref_known(v_pre_1643_, 2);
v___x_1651_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2));
v___x_1652_ = lean_string_dec_eq(v_str_1650_, v___x_1651_);
if (v___x_1652_ == 0)
{
uint8_t v___x_1653_; 
lean_del_object(v___x_1647_);
v___x_1653_ = lean_string_dec_eq(v_str_1650_, v___x_1592_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
lean_del_object(v___x_1257_);
v___x_1654_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82));
v___x_1655_ = lean_string_dec_eq(v_str_1650_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79));
v___x_1657_ = lean_string_dec_eq(v_str_1650_, v___x_1656_);
lean_dec_ref(v_str_1650_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec_ref(v_str_1649_);
lean_dec(v_snd_1645_);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_r_1613_);
return v___x_1658_;
}
else
{
lean_object* v___x_1659_; uint8_t v___x_1660_; 
v___x_1659_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86));
v___x_1660_ = lean_string_dec_eq(v_str_1649_, v___x_1659_);
lean_dec_ref(v_str_1649_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; 
lean_dec(v_snd_1645_);
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_r_1613_);
return v___x_1661_;
}
else
{
lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = lean_array_get_size(v_snd_1645_);
v___x_1663_ = lean_nat_dec_eq(v___x_1662_, v___x_1607_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; 
lean_dec(v_snd_1645_);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v_r_1613_);
return v___x_1664_;
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = lean_array_fget(v_snd_1645_, v___x_1586_);
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = lean_array_fget(v_snd_1645_, v___x_1666_);
lean_dec(v_snd_1645_);
v_n_1615_ = v___x_1665_;
v_x_1616_ = v___x_1667_;
goto v___jp_1614_;
}
}
}
}
else
{
lean_object* v___x_1668_; uint8_t v___x_1669_; 
lean_dec_ref(v_str_1650_);
v___x_1668_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87));
v___x_1669_ = lean_string_dec_eq(v_str_1649_, v___x_1668_);
lean_dec_ref(v_str_1649_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
lean_dec(v_snd_1645_);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_r_1613_);
return v___x_1670_;
}
else
{
lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1671_ = lean_array_get_size(v_snd_1645_);
v___x_1672_ = lean_nat_dec_eq(v___x_1671_, v___x_1607_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; 
lean_dec(v_snd_1645_);
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_r_1613_);
return v___x_1673_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_array_fget(v_snd_1645_, v___x_1586_);
v___x_1675_ = lean_unsigned_to_nat(1u);
v___x_1676_ = lean_array_fget(v_snd_1645_, v___x_1675_);
lean_dec(v_snd_1645_);
v_n_1625_ = v___x_1674_;
v_i_1626_ = v___x_1676_;
goto v___jp_1624_;
}
}
}
}
else
{
lean_object* v___x_1677_; uint8_t v___x_1678_; 
lean_dec_ref(v_str_1650_);
v___x_1677_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88));
v___x_1678_ = lean_string_dec_eq(v_str_1649_, v___x_1677_);
lean_dec_ref(v_str_1649_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_dec(v_snd_1645_);
lean_del_object(v___x_1257_);
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_r_1613_);
return v___x_1679_;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1680_ = lean_array_get_size(v_snd_1645_);
v___x_1681_ = lean_unsigned_to_nat(1u);
v___x_1682_ = lean_nat_dec_eq(v___x_1680_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; 
lean_dec(v_snd_1645_);
lean_del_object(v___x_1257_);
v___x_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_r_1613_);
return v___x_1683_;
}
else
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_array_fget(v_snd_1645_, v___x_1586_);
lean_dec(v_snd_1645_);
v_x_1635_ = v___x_1684_;
goto v___jp_1634_;
}
}
}
}
else
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
lean_dec_ref(v_str_1650_);
lean_del_object(v___x_1257_);
v___x_1685_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9));
v___x_1686_ = lean_string_dec_eq(v_str_1649_, v___x_1685_);
lean_dec_ref(v_str_1649_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; 
lean_del_object(v___x_1647_);
lean_dec(v_snd_1645_);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v_r_1613_);
return v___x_1687_;
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v___x_1688_ = lean_array_get_size(v_snd_1645_);
v___x_1689_ = lean_unsigned_to_nat(6u);
v___x_1690_ = lean_nat_dec_eq(v___x_1688_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
lean_del_object(v___x_1647_);
lean_dec(v_snd_1645_);
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_r_1613_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1692_ = lean_unsigned_to_nat(4u);
v___x_1693_ = lean_array_fget(v_snd_1645_, v___x_1692_);
v___x_1694_ = lean_unsigned_to_nat(5u);
v___x_1695_ = lean_array_fget(v_snd_1645_, v___x_1694_);
lean_dec(v_snd_1645_);
v___x_1696_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90));
v___x_1697_ = l_Lean_Expr_const___override(v___x_1696_, v_us_1590_);
v___x_1698_ = l_Lean_mkAppB(v___x_1697_, v___x_1693_, v___x_1695_);
v___x_1699_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1698_, v_r_1613_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1701_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 1);
lean_ctor_set(v___x_1647_, 1, v_r_1613_);
lean_ctor_set(v___x_1647_, 0, v___x_1698_);
v___x_1701_ = v___x_1647_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_r_1613_);
v___x_1701_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
return v___x_1702_;
}
}
else
{
lean_object* v___x_1704_; 
lean_dec_ref(v___x_1698_);
lean_del_object(v___x_1647_);
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_r_1613_);
return v___x_1704_;
}
}
}
}
}
}
else
{
lean_object* v___x_1707_; 
lean_dec_ref_known(v_pre_1643_, 2);
lean_dec_ref_known(v_fst_1642_, 2);
lean_dec_ref(v___x_1641_);
lean_del_object(v___x_1257_);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_r_1613_);
return v___x_1707_;
}
}
else
{
lean_object* v___x_1708_; 
lean_dec(v_pre_1643_);
lean_dec_ref_known(v_fst_1642_, 2);
lean_dec_ref(v___x_1641_);
lean_del_object(v___x_1257_);
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v_r_1613_);
return v___x_1708_;
}
}
else
{
lean_object* v___x_1709_; 
lean_dec(v_fst_1642_);
lean_dec_ref(v___x_1641_);
lean_del_object(v___x_1257_);
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_r_1613_);
return v___x_1709_;
}
}
else
{
lean_object* v___x_1710_; lean_object* v_fst_1711_; 
v___x_1710_ = l_Lean_Expr_getAppFnArgs(v___x_1608_);
v_fst_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_fst_1711_);
if (lean_obj_tag(v_fst_1711_) == 1)
{
lean_object* v_pre_1712_; 
v_pre_1712_ = lean_ctor_get(v_fst_1711_, 0);
lean_inc(v_pre_1712_);
if (lean_obj_tag(v_pre_1712_) == 1)
{
lean_object* v_pre_1713_; 
v_pre_1713_ = lean_ctor_get(v_pre_1712_, 0);
if (lean_obj_tag(v_pre_1713_) == 0)
{
lean_object* v_snd_1714_; lean_object* v_str_1715_; lean_object* v_str_1716_; uint8_t v___x_1717_; 
v_snd_1714_ = lean_ctor_get(v___x_1710_, 1);
lean_inc(v_snd_1714_);
lean_dec_ref(v___x_1710_);
v_str_1715_ = lean_ctor_get(v_fst_1711_, 1);
lean_inc_ref(v_str_1715_);
lean_dec_ref_known(v_fst_1711_, 2);
v_str_1716_ = lean_ctor_get(v_pre_1712_, 1);
lean_inc_ref(v_str_1716_);
lean_dec_ref_known(v_pre_1712_, 2);
v___x_1717_ = lean_string_dec_eq(v_str_1716_, v___x_1592_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
lean_del_object(v___x_1257_);
v___x_1718_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82));
v___x_1719_ = lean_string_dec_eq(v_str_1716_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1720_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79));
v___x_1721_ = lean_string_dec_eq(v_str_1716_, v___x_1720_);
lean_dec_ref(v_str_1716_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_dec_ref(v_str_1715_);
lean_dec(v_snd_1714_);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_r_1613_);
return v___x_1722_;
}
else
{
lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___x_1723_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86));
v___x_1724_ = lean_string_dec_eq(v_str_1715_, v___x_1723_);
lean_dec_ref(v_str_1715_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; 
lean_dec(v_snd_1714_);
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_r_1613_);
return v___x_1725_;
}
else
{
lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1726_ = lean_array_get_size(v_snd_1714_);
v___x_1727_ = lean_nat_dec_eq(v___x_1726_, v___x_1607_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; 
lean_dec(v_snd_1714_);
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_r_1613_);
return v___x_1728_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = lean_array_fget(v_snd_1714_, v___x_1586_);
v___x_1730_ = lean_unsigned_to_nat(1u);
v___x_1731_ = lean_array_fget(v_snd_1714_, v___x_1730_);
lean_dec(v_snd_1714_);
v_n_1615_ = v___x_1729_;
v_x_1616_ = v___x_1731_;
goto v___jp_1614_;
}
}
}
}
else
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
lean_dec_ref(v_str_1716_);
v___x_1732_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87));
v___x_1733_ = lean_string_dec_eq(v_str_1715_, v___x_1732_);
lean_dec_ref(v_str_1715_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
lean_dec(v_snd_1714_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_r_1613_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1735_ = lean_array_get_size(v_snd_1714_);
v___x_1736_ = lean_nat_dec_eq(v___x_1735_, v___x_1607_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; 
lean_dec(v_snd_1714_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v_r_1613_);
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = lean_array_fget(v_snd_1714_, v___x_1586_);
v___x_1739_ = lean_unsigned_to_nat(1u);
v___x_1740_ = lean_array_fget(v_snd_1714_, v___x_1739_);
lean_dec(v_snd_1714_);
v_n_1625_ = v___x_1738_;
v_i_1626_ = v___x_1740_;
goto v___jp_1624_;
}
}
}
}
else
{
lean_object* v___x_1741_; uint8_t v___x_1742_; 
lean_dec_ref(v_str_1716_);
v___x_1741_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88));
v___x_1742_ = lean_string_dec_eq(v_str_1715_, v___x_1741_);
lean_dec_ref(v_str_1715_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; 
lean_dec(v_snd_1714_);
lean_del_object(v___x_1257_);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_r_1613_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1744_ = lean_array_get_size(v_snd_1714_);
v___x_1745_ = lean_unsigned_to_nat(1u);
v___x_1746_ = lean_nat_dec_eq(v___x_1744_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; 
lean_dec(v_snd_1714_);
lean_del_object(v___x_1257_);
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v_r_1613_);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_array_fget(v_snd_1714_, v___x_1586_);
lean_dec(v_snd_1714_);
v_x_1635_ = v___x_1748_;
goto v___jp_1634_;
}
}
}
}
else
{
lean_object* v___x_1749_; 
lean_dec_ref_known(v_pre_1712_, 2);
lean_dec_ref_known(v_fst_1711_, 2);
lean_dec_ref(v___x_1710_);
lean_del_object(v___x_1257_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v_r_1613_);
return v___x_1749_;
}
}
else
{
lean_object* v___x_1750_; 
lean_dec_ref_known(v_fst_1711_, 2);
lean_dec(v_pre_1712_);
lean_dec_ref(v___x_1710_);
lean_del_object(v___x_1257_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_r_1613_);
return v___x_1750_;
}
}
else
{
lean_object* v___x_1751_; 
lean_dec(v_fst_1711_);
lean_dec_ref(v___x_1710_);
lean_del_object(v___x_1257_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v_r_1613_);
return v___x_1751_;
}
}
v___jp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1617_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81));
v___x_1618_ = l_Lean_Expr_const___override(v___x_1617_, v_us_1590_);
v___x_1619_ = l_Lean_mkAppB(v___x_1618_, v_n_1615_, v_x_1616_);
v___x_1620_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1619_, v_r_1613_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v_r_1613_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
else
{
lean_object* v___x_1623_; 
lean_dec_ref(v___x_1619_);
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_r_1613_);
return v___x_1623_;
}
}
v___jp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1627_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83));
v___x_1628_ = l_Lean_Expr_const___override(v___x_1627_, v_us_1590_);
v___x_1629_ = l_Lean_mkAppB(v___x_1628_, v_n_1625_, v_i_1626_);
v___x_1630_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1629_, v_r_1613_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v_r_1613_);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
else
{
lean_object* v___x_1633_; 
lean_dec_ref(v___x_1629_);
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v_r_1613_);
return v___x_1633_;
}
}
v___jp_1634_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1636_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85));
v___x_1637_ = l_Lean_Expr_const___override(v___x_1636_, v_us_1590_);
lean_inc_ref(v_x_1635_);
v___x_1638_ = l_Lean_Expr_app___override(v___x_1637_, v_x_1635_);
v___x_1639_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1638_, v_r_1613_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v_r_1613_);
v___y_1594_ = v_x_1635_;
v___y_1595_ = v___x_1640_;
goto v___jp_1593_;
}
else
{
lean_dec_ref(v___x_1638_);
v___y_1594_ = v_x_1635_;
v___y_1595_ = v_r_1613_;
goto v___jp_1593_;
}
}
}
else
{
lean_dec(v_us_1590_);
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
}
v___jp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1596_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76));
v___x_1597_ = l_Lean_Expr_const___override(v___x_1596_, v_us_1590_);
v___x_1598_ = l_Lean_Expr_app___override(v___x_1597_, v___y_1594_);
v___x_1599_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1598_, v___y_1595_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1601_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 1);
lean_ctor_set(v___x_1257_, 1, v___y_1595_);
lean_ctor_set(v___x_1257_, 0, v___x_1598_);
v___x_1601_ = v___x_1257_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v___y_1595_);
v___x_1601_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
}
else
{
lean_object* v___x_1604_; 
lean_dec_ref(v___x_1598_);
lean_del_object(v___x_1257_);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___y_1595_);
return v___x_1604_;
}
}
}
else
{
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
}
else
{
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
}
else
{
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
goto v___jp_1239_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1253_, 2);
lean_dec_ref_known(v_fst_1252_, 2);
lean_dec_ref(v___x_1251_);
goto v___jp_1239_;
}
}
case 0:
{
lean_object* v_snd_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1784_; 
v_snd_1754_ = lean_ctor_get(v___x_1251_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; 
v_unused_1785_ = lean_ctor_get(v___x_1251_, 0);
lean_dec(v_unused_1785_);
v___x_1756_ = v___x_1251_;
v_isShared_1757_ = v_isSharedCheck_1784_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_snd_1754_);
lean_dec(v___x_1251_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1784_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_str_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_str_1758_ = lean_ctor_get(v_fst_1252_, 1);
lean_inc_ref(v_str_1758_);
lean_dec_ref_known(v_fst_1252_, 2);
v___x_1759_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91));
v___x_1760_ = lean_string_dec_eq(v_str_1758_, v___x_1759_);
lean_dec_ref(v_str_1758_);
if (v___x_1760_ == 0)
{
lean_del_object(v___x_1756_);
lean_dec(v_snd_1754_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1761_ = lean_array_get_size(v_snd_1754_);
v___x_1762_ = lean_unsigned_to_nat(5u);
v___x_1763_ = lean_nat_dec_eq(v___x_1761_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_del_object(v___x_1756_);
lean_dec(v_snd_1754_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = lean_array_fget(v_snd_1754_, v___x_1764_);
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1768_ = lean_expr_eqv(v___x_1765_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; 
lean_dec(v___x_1765_);
lean_del_object(v___x_1756_);
lean_dec(v_snd_1754_);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1766_);
return v___x_1769_;
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1770_ = lean_unsigned_to_nat(1u);
v___x_1771_ = lean_array_fget(v_snd_1754_, v___x_1770_);
v___x_1772_ = lean_unsigned_to_nat(2u);
v___x_1773_ = lean_array_fget(v_snd_1754_, v___x_1772_);
v___x_1774_ = lean_unsigned_to_nat(3u);
v___x_1775_ = lean_array_fget(v_snd_1754_, v___x_1774_);
v___x_1776_ = lean_unsigned_to_nat(4u);
v___x_1777_ = lean_array_fget(v_snd_1754_, v___x_1776_);
lean_dec(v_snd_1754_);
v___x_1778_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94);
v___x_1779_ = l_Lean_mkApp5(v___x_1778_, v___x_1765_, v___x_1771_, v___x_1773_, v___x_1775_, v___x_1777_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set_tag(v___x_1756_, 1);
lean_ctor_set(v___x_1756_, 1, v___x_1766_);
lean_ctor_set(v___x_1756_, 0, v___x_1779_);
v___x_1781_ = v___x_1756_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v___x_1766_);
v___x_1781_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_fst_1252_, 2);
lean_dec_ref(v___x_1251_);
goto v___jp_1239_;
}
}
}
else
{
lean_dec(v_fst_1252_);
lean_dec_ref(v___x_1251_);
goto v___jp_1239_;
}
v___jp_1233_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_box(0);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
v___jp_1236_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
v___jp_1239_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
v___jp_1242_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
v___jp_1245_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_box(0);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
v___jp_1248_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1226_ = stack[0].m_obj;
lean_object* v_a_1227_ = stack[1].m_obj;
lean_object* v_a_1228_ = stack[2].m_obj;
lean_object* v_a_1229_ = stack[3].m_obj;
lean_object* v_a_1230_ = stack[4].m_obj;
lean_object* v_a_1231_ = stack[5].m_obj;
lean_object* v_res_1786_;
v_res_1786_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_e_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
stack->m_obj
 = v_res_1786_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(lean_object* v_e_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_e_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
lean_dec_ref(v_a_1788_);
return v_res_1794_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object* v_e_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, uint8_t v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_e_1795_, v_a_1798_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_analyzeAtom_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1795_ = stack[0].m_obj;
lean_object* v_a_1796_ = stack[1].m_obj;
lean_object* v_a_1797_ = stack[2].m_obj;
lean_object* v_a_1798_ = stack[3].m_obj;
uint8_t v_a_1799_ = stack[4].m_num;
lean_object* v_a_1800_ = stack[5].m_obj;
lean_object* v_a_1801_ = stack[6].m_obj;
lean_object* v_a_1802_ = stack[7].m_obj;
lean_object* v_a_1803_ = stack[8].m_obj;
lean_object* v_a_1804_ = stack[9].m_obj;
lean_object* v_res_1807_;
v_res_1807_ = l_Lean_Elab_Tactic_Omega_analyzeAtom(v_e_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
stack->m_obj
 = v_res_1807_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object* v_e_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
uint8_t v_a_boxed_1819_; lean_object* v_res_1820_; 
v_a_boxed_1819_ = lean_unbox(v_a_1812_);
v_res_1820_ = l_Lean_Elab_Tactic_Omega_analyzeAtom(v_e_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_boxed_1819_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec(v_a_1809_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(lean_object* v_a_1821_, lean_object* v_x_1822_){
_start:
{
if (lean_obj_tag(v_x_1822_) == 0)
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_box(0);
return v___x_1823_;
}
else
{
lean_object* v_key_1824_; lean_object* v_value_1825_; lean_object* v_tail_1826_; uint8_t v___x_1827_; 
v_key_1824_ = lean_ctor_get(v_x_1822_, 0);
v_value_1825_ = lean_ctor_get(v_x_1822_, 1);
v_tail_1826_ = lean_ctor_get(v_x_1822_, 2);
v___x_1827_ = lean_expr_eqv(v_key_1824_, v_a_1821_);
if (v___x_1827_ == 0)
{
v_x_1822_ = v_tail_1826_;
goto _start;
}
else
{
lean_object* v___x_1829_; 
lean_inc(v_value_1825_);
v___x_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1829_, 0, v_value_1825_);
return v___x_1829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg___boxed(lean_object* v_a_1830_, lean_object* v_x_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_1830_, v_x_1831_);
lean_dec(v_x_1831_);
lean_dec_ref(v_a_1830_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object* v_m_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_buckets_1835_; lean_object* v___x_1836_; uint64_t v___x_1837_; uint64_t v___x_1838_; uint64_t v___x_1839_; uint64_t v_fold_1840_; uint64_t v___x_1841_; uint64_t v___x_1842_; uint64_t v___x_1843_; size_t v___x_1844_; size_t v___x_1845_; size_t v___x_1846_; size_t v___x_1847_; size_t v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_buckets_1835_ = lean_ctor_get(v_m_1833_, 1);
v___x_1836_ = lean_array_get_size(v_buckets_1835_);
v___x_1837_ = l_Lean_Expr_hash(v_a_1834_);
v___x_1838_ = 32ULL;
v___x_1839_ = lean_uint64_shift_right(v___x_1837_, v___x_1838_);
v_fold_1840_ = lean_uint64_xor(v___x_1837_, v___x_1839_);
v___x_1841_ = 16ULL;
v___x_1842_ = lean_uint64_shift_right(v_fold_1840_, v___x_1841_);
v___x_1843_ = lean_uint64_xor(v_fold_1840_, v___x_1842_);
v___x_1844_ = lean_uint64_to_usize(v___x_1843_);
v___x_1845_ = lean_usize_of_nat(v___x_1836_);
v___x_1846_ = ((size_t)1ULL);
v___x_1847_ = lean_usize_sub(v___x_1845_, v___x_1846_);
v___x_1848_ = lean_usize_land(v___x_1844_, v___x_1847_);
v___x_1849_ = lean_array_uget_borrowed(v_buckets_1835_, v___x_1848_);
v___x_1850_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_1834_, v___x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(lean_object* v_m_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_1851_, v_a_1852_);
lean_dec_ref(v_a_1852_);
lean_dec_ref(v_m_1851_);
return v_res_1853_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(lean_object* v_a_1854_, lean_object* v_x_1855_){
_start:
{
if (lean_obj_tag(v_x_1855_) == 0)
{
uint8_t v___x_1856_; 
v___x_1856_ = 0;
return v___x_1856_;
}
else
{
lean_object* v_key_1857_; lean_object* v_tail_1858_; uint8_t v___x_1859_; 
v_key_1857_ = lean_ctor_get(v_x_1855_, 0);
v_tail_1858_ = lean_ctor_get(v_x_1855_, 2);
v___x_1859_ = lean_expr_eqv(v_key_1857_, v_a_1854_);
if (v___x_1859_ == 0)
{
v_x_1855_ = v_tail_1858_;
goto _start;
}
else
{
return v___x_1859_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1854_ = stack[0].m_obj;
lean_object* v_x_1855_ = stack[1].m_obj;
uint8_t v_res_1861_;
v_res_1861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_1854_, v_x_1855_);
stack->m_num = v_res_1861_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg___boxed(lean_object* v_a_1862_, lean_object* v_x_1863_){
_start:
{
uint8_t v_res_1864_; lean_object* v_r_1865_; 
v_res_1864_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_1862_, v_x_1863_);
lean_dec(v_x_1863_);
lean_dec_ref(v_a_1862_);
v_r_1865_ = lean_box(v_res_1864_);
return v_r_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
if (lean_obj_tag(v_x_1867_) == 0)
{
return v_x_1866_;
}
else
{
lean_object* v_key_1868_; lean_object* v_value_1869_; lean_object* v_tail_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1893_; 
v_key_1868_ = lean_ctor_get(v_x_1867_, 0);
v_value_1869_ = lean_ctor_get(v_x_1867_, 1);
v_tail_1870_ = lean_ctor_get(v_x_1867_, 2);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_x_1867_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1872_ = v_x_1867_;
v_isShared_1873_ = v_isSharedCheck_1893_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_tail_1870_);
lean_inc(v_value_1869_);
lean_inc(v_key_1868_);
lean_dec(v_x_1867_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1893_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; uint64_t v___x_1875_; uint64_t v___x_1876_; uint64_t v___x_1877_; uint64_t v_fold_1878_; uint64_t v___x_1879_; uint64_t v___x_1880_; uint64_t v___x_1881_; size_t v___x_1882_; size_t v___x_1883_; size_t v___x_1884_; size_t v___x_1885_; size_t v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1874_ = lean_array_get_size(v_x_1866_);
v___x_1875_ = l_Lean_Expr_hash(v_key_1868_);
v___x_1876_ = 32ULL;
v___x_1877_ = lean_uint64_shift_right(v___x_1875_, v___x_1876_);
v_fold_1878_ = lean_uint64_xor(v___x_1875_, v___x_1877_);
v___x_1879_ = 16ULL;
v___x_1880_ = lean_uint64_shift_right(v_fold_1878_, v___x_1879_);
v___x_1881_ = lean_uint64_xor(v_fold_1878_, v___x_1880_);
v___x_1882_ = lean_uint64_to_usize(v___x_1881_);
v___x_1883_ = lean_usize_of_nat(v___x_1874_);
v___x_1884_ = ((size_t)1ULL);
v___x_1885_ = lean_usize_sub(v___x_1883_, v___x_1884_);
v___x_1886_ = lean_usize_land(v___x_1882_, v___x_1885_);
v___x_1887_ = lean_array_uget_borrowed(v_x_1866_, v___x_1886_);
lean_inc(v___x_1887_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 2, v___x_1887_);
v___x_1889_ = v___x_1872_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_key_1868_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_value_1869_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_array_uset(v_x_1866_, v___x_1886_, v___x_1889_);
v_x_1866_ = v___x_1890_;
v_x_1867_ = v_tail_1870_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1894_, lean_object* v_source_1895_, lean_object* v_target_1896_){
_start:
{
lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = lean_array_get_size(v_source_1895_);
v___x_1898_ = lean_nat_dec_lt(v_i_1894_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_dec_ref(v_source_1895_);
lean_dec(v_i_1894_);
return v_target_1896_;
}
else
{
lean_object* v_es_1899_; lean_object* v___x_1900_; lean_object* v_source_1901_; lean_object* v_target_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v_es_1899_ = lean_array_fget(v_source_1895_, v_i_1894_);
v___x_1900_ = lean_box(0);
v_source_1901_ = lean_array_fset(v_source_1895_, v_i_1894_, v___x_1900_);
v_target_1902_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(v_target_1896_, v_es_1899_);
v___x_1903_ = lean_unsigned_to_nat(1u);
v___x_1904_ = lean_nat_add(v_i_1894_, v___x_1903_);
lean_dec(v_i_1894_);
v_i_1894_ = v___x_1904_;
v_source_1895_ = v_source_1901_;
v_target_1896_ = v_target_1902_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(lean_object* v_data_1906_){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v_nbuckets_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1907_ = lean_array_get_size(v_data_1906_);
v___x_1908_ = lean_unsigned_to_nat(2u);
v_nbuckets_1909_ = lean_nat_mul(v___x_1907_, v___x_1908_);
v___x_1910_ = lean_unsigned_to_nat(0u);
v___x_1911_ = lean_box(0);
v___x_1912_ = lean_mk_array(v_nbuckets_1909_, v___x_1911_);
v___x_1913_ = lean_array_propagate_mark(v_data_1906_, v___x_1912_);
v___x_1914_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(v___x_1910_, v_data_1906_, v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(lean_object* v_a_1915_, lean_object* v_b_1916_, lean_object* v_x_1917_){
_start:
{
if (lean_obj_tag(v_x_1917_) == 0)
{
lean_dec(v_b_1916_);
lean_dec_ref(v_a_1915_);
return v_x_1917_;
}
else
{
lean_object* v_key_1918_; lean_object* v_value_1919_; lean_object* v_tail_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1932_; 
v_key_1918_ = lean_ctor_get(v_x_1917_, 0);
v_value_1919_ = lean_ctor_get(v_x_1917_, 1);
v_tail_1920_ = lean_ctor_get(v_x_1917_, 2);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_x_1917_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1922_ = v_x_1917_;
v_isShared_1923_ = v_isSharedCheck_1932_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_tail_1920_);
lean_inc(v_value_1919_);
lean_inc(v_key_1918_);
lean_dec(v_x_1917_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1932_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_expr_eqv(v_key_1918_, v_a_1915_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_1915_, v_b_1916_, v_tail_1920_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 2, v___x_1925_);
v___x_1927_ = v___x_1922_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_key_1918_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_value_1919_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
else
{
lean_object* v___x_1930_; 
lean_dec(v_value_1919_);
lean_dec(v_key_1918_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 1, v_b_1916_);
lean_ctor_set(v___x_1922_, 0, v_a_1915_);
v___x_1930_ = v___x_1922_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1915_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_b_1916_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_tail_1920_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object* v_m_1933_, lean_object* v_a_1934_, lean_object* v_b_1935_){
_start:
{
lean_object* v_size_1936_; lean_object* v_buckets_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1980_; 
v_size_1936_ = lean_ctor_get(v_m_1933_, 0);
v_buckets_1937_ = lean_ctor_get(v_m_1933_, 1);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_m_1933_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1939_ = v_m_1933_;
v_isShared_1940_ = v_isSharedCheck_1980_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_buckets_1937_);
lean_inc(v_size_1936_);
lean_dec(v_m_1933_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1980_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; uint64_t v___x_1942_; uint64_t v___x_1943_; uint64_t v___x_1944_; uint64_t v_fold_1945_; uint64_t v___x_1946_; uint64_t v___x_1947_; uint64_t v___x_1948_; size_t v___x_1949_; size_t v___x_1950_; size_t v___x_1951_; size_t v___x_1952_; size_t v___x_1953_; lean_object* v_bkt_1954_; uint8_t v___x_1955_; 
v___x_1941_ = lean_array_get_size(v_buckets_1937_);
v___x_1942_ = l_Lean_Expr_hash(v_a_1934_);
v___x_1943_ = 32ULL;
v___x_1944_ = lean_uint64_shift_right(v___x_1942_, v___x_1943_);
v_fold_1945_ = lean_uint64_xor(v___x_1942_, v___x_1944_);
v___x_1946_ = 16ULL;
v___x_1947_ = lean_uint64_shift_right(v_fold_1945_, v___x_1946_);
v___x_1948_ = lean_uint64_xor(v_fold_1945_, v___x_1947_);
v___x_1949_ = lean_uint64_to_usize(v___x_1948_);
v___x_1950_ = lean_usize_of_nat(v___x_1941_);
v___x_1951_ = ((size_t)1ULL);
v___x_1952_ = lean_usize_sub(v___x_1950_, v___x_1951_);
v___x_1953_ = lean_usize_land(v___x_1949_, v___x_1952_);
v_bkt_1954_ = lean_array_uget_borrowed(v_buckets_1937_, v___x_1953_);
v___x_1955_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_1934_, v_bkt_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v_size_x27_1957_; lean_object* v___x_1958_; lean_object* v_buckets_x27_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1956_ = lean_unsigned_to_nat(1u);
v_size_x27_1957_ = lean_nat_add(v_size_1936_, v___x_1956_);
lean_dec(v_size_1936_);
lean_inc(v_bkt_1954_);
v___x_1958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1958_, 0, v_a_1934_);
lean_ctor_set(v___x_1958_, 1, v_b_1935_);
lean_ctor_set(v___x_1958_, 2, v_bkt_1954_);
v_buckets_x27_1959_ = lean_array_uset(v_buckets_1937_, v___x_1953_, v___x_1958_);
v___x_1960_ = lean_unsigned_to_nat(4u);
v___x_1961_ = lean_nat_mul(v_size_x27_1957_, v___x_1960_);
v___x_1962_ = lean_unsigned_to_nat(3u);
v___x_1963_ = lean_nat_div(v___x_1961_, v___x_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_array_get_size(v_buckets_x27_1959_);
v___x_1965_ = lean_nat_dec_le(v___x_1963_, v___x_1964_);
lean_dec(v___x_1963_);
if (v___x_1965_ == 0)
{
lean_object* v_val_1966_; lean_object* v___x_1968_; 
v_val_1966_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_buckets_x27_1959_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 1, v_val_1966_);
lean_ctor_set(v___x_1939_, 0, v_size_x27_1957_);
v___x_1968_ = v___x_1939_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_size_x27_1957_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_val_1966_);
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
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 1, v_buckets_x27_1959_);
lean_ctor_set(v___x_1939_, 0, v_size_x27_1957_);
v___x_1971_ = v___x_1939_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_size_x27_1957_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_buckets_x27_1959_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
else
{
lean_object* v___x_1973_; lean_object* v_buckets_x27_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
lean_inc(v_bkt_1954_);
v___x_1973_ = lean_box(0);
v_buckets_x27_1974_ = lean_array_uset(v_buckets_1937_, v___x_1953_, v___x_1973_);
v___x_1975_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_1934_, v_b_1935_, v_bkt_1954_);
v___x_1976_ = lean_array_uset(v_buckets_x27_1974_, v___x_1953_, v___x_1975_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 1, v___x_1976_);
v___x_1978_ = v___x_1939_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_size_1936_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(lean_object* v_msgData_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v_env_1988_; uint8_t v___x_1989_; lean_object* v_env_1990_; lean_object* v___x_1991_; lean_object* v_toCold_1992_; lean_object* v_mctx_1993_; lean_object* v_lctx_1994_; lean_object* v_options_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1987_ = lean_st_ref_get(v___y_1985_);
v_env_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc_ref(v_env_1988_);
lean_dec(v___x_1987_);
v___x_1989_ = 0;
v_env_1990_ = l_Lean_Environment_setRecordingDeps(v_env_1988_, v___x_1989_);
v___x_1991_ = lean_st_ref_get(v___y_1983_);
v_toCold_1992_ = lean_ctor_get(v___y_1984_, 0);
v_mctx_1993_ = lean_ctor_get(v___x_1991_, 0);
lean_inc_ref(v_mctx_1993_);
lean_dec(v___x_1991_);
v_lctx_1994_ = lean_ctor_get(v___y_1982_, 2);
v_options_1995_ = lean_ctor_get(v_toCold_1992_, 2);
lean_inc_ref(v_options_1995_);
lean_inc_ref(v_lctx_1994_);
v___x_1996_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1996_, 0, v_env_1990_);
lean_ctor_set(v___x_1996_, 1, v_mctx_1993_);
lean_ctor_set(v___x_1996_, 2, v_lctx_1994_);
lean_ctor_set(v___x_1996_, 3, v_options_1995_);
v___x_1997_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v_msgData_1981_);
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1981_ = stack[0].m_obj;
lean_object* v___y_1982_ = stack[1].m_obj;
lean_object* v___y_1983_ = stack[2].m_obj;
lean_object* v___y_1984_ = stack[3].m_obj;
lean_object* v___y_1985_ = stack[4].m_obj;
lean_object* v_res_1999_;
v_res_1999_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(v_msgData_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
stack->m_obj
 = v_res_1999_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8___boxed(lean_object* v_msgData_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(v_msgData_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2006_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2007_; double v___x_2008_; 
v___x_2007_ = lean_unsigned_to_nat(0u);
v___x_2008_ = lean_float_of_nat(v___x_2007_);
return v___x_2008_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(lean_object* v_cls_2012_, lean_object* v_msg_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_ref_2019_; lean_object* v___x_2020_; lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2066_; 
v_ref_2019_ = lean_ctor_get(v___y_2016_, 2);
v___x_2020_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(v_msg_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2066_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2066_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v_traceState_2026_; lean_object* v_env_2027_; lean_object* v_nextMacroScope_2028_; lean_object* v_ngen_2029_; lean_object* v_auxDeclNGen_2030_; lean_object* v_cache_2031_; lean_object* v_recordedDeps_2032_; lean_object* v_messages_2033_; lean_object* v_infoState_2034_; lean_object* v_snapshotTasks_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2065_; 
v___x_2025_ = lean_st_ref_take(v___y_2017_);
v_traceState_2026_ = lean_ctor_get(v___x_2025_, 4);
v_env_2027_ = lean_ctor_get(v___x_2025_, 0);
v_nextMacroScope_2028_ = lean_ctor_get(v___x_2025_, 1);
v_ngen_2029_ = lean_ctor_get(v___x_2025_, 2);
v_auxDeclNGen_2030_ = lean_ctor_get(v___x_2025_, 3);
v_cache_2031_ = lean_ctor_get(v___x_2025_, 5);
v_recordedDeps_2032_ = lean_ctor_get(v___x_2025_, 6);
v_messages_2033_ = lean_ctor_get(v___x_2025_, 7);
v_infoState_2034_ = lean_ctor_get(v___x_2025_, 8);
v_snapshotTasks_2035_ = lean_ctor_get(v___x_2025_, 9);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2037_ = v___x_2025_;
v_isShared_2038_ = v_isSharedCheck_2065_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_snapshotTasks_2035_);
lean_inc(v_infoState_2034_);
lean_inc(v_messages_2033_);
lean_inc(v_recordedDeps_2032_);
lean_inc(v_cache_2031_);
lean_inc(v_traceState_2026_);
lean_inc(v_auxDeclNGen_2030_);
lean_inc(v_ngen_2029_);
lean_inc(v_nextMacroScope_2028_);
lean_inc(v_env_2027_);
lean_dec(v___x_2025_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2065_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
uint64_t v_tid_2039_; lean_object* v_traces_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2064_; 
v_tid_2039_ = lean_ctor_get_uint64(v_traceState_2026_, sizeof(void*)*1);
v_traces_2040_ = lean_ctor_get(v_traceState_2026_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_traceState_2026_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2042_ = v_traceState_2026_;
v_isShared_2043_ = v_isSharedCheck_2064_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_traces_2040_);
lean_dec(v_traceState_2026_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2064_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; double v___x_2046_; uint8_t v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0);
v___x_2047_ = 0;
v___x_2048_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1));
v___x_2049_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2049_, 0, v_cls_2012_);
lean_ctor_set(v___x_2049_, 1, v___x_2045_);
lean_ctor_set(v___x_2049_, 2, v___x_2048_);
lean_ctor_set_float(v___x_2049_, sizeof(void*)*3, v___x_2046_);
lean_ctor_set_float(v___x_2049_, sizeof(void*)*3 + 8, v___x_2046_);
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*3 + 16, v___x_2047_);
v___x_2050_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2));
v___x_2051_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2049_);
lean_ctor_set(v___x_2051_, 1, v_a_2021_);
lean_ctor_set(v___x_2051_, 2, v___x_2050_);
lean_inc(v_ref_2019_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v_ref_2019_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v___x_2053_ = l_Lean_PersistentArray_push___redArg(v_traces_2040_, v___x_2052_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2053_);
v___x_2055_ = v___x_2042_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2053_);
lean_ctor_set_uint64(v_reuseFailAlloc_2063_, sizeof(void*)*1, v_tid_2039_);
v___x_2055_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2057_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 4, v___x_2055_);
v___x_2057_ = v___x_2037_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_env_2027_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_nextMacroScope_2028_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v_ngen_2029_);
lean_ctor_set(v_reuseFailAlloc_2062_, 3, v_auxDeclNGen_2030_);
lean_ctor_set(v_reuseFailAlloc_2062_, 4, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2062_, 5, v_cache_2031_);
lean_ctor_set(v_reuseFailAlloc_2062_, 6, v_recordedDeps_2032_);
lean_ctor_set(v_reuseFailAlloc_2062_, 7, v_messages_2033_);
lean_ctor_set(v_reuseFailAlloc_2062_, 8, v_infoState_2034_);
lean_ctor_set(v_reuseFailAlloc_2062_, 9, v_snapshotTasks_2035_);
v___x_2057_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = lean_st_ref_put(v___y_2017_, v___x_2057_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2044_);
v___x_2060_ = v___x_2023_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2044_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2012_ = stack[0].m_obj;
lean_object* v_msg_2013_ = stack[1].m_obj;
lean_object* v___y_2014_ = stack[2].m_obj;
lean_object* v___y_2015_ = stack[3].m_obj;
lean_object* v___y_2016_ = stack[4].m_obj;
lean_object* v___y_2017_ = stack[5].m_obj;
lean_object* v_res_2067_;
v_res_2067_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v_cls_2012_, v_msg_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
stack->m_obj
 = v_res_2067_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___boxed(lean_object* v_cls_2068_, lean_object* v_msg_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v_cls_2068_, v_msg_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
return v_res_2075_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object* v_x_2076_, lean_object* v_x_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
if (lean_obj_tag(v_x_2076_) == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = l_List_reverse___redArg(v_x_2077_);
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
else
{
lean_object* v_head_2085_; lean_object* v_tail_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2104_; 
v_head_2085_ = lean_ctor_get(v_x_2076_, 0);
v_tail_2086_ = lean_ctor_get(v_x_2076_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_x_2076_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2088_ = v_x_2076_;
v_isShared_2089_ = v_isSharedCheck_2104_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_tail_2086_);
lean_inc(v_head_2085_);
lean_dec(v_x_2076_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2104_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; 
lean_inc(v___y_2081_);
lean_inc_ref(v___y_2080_);
lean_inc(v___y_2079_);
lean_inc_ref(v___y_2078_);
v___x_2090_ = lean_infer_type(v_head_2085_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2093_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 1, v_x_2077_);
lean_ctor_set(v___x_2088_, 0, v_a_2091_);
v___x_2093_ = v___x_2088_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2091_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_x_2077_);
v___x_2093_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
v_x_2076_ = v_tail_2086_;
v_x_2077_ = v___x_2093_;
goto _start;
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_del_object(v___x_2088_);
lean_dec(v_tail_2086_);
lean_dec(v_x_2077_);
v_a_2096_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2090_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2090_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2076_ = stack[0].m_obj;
lean_object* v_x_2077_ = stack[1].m_obj;
lean_object* v___y_2078_ = stack[2].m_obj;
lean_object* v___y_2079_ = stack[3].m_obj;
lean_object* v___y_2080_ = stack[4].m_obj;
lean_object* v___y_2081_ = stack[5].m_obj;
lean_object* v_res_2105_;
v_res_2105_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_x_2076_, v_x_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
stack->m_obj
 = v_res_2105_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(lean_object* v_x_2106_, lean_object* v_x_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_x_2106_, v_x_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
if (lean_obj_tag(v_a_2114_) == 0)
{
lean_object* v___x_2116_; 
v___x_2116_ = l_List_reverse___redArg(v_a_2115_);
return v___x_2116_;
}
else
{
lean_object* v_head_2117_; lean_object* v_tail_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2127_; 
v_head_2117_ = lean_ctor_get(v_a_2114_, 0);
v_tail_2118_ = lean_ctor_get(v_a_2114_, 1);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_a_2114_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2120_ = v_a_2114_;
v_isShared_2121_ = v_isSharedCheck_2127_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_tail_2118_);
lean_inc(v_head_2117_);
lean_dec(v_a_2114_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2127_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2122_ = l_Lean_MessageData_ofExpr(v_head_2117_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 1, v_a_2115_);
lean_ctor_set(v___x_2120_, 0, v___x_2122_);
v___x_2124_ = v___x_2120_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_a_2115_);
v___x_2124_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
v_a_2114_ = v_tail_2118_;
v_a_2115_ = v___x_2124_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__1));
v___x_2135_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__3));
v___x_2136_ = l_Lean_Name_append(v___x_2135_, v___x_2134_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__5));
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
return v___x_2139_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__7));
v___x_2142_ = l_Lean_stringToMessageData(v___x_2141_);
return v___x_2142_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object* v_e_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, uint8_t v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_st_ref_get(v_a_2145_);
v___x_2155_ = l_Lean_Meta_Canonicalizer_canon(v_e_2143_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2254_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2254_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2254_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___x_2172_; 
v___x_2172_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v___x_2154_, v_a_2156_);
lean_dec(v___x_2154_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_toCold_2173_; lean_object* v_options_2174_; lean_object* v_inheritedTraceOptions_2175_; uint8_t v_hasTrace_2176_; lean_object* v___x_2177_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; uint8_t v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; 
v_toCold_2173_ = lean_ctor_get(v_a_2151_, 0);
v_options_2174_ = lean_ctor_get(v_toCold_2173_, 2);
v_inheritedTraceOptions_2175_ = lean_ctor_get(v_toCold_2173_, 11);
v_hasTrace_2176_ = lean_ctor_get_uint8(v_options_2174_, sizeof(void*)*1);
v___x_2177_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__1));
if (v_hasTrace_2176_ == 0)
{
v___y_2179_ = v_a_2144_;
v___y_2180_ = v_a_2145_;
v___y_2181_ = v_a_2146_;
v___y_2182_ = v_a_2147_;
v___y_2183_ = v_a_2148_;
v___y_2184_ = v_a_2149_;
v___y_2185_ = v_a_2150_;
v___y_2186_ = v_a_2151_;
v___y_2187_ = v_a_2152_;
goto v___jp_2178_;
}
else
{
lean_object* v___x_2230_; uint8_t v___x_2231_; 
v___x_2230_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__4, &l_Lean_Elab_Tactic_Omega_lookup___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4);
v___x_2231_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2175_, v_options_2174_, v___x_2230_);
if (v___x_2231_ == 0)
{
v___y_2179_ = v_a_2144_;
v___y_2180_ = v_a_2145_;
v___y_2181_ = v_a_2146_;
v___y_2182_ = v_a_2147_;
v___y_2183_ = v_a_2148_;
v___y_2184_ = v_a_2149_;
v___y_2185_ = v_a_2150_;
v___y_2186_ = v_a_2151_;
v___y_2187_ = v_a_2152_;
goto v___jp_2178_;
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2232_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__8, &l_Lean_Elab_Tactic_Omega_lookup___closed__8_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8);
lean_inc(v_a_2156_);
v___x_2233_ = l_Lean_MessageData_ofExpr(v_a_2156_);
v___x_2234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2232_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v___x_2177_, v___x_2234_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_dec_ref_known(v___x_2235_, 1);
v___y_2179_ = v_a_2144_;
v___y_2180_ = v_a_2145_;
v___y_2181_ = v_a_2146_;
v___y_2182_ = v_a_2147_;
v___y_2183_ = v_a_2148_;
v___y_2184_ = v_a_2149_;
v___y_2185_ = v_a_2150_;
v___y_2186_ = v_a_2151_;
v___y_2187_ = v_a_2152_;
goto v___jp_2178_;
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_del_object(v___x_2158_);
lean_dec(v_a_2156_);
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
v___jp_2178_:
{
lean_object* v___x_2188_; 
lean_inc(v_a_2156_);
v___x_2188_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_a_2156_, v___y_2181_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_toCold_2189_; lean_object* v_options_2190_; uint8_t v_hasTrace_2191_; 
v_toCold_2189_ = lean_ctor_get(v___y_2186_, 0);
v_options_2190_ = lean_ctor_get(v_toCold_2189_, 2);
v_hasTrace_2191_ = lean_ctor_get_uint8(v_options_2190_, sizeof(void*)*1);
if (v_hasTrace_2191_ == 0)
{
lean_object* v_a_2192_; 
v_a_2192_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v___x_2188_, 1);
v___y_2161_ = v_a_2192_;
v___y_2162_ = v___y_2180_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2193_; lean_object* v_inheritedTraceOptions_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v_a_2193_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2188_, 1);
v_inheritedTraceOptions_2194_ = lean_ctor_get(v_toCold_2189_, 11);
v___x_2195_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__4, &l_Lean_Elab_Tactic_Omega_lookup___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4);
v___x_2196_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2194_, v_options_2190_, v___x_2195_);
if (v___x_2196_ == 0)
{
v___y_2161_ = v_a_2193_;
v___y_2162_ = v___y_2180_;
goto v___jp_2160_;
}
else
{
uint8_t v___x_2197_; 
v___x_2197_ = l_List_isEmpty___redArg(v_a_2193_);
if (v___x_2197_ == 0)
{
if (v___x_2196_ == 0)
{
v___y_2161_ = v_a_2193_;
v___y_2162_ = v___y_2180_;
goto v___jp_2160_;
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = lean_box(0);
lean_inc(v_a_2193_);
v___x_2199_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_a_2193_, v___x_2198_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2199_, 1);
v___x_2201_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__6, &l_Lean_Elab_Tactic_Omega_lookup___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6);
v___x_2202_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(v_a_2200_, v___x_2198_);
v___x_2203_ = l_Lean_MessageData_ofList(v___x_2202_);
v___x_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2201_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v___x_2177_, v___x_2204_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_dec_ref_known(v___x_2205_, 1);
v___y_2161_ = v_a_2193_;
v___y_2162_ = v___y_2180_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_a_2193_);
lean_del_object(v___x_2158_);
lean_dec(v_a_2156_);
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
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_a_2193_);
lean_del_object(v___x_2158_);
lean_dec(v_a_2156_);
v_a_2214_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2199_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2199_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
else
{
v___y_2161_ = v_a_2193_;
v___y_2162_ = v___y_2180_;
goto v___jp_2160_;
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_del_object(v___x_2158_);
lean_dec(v_a_2156_);
v_a_2222_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2188_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2188_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
else
{
lean_object* v_val_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2253_; 
lean_del_object(v___x_2158_);
lean_dec(v_a_2156_);
v_val_2244_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2246_ = v___x_2172_;
v_isShared_2247_ = v_isSharedCheck_2253_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_val_2244_);
lean_dec(v___x_2172_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2253_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2248_ = lean_box(0);
v___x_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2249_, 0, v_val_2244_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set_tag(v___x_2246_, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2249_);
v___x_2251_ = v___x_2246_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
v___jp_2160_:
{
lean_object* v___x_2163_; lean_object* v_size_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2163_ = lean_st_ref_take(v___y_2162_);
v_size_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc_n(v_size_2164_, 2);
v___x_2165_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v___x_2163_, v_a_2156_, v_size_2164_);
v___x_2166_ = lean_st_ref_put(v___y_2162_, v___x_2165_);
v___x_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___y_2161_);
v___x_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2168_, 0, v_size_2164_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2168_);
v___x_2170_ = v___x_2158_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v___x_2154_);
v_a_2255_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2155_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2155_);
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
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_lookup_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2143_ = stack[0].m_obj;
lean_object* v_a_2144_ = stack[1].m_obj;
lean_object* v_a_2145_ = stack[2].m_obj;
lean_object* v_a_2146_ = stack[3].m_obj;
uint8_t v_a_2147_ = stack[4].m_num;
lean_object* v_a_2148_ = stack[5].m_obj;
lean_object* v_a_2149_ = stack[6].m_obj;
lean_object* v_a_2150_ = stack[7].m_obj;
lean_object* v_a_2151_ = stack[8].m_obj;
lean_object* v_a_2152_ = stack[9].m_obj;
lean_object* v_res_2263_;
v_res_2263_ = l_Lean_Elab_Tactic_Omega_lookup(v_e_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
stack->m_obj
 = v_res_2263_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object* v_e_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
uint8_t v_a_boxed_2275_; lean_object* v_res_2276_; 
v_a_boxed_2275_ = lean_unbox(v_a_2268_);
v_res_2276_ = l_Lean_Elab_Tactic_Omega_lookup(v_e_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_boxed_2275_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2267_);
lean_dec(v_a_2266_);
lean_dec(v_a_2265_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(lean_object* v_00_u03b2_2277_, lean_object* v_m_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_2278_, v_a_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(lean_object* v_00_u03b2_2281_, lean_object* v_m_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(v_00_u03b2_2281_, v_m_2282_, v_a_2283_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v_m_2282_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object* v_00_u03b2_2285_, lean_object* v_m_2286_, lean_object* v_a_2287_, lean_object* v_b_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v_m_2286_, v_a_2287_, v_b_2288_);
return v___x_2289_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object* v_x_2290_, lean_object* v_x_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, uint8_t v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_x_2290_, v_x_2291_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
return v___x_2302_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2290_ = stack[0].m_obj;
lean_object* v_x_2291_ = stack[1].m_obj;
lean_object* v___y_2292_ = stack[2].m_obj;
lean_object* v___y_2293_ = stack[3].m_obj;
lean_object* v___y_2294_ = stack[4].m_obj;
uint8_t v___y_2295_ = stack[5].m_num;
lean_object* v___y_2296_ = stack[6].m_obj;
lean_object* v___y_2297_ = stack[7].m_obj;
lean_object* v___y_2298_ = stack[8].m_obj;
lean_object* v___y_2299_ = stack[9].m_obj;
lean_object* v___y_2300_ = stack[10].m_obj;
lean_object* v_res_2303_;
v_res_2303_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(v_x_2290_, v_x_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
stack->m_obj
 = v_res_2303_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(lean_object* v_x_2304_, lean_object* v_x_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
uint8_t v___y_34420__boxed_2316_; lean_object* v_res_2317_; 
v___y_34420__boxed_2316_ = lean_unbox(v___y_2309_);
v_res_2317_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(v_x_2304_, v_x_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_34420__boxed_2316_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec(v___y_2306_);
return v_res_2317_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(lean_object* v_cls_2318_, lean_object* v_msg_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, uint8_t v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v_cls_2318_, v_msg_2319_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
return v___x_2330_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2318_ = stack[0].m_obj;
lean_object* v_msg_2319_ = stack[1].m_obj;
lean_object* v___y_2320_ = stack[2].m_obj;
lean_object* v___y_2321_ = stack[3].m_obj;
lean_object* v___y_2322_ = stack[4].m_obj;
uint8_t v___y_2323_ = stack[5].m_num;
lean_object* v___y_2324_ = stack[6].m_obj;
lean_object* v___y_2325_ = stack[7].m_obj;
lean_object* v___y_2326_ = stack[8].m_obj;
lean_object* v___y_2327_ = stack[9].m_obj;
lean_object* v___y_2328_ = stack[10].m_obj;
lean_object* v_res_2331_;
v_res_2331_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(v_cls_2318_, v_msg_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
stack->m_obj
 = v_res_2331_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___boxed(lean_object* v_cls_2332_, lean_object* v_msg_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
uint8_t v___y_34481__boxed_2344_; lean_object* v_res_2345_; 
v___y_34481__boxed_2344_ = lean_unbox(v___y_2337_);
v_res_2345_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(v_cls_2332_, v_msg_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_34481__boxed_2344_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec(v___y_2334_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(lean_object* v_00_u03b2_2346_, lean_object* v_a_2347_, lean_object* v_x_2348_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_2347_, v_x_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2350_, lean_object* v_a_2351_, lean_object* v_x_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(v_00_u03b2_2350_, v_a_2351_, v_x_2352_);
lean_dec(v_x_2352_);
lean_dec_ref(v_a_2351_);
return v_res_2353_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(lean_object* v_00_u03b2_2354_, lean_object* v_a_2355_, lean_object* v_x_2356_){
_start:
{
uint8_t v___x_2357_; 
v___x_2357_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_2355_, v_x_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2355_ = stack[1].m_obj;
lean_object* v_x_2356_ = stack[2].m_obj;
uint8_t v_res_2358_;
v_res_2358_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(lean_box(0), v_a_2355_, v_x_2356_);
stack->m_num = v_res_2358_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2359_, lean_object* v_a_2360_, lean_object* v_x_2361_){
_start:
{
uint8_t v_res_2362_; lean_object* v_r_2363_; 
v_res_2362_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(v_00_u03b2_2359_, v_a_2360_, v_x_2361_);
lean_dec(v_x_2361_);
lean_dec_ref(v_a_2360_);
v_r_2363_ = lean_box(v_res_2362_);
return v_r_2363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3(lean_object* v_00_u03b2_2364_, lean_object* v_data_2365_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_data_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4(lean_object* v_00_u03b2_2367_, lean_object* v_a_2368_, lean_object* v_b_2369_, lean_object* v_x_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_2368_, v_b_2369_, v_x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2372_, lean_object* v_i_2373_, lean_object* v_source_2374_, lean_object* v_target_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(v_i_2373_, v_source_2374_, v_target_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(v_x_2378_, v_x_2379_);
return v___x_2380_;
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
