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
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Omega_lookup___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "New facts: "};
static const lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_lookup___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_lookup___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Omega_lookup___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "New atom: "};
static const lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_lookup___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_lookup___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(lean_object* v_x1_114_, lean_object* v_x2_115_){
_start:
{
lean_object* v_snd_116_; lean_object* v_snd_117_; uint8_t v___x_118_; 
v_snd_116_ = lean_ctor_get(v_x1_114_, 1);
v_snd_117_ = lean_ctor_get(v_x2_115_, 1);
v___x_118_ = lean_nat_dec_lt(v_snd_116_, v_snd_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(lean_object* v_x1_119_, lean_object* v_x2_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v_x1_119_, v_x2_120_);
lean_dec_ref(v_x2_120_);
lean_dec_ref(v_x1_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(lean_object* v_as_124_, lean_object* v_lo_125_, lean_object* v_hi_126_){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = lean_nat_dec_lt(v_lo_125_, v_hi_126_);
if (v___x_127_ == 0)
{
lean_dec(v_lo_125_);
return v_as_124_;
}
else
{
lean_object* v___f_128_; lean_object* v___x_129_; lean_object* v_fst_130_; lean_object* v_snd_131_; uint8_t v___x_132_; 
v___f_128_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___closed__0));
lean_inc(v_lo_125_);
v___x_129_ = l_Array_qpartition___redArg(v_as_124_, v___f_128_, v_lo_125_, v_hi_126_);
v_fst_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_fst_130_);
v_snd_131_ = lean_ctor_get(v___x_129_, 1);
lean_inc(v_snd_131_);
lean_dec_ref(v___x_129_);
v___x_132_ = lean_nat_dec_le(v_hi_126_, v_fst_130_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_snd_131_, v_lo_125_, v_fst_130_);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_add(v_fst_130_, v___x_134_);
lean_dec(v_fst_130_);
v_as_124_ = v___x_133_;
v_lo_125_ = v___x_135_;
goto _start;
}
else
{
lean_dec(v_fst_130_);
lean_dec(v_lo_125_);
return v_snd_131_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___boxed(lean_object* v_as_137_, lean_object* v_lo_138_, lean_object* v_hi_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_as_137_, v_lo_138_, v_hi_139_);
lean_dec(v_hi_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
return v_x_141_;
}
else
{
lean_object* v_key_143_; lean_object* v_value_144_; lean_object* v_tail_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_key_143_ = lean_ctor_get(v_x_142_, 0);
v_value_144_ = lean_ctor_get(v_x_142_, 1);
v_tail_145_ = lean_ctor_get(v_x_142_, 2);
lean_inc(v_value_144_);
lean_inc(v_key_143_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v_key_143_);
lean_ctor_set(v___x_146_, 1, v_value_144_);
v___x_147_ = lean_array_push(v_x_141_, v___x_146_);
v_x_141_ = v___x_147_;
v_x_142_ = v_tail_145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___boxed(lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(v_x_149_, v_x_150_);
lean_dec(v_x_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(lean_object* v_as_152_, size_t v_i_153_, size_t v_stop_154_, lean_object* v_b_155_){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = lean_usize_dec_eq(v_i_153_, v_stop_154_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; size_t v___x_159_; size_t v___x_160_; 
v___x_157_ = lean_array_uget_borrowed(v_as_152_, v_i_153_);
v___x_158_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(v_b_155_, v___x_157_);
v___x_159_ = ((size_t)1ULL);
v___x_160_ = lean_usize_add(v_i_153_, v___x_159_);
v_i_153_ = v___x_160_;
v_b_155_ = v___x_158_;
goto _start;
}
else
{
return v_b_155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3___boxed(lean_object* v_as_162_, lean_object* v_i_163_, lean_object* v_stop_164_, lean_object* v_b_165_){
_start:
{
size_t v_i_boxed_166_; size_t v_stop_boxed_167_; lean_object* v_res_168_; 
v_i_boxed_166_ = lean_unbox_usize(v_i_163_);
lean_dec(v_i_163_);
v_stop_boxed_167_ = lean_unbox_usize(v_stop_164_);
lean_dec(v_stop_164_);
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_as_162_, v_i_boxed_166_, v_stop_boxed_167_, v_b_165_);
lean_dec_ref(v_as_162_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(size_t v_sz_169_, size_t v_i_170_, lean_object* v_bs_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = lean_usize_dec_lt(v_i_170_, v_sz_169_);
if (v___x_172_ == 0)
{
return v_bs_171_;
}
else
{
lean_object* v_v_173_; lean_object* v_fst_174_; lean_object* v___x_175_; lean_object* v_bs_x27_176_; size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; 
v_v_173_ = lean_array_uget_borrowed(v_bs_171_, v_i_170_);
v_fst_174_ = lean_ctor_get(v_v_173_, 0);
lean_inc(v_fst_174_);
v___x_175_ = lean_unsigned_to_nat(0u);
v_bs_x27_176_ = lean_array_uset(v_bs_171_, v_i_170_, v___x_175_);
v___x_177_ = ((size_t)1ULL);
v___x_178_ = lean_usize_add(v_i_170_, v___x_177_);
v___x_179_ = lean_array_uset(v_bs_x27_176_, v_i_170_, v_fst_174_);
v_i_170_ = v___x_178_;
v_bs_171_ = v___x_179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(lean_object* v_sz_181_, lean_object* v_i_182_, lean_object* v_bs_183_){
_start:
{
size_t v_sz_boxed_184_; size_t v_i_boxed_185_; lean_object* v_res_186_; 
v_sz_boxed_184_ = lean_unbox_usize(v_sz_181_);
lean_dec(v_sz_181_);
v_i_boxed_185_ = lean_unbox_usize(v_i_182_);
lean_dec(v_i_182_);
v_res_186_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_boxed_184_, v_i_boxed_185_, v_bs_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg(lean_object* v_a_187_){
_start:
{
lean_object* v___x_189_; lean_object* v___y_191_; lean_object* v___y_197_; lean_object* v___y_198_; lean_object* v___y_199_; lean_object* v___y_200_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_209_; lean_object* v_size_216_; lean_object* v_buckets_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_189_ = lean_st_ref_get(v_a_187_);
v_size_216_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_size_216_);
v_buckets_217_ = lean_ctor_get(v___x_189_, 1);
lean_inc_ref(v_buckets_217_);
lean_dec(v___x_189_);
v___x_218_ = lean_mk_empty_array_with_capacity(v_size_216_);
lean_dec(v_size_216_);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_array_get_size(v_buckets_217_);
v___x_221_ = lean_nat_dec_lt(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_dec_ref(v_buckets_217_);
v___y_209_ = v___x_218_;
goto v___jp_208_;
}
else
{
uint8_t v___x_222_; 
v___x_222_ = lean_nat_dec_le(v___x_220_, v___x_220_);
if (v___x_222_ == 0)
{
if (v___x_221_ == 0)
{
lean_dec_ref(v_buckets_217_);
v___y_209_ = v___x_218_;
goto v___jp_208_;
}
else
{
size_t v___x_223_; size_t v___x_224_; lean_object* v___x_225_; 
v___x_223_ = ((size_t)0ULL);
v___x_224_ = lean_usize_of_nat(v___x_220_);
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_buckets_217_, v___x_223_, v___x_224_, v___x_218_);
lean_dec_ref(v_buckets_217_);
v___y_209_ = v___x_225_;
goto v___jp_208_;
}
}
else
{
size_t v___x_226_; size_t v___x_227_; lean_object* v___x_228_; 
v___x_226_ = ((size_t)0ULL);
v___x_227_ = lean_usize_of_nat(v___x_220_);
v___x_228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_buckets_217_, v___x_226_, v___x_227_, v___x_218_);
lean_dec_ref(v_buckets_217_);
v___y_209_ = v___x_228_;
goto v___jp_208_;
}
}
v___jp_190_:
{
size_t v_sz_192_; size_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_sz_192_ = lean_array_size(v___y_191_);
v___x_193_ = ((size_t)0ULL);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_192_, v___x_193_, v___y_191_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
v___jp_196_:
{
lean_object* v___x_201_; 
lean_dec(v___y_199_);
v___x_201_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v___y_198_, v___y_197_, v___y_200_);
lean_dec(v___y_200_);
v___y_191_ = v___x_201_;
goto v___jp_190_;
}
v___jp_202_:
{
uint8_t v___x_207_; 
v___x_207_ = lean_nat_dec_le(v___y_206_, v___y_203_);
if (v___x_207_ == 0)
{
lean_dec(v___y_203_);
lean_inc(v___y_206_);
v___y_197_ = v___y_206_;
v___y_198_ = v___y_204_;
v___y_199_ = v___y_205_;
v___y_200_ = v___y_206_;
goto v___jp_196_;
}
else
{
v___y_197_ = v___y_206_;
v___y_198_ = v___y_204_;
v___y_199_ = v___y_205_;
v___y_200_ = v___y_203_;
goto v___jp_196_;
}
}
v___jp_208_:
{
lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_210_ = lean_array_get_size(v___y_209_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_nat_dec_eq(v___x_210_, v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_sub(v___x_210_, v___x_213_);
v___x_215_ = lean_nat_dec_le(v___x_211_, v___x_214_);
if (v___x_215_ == 0)
{
lean_inc(v___x_214_);
v___y_203_ = v___x_214_;
v___y_204_ = v___y_209_;
v___y_205_ = v___x_210_;
v___y_206_ = v___x_214_;
goto v___jp_202_;
}
else
{
v___y_203_ = v___x_214_;
v___y_204_ = v___y_209_;
v___y_205_ = v___x_210_;
v___y_206_ = v___x_211_;
goto v___jp_202_;
}
}
else
{
v___y_191_ = v___y_209_;
goto v___jp_190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg___boxed(lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_229_);
lean_dec(v_a_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, uint8_t v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_233_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
uint8_t v_a_boxed_253_; lean_object* v_res_254_; 
v_a_boxed_253_ = lean_unbox(v_a_246_);
v_res_254_ = l_Lean_Elab_Tactic_Omega_atoms(v_a_243_, v_a_244_, v_a_245_, v_a_boxed_253_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec(v_a_243_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(lean_object* v_n_255_, lean_object* v_as_256_, lean_object* v_lo_257_, lean_object* v_hi_258_, lean_object* v_w_259_, lean_object* v_hlo_260_, lean_object* v_hhi_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_as_256_, v_lo_257_, v_hi_258_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(lean_object* v_n_263_, lean_object* v_as_264_, lean_object* v_lo_265_, lean_object* v_hi_266_, lean_object* v_w_267_, lean_object* v_hlo_268_, lean_object* v_hhi_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(v_n_263_, v_as_264_, v_lo_265_, v_hi_266_, v_w_267_, v_hlo_268_, v_hhi_269_);
lean_dec(v_hi_266_);
lean_dec(v_n_263_);
return v_res_270_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_box(0);
v___x_275_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1));
v___x_276_ = l_Lean_Expr_const___override(v___x_275_, v___x_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg(lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_283_; lean_object* v_a_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_283_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_277_);
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref(v___x_283_);
v___x_285_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_286_ = lean_array_to_list(v_a_284_);
v___x_287_ = l_Lean_Meta_mkListLit(v___x_285_, v___x_286_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___boxed(lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList(lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, uint8_t v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(v_a_296_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___boxed(lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
uint8_t v_a_boxed_316_; lean_object* v_res_317_; 
v_a_boxed_316_ = lean_unbox(v_a_309_);
v_res_317_ = l_Lean_Elab_Tactic_Omega_atomsList(v_a_306_, v_a_307_, v_a_308_, v_a_boxed_316_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec(v_a_306_);
return v_res_317_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = lean_box(0);
v___x_328_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4));
v___x_329_ = l_Lean_Expr_const___override(v___x_328_, v___x_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_346_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_346_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_346_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_346_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_341_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5, &l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5);
v___x_342_ = l_Lean_Expr_app___override(v___x_341_, v_a_337_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_342_);
v___x_344_ = v___x_339_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___boxed(lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs(lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, uint8_t v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_355_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
uint8_t v_a_boxed_375_; lean_object* v_res_376_; 
v_a_boxed_375_ = lean_unbox(v_a_368_);
v_res_376_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs(v_a_365_, v_a_366_, v_a_367_, v_a_boxed_375_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec(v_a_365_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg(lean_object* v_t_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, uint8_t v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_388_ = lean_st_ref_get(v_a_379_);
v___x_389_ = lean_st_ref_get(v_a_378_);
v___x_390_ = lean_box(v_a_381_);
lean_inc(v_a_386_);
lean_inc_ref(v_a_385_);
lean_inc(v_a_384_);
lean_inc_ref(v_a_383_);
lean_inc(v_a_382_);
lean_inc_ref(v_a_380_);
lean_inc(v_a_379_);
lean_inc(v_a_378_);
v___x_391_ = lean_apply_10(v_t_377_, v_a_378_, v_a_379_, v_a_380_, v___x_390_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, lean_box(0));
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_410_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_410_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_410_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_410_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_snd_396_; uint8_t v___x_397_; 
v_snd_396_ = lean_ctor_get(v_a_392_, 1);
v___x_397_ = lean_unbox(v_snd_396_);
if (v___x_397_ == 0)
{
lean_object* v_fst_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v_fst_398_ = lean_ctor_get(v_a_392_, 0);
lean_inc(v_fst_398_);
lean_dec(v_a_392_);
v___x_399_ = lean_st_ref_take(v_a_379_);
lean_dec(v___x_399_);
v___x_400_ = lean_st_ref_set(v_a_379_, v___x_388_);
v___x_401_ = lean_st_ref_take(v_a_378_);
lean_dec(v___x_401_);
v___x_402_ = lean_st_ref_set(v_a_378_, v___x_389_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v_fst_398_);
v___x_404_ = v___x_394_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_fst_398_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
else
{
lean_object* v_fst_406_; lean_object* v___x_408_; 
lean_dec(v___x_389_);
lean_dec(v___x_388_);
v_fst_406_ = lean_ctor_get(v_a_392_, 0);
lean_inc(v_fst_406_);
lean_dec(v_a_392_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v_fst_406_);
v___x_408_ = v___x_394_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_fst_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec(v___x_389_);
lean_dec(v___x_388_);
v_a_411_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_391_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_391_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg___boxed(lean_object* v_t_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
uint8_t v_a_boxed_430_; lean_object* v_res_431_; 
v_a_boxed_430_ = lean_unbox(v_a_423_);
v_res_431_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(v_t_419_, v_a_420_, v_a_421_, v_a_422_, v_a_boxed_430_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec(v_a_420_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen(lean_object* v_00_u03b1_432_, lean_object* v_t_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, uint8_t v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(v_t_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___boxed(lean_object* v_00_u03b1_445_, lean_object* v_t_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
uint8_t v_a_boxed_457_; lean_object* v_res_458_; 
v_a_boxed_457_ = lean_unbox(v_a_450_);
v_res_458_ = l_Lean_Elab_Tactic_Omega_commitWhen(v_00_u03b1_445_, v_t_446_, v_a_447_, v_a_448_, v_a_449_, v_a_boxed_457_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(lean_object* v_t_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, uint8_t v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_box(v___y_463_);
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_462_);
lean_inc(v___y_461_);
lean_inc(v___y_460_);
v___x_471_ = lean_apply_10(v_t_459_, v___y_460_, v___y_461_, v___y_462_, v___x_470_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, lean_box(0));
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_482_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_482_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_482_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_482_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_476_ = 0;
v___x_477_ = lean_box(v___x_476_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v_a_472_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_478_);
v___x_480_ = v___x_474_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_a_483_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_471_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_471_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed(lean_object* v_t_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
uint8_t v___y_657__boxed_502_; lean_object* v_res_503_; 
v___y_657__boxed_502_ = lean_unbox(v___y_495_);
v_res_503_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(v_t_491_, v___y_492_, v___y_493_, v___y_494_, v___y_657__boxed_502_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec(v___y_492_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(lean_object* v_t_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, uint8_t v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___f_515_; lean_object* v___x_516_; 
v___f_515_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_515_, 0, v_t_504_);
v___x_516_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(v___f_515_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___boxed(lean_object* v_t_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
uint8_t v_a_boxed_528_; lean_object* v_res_529_; 
v_a_boxed_528_ = lean_unbox(v_a_521_);
v_res_529_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(v_t_517_, v_a_518_, v_a_519_, v_a_520_, v_a_boxed_528_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec(v_a_518_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_object* v_00_u03b1_530_, lean_object* v_t_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, uint8_t v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(v_t_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(lean_object* v_00_u03b1_543_, lean_object* v_t_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
uint8_t v_a_boxed_555_; lean_object* v_res_556_; 
v_a_boxed_555_ = lean_unbox(v_a_548_);
v_res_556_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState(v_00_u03b1_543_, v_t_544_, v_a_545_, v_a_546_, v_a_547_, v_a_boxed_555_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec(v_a_545_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f(lean_object* v_n_559_){
_start:
{
lean_object* v___x_560_; lean_object* v_fst_561_; 
lean_inc_ref(v_n_559_);
v___x_560_ = l_Lean_Expr_getAppFnArgs(v_n_559_);
v_fst_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_fst_561_);
if (lean_obj_tag(v_fst_561_) == 1)
{
lean_object* v_pre_562_; 
v_pre_562_ = lean_ctor_get(v_fst_561_, 0);
lean_inc(v_pre_562_);
if (lean_obj_tag(v_pre_562_) == 1)
{
lean_object* v_pre_563_; 
v_pre_563_ = lean_ctor_get(v_pre_562_, 0);
if (lean_obj_tag(v_pre_563_) == 0)
{
lean_object* v_snd_564_; lean_object* v_str_565_; lean_object* v_str_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_snd_564_ = lean_ctor_get(v___x_560_, 1);
lean_inc(v_snd_564_);
lean_dec_ref(v___x_560_);
v_str_565_ = lean_ctor_get(v_fst_561_, 1);
lean_inc_ref(v_str_565_);
lean_dec_ref(v_fst_561_);
v_str_566_ = lean_ctor_get(v_pre_562_, 1);
lean_inc_ref(v_str_566_);
lean_dec_ref(v_pre_562_);
v___x_567_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_568_ = lean_string_dec_eq(v_str_566_, v___x_567_);
lean_dec_ref(v_str_566_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
lean_dec_ref(v_str_565_);
lean_dec(v_snd_564_);
v___x_569_ = l_Lean_Expr_nat_x3f(v_n_559_);
return v___x_569_;
}
else
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_571_ = lean_string_dec_eq(v_str_565_, v___x_570_);
lean_dec_ref(v_str_565_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
lean_dec(v_snd_564_);
v___x_572_ = l_Lean_Expr_nat_x3f(v_n_559_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_573_ = lean_array_get_size(v_snd_564_);
v___x_574_ = lean_unsigned_to_nat(3u);
v___x_575_ = lean_nat_dec_eq(v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
lean_dec(v_snd_564_);
v___x_576_ = l_Lean_Expr_nat_x3f(v_n_559_);
return v___x_576_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec_ref(v_n_559_);
v___x_577_ = lean_unsigned_to_nat(2u);
v___x_578_ = lean_array_fget(v_snd_564_, v___x_577_);
lean_dec(v_snd_564_);
v___x_579_ = l_Lean_Expr_nat_x3f(v___x_578_);
return v___x_579_;
}
}
}
}
else
{
lean_object* v___x_580_; 
lean_dec_ref(v_pre_562_);
lean_dec_ref(v_fst_561_);
lean_dec_ref(v___x_560_);
v___x_580_ = l_Lean_Expr_nat_x3f(v_n_559_);
return v___x_580_;
}
}
else
{
lean_object* v___x_581_; 
lean_dec(v_pre_562_);
lean_dec_ref(v_fst_561_);
lean_dec_ref(v___x_560_);
v___x_581_ = l_Lean_Expr_nat_x3f(v_n_559_);
return v___x_581_;
}
}
else
{
lean_object* v___x_582_; 
lean_dec(v_fst_561_);
lean_dec_ref(v___x_560_);
v___x_582_ = l_Lean_Expr_nat_x3f(v_n_559_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_Tactic_Omega_intCast_x3f_spec__0(lean_object* v_a_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = lean_nat_to_int(v_a_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_intCast_x3f(lean_object* v_n_585_){
_start:
{
lean_object* v___x_586_; lean_object* v_fst_587_; 
lean_inc_ref(v_n_585_);
v___x_586_ = l_Lean_Expr_getAppFnArgs(v_n_585_);
v_fst_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_fst_587_);
if (lean_obj_tag(v_fst_587_) == 1)
{
lean_object* v_pre_588_; 
v_pre_588_ = lean_ctor_get(v_fst_587_, 0);
lean_inc(v_pre_588_);
if (lean_obj_tag(v_pre_588_) == 1)
{
lean_object* v_pre_589_; 
v_pre_589_ = lean_ctor_get(v_pre_588_, 0);
if (lean_obj_tag(v_pre_589_) == 0)
{
lean_object* v_snd_590_; lean_object* v_str_591_; lean_object* v_str_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_snd_590_ = lean_ctor_get(v___x_586_, 1);
lean_inc(v_snd_590_);
lean_dec_ref(v___x_586_);
v_str_591_ = lean_ctor_get(v_fst_587_, 1);
lean_inc_ref(v_str_591_);
lean_dec_ref(v_fst_587_);
v_str_592_ = lean_ctor_get(v_pre_588_, 1);
lean_inc_ref(v_str_592_);
lean_dec_ref(v_pre_588_);
v___x_593_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_594_ = lean_string_dec_eq(v_str_592_, v___x_593_);
lean_dec_ref(v_str_592_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
lean_dec_ref(v_str_591_);
lean_dec(v_snd_590_);
v___x_595_ = l_Lean_Expr_int_x3f(v_n_585_);
return v___x_595_;
}
else
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_597_ = lean_string_dec_eq(v_str_591_, v___x_596_);
lean_dec_ref(v_str_591_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
lean_dec(v_snd_590_);
v___x_598_ = l_Lean_Expr_int_x3f(v_n_585_);
return v___x_598_;
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_599_ = lean_array_get_size(v_snd_590_);
v___x_600_ = lean_unsigned_to_nat(3u);
v___x_601_ = lean_nat_dec_eq(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_dec(v_snd_590_);
v___x_602_ = l_Lean_Expr_int_x3f(v_n_585_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec_ref(v_n_585_);
v___x_603_ = lean_unsigned_to_nat(2u);
v___x_604_ = lean_array_fget(v_snd_590_, v___x_603_);
lean_dec(v_snd_590_);
v___x_605_ = l_Lean_Expr_nat_x3f(v___x_604_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v___x_606_; 
v___x_606_ = lean_box(0);
return v___x_606_;
}
else
{
lean_object* v_val_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_615_; 
v_val_607_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_615_ == 0)
{
v___x_609_ = v___x_605_;
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_val_607_);
lean_dec(v___x_605_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_nat_to_int(v_val_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_616_; 
lean_dec_ref(v_pre_588_);
lean_dec_ref(v_fst_587_);
lean_dec_ref(v___x_586_);
v___x_616_ = l_Lean_Expr_int_x3f(v_n_585_);
return v___x_616_;
}
}
else
{
lean_object* v___x_617_; 
lean_dec(v_pre_588_);
lean_dec_ref(v_fst_587_);
lean_dec_ref(v___x_586_);
v___x_617_ = l_Lean_Expr_int_x3f(v_n_585_);
return v___x_617_;
}
}
else
{
lean_object* v___x_618_; 
lean_dec(v_fst_587_);
lean_dec_ref(v___x_586_);
v___x_618_ = l_Lean_Expr_int_x3f(v_n_585_);
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f(lean_object* v_e_634_){
_start:
{
lean_object* v___x_635_; lean_object* v_fst_636_; 
lean_inc_ref(v_e_634_);
v___x_635_ = l_Lean_Expr_getAppFnArgs(v_e_634_);
v_fst_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_fst_636_);
if (lean_obj_tag(v_fst_636_) == 1)
{
lean_object* v_pre_637_; 
v_pre_637_ = lean_ctor_get(v_fst_636_, 0);
lean_inc(v_pre_637_);
if (lean_obj_tag(v_pre_637_) == 1)
{
lean_object* v_pre_638_; 
v_pre_638_ = lean_ctor_get(v_pre_637_, 0);
if (lean_obj_tag(v_pre_638_) == 0)
{
lean_object* v_snd_639_; lean_object* v_str_640_; lean_object* v_str_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_snd_639_ = lean_ctor_get(v___x_635_, 1);
lean_inc(v_snd_639_);
lean_dec_ref(v___x_635_);
v_str_640_ = lean_ctor_get(v_fst_636_, 1);
lean_inc_ref(v_str_640_);
lean_dec_ref(v_fst_636_);
v_str_641_ = lean_ctor_get(v_pre_637_, 1);
lean_inc_ref(v_str_641_);
lean_dec_ref(v_pre_637_);
v___x_642_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_643_ = lean_string_dec_eq(v_str_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0));
v___x_645_ = lean_string_dec_eq(v_str_641_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1));
v___x_647_ = lean_string_dec_eq(v_str_641_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2));
v___x_649_ = lean_string_dec_eq(v_str_641_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3));
v___x_651_ = lean_string_dec_eq(v_str_641_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4));
v___x_653_ = lean_string_dec_eq(v_str_641_, v___x_652_);
lean_dec_ref(v_str_641_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec_ref(v_str_640_);
lean_dec(v_snd_639_);
v___x_654_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_656_ = lean_string_dec_eq(v_str_640_, v___x_655_);
lean_dec_ref(v_str_640_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
lean_dec(v_snd_639_);
v___x_657_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_array_get_size(v_snd_639_);
v___x_659_ = lean_unsigned_to_nat(6u);
v___x_660_ = lean_nat_dec_eq(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_dec(v_snd_639_);
v___x_661_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_661_;
}
else
{
lean_object* v___f_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec_ref(v_e_634_);
v___f_662_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6));
v___x_663_ = lean_unsigned_to_nat(4u);
v___x_664_ = lean_array_fget(v_snd_639_, v___x_663_);
v___x_665_ = lean_unsigned_to_nat(5u);
v___x_666_ = lean_array_fget(v_snd_639_, v___x_665_);
lean_dec(v_snd_639_);
v___x_667_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_662_, v___x_664_, v___x_666_);
return v___x_667_;
}
}
}
}
else
{
lean_object* v___x_668_; uint8_t v___x_669_; 
lean_dec_ref(v_str_641_);
v___x_668_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7));
v___x_669_ = lean_string_dec_eq(v_str_640_, v___x_668_);
lean_dec_ref(v_str_640_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v_snd_639_);
v___x_670_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = lean_array_get_size(v_snd_639_);
v___x_672_ = lean_unsigned_to_nat(6u);
v___x_673_ = lean_nat_dec_eq(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_dec(v_snd_639_);
v___x_674_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_674_;
}
else
{
lean_object* v___f_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec_ref(v_e_634_);
v___f_675_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8));
v___x_676_ = lean_unsigned_to_nat(4u);
v___x_677_ = lean_array_fget(v_snd_639_, v___x_676_);
v___x_678_ = lean_unsigned_to_nat(5u);
v___x_679_ = lean_array_fget(v_snd_639_, v___x_678_);
lean_dec(v_snd_639_);
v___x_680_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_675_, v___x_677_, v___x_679_);
return v___x_680_;
}
}
}
}
else
{
lean_object* v___x_681_; uint8_t v___x_682_; 
lean_dec_ref(v_str_641_);
v___x_681_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9));
v___x_682_ = lean_string_dec_eq(v_str_640_, v___x_681_);
lean_dec_ref(v_str_640_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
lean_dec(v_snd_639_);
v___x_683_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_683_;
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_684_ = lean_array_get_size(v_snd_639_);
v___x_685_ = lean_unsigned_to_nat(6u);
v___x_686_ = lean_nat_dec_eq(v___x_684_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
lean_dec(v_snd_639_);
v___x_687_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_687_;
}
else
{
lean_object* v___f_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec_ref(v_e_634_);
v___f_688_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10));
v___x_689_ = lean_unsigned_to_nat(4u);
v___x_690_ = lean_array_fget(v_snd_639_, v___x_689_);
v___x_691_ = lean_unsigned_to_nat(5u);
v___x_692_ = lean_array_fget(v_snd_639_, v___x_691_);
lean_dec(v_snd_639_);
v___x_693_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_688_, v___x_690_, v___x_692_);
return v___x_693_;
}
}
}
}
else
{
lean_object* v___x_694_; uint8_t v___x_695_; 
lean_dec_ref(v_str_641_);
v___x_694_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11));
v___x_695_ = lean_string_dec_eq(v_str_640_, v___x_694_);
lean_dec_ref(v_str_640_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
lean_dec(v_snd_639_);
v___x_696_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_696_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_697_ = lean_array_get_size(v_snd_639_);
v___x_698_ = lean_unsigned_to_nat(6u);
v___x_699_ = lean_nat_dec_eq(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
lean_dec(v_snd_639_);
v___x_700_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_700_;
}
else
{
lean_object* v___f_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec_ref(v_e_634_);
v___f_701_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12));
v___x_702_ = lean_unsigned_to_nat(4u);
v___x_703_ = lean_array_fget(v_snd_639_, v___x_702_);
v___x_704_ = lean_unsigned_to_nat(5u);
v___x_705_ = lean_array_fget(v_snd_639_, v___x_704_);
lean_dec(v_snd_639_);
v___x_706_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_701_, v___x_703_, v___x_705_);
return v___x_706_;
}
}
}
}
else
{
lean_object* v___x_707_; uint8_t v___x_708_; 
lean_dec_ref(v_str_641_);
v___x_707_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13));
v___x_708_ = lean_string_dec_eq(v_str_640_, v___x_707_);
lean_dec_ref(v_str_640_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
lean_dec(v_snd_639_);
v___x_709_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_710_ = lean_array_get_size(v_snd_639_);
v___x_711_ = lean_unsigned_to_nat(6u);
v___x_712_ = lean_nat_dec_eq(v___x_710_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_dec(v_snd_639_);
v___x_713_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_713_;
}
else
{
lean_object* v___f_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec_ref(v_e_634_);
v___f_714_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14));
v___x_715_ = lean_unsigned_to_nat(4u);
v___x_716_ = lean_array_fget(v_snd_639_, v___x_715_);
v___x_717_ = lean_unsigned_to_nat(5u);
v___x_718_ = lean_array_fget(v_snd_639_, v___x_717_);
lean_dec(v_snd_639_);
v___x_719_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_714_, v___x_716_, v___x_718_);
return v___x_719_;
}
}
}
}
else
{
lean_object* v___x_720_; uint8_t v___x_721_; 
lean_dec_ref(v_str_641_);
v___x_720_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_721_ = lean_string_dec_eq(v_str_640_, v___x_720_);
lean_dec_ref(v_str_640_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec(v_snd_639_);
v___x_722_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_722_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_723_ = lean_array_get_size(v_snd_639_);
v___x_724_ = lean_unsigned_to_nat(3u);
v___x_725_ = lean_nat_dec_eq(v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec(v_snd_639_);
v___x_726_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec_ref(v_e_634_);
v___x_727_ = lean_unsigned_to_nat(2u);
v___x_728_ = lean_array_fget(v_snd_639_, v___x_727_);
lean_dec(v_snd_639_);
v_e_634_ = v___x_728_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_730_; 
lean_dec_ref(v_pre_637_);
lean_dec_ref(v_fst_636_);
lean_dec_ref(v___x_635_);
v___x_730_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_730_;
}
}
else
{
lean_object* v___x_731_; 
lean_dec(v_pre_637_);
lean_dec_ref(v_fst_636_);
lean_dec_ref(v___x_635_);
v___x_731_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_731_;
}
}
else
{
lean_object* v___x_732_; 
lean_dec(v_fst_636_);
lean_dec_ref(v___x_635_);
v___x_732_ = l_Lean_Expr_nat_x3f(v_e_634_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(lean_object* v_f_733_, lean_object* v_x_734_, lean_object* v_y_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_x_734_);
if (lean_obj_tag(v___x_736_) == 1)
{
lean_object* v_val_737_; lean_object* v___x_738_; 
v_val_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_val_737_);
lean_dec_ref(v___x_736_);
v___x_738_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_y_735_);
if (lean_obj_tag(v___x_738_) == 1)
{
lean_object* v_val_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_747_; 
v_val_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_747_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_val_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_apply_2(v_f_733_, v_val_737_, v_val_739_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_743_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v___x_748_; 
lean_dec(v___x_738_);
lean_dec(v_val_737_);
lean_dec_ref(v_f_733_);
v___x_748_ = lean_box(0);
return v___x_748_;
}
}
else
{
lean_object* v___x_749_; 
lean_dec(v___x_736_);
lean_dec_ref(v_y_735_);
lean_dec_ref(v_f_733_);
v___x_749_ = lean_box(0);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f(lean_object* v_e_754_){
_start:
{
lean_object* v___x_755_; lean_object* v_fst_756_; 
lean_inc_ref(v_e_754_);
v___x_755_ = l_Lean_Expr_getAppFnArgs(v_e_754_);
v_fst_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_fst_756_);
if (lean_obj_tag(v_fst_756_) == 1)
{
lean_object* v_pre_757_; 
v_pre_757_ = lean_ctor_get(v_fst_756_, 0);
lean_inc(v_pre_757_);
if (lean_obj_tag(v_pre_757_) == 1)
{
lean_object* v_pre_758_; 
v_pre_758_ = lean_ctor_get(v_pre_757_, 0);
if (lean_obj_tag(v_pre_758_) == 0)
{
lean_object* v_snd_759_; lean_object* v_str_760_; lean_object* v_str_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_snd_759_ = lean_ctor_get(v___x_755_, 1);
lean_inc(v_snd_759_);
lean_dec_ref(v___x_755_);
v_str_760_ = lean_ctor_get(v_fst_756_, 1);
lean_inc_ref(v_str_760_);
lean_dec_ref(v_fst_756_);
v_str_761_ = lean_ctor_get(v_pre_757_, 1);
lean_inc_ref(v_str_761_);
lean_dec_ref(v_pre_757_);
v___x_762_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_763_ = lean_string_dec_eq(v_str_761_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0));
v___x_765_ = lean_string_dec_eq(v_str_761_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1));
v___x_767_ = lean_string_dec_eq(v_str_761_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2));
v___x_769_ = lean_string_dec_eq(v_str_761_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3));
v___x_771_ = lean_string_dec_eq(v_str_761_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4));
v___x_773_ = lean_string_dec_eq(v_str_761_, v___x_772_);
lean_dec_ref(v_str_761_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; 
lean_dec_ref(v_str_760_);
lean_dec(v_snd_759_);
v___x_774_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_774_;
}
else
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_776_ = lean_string_dec_eq(v_str_760_, v___x_775_);
lean_dec_ref(v_str_760_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
lean_dec(v_snd_759_);
v___x_777_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_777_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = lean_array_get_size(v_snd_759_);
v___x_779_ = lean_unsigned_to_nat(6u);
v___x_780_ = lean_nat_dec_eq(v___x_778_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_dec(v_snd_759_);
v___x_781_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_781_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref(v_e_754_);
v___x_782_ = lean_unsigned_to_nat(4u);
v___x_783_ = lean_array_fget_borrowed(v_snd_759_, v___x_782_);
lean_inc(v___x_783_);
v___x_784_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v___x_783_);
if (lean_obj_tag(v___x_784_) == 1)
{
lean_object* v_val_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_val_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_val_785_);
lean_dec_ref(v___x_784_);
v___x_786_ = lean_unsigned_to_nat(5u);
v___x_787_ = lean_array_fget(v_snd_759_, v___x_786_);
lean_dec(v_snd_759_);
v___x_788_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_787_);
if (lean_obj_tag(v___x_788_) == 1)
{
lean_object* v_val_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_val_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_797_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_val_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = l_Int_pow(v_val_785_, v_val_789_);
lean_dec(v_val_789_);
lean_dec(v_val_785_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_object* v___x_798_; 
lean_dec(v___x_788_);
lean_dec(v_val_785_);
v___x_798_ = lean_box(0);
return v___x_798_;
}
}
else
{
lean_object* v___x_799_; 
lean_dec(v___x_784_);
lean_dec(v_snd_759_);
v___x_799_ = lean_box(0);
return v___x_799_;
}
}
}
}
}
else
{
lean_object* v___x_800_; uint8_t v___x_801_; 
lean_dec_ref(v_str_761_);
v___x_800_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7));
v___x_801_ = lean_string_dec_eq(v_str_760_, v___x_800_);
lean_dec_ref(v_str_760_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; 
lean_dec(v_snd_759_);
v___x_802_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_802_;
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_803_ = lean_array_get_size(v_snd_759_);
v___x_804_ = lean_unsigned_to_nat(6u);
v___x_805_ = lean_nat_dec_eq(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec(v_snd_759_);
v___x_806_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_806_;
}
else
{
lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec_ref(v_e_754_);
v___f_807_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0));
v___x_808_ = lean_unsigned_to_nat(4u);
v___x_809_ = lean_array_fget(v_snd_759_, v___x_808_);
v___x_810_ = lean_unsigned_to_nat(5u);
v___x_811_ = lean_array_fget(v_snd_759_, v___x_810_);
lean_dec(v_snd_759_);
v___x_812_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_807_, v___x_809_, v___x_811_);
return v___x_812_;
}
}
}
}
else
{
lean_object* v___x_813_; uint8_t v___x_814_; 
lean_dec_ref(v_str_761_);
v___x_813_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9));
v___x_814_ = lean_string_dec_eq(v_str_760_, v___x_813_);
lean_dec_ref(v_str_760_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
lean_dec(v_snd_759_);
v___x_815_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_815_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_816_ = lean_array_get_size(v_snd_759_);
v___x_817_ = lean_unsigned_to_nat(6u);
v___x_818_ = lean_nat_dec_eq(v___x_816_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; 
lean_dec(v_snd_759_);
v___x_819_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_819_;
}
else
{
lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec_ref(v_e_754_);
v___f_820_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1));
v___x_821_ = lean_unsigned_to_nat(4u);
v___x_822_ = lean_array_fget(v_snd_759_, v___x_821_);
v___x_823_ = lean_unsigned_to_nat(5u);
v___x_824_ = lean_array_fget(v_snd_759_, v___x_823_);
lean_dec(v_snd_759_);
v___x_825_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_820_, v___x_822_, v___x_824_);
return v___x_825_;
}
}
}
}
else
{
lean_object* v___x_826_; uint8_t v___x_827_; 
lean_dec_ref(v_str_761_);
v___x_826_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11));
v___x_827_ = lean_string_dec_eq(v_str_760_, v___x_826_);
lean_dec_ref(v_str_760_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
lean_dec(v_snd_759_);
v___x_828_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_828_;
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_829_ = lean_array_get_size(v_snd_759_);
v___x_830_ = lean_unsigned_to_nat(6u);
v___x_831_ = lean_nat_dec_eq(v___x_829_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
lean_dec(v_snd_759_);
v___x_832_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_832_;
}
else
{
lean_object* v___f_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v_e_754_);
v___f_833_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2));
v___x_834_ = lean_unsigned_to_nat(4u);
v___x_835_ = lean_array_fget(v_snd_759_, v___x_834_);
v___x_836_ = lean_unsigned_to_nat(5u);
v___x_837_ = lean_array_fget(v_snd_759_, v___x_836_);
lean_dec(v_snd_759_);
v___x_838_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_833_, v___x_835_, v___x_837_);
return v___x_838_;
}
}
}
}
else
{
lean_object* v___x_839_; uint8_t v___x_840_; 
lean_dec_ref(v_str_761_);
v___x_839_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13));
v___x_840_ = lean_string_dec_eq(v_str_760_, v___x_839_);
lean_dec_ref(v_str_760_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec(v_snd_759_);
v___x_841_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_841_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_842_ = lean_array_get_size(v_snd_759_);
v___x_843_ = lean_unsigned_to_nat(6u);
v___x_844_ = lean_nat_dec_eq(v___x_842_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
lean_dec(v_snd_759_);
v___x_845_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_845_;
}
else
{
lean_object* v___f_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref(v_e_754_);
v___f_846_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3));
v___x_847_ = lean_unsigned_to_nat(4u);
v___x_848_ = lean_array_fget(v_snd_759_, v___x_847_);
v___x_849_ = lean_unsigned_to_nat(5u);
v___x_850_ = lean_array_fget(v_snd_759_, v___x_849_);
lean_dec(v_snd_759_);
v___x_851_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_846_, v___x_848_, v___x_850_);
return v___x_851_;
}
}
}
}
else
{
lean_object* v___x_852_; uint8_t v___x_853_; 
lean_dec_ref(v_str_761_);
v___x_852_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_853_ = lean_string_dec_eq(v_str_760_, v___x_852_);
lean_dec_ref(v_str_760_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; 
lean_dec(v_snd_759_);
v___x_854_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_854_;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_855_ = lean_array_get_size(v_snd_759_);
v___x_856_ = lean_unsigned_to_nat(3u);
v___x_857_ = lean_nat_dec_eq(v___x_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; 
lean_dec(v_snd_759_);
v___x_858_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_858_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec_ref(v_e_754_);
v___x_859_ = lean_unsigned_to_nat(2u);
v___x_860_ = lean_array_fget(v_snd_759_, v___x_859_);
lean_dec(v_snd_759_);
v___x_861_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_860_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v___x_862_; 
v___x_862_ = lean_box(0);
return v___x_862_;
}
else
{
lean_object* v_val_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_871_; 
v_val_863_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_871_ == 0)
{
v___x_865_ = v___x_861_;
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_val_863_);
lean_dec(v___x_861_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_867_ = lean_nat_to_int(v_val_863_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_867_);
v___x_869_ = v___x_865_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_872_; 
lean_dec_ref(v_pre_757_);
lean_dec_ref(v_fst_756_);
lean_dec_ref(v___x_755_);
v___x_872_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_872_;
}
}
else
{
lean_object* v___x_873_; 
lean_dec_ref(v_fst_756_);
lean_dec(v_pre_757_);
lean_dec_ref(v___x_755_);
v___x_873_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_873_;
}
}
else
{
lean_object* v___x_874_; 
lean_dec(v_fst_756_);
lean_dec_ref(v___x_755_);
v___x_874_ = l_Lean_Expr_int_x3f(v_e_754_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object* v_f_875_, lean_object* v_x_876_, lean_object* v_y_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_x_876_);
if (lean_obj_tag(v___x_878_) == 1)
{
lean_object* v_val_879_; lean_object* v___x_880_; 
v_val_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_val_879_);
lean_dec_ref(v___x_878_);
v___x_880_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_y_877_);
if (lean_obj_tag(v___x_880_) == 1)
{
lean_object* v_val_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_889_; 
v_val_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_889_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_val_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = lean_apply_2(v_f_875_, v_val_879_, v_val_881_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_885_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
else
{
lean_object* v___x_890_; 
lean_dec(v___x_880_);
lean_dec(v_val_879_);
lean_dec_ref(v_f_875_);
v___x_890_ = lean_box(0);
return v___x_890_;
}
}
else
{
lean_object* v___x_891_; 
lean_dec(v___x_878_);
lean_dec_ref(v_y_877_);
lean_dec_ref(v_f_875_);
v___x_891_ = lean_box(0);
return v___x_891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object* v_a_892_, lean_object* v_b_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v___x_899_; 
lean_inc_ref(v_a_892_);
v___x_899_ = l_Lean_Meta_mkEqRefl(v_a_892_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref(v___x_899_);
v___x_901_ = l_Lean_Meta_mkEq(v_a_892_, v_b_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_910_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_910_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_910_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_910_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = l_Lean_Meta_mkExpectedPropHint(v_a_900_, v_a_902_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_906_);
v___x_908_ = v___x_904_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
else
{
lean_dec(v_a_900_);
return v___x_901_;
}
}
else
{
lean_dec_ref(v_b_893_);
lean_dec_ref(v_a_892_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType___boxed(lean_object* v_a_911_, lean_object* v_b_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v_a_911_, v_b_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
return v_res_918_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(lean_object* v_a_919_, lean_object* v_x_920_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
uint8_t v___x_921_; 
v___x_921_ = 0;
return v___x_921_;
}
else
{
lean_object* v_head_922_; lean_object* v_tail_923_; uint8_t v___x_924_; 
v_head_922_ = lean_ctor_get(v_x_920_, 0);
v_tail_923_ = lean_ctor_get(v_x_920_, 1);
v___x_924_ = lean_expr_eqv(v_a_919_, v_head_922_);
if (v___x_924_ == 0)
{
v_x_920_ = v_tail_923_;
goto _start;
}
else
{
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0___boxed(lean_object* v_a_926_, lean_object* v_x_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v_a_926_, v_x_927_);
lean_dec(v_x_927_);
lean_dec_ref(v_a_926_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = lean_box(0);
v___x_939_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5));
v___x_940_ = l_Lean_Expr_const___override(v___x_939_, v___x_938_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = lean_box(0);
v___x_946_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8));
v___x_947_ = l_Lean_Expr_const___override(v___x_946_, v___x_945_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = lean_box(0);
v___x_954_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12));
v___x_955_ = l_Lean_Expr_const___override(v___x_954_, v___x_953_);
return v___x_955_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = lean_box(0);
v___x_961_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15));
v___x_962_ = l_Lean_Expr_const___override(v___x_961_, v___x_960_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = l_Lean_Level_ofNat(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_unsigned_to_nat(0u);
v___x_983_ = l_Lean_mkNatLit(v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_nat_to_int(v___x_1006_);
return v___x_1007_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39(void){
_start:
{
lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
v___x_1009_ = lean_int_dec_le(v___x_1008_, v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
v___x_1020_ = lean_int_neg(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45);
v___x_1022_ = l_Int_toNat(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46);
v___x_1024_ = l_Lean_instToExprInt_mkNat(v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
v___x_1026_ = l_Int_toNat(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48);
v___x_1028_ = l_Lean_instToExprInt_mkNat(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23);
v___x_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_1029_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1033_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22));
v___x_1034_ = l_Lean_Expr_const___override(v___x_1033_, v___x_1032_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53));
v___x_1041_ = l_Lean_Expr_const___override(v___x_1040_, v___x_1039_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = lean_box(0);
v___x_1049_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56));
v___x_1050_ = l_Lean_Expr_const___override(v___x_1049_, v___x_1048_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = lean_box(0);
v___x_1052_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33));
v___x_1053_ = l_Lean_Expr_const___override(v___x_1052_, v___x_1051_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35));
v___x_1056_ = l_Lean_Expr_const___override(v___x_1055_, v___x_1054_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37));
v___x_1059_ = l_Lean_Expr_const___override(v___x_1058_, v___x_1057_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1061_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42));
v___x_1062_ = l_Lean_Expr_const___override(v___x_1061_, v___x_1060_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44));
v___x_1065_ = l_Lean_Expr_const___override(v___x_1064_, v___x_1063_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1066_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47);
v___x_1067_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62);
v___x_1068_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1069_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61);
v___x_1070_ = l_Lean_mkApp3(v___x_1069_, v___x_1068_, v___x_1067_, v___x_1066_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_unsigned_to_nat(1u);
v___x_1075_ = l_Lean_Level_ofNat(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66);
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1076_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67);
v___x_1080_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65));
v___x_1081_ = l_Lean_Expr_const___override(v___x_1080_, v___x_1079_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = lean_box(0);
v___x_1087_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70));
v___x_1088_ = l_Lean_Expr_const___override(v___x_1087_, v___x_1086_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = lean_box(0);
v___x_1094_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73));
v___x_1095_ = l_Lean_Expr_const___override(v___x_1094_, v___x_1093_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93));
v___x_1136_ = l_Lean_Expr_const___override(v___x_1135_, v___x_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(lean_object* v_e_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___x_1162_; lean_object* v_fst_1163_; 
v___x_1162_ = l_Lean_Expr_getAppFnArgs(v_e_1137_);
v_fst_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_fst_1163_);
if (lean_obj_tag(v_fst_1163_) == 1)
{
lean_object* v_pre_1164_; 
v_pre_1164_ = lean_ctor_get(v_fst_1163_, 0);
switch(lean_obj_tag(v_pre_1164_))
{
case 1:
{
lean_object* v_pre_1165_; 
lean_inc_ref(v_pre_1164_);
v_pre_1165_ = lean_ctor_get(v_pre_1164_, 0);
if (lean_obj_tag(v_pre_1165_) == 0)
{
lean_object* v_snd_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1663_; 
v_snd_1166_ = lean_ctor_get(v___x_1162_, 1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; 
v_unused_1664_ = lean_ctor_get(v___x_1162_, 0);
lean_dec(v_unused_1664_);
v___x_1168_ = v___x_1162_;
v_isShared_1169_ = v_isSharedCheck_1663_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_snd_1166_);
lean_dec(v___x_1162_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1663_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_str_1170_; lean_object* v_str_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_str_1170_ = lean_ctor_get(v_fst_1163_, 1);
lean_inc_ref(v_str_1170_);
lean_dec_ref(v_fst_1163_);
v_str_1171_ = lean_ctor_get(v_pre_1164_, 1);
lean_inc_ref(v_str_1171_);
lean_dec_ref(v_pre_1164_);
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0));
v___x_1173_ = lean_string_dec_eq(v_str_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3));
v___x_1175_ = lean_string_dec_eq(v_str_1171_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0));
v___x_1177_ = lean_string_dec_eq(v_str_1171_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1));
v___x_1179_ = lean_string_dec_eq(v_str_1171_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2));
v___x_1181_ = lean_string_dec_eq(v_str_1171_, v___x_1180_);
lean_dec_ref(v_str_1171_);
if (v___x_1181_ == 0)
{
lean_dec_ref(v_str_1170_);
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3));
v___x_1183_ = lean_string_dec_eq(v_str_1170_, v___x_1182_);
lean_dec_ref(v_str_1170_);
if (v___x_1183_ == 0)
{
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1184_ = lean_array_get_size(v_snd_1166_);
v___x_1185_ = lean_unsigned_to_nat(4u);
v___x_1186_ = lean_nat_dec_eq(v___x_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1187_ = lean_unsigned_to_nat(2u);
v___x_1188_ = lean_array_fget(v_snd_1166_, v___x_1187_);
v___x_1189_ = lean_unsigned_to_nat(3u);
v___x_1190_ = lean_array_fget(v_snd_1166_, v___x_1189_);
lean_dec(v_snd_1166_);
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6);
lean_inc(v___x_1190_);
lean_inc(v___x_1188_);
v___x_1193_ = l_Lean_mkAppB(v___x_1192_, v___x_1188_, v___x_1190_);
v___x_1194_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9);
v___x_1195_ = l_Lean_mkAppB(v___x_1194_, v___x_1188_, v___x_1190_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 1);
lean_ctor_set(v___x_1168_, 1, v___x_1191_);
lean_ctor_set(v___x_1168_, 0, v___x_1195_);
v___x_1197_ = v___x_1168_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1191_);
v___x_1197_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1193_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
}
}
}
}
else
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
lean_dec_ref(v_str_1171_);
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10));
v___x_1202_ = lean_string_dec_eq(v_str_1170_, v___x_1201_);
lean_dec_ref(v_str_1170_);
if (v___x_1202_ == 0)
{
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1203_ = lean_array_get_size(v_snd_1166_);
v___x_1204_ = lean_unsigned_to_nat(4u);
v___x_1205_ = lean_nat_dec_eq(v___x_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1206_ = lean_unsigned_to_nat(2u);
v___x_1207_ = lean_array_fget(v_snd_1166_, v___x_1206_);
v___x_1208_ = lean_unsigned_to_nat(3u);
v___x_1209_ = lean_array_fget(v_snd_1166_, v___x_1208_);
lean_dec(v_snd_1166_);
v___x_1210_ = lean_box(0);
v___x_1211_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13);
lean_inc(v___x_1209_);
lean_inc(v___x_1207_);
v___x_1212_ = l_Lean_mkAppB(v___x_1211_, v___x_1207_, v___x_1209_);
v___x_1213_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16);
v___x_1214_ = l_Lean_mkAppB(v___x_1213_, v___x_1207_, v___x_1209_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 1);
lean_ctor_set(v___x_1168_, 1, v___x_1210_);
lean_ctor_set(v___x_1168_, 0, v___x_1214_);
v___x_1216_ = v___x_1168_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v___x_1210_);
v___x_1216_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1212_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
}
}
}
}
else
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
lean_dec_ref(v_str_1171_);
v___x_1220_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17));
v___x_1221_ = lean_string_dec_eq(v_str_1170_, v___x_1220_);
lean_dec_ref(v_str_1170_);
if (v___x_1221_ == 0)
{
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1222_ = lean_array_get_size(v_snd_1166_);
v___x_1223_ = lean_unsigned_to_nat(6u);
v___x_1224_ = lean_nat_dec_eq(v___x_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v_fst_1228_; 
v___x_1225_ = lean_unsigned_to_nat(5u);
v___x_1226_ = lean_array_fget(v_snd_1166_, v___x_1225_);
lean_inc(v___x_1226_);
v___x_1227_ = l_Lean_Expr_getAppFnArgs(v___x_1226_);
v_fst_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_fst_1228_);
if (lean_obj_tag(v_fst_1228_) == 1)
{
lean_object* v_pre_1229_; 
v_pre_1229_ = lean_ctor_get(v_fst_1228_, 0);
lean_inc(v_pre_1229_);
if (lean_obj_tag(v_pre_1229_) == 1)
{
lean_object* v_pre_1230_; 
v_pre_1230_ = lean_ctor_get(v_pre_1229_, 0);
if (lean_obj_tag(v_pre_1230_) == 0)
{
lean_object* v_snd_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1430_; 
v_snd_1231_ = lean_ctor_get(v___x_1227_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; 
v_unused_1431_ = lean_ctor_get(v___x_1227_, 0);
lean_dec(v_unused_1431_);
v___x_1233_ = v___x_1227_;
v_isShared_1234_ = v_isSharedCheck_1430_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_snd_1231_);
lean_dec(v___x_1227_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1430_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v_str_1235_; lean_object* v_str_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v_str_1235_ = lean_ctor_get(v_fst_1228_, 1);
lean_inc_ref(v_str_1235_);
lean_dec_ref(v_fst_1228_);
v_str_1236_ = lean_ctor_get(v_pre_1229_, 1);
lean_inc_ref(v_str_1236_);
lean_dec_ref(v_pre_1229_);
v___x_1237_ = lean_unsigned_to_nat(4u);
v___x_1238_ = lean_array_fget(v_snd_1166_, v___x_1237_);
lean_dec(v_snd_1166_);
v___x_1276_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4));
v___x_1277_ = lean_string_dec_eq(v_str_1236_, v___x_1276_);
if (v___x_1277_ == 0)
{
uint8_t v___x_1278_; 
v___x_1278_ = lean_string_dec_eq(v_str_1236_, v___x_1172_);
lean_dec_ref(v_str_1236_);
if (v___x_1278_ == 0)
{
lean_dec(v___x_1238_);
lean_dec_ref(v_str_1235_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1153_;
}
else
{
lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1279_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1280_ = lean_string_dec_eq(v_str_1235_, v___x_1279_);
lean_dec_ref(v_str_1235_);
if (v___x_1280_ == 0)
{
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1153_;
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1281_ = lean_array_get_size(v_snd_1231_);
v___x_1282_ = lean_unsigned_to_nat(3u);
v___x_1283_ = lean_nat_dec_eq(v___x_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1153_;
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_array_fget_borrowed(v_snd_1231_, v___x_1284_);
if (lean_obj_tag(v___x_1285_) == 4)
{
lean_object* v_declName_1286_; 
v_declName_1286_ = lean_ctor_get(v___x_1285_, 0);
if (lean_obj_tag(v_declName_1286_) == 1)
{
lean_object* v_pre_1287_; 
v_pre_1287_ = lean_ctor_get(v_declName_1286_, 0);
if (lean_obj_tag(v_pre_1287_) == 0)
{
lean_object* v_us_1288_; lean_object* v_str_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_us_1288_ = lean_ctor_get(v___x_1285_, 1);
lean_inc(v_us_1288_);
v_str_1289_ = lean_ctor_get(v_declName_1286_, 1);
v___x_1290_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1291_ = lean_string_dec_eq(v_str_1289_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_dec(v_us_1288_);
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1153_;
}
else
{
if (lean_obj_tag(v_us_1288_) == 0)
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_fst_1295_; 
v___x_1292_ = lean_unsigned_to_nat(2u);
v___x_1293_ = lean_array_fget(v_snd_1231_, v___x_1292_);
lean_dec(v_snd_1231_);
lean_inc(v___x_1293_);
v___x_1294_ = l_Lean_Expr_getAppFnArgs(v___x_1293_);
v_fst_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_fst_1295_);
if (lean_obj_tag(v_fst_1295_) == 1)
{
lean_object* v_pre_1296_; 
v_pre_1296_ = lean_ctor_get(v_fst_1295_, 0);
lean_inc(v_pre_1296_);
if (lean_obj_tag(v_pre_1296_) == 1)
{
lean_object* v_pre_1297_; 
v_pre_1297_ = lean_ctor_get(v_pre_1296_, 0);
if (lean_obj_tag(v_pre_1297_) == 0)
{
lean_object* v_snd_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1377_; 
v_snd_1298_ = lean_ctor_get(v___x_1294_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v___x_1294_, 0);
lean_dec(v_unused_1378_);
v___x_1300_ = v___x_1294_;
v_isShared_1301_ = v_isSharedCheck_1377_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_snd_1298_);
lean_dec(v___x_1294_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1377_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v_str_1302_; lean_object* v_str_1303_; uint8_t v___x_1304_; 
v_str_1302_ = lean_ctor_get(v_fst_1295_, 1);
lean_inc_ref(v_str_1302_);
lean_dec_ref(v_fst_1295_);
v_str_1303_ = lean_ctor_get(v_pre_1296_, 1);
lean_inc_ref(v_str_1303_);
lean_dec_ref(v_pre_1296_);
v___x_1304_ = lean_string_dec_eq(v_str_1303_, v___x_1276_);
lean_dec_ref(v_str_1303_);
if (v___x_1304_ == 0)
{
lean_dec_ref(v_str_1302_);
lean_del_object(v___x_1300_);
lean_dec(v_snd_1298_);
lean_dec(v___x_1293_);
lean_del_object(v___x_1233_);
lean_del_object(v___x_1168_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_1306_ = lean_string_dec_eq(v_str_1302_, v___x_1305_);
lean_dec_ref(v_str_1302_);
if (v___x_1306_ == 0)
{
lean_del_object(v___x_1300_);
lean_dec(v_snd_1298_);
lean_dec(v___x_1293_);
lean_del_object(v___x_1233_);
lean_del_object(v___x_1168_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = lean_array_get_size(v_snd_1298_);
v___x_1308_ = lean_nat_dec_eq(v___x_1307_, v___x_1223_);
if (v___x_1308_ == 0)
{
lean_del_object(v___x_1300_);
lean_dec(v_snd_1298_);
lean_dec(v___x_1293_);
lean_del_object(v___x_1233_);
lean_del_object(v___x_1168_);
goto v___jp_1239_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_array_fget(v_snd_1298_, v___x_1237_);
lean_inc(v___x_1309_);
v___x_1310_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1309_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_dec(v___x_1309_);
lean_del_object(v___x_1300_);
lean_dec(v_snd_1298_);
lean_dec(v___x_1293_);
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1159_;
}
else
{
lean_object* v_val_1311_; uint8_t v___x_1312_; 
v_val_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_val_1311_);
lean_dec_ref(v___x_1310_);
v___x_1312_ = lean_nat_dec_eq(v_val_1311_, v___x_1284_);
lean_dec(v_val_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1313_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22));
v___x_1314_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23);
if (v_isShared_1301_ == 0)
{
lean_ctor_set_tag(v___x_1300_, 1);
lean_ctor_set(v___x_1300_, 1, v_us_1288_);
lean_ctor_set(v___x_1300_, 0, v___x_1314_);
v___x_1316_ = v___x_1300_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_us_1288_);
v___x_1316_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v_b__pos_1323_; lean_object* v___x_1324_; 
lean_inc_ref(v___x_1316_);
v___x_1317_ = l_Lean_Expr_const___override(v___x_1313_, v___x_1316_);
v___x_1318_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24));
v___x_1319_ = l_Lean_Expr_const___override(v___x_1318_, v_us_1288_);
v___x_1320_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26));
v___x_1321_ = l_Lean_Expr_const___override(v___x_1320_, v_us_1288_);
v___x_1322_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27);
lean_inc(v___x_1309_);
v_b__pos_1323_ = l_Lean_mkApp4(v___x_1317_, v___x_1319_, v___x_1321_, v___x_1322_, v___x_1309_);
v___x_1324_ = l_Lean_Meta_mkDecideProof(v_b__pos_1323_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1367_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1367_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1367_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___y_1341_; uint8_t v___x_1357_; 
v___x_1329_ = lean_array_fget(v_snd_1298_, v___x_1225_);
lean_dec(v_snd_1298_);
v___x_1330_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29));
v___x_1331_ = l_Lean_Expr_const___override(v___x_1330_, v_us_1288_);
v___x_1332_ = l_Lean_mkApp3(v___x_1331_, v___x_1309_, v___x_1329_, v_a_1325_);
v___x_1333_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31));
v___x_1334_ = l_Lean_Expr_const___override(v___x_1333_, v_us_1288_);
v___x_1335_ = l_Lean_mkAppB(v___x_1334_, v___x_1293_, v___x_1332_);
v___x_1336_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33));
v___x_1337_ = l_Lean_Expr_const___override(v___x_1336_, v_us_1288_);
v___x_1338_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35));
v___x_1339_ = l_Lean_Expr_const___override(v___x_1338_, v_us_1288_);
v___x_1357_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42));
v___x_1359_ = l_Lean_Expr_const___override(v___x_1358_, v___x_1316_);
v___x_1360_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1));
v___x_1361_ = l_Lean_Expr_const___override(v___x_1360_, v_us_1288_);
v___x_1362_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44));
v___x_1363_ = l_Lean_Expr_const___override(v___x_1362_, v_us_1288_);
v___x_1364_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47);
v___x_1365_ = l_Lean_mkApp3(v___x_1359_, v___x_1361_, v___x_1363_, v___x_1364_);
v___y_1341_ = v___x_1365_;
goto v___jp_1340_;
}
else
{
lean_object* v___x_1366_; 
lean_dec_ref(v___x_1316_);
v___x_1366_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1341_ = v___x_1366_;
goto v___jp_1340_;
}
v___jp_1340_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
lean_inc_ref(v___x_1335_);
lean_inc(v___x_1226_);
v___x_1342_ = l_Lean_mkApp3(v___x_1339_, v___x_1226_, v___y_1341_, v___x_1335_);
lean_inc(v___x_1226_);
lean_inc(v___x_1238_);
v___x_1343_ = l_Lean_mkApp3(v___x_1337_, v___x_1238_, v___x_1226_, v___x_1342_);
v___x_1344_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37));
v___x_1345_ = l_Lean_Expr_const___override(v___x_1344_, v_us_1288_);
v___x_1346_ = l_Lean_mkApp3(v___x_1345_, v___x_1238_, v___x_1226_, v___x_1335_);
v___x_1347_ = lean_box(0);
if (v_isShared_1234_ == 0)
{
lean_ctor_set_tag(v___x_1233_, 1);
lean_ctor_set(v___x_1233_, 1, v___x_1347_);
lean_ctor_set(v___x_1233_, 0, v___x_1346_);
v___x_1349_ = v___x_1233_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1351_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 1);
lean_ctor_set(v___x_1168_, 1, v___x_1349_);
lean_ctor_set(v___x_1168_, 0, v___x_1343_);
v___x_1351_ = v___x_1168_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1353_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1351_);
v___x_1353_ = v___x_1327_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v___x_1316_);
lean_dec(v___x_1309_);
lean_dec(v_snd_1298_);
lean_dec(v___x_1293_);
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
v_a_1368_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1324_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1324_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
else
{
lean_dec(v___x_1309_);
lean_del_object(v___x_1300_);
lean_dec(v_snd_1298_);
lean_dec(v___x_1293_);
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1159_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_1296_);
lean_dec_ref(v_fst_1295_);
lean_dec_ref(v___x_1294_);
lean_dec(v___x_1293_);
lean_del_object(v___x_1233_);
lean_del_object(v___x_1168_);
goto v___jp_1239_;
}
}
else
{
lean_dec(v_pre_1296_);
lean_dec_ref(v_fst_1295_);
lean_dec_ref(v___x_1294_);
lean_dec(v___x_1293_);
lean_del_object(v___x_1233_);
lean_del_object(v___x_1168_);
goto v___jp_1239_;
}
}
else
{
lean_dec(v_fst_1295_);
lean_dec_ref(v___x_1294_);
lean_dec(v___x_1293_);
lean_del_object(v___x_1233_);
lean_del_object(v___x_1168_);
goto v___jp_1239_;
}
}
else
{
lean_dec(v_us_1288_);
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1153_;
}
}
}
else
{
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1153_;
}
}
else
{
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1153_;
}
}
else
{
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1153_;
}
}
}
}
}
else
{
lean_object* v___x_1379_; uint8_t v___x_1380_; 
lean_dec_ref(v_str_1236_);
v___x_1379_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5));
v___x_1380_ = lean_string_dec_eq(v_str_1235_, v___x_1379_);
lean_dec_ref(v_str_1235_);
if (v___x_1380_ == 0)
{
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1153_;
}
else
{
lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1381_ = lean_array_get_size(v_snd_1231_);
v___x_1382_ = lean_nat_dec_eq(v___x_1381_, v___x_1223_);
if (v___x_1382_ == 0)
{
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1153_;
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_array_fget(v_snd_1231_, v___x_1237_);
lean_inc(v___x_1383_);
v___x_1384_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1383_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_dec(v___x_1383_);
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1147_;
}
else
{
lean_object* v_val_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_val_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_val_1385_);
lean_dec_ref(v___x_1384_);
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = lean_nat_dec_eq(v_val_1385_, v___x_1386_);
lean_dec(v_val_1385_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___y_1394_; uint8_t v___x_1427_; 
v___x_1388_ = lean_array_fget(v_snd_1231_, v___x_1225_);
lean_dec(v_snd_1231_);
v___x_1389_ = lean_box(0);
v___x_1390_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51);
v___x_1391_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1392_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
v___x_1427_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
v___y_1394_ = v___x_1428_;
goto v___jp_1393_;
}
else
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1394_ = v___x_1429_;
goto v___jp_1393_;
}
v___jp_1393_:
{
lean_object* v_b__pos_1395_; lean_object* v___x_1396_; 
lean_inc(v___x_1383_);
lean_inc_ref(v___y_1394_);
v_b__pos_1395_ = l_Lean_mkApp4(v___x_1390_, v___x_1391_, v___x_1392_, v___y_1394_, v___x_1383_);
v___x_1396_ = l_Lean_Meta_mkDecideProof(v_b__pos_1395_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1418_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1418_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1418_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1401_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57);
v___x_1402_ = l_Lean_mkApp3(v___x_1401_, v___x_1383_, v___x_1388_, v_a_1397_);
v___x_1403_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58);
v___x_1404_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59);
lean_inc_ref(v___x_1402_);
lean_inc(v___x_1226_);
v___x_1405_ = l_Lean_mkApp3(v___x_1404_, v___x_1226_, v___y_1394_, v___x_1402_);
lean_inc(v___x_1226_);
lean_inc(v___x_1238_);
v___x_1406_ = l_Lean_mkApp3(v___x_1403_, v___x_1238_, v___x_1226_, v___x_1405_);
v___x_1407_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60);
v___x_1408_ = l_Lean_mkApp3(v___x_1407_, v___x_1238_, v___x_1226_, v___x_1402_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set_tag(v___x_1233_, 1);
lean_ctor_set(v___x_1233_, 1, v___x_1389_);
lean_ctor_set(v___x_1233_, 0, v___x_1408_);
v___x_1410_ = v___x_1233_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___x_1389_);
v___x_1410_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1412_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 1);
lean_ctor_set(v___x_1168_, 1, v___x_1410_);
lean_ctor_set(v___x_1168_, 0, v___x_1406_);
v___x_1412_ = v___x_1168_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1412_);
v___x_1414_ = v___x_1399_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec_ref(v___y_1394_);
lean_dec(v___x_1388_);
lean_dec(v___x_1383_);
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
v_a_1419_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1396_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1396_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
else
{
lean_dec(v___x_1383_);
lean_dec(v___x_1238_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
goto v___jp_1147_;
}
}
}
}
}
v___jp_1239_:
{
lean_object* v___x_1240_; lean_object* v_fst_1241_; 
v___x_1240_ = l_Lean_Expr_getAppFnArgs(v___x_1238_);
v_fst_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_fst_1241_);
if (lean_obj_tag(v_fst_1241_) == 1)
{
lean_object* v_pre_1242_; 
v_pre_1242_ = lean_ctor_get(v_fst_1241_, 0);
lean_inc(v_pre_1242_);
if (lean_obj_tag(v_pre_1242_) == 1)
{
lean_object* v_pre_1243_; 
v_pre_1243_ = lean_ctor_get(v_pre_1242_, 0);
if (lean_obj_tag(v_pre_1243_) == 0)
{
lean_object* v_snd_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1274_; 
v_snd_1244_ = lean_ctor_get(v___x_1240_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1240_, 0);
lean_dec(v_unused_1275_);
v___x_1246_ = v___x_1240_;
v_isShared_1247_ = v_isSharedCheck_1274_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_snd_1244_);
lean_dec(v___x_1240_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1274_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_str_1248_; lean_object* v_str_1249_; uint8_t v___x_1250_; 
v_str_1248_ = lean_ctor_get(v_fst_1241_, 1);
lean_inc_ref(v_str_1248_);
lean_dec_ref(v_fst_1241_);
v_str_1249_ = lean_ctor_get(v_pre_1242_, 1);
lean_inc_ref(v_str_1249_);
lean_dec_ref(v_pre_1242_);
v___x_1250_ = lean_string_dec_eq(v_str_1249_, v___x_1172_);
lean_dec_ref(v_str_1249_);
if (v___x_1250_ == 0)
{
lean_dec_ref(v_str_1248_);
lean_del_object(v___x_1246_);
lean_dec(v_snd_1244_);
lean_dec(v___x_1226_);
goto v___jp_1156_;
}
else
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1252_ = lean_string_dec_eq(v_str_1248_, v___x_1251_);
lean_dec_ref(v_str_1248_);
if (v___x_1252_ == 0)
{
lean_del_object(v___x_1246_);
lean_dec(v_snd_1244_);
lean_dec(v___x_1226_);
goto v___jp_1156_;
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1253_ = lean_array_get_size(v_snd_1244_);
v___x_1254_ = lean_unsigned_to_nat(3u);
v___x_1255_ = lean_nat_dec_eq(v___x_1253_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_del_object(v___x_1246_);
lean_dec(v_snd_1244_);
lean_dec(v___x_1226_);
goto v___jp_1156_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_array_fget_borrowed(v_snd_1244_, v___x_1256_);
if (lean_obj_tag(v___x_1257_) == 4)
{
lean_object* v_declName_1258_; 
v_declName_1258_ = lean_ctor_get(v___x_1257_, 0);
if (lean_obj_tag(v_declName_1258_) == 1)
{
lean_object* v_pre_1259_; 
v_pre_1259_ = lean_ctor_get(v_declName_1258_, 0);
if (lean_obj_tag(v_pre_1259_) == 0)
{
lean_object* v_us_1260_; lean_object* v_str_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_us_1260_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_us_1260_);
v_str_1261_ = lean_ctor_get(v_declName_1258_, 1);
v___x_1262_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1263_ = lean_string_dec_eq(v_str_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_dec(v_us_1260_);
lean_del_object(v___x_1246_);
lean_dec(v_snd_1244_);
lean_dec(v___x_1226_);
goto v___jp_1156_;
}
else
{
if (lean_obj_tag(v_us_1260_) == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1264_ = lean_unsigned_to_nat(2u);
v___x_1265_ = lean_array_fget(v_snd_1244_, v___x_1264_);
lean_dec(v_snd_1244_);
v___x_1266_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19));
v___x_1267_ = l_Lean_Expr_const___override(v___x_1266_, v_us_1260_);
v___x_1268_ = l_Lean_mkAppB(v___x_1267_, v___x_1265_, v___x_1226_);
v___x_1269_ = lean_box(0);
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 1);
lean_ctor_set(v___x_1246_, 1, v___x_1269_);
lean_ctor_set(v___x_1246_, 0, v___x_1268_);
v___x_1271_ = v___x_1246_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
return v___x_1272_;
}
}
else
{
lean_dec(v_us_1260_);
lean_del_object(v___x_1246_);
lean_dec(v_snd_1244_);
lean_dec(v___x_1226_);
goto v___jp_1156_;
}
}
}
else
{
lean_del_object(v___x_1246_);
lean_dec(v_snd_1244_);
lean_dec(v___x_1226_);
goto v___jp_1156_;
}
}
else
{
lean_del_object(v___x_1246_);
lean_dec(v_snd_1244_);
lean_dec(v___x_1226_);
goto v___jp_1156_;
}
}
else
{
lean_del_object(v___x_1246_);
lean_dec(v_snd_1244_);
lean_dec(v___x_1226_);
goto v___jp_1156_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_1242_);
lean_dec_ref(v_fst_1241_);
lean_dec_ref(v___x_1240_);
lean_dec(v___x_1226_);
goto v___jp_1156_;
}
}
else
{
lean_dec(v_pre_1242_);
lean_dec_ref(v_fst_1241_);
lean_dec_ref(v___x_1240_);
lean_dec(v___x_1226_);
goto v___jp_1156_;
}
}
else
{
lean_dec(v_fst_1241_);
lean_dec_ref(v___x_1240_);
lean_dec(v___x_1226_);
goto v___jp_1156_;
}
}
}
}
else
{
lean_dec_ref(v_pre_1229_);
lean_dec_ref(v_fst_1228_);
lean_dec_ref(v___x_1227_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1153_;
}
}
else
{
lean_dec_ref(v_fst_1228_);
lean_dec(v_pre_1229_);
lean_dec_ref(v___x_1227_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1153_;
}
}
else
{
lean_dec(v_fst_1228_);
lean_dec_ref(v___x_1227_);
lean_dec(v___x_1226_);
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1153_;
}
}
}
}
}
else
{
lean_object* v___x_1432_; uint8_t v___x_1433_; 
lean_dec_ref(v_str_1171_);
v___x_1432_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7));
v___x_1433_ = lean_string_dec_eq(v_str_1170_, v___x_1432_);
lean_dec_ref(v_str_1170_);
if (v___x_1433_ == 0)
{
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = lean_array_get_size(v_snd_1166_);
v___x_1435_ = lean_unsigned_to_nat(6u);
v___x_1436_ = lean_nat_dec_eq(v___x_1434_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = lean_unsigned_to_nat(5u);
v___x_1438_ = lean_array_fget(v_snd_1166_, v___x_1437_);
lean_inc(v___x_1438_);
v___x_1439_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_1438_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_dec(v___x_1438_);
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1144_;
}
else
{
lean_object* v_val_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_val_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_val_1440_);
lean_dec_ref(v___x_1439_);
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = lean_nat_dec_eq(v_val_1440_, v___x_1441_);
lean_dec(v_val_1440_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___y_1449_; uint8_t v___x_1489_; 
v___x_1443_ = lean_unsigned_to_nat(4u);
v___x_1444_ = lean_array_fget(v_snd_1166_, v___x_1443_);
lean_dec(v_snd_1166_);
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68);
v___x_1447_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1489_ = lean_uint8_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
v___y_1449_ = v___x_1490_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
v___y_1449_ = v___x_1491_;
goto v___jp_1448_;
}
v___jp_1448_:
{
lean_object* v_ne__zero_1450_; lean_object* v___x_1451_; 
lean_inc_ref(v___y_1449_);
lean_inc(v___x_1438_);
v_ne__zero_1450_ = l_Lean_mkApp3(v___x_1446_, v___x_1447_, v___x_1438_, v___y_1449_);
v___x_1451_ = l_Lean_Meta_mkDecideProof(v_ne__zero_1450_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_pos_1455_; lean_object* v___x_1456_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref(v___x_1451_);
v___x_1453_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51);
v___x_1454_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
lean_inc(v___x_1438_);
v_pos_1455_ = l_Lean_mkApp4(v___x_1453_, v___x_1447_, v___x_1454_, v___y_1449_, v___x_1438_);
v___x_1456_ = l_Lean_Meta_mkDecideProof(v_pos_1455_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1472_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1472_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1472_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1461_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71);
lean_inc(v___x_1438_);
lean_inc(v___x_1444_);
v___x_1462_ = l_Lean_mkApp3(v___x_1461_, v___x_1444_, v___x_1438_, v_a_1452_);
v___x_1463_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74);
v___x_1464_ = l_Lean_mkApp3(v___x_1463_, v___x_1444_, v___x_1438_, v_a_1457_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 1);
lean_ctor_set(v___x_1168_, 1, v___x_1445_);
lean_ctor_set(v___x_1168_, 0, v___x_1464_);
v___x_1466_ = v___x_1168_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v___x_1445_);
v___x_1466_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1469_; 
v___x_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1462_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1467_);
v___x_1469_ = v___x_1459_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_a_1452_);
lean_dec(v___x_1444_);
lean_dec(v___x_1438_);
lean_del_object(v___x_1168_);
v_a_1473_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1456_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1456_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v___y_1449_);
lean_dec(v___x_1444_);
lean_dec(v___x_1438_);
lean_del_object(v___x_1168_);
v_a_1481_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1451_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1451_);
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
lean_dec(v___x_1438_);
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1144_;
}
}
}
}
}
}
else
{
lean_object* v___x_1492_; uint8_t v___x_1493_; 
lean_dec_ref(v_str_1171_);
v___x_1492_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1));
v___x_1493_ = lean_string_dec_eq(v_str_1170_, v___x_1492_);
lean_dec_ref(v_str_1170_);
if (v___x_1493_ == 0)
{
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1494_ = lean_array_get_size(v_snd_1166_);
v___x_1495_ = lean_unsigned_to_nat(3u);
v___x_1496_ = lean_nat_dec_eq(v___x_1494_, v___x_1495_);
if (v___x_1496_ == 0)
{
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_unsigned_to_nat(0u);
v___x_1498_ = lean_array_fget_borrowed(v_snd_1166_, v___x_1497_);
if (lean_obj_tag(v___x_1498_) == 4)
{
lean_object* v_declName_1499_; 
v_declName_1499_ = lean_ctor_get(v___x_1498_, 0);
if (lean_obj_tag(v_declName_1499_) == 1)
{
lean_object* v_pre_1500_; 
v_pre_1500_ = lean_ctor_get(v_declName_1499_, 0);
if (lean_obj_tag(v_pre_1500_) == 0)
{
lean_object* v_us_1501_; lean_object* v_str_1502_; lean_object* v___x_1503_; lean_object* v___y_1505_; lean_object* v___y_1506_; uint8_t v___x_1516_; 
v_us_1501_ = lean_ctor_get(v___x_1498_, 1);
lean_inc(v_us_1501_);
v_str_1502_ = lean_ctor_get(v_declName_1499_, 1);
v___x_1503_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0));
v___x_1516_ = lean_string_dec_eq(v_str_1502_, v___x_1503_);
if (v___x_1516_ == 0)
{
lean_dec(v_us_1501_);
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
else
{
if (lean_obj_tag(v_us_1501_) == 0)
{
uint8_t v_splitNatSub_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_r_1524_; lean_object* v_n_1526_; lean_object* v_x_1527_; lean_object* v_n_1536_; lean_object* v_i_1537_; lean_object* v_x_1546_; 
v_splitNatSub_1517_ = lean_ctor_get_uint8(v_a_1138_, 1);
v___x_1518_ = lean_unsigned_to_nat(2u);
v___x_1519_ = lean_array_fget(v_snd_1166_, v___x_1518_);
lean_dec(v_snd_1166_);
v___x_1520_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78));
v___x_1521_ = l_Lean_Expr_const___override(v___x_1520_, v_us_1501_);
lean_inc(v___x_1519_);
v___x_1522_ = l_Lean_Expr_app___override(v___x_1521_, v___x_1519_);
v___x_1523_ = lean_box(0);
v_r_1524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_r_1524_, 0, v___x_1522_);
lean_ctor_set(v_r_1524_, 1, v___x_1523_);
if (v_splitNatSub_1517_ == 1)
{
lean_object* v___x_1552_; lean_object* v_fst_1553_; 
v___x_1552_ = l_Lean_Expr_getAppFnArgs(v___x_1519_);
v_fst_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_fst_1553_);
if (lean_obj_tag(v_fst_1553_) == 1)
{
lean_object* v_pre_1554_; 
v_pre_1554_ = lean_ctor_get(v_fst_1553_, 0);
lean_inc(v_pre_1554_);
if (lean_obj_tag(v_pre_1554_) == 1)
{
lean_object* v_pre_1555_; 
v_pre_1555_ = lean_ctor_get(v_pre_1554_, 0);
if (lean_obj_tag(v_pre_1555_) == 0)
{
lean_object* v_snd_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1616_; 
v_snd_1556_ = lean_ctor_get(v___x_1552_, 1);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; 
v_unused_1617_ = lean_ctor_get(v___x_1552_, 0);
lean_dec(v_unused_1617_);
v___x_1558_ = v___x_1552_;
v_isShared_1559_ = v_isSharedCheck_1616_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_snd_1556_);
lean_dec(v___x_1552_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1616_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v_str_1560_; lean_object* v_str_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v_str_1560_ = lean_ctor_get(v_fst_1553_, 1);
lean_inc_ref(v_str_1560_);
lean_dec_ref(v_fst_1553_);
v_str_1561_ = lean_ctor_get(v_pre_1554_, 1);
lean_inc_ref(v_str_1561_);
lean_dec_ref(v_pre_1554_);
v___x_1562_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2));
v___x_1563_ = lean_string_dec_eq(v_str_1561_, v___x_1562_);
if (v___x_1563_ == 0)
{
uint8_t v___x_1564_; 
lean_del_object(v___x_1558_);
v___x_1564_ = lean_string_dec_eq(v_str_1561_, v___x_1503_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; uint8_t v___x_1566_; 
lean_del_object(v___x_1168_);
v___x_1565_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82));
v___x_1566_ = lean_string_dec_eq(v_str_1561_, v___x_1565_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79));
v___x_1568_ = lean_string_dec_eq(v_str_1561_, v___x_1567_);
lean_dec_ref(v_str_1561_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_dec_ref(v_str_1560_);
lean_dec(v_snd_1556_);
v___x_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1569_, 0, v_r_1524_);
return v___x_1569_;
}
else
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86));
v___x_1571_ = lean_string_dec_eq(v_str_1560_, v___x_1570_);
lean_dec_ref(v_str_1560_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; 
lean_dec(v_snd_1556_);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v_r_1524_);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = lean_array_get_size(v_snd_1556_);
v___x_1574_ = lean_nat_dec_eq(v___x_1573_, v___x_1518_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; 
lean_dec(v_snd_1556_);
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v_r_1524_);
return v___x_1575_;
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = lean_array_fget(v_snd_1556_, v___x_1497_);
v___x_1577_ = lean_unsigned_to_nat(1u);
v___x_1578_ = lean_array_fget(v_snd_1556_, v___x_1577_);
lean_dec(v_snd_1556_);
v_n_1526_ = v___x_1576_;
v_x_1527_ = v___x_1578_;
goto v___jp_1525_;
}
}
}
}
else
{
lean_object* v___x_1579_; uint8_t v___x_1580_; 
lean_dec_ref(v_str_1561_);
v___x_1579_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87));
v___x_1580_ = lean_string_dec_eq(v_str_1560_, v___x_1579_);
lean_dec_ref(v_str_1560_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_dec(v_snd_1556_);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v_r_1524_);
return v___x_1581_;
}
else
{
lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = lean_array_get_size(v_snd_1556_);
v___x_1583_ = lean_nat_dec_eq(v___x_1582_, v___x_1518_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_dec(v_snd_1556_);
v___x_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1584_, 0, v_r_1524_);
return v___x_1584_;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = lean_array_fget(v_snd_1556_, v___x_1497_);
v___x_1586_ = lean_unsigned_to_nat(1u);
v___x_1587_ = lean_array_fget(v_snd_1556_, v___x_1586_);
lean_dec(v_snd_1556_);
v_n_1536_ = v___x_1585_;
v_i_1537_ = v___x_1587_;
goto v___jp_1535_;
}
}
}
}
else
{
lean_object* v___x_1588_; uint8_t v___x_1589_; 
lean_dec_ref(v_str_1561_);
v___x_1588_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88));
v___x_1589_ = lean_string_dec_eq(v_str_1560_, v___x_1588_);
lean_dec_ref(v_str_1560_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; 
lean_dec(v_snd_1556_);
lean_del_object(v___x_1168_);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v_r_1524_);
return v___x_1590_;
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1591_ = lean_array_get_size(v_snd_1556_);
v___x_1592_ = lean_unsigned_to_nat(1u);
v___x_1593_ = lean_nat_dec_eq(v___x_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
lean_dec(v_snd_1556_);
lean_del_object(v___x_1168_);
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_r_1524_);
return v___x_1594_;
}
else
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_array_fget(v_snd_1556_, v___x_1497_);
lean_dec(v_snd_1556_);
v_x_1546_ = v___x_1595_;
goto v___jp_1545_;
}
}
}
}
else
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
lean_dec_ref(v_str_1561_);
lean_del_object(v___x_1168_);
v___x_1596_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9));
v___x_1597_ = lean_string_dec_eq(v_str_1560_, v___x_1596_);
lean_dec_ref(v_str_1560_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
lean_del_object(v___x_1558_);
lean_dec(v_snd_1556_);
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v_r_1524_);
return v___x_1598_;
}
else
{
lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1599_ = lean_array_get_size(v_snd_1556_);
v___x_1600_ = lean_unsigned_to_nat(6u);
v___x_1601_ = lean_nat_dec_eq(v___x_1599_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
lean_del_object(v___x_1558_);
lean_dec(v_snd_1556_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_r_1524_);
return v___x_1602_;
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1603_ = lean_unsigned_to_nat(4u);
v___x_1604_ = lean_array_fget(v_snd_1556_, v___x_1603_);
v___x_1605_ = lean_unsigned_to_nat(5u);
v___x_1606_ = lean_array_fget(v_snd_1556_, v___x_1605_);
lean_dec(v_snd_1556_);
v___x_1607_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90));
v___x_1608_ = l_Lean_Expr_const___override(v___x_1607_, v_us_1501_);
v___x_1609_ = l_Lean_mkAppB(v___x_1608_, v___x_1604_, v___x_1606_);
v___x_1610_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1609_, v_r_1524_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1612_; 
if (v_isShared_1559_ == 0)
{
lean_ctor_set_tag(v___x_1558_, 1);
lean_ctor_set(v___x_1558_, 1, v_r_1524_);
lean_ctor_set(v___x_1558_, 0, v___x_1609_);
v___x_1612_ = v___x_1558_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_r_1524_);
v___x_1612_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
return v___x_1613_;
}
}
else
{
lean_object* v___x_1615_; 
lean_dec_ref(v___x_1609_);
lean_del_object(v___x_1558_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_r_1524_);
return v___x_1615_;
}
}
}
}
}
}
else
{
lean_object* v___x_1618_; 
lean_dec_ref(v_pre_1554_);
lean_dec_ref(v_fst_1553_);
lean_dec_ref(v___x_1552_);
lean_del_object(v___x_1168_);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v_r_1524_);
return v___x_1618_;
}
}
else
{
lean_object* v___x_1619_; 
lean_dec(v_pre_1554_);
lean_dec_ref(v_fst_1553_);
lean_dec_ref(v___x_1552_);
lean_del_object(v___x_1168_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v_r_1524_);
return v___x_1619_;
}
}
else
{
lean_object* v___x_1620_; 
lean_dec(v_fst_1553_);
lean_dec_ref(v___x_1552_);
lean_del_object(v___x_1168_);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v_r_1524_);
return v___x_1620_;
}
}
else
{
lean_object* v___x_1621_; lean_object* v_fst_1622_; 
v___x_1621_ = l_Lean_Expr_getAppFnArgs(v___x_1519_);
v_fst_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_fst_1622_);
if (lean_obj_tag(v_fst_1622_) == 1)
{
lean_object* v_pre_1623_; 
v_pre_1623_ = lean_ctor_get(v_fst_1622_, 0);
lean_inc(v_pre_1623_);
if (lean_obj_tag(v_pre_1623_) == 1)
{
lean_object* v_pre_1624_; 
v_pre_1624_ = lean_ctor_get(v_pre_1623_, 0);
if (lean_obj_tag(v_pre_1624_) == 0)
{
lean_object* v_snd_1625_; lean_object* v_str_1626_; lean_object* v_str_1627_; uint8_t v___x_1628_; 
v_snd_1625_ = lean_ctor_get(v___x_1621_, 1);
lean_inc(v_snd_1625_);
lean_dec_ref(v___x_1621_);
v_str_1626_ = lean_ctor_get(v_fst_1622_, 1);
lean_inc_ref(v_str_1626_);
lean_dec_ref(v_fst_1622_);
v_str_1627_ = lean_ctor_get(v_pre_1623_, 1);
lean_inc_ref(v_str_1627_);
lean_dec_ref(v_pre_1623_);
v___x_1628_ = lean_string_dec_eq(v_str_1627_, v___x_1503_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
lean_del_object(v___x_1168_);
v___x_1629_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82));
v___x_1630_ = lean_string_dec_eq(v_str_1627_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79));
v___x_1632_ = lean_string_dec_eq(v_str_1627_, v___x_1631_);
lean_dec_ref(v_str_1627_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; 
lean_dec_ref(v_str_1626_);
lean_dec(v_snd_1625_);
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v_r_1524_);
return v___x_1633_;
}
else
{
lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86));
v___x_1635_ = lean_string_dec_eq(v_str_1626_, v___x_1634_);
lean_dec_ref(v_str_1626_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; 
lean_dec(v_snd_1625_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v_r_1524_);
return v___x_1636_;
}
else
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = lean_array_get_size(v_snd_1625_);
v___x_1638_ = lean_nat_dec_eq(v___x_1637_, v___x_1518_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; 
lean_dec(v_snd_1625_);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v_r_1524_);
return v___x_1639_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = lean_array_fget(v_snd_1625_, v___x_1497_);
v___x_1641_ = lean_unsigned_to_nat(1u);
v___x_1642_ = lean_array_fget(v_snd_1625_, v___x_1641_);
lean_dec(v_snd_1625_);
v_n_1526_ = v___x_1640_;
v_x_1527_ = v___x_1642_;
goto v___jp_1525_;
}
}
}
}
else
{
lean_object* v___x_1643_; uint8_t v___x_1644_; 
lean_dec_ref(v_str_1627_);
v___x_1643_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87));
v___x_1644_ = lean_string_dec_eq(v_str_1626_, v___x_1643_);
lean_dec_ref(v_str_1626_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; 
lean_dec(v_snd_1625_);
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v_r_1524_);
return v___x_1645_;
}
else
{
lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = lean_array_get_size(v_snd_1625_);
v___x_1647_ = lean_nat_dec_eq(v___x_1646_, v___x_1518_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_dec(v_snd_1625_);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v_r_1524_);
return v___x_1648_;
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = lean_array_fget(v_snd_1625_, v___x_1497_);
v___x_1650_ = lean_unsigned_to_nat(1u);
v___x_1651_ = lean_array_fget(v_snd_1625_, v___x_1650_);
lean_dec(v_snd_1625_);
v_n_1536_ = v___x_1649_;
v_i_1537_ = v___x_1651_;
goto v___jp_1535_;
}
}
}
}
else
{
lean_object* v___x_1652_; uint8_t v___x_1653_; 
lean_dec_ref(v_str_1627_);
v___x_1652_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88));
v___x_1653_ = lean_string_dec_eq(v_str_1626_, v___x_1652_);
lean_dec_ref(v_str_1626_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
lean_dec(v_snd_1625_);
lean_del_object(v___x_1168_);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_r_1524_);
return v___x_1654_;
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1655_ = lean_array_get_size(v_snd_1625_);
v___x_1656_ = lean_unsigned_to_nat(1u);
v___x_1657_ = lean_nat_dec_eq(v___x_1655_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec(v_snd_1625_);
lean_del_object(v___x_1168_);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_r_1524_);
return v___x_1658_;
}
else
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_array_fget(v_snd_1625_, v___x_1497_);
lean_dec(v_snd_1625_);
v_x_1546_ = v___x_1659_;
goto v___jp_1545_;
}
}
}
}
else
{
lean_object* v___x_1660_; 
lean_dec_ref(v_pre_1623_);
lean_dec_ref(v_fst_1622_);
lean_dec_ref(v___x_1621_);
lean_del_object(v___x_1168_);
v___x_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1660_, 0, v_r_1524_);
return v___x_1660_;
}
}
else
{
lean_object* v___x_1661_; 
lean_dec(v_pre_1623_);
lean_dec_ref(v_fst_1622_);
lean_dec_ref(v___x_1621_);
lean_del_object(v___x_1168_);
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_r_1524_);
return v___x_1661_;
}
}
else
{
lean_object* v___x_1662_; 
lean_dec(v_fst_1622_);
lean_dec_ref(v___x_1621_);
lean_del_object(v___x_1168_);
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v_r_1524_);
return v___x_1662_;
}
}
v___jp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1528_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81));
v___x_1529_ = l_Lean_Expr_const___override(v___x_1528_, v_us_1501_);
v___x_1530_ = l_Lean_mkAppB(v___x_1529_, v_n_1526_, v_x_1527_);
v___x_1531_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1530_, v_r_1524_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v_r_1524_);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
else
{
lean_object* v___x_1534_; 
lean_dec_ref(v___x_1530_);
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_r_1524_);
return v___x_1534_;
}
}
v___jp_1535_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1538_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83));
v___x_1539_ = l_Lean_Expr_const___override(v___x_1538_, v_us_1501_);
v___x_1540_ = l_Lean_mkAppB(v___x_1539_, v_n_1536_, v_i_1537_);
v___x_1541_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1540_, v_r_1524_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v_r_1524_);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
return v___x_1543_;
}
else
{
lean_object* v___x_1544_; 
lean_dec_ref(v___x_1540_);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_r_1524_);
return v___x_1544_;
}
}
v___jp_1545_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1547_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85));
v___x_1548_ = l_Lean_Expr_const___override(v___x_1547_, v_us_1501_);
lean_inc_ref(v_x_1546_);
v___x_1549_ = l_Lean_Expr_app___override(v___x_1548_, v_x_1546_);
v___x_1550_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1549_, v_r_1524_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v_r_1524_);
v___y_1505_ = v_x_1546_;
v___y_1506_ = v___x_1551_;
goto v___jp_1504_;
}
else
{
lean_dec_ref(v___x_1549_);
v___y_1505_ = v_x_1546_;
v___y_1506_ = v_r_1524_;
goto v___jp_1504_;
}
}
}
else
{
lean_dec(v_us_1501_);
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
}
v___jp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1507_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76));
v___x_1508_ = l_Lean_Expr_const___override(v___x_1507_, v_us_1501_);
v___x_1509_ = l_Lean_Expr_app___override(v___x_1508_, v___y_1505_);
v___x_1510_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v___x_1509_, v___y_1506_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1512_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 1);
lean_ctor_set(v___x_1168_, 1, v___y_1506_);
lean_ctor_set(v___x_1168_, 0, v___x_1509_);
v___x_1512_ = v___x_1168_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___y_1506_);
v___x_1512_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
else
{
lean_object* v___x_1515_; 
lean_dec_ref(v___x_1509_);
lean_del_object(v___x_1168_);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___y_1506_);
return v___x_1515_;
}
}
}
else
{
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
}
else
{
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
}
else
{
lean_del_object(v___x_1168_);
lean_dec(v_snd_1166_);
goto v___jp_1150_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_1164_);
lean_dec_ref(v_fst_1163_);
lean_dec_ref(v___x_1162_);
goto v___jp_1150_;
}
}
case 0:
{
lean_object* v_snd_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1695_; 
v_snd_1665_ = lean_ctor_get(v___x_1162_, 1);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; 
v_unused_1696_ = lean_ctor_get(v___x_1162_, 0);
lean_dec(v_unused_1696_);
v___x_1667_ = v___x_1162_;
v_isShared_1668_ = v_isSharedCheck_1695_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_snd_1665_);
lean_dec(v___x_1162_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1695_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_str_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v_str_1669_ = lean_ctor_get(v_fst_1163_, 1);
lean_inc_ref(v_str_1669_);
lean_dec_ref(v_fst_1163_);
v___x_1670_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91));
v___x_1671_ = lean_string_dec_eq(v_str_1669_, v___x_1670_);
lean_dec_ref(v_str_1669_);
if (v___x_1671_ == 0)
{
lean_del_object(v___x_1667_);
lean_dec(v_snd_1665_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1672_ = lean_array_get_size(v_snd_1665_);
v___x_1673_ = lean_unsigned_to_nat(5u);
v___x_1674_ = lean_nat_dec_eq(v___x_1672_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_del_object(v___x_1667_);
lean_dec(v_snd_1665_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = lean_array_fget(v_snd_1665_, v___x_1675_);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2, &l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
v___x_1679_ = lean_expr_eqv(v___x_1676_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; 
lean_dec(v___x_1676_);
lean_del_object(v___x_1667_);
lean_dec(v_snd_1665_);
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1677_);
return v___x_1680_;
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1681_ = lean_unsigned_to_nat(1u);
v___x_1682_ = lean_array_fget(v_snd_1665_, v___x_1681_);
v___x_1683_ = lean_unsigned_to_nat(2u);
v___x_1684_ = lean_array_fget(v_snd_1665_, v___x_1683_);
v___x_1685_ = lean_unsigned_to_nat(3u);
v___x_1686_ = lean_array_fget(v_snd_1665_, v___x_1685_);
v___x_1687_ = lean_unsigned_to_nat(4u);
v___x_1688_ = lean_array_fget(v_snd_1665_, v___x_1687_);
lean_dec(v_snd_1665_);
v___x_1689_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94, &l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94_once, _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94);
v___x_1690_ = l_Lean_mkApp5(v___x_1689_, v___x_1676_, v___x_1682_, v___x_1684_, v___x_1686_, v___x_1688_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 1);
lean_ctor_set(v___x_1667_, 1, v___x_1677_);
lean_ctor_set(v___x_1667_, 0, v___x_1690_);
v___x_1692_ = v___x_1667_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1677_);
v___x_1692_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
return v___x_1693_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_fst_1163_);
lean_dec_ref(v___x_1162_);
goto v___jp_1150_;
}
}
}
else
{
lean_dec(v_fst_1163_);
lean_dec_ref(v___x_1162_);
goto v___jp_1150_;
}
v___jp_1144_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
v___jp_1147_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = lean_box(0);
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
v___jp_1150_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_box(0);
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
v___jp_1153_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
v___jp_1156_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
v___jp_1159_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(lean_object* v_e_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_e_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec_ref(v_a_1698_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object* v_e_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, uint8_t v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_e_1705_, v_a_1708_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object* v_e_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
uint8_t v_a_boxed_1728_; lean_object* v_res_1729_; 
v_a_boxed_1728_ = lean_unbox(v_a_1721_);
v_res_1729_ = l_Lean_Elab_Tactic_Omega_analyzeAtom(v_e_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_boxed_1728_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec(v_a_1718_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object* v_cls_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_options_1736_; uint8_t v_hasTrace_1737_; 
v_options_1736_ = lean_ctor_get(v___y_1734_, 2);
v_hasTrace_1737_ = lean_ctor_get_uint8(v_options_1736_, sizeof(void*)*1);
if (v_hasTrace_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v_cls_1733_);
v___x_1738_ = lean_box(v_hasTrace_1737_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
else
{
lean_object* v_inheritedTraceOptions_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_inheritedTraceOptions_1740_ = lean_ctor_get(v___y_1734_, 13);
v___x_1741_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1));
v___x_1742_ = l_Lean_Name_append(v___x_1741_, v_cls_1733_);
v___x_1743_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1740_, v_options_1736_, v___x_1742_);
lean_dec(v___x_1742_);
v___x_1744_ = lean_box(v___x_1743_);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(lean_object* v_cls_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_cls_1746_, v___y_1747_);
lean_dec_ref(v___y_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object* v_cls_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, uint8_t v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_cls_1750_, v___y_1758_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(lean_object* v_cls_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
uint8_t v___y_33096__boxed_1773_; lean_object* v_res_1774_; 
v___y_33096__boxed_1773_ = lean_unbox(v___y_1766_);
v_res_1774_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(v_cls_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_33096__boxed_1773_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec(v___y_1763_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(lean_object* v_a_1775_, lean_object* v_x_1776_){
_start:
{
if (lean_obj_tag(v_x_1776_) == 0)
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_box(0);
return v___x_1777_;
}
else
{
lean_object* v_key_1778_; lean_object* v_value_1779_; lean_object* v_tail_1780_; uint8_t v___x_1781_; 
v_key_1778_ = lean_ctor_get(v_x_1776_, 0);
v_value_1779_ = lean_ctor_get(v_x_1776_, 1);
v_tail_1780_ = lean_ctor_get(v_x_1776_, 2);
v___x_1781_ = lean_expr_eqv(v_key_1778_, v_a_1775_);
if (v___x_1781_ == 0)
{
v_x_1776_ = v_tail_1780_;
goto _start;
}
else
{
lean_object* v___x_1783_; 
lean_inc(v_value_1779_);
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_value_1779_);
return v___x_1783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg___boxed(lean_object* v_a_1784_, lean_object* v_x_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_1784_, v_x_1785_);
lean_dec(v_x_1785_);
lean_dec_ref(v_a_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object* v_m_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_buckets_1789_; lean_object* v___x_1790_; uint64_t v___x_1791_; uint64_t v___x_1792_; uint64_t v___x_1793_; uint64_t v_fold_1794_; uint64_t v___x_1795_; uint64_t v___x_1796_; uint64_t v___x_1797_; size_t v___x_1798_; size_t v___x_1799_; size_t v___x_1800_; size_t v___x_1801_; size_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v_buckets_1789_ = lean_ctor_get(v_m_1787_, 1);
v___x_1790_ = lean_array_get_size(v_buckets_1789_);
v___x_1791_ = l_Lean_Expr_hash(v_a_1788_);
v___x_1792_ = 32ULL;
v___x_1793_ = lean_uint64_shift_right(v___x_1791_, v___x_1792_);
v_fold_1794_ = lean_uint64_xor(v___x_1791_, v___x_1793_);
v___x_1795_ = 16ULL;
v___x_1796_ = lean_uint64_shift_right(v_fold_1794_, v___x_1795_);
v___x_1797_ = lean_uint64_xor(v_fold_1794_, v___x_1796_);
v___x_1798_ = lean_uint64_to_usize(v___x_1797_);
v___x_1799_ = lean_usize_of_nat(v___x_1790_);
v___x_1800_ = ((size_t)1ULL);
v___x_1801_ = lean_usize_sub(v___x_1799_, v___x_1800_);
v___x_1802_ = lean_usize_land(v___x_1798_, v___x_1801_);
v___x_1803_ = lean_array_uget_borrowed(v_buckets_1789_, v___x_1802_);
v___x_1804_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_1788_, v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(lean_object* v_m_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_1805_, v_a_1806_);
lean_dec_ref(v_a_1806_);
lean_dec_ref(v_m_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg(lean_object* v_x_1808_, lean_object* v_x_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
if (lean_obj_tag(v_x_1808_) == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = l_List_reverse___redArg(v_x_1809_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
else
{
lean_object* v_head_1817_; lean_object* v_tail_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1836_; 
v_head_1817_ = lean_ctor_get(v_x_1808_, 0);
v_tail_1818_ = lean_ctor_get(v_x_1808_, 1);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_x_1808_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1820_ = v_x_1808_;
v_isShared_1821_ = v_isSharedCheck_1836_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_tail_1818_);
lean_inc(v_head_1817_);
lean_dec(v_x_1808_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1836_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; 
lean_inc(v___y_1813_);
lean_inc_ref(v___y_1812_);
lean_inc(v___y_1811_);
lean_inc_ref(v___y_1810_);
v___x_1822_ = lean_infer_type(v_head_1817_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref(v___x_1822_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 1, v_x_1809_);
lean_ctor_set(v___x_1820_, 0, v_a_1823_);
v___x_1825_ = v___x_1820_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1823_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_x_1809_);
v___x_1825_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
v_x_1808_ = v_tail_1818_;
v_x_1809_ = v___x_1825_;
goto _start;
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_del_object(v___x_1820_);
lean_dec(v_tail_1818_);
lean_dec(v_x_1809_);
v_a_1828_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1822_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1822_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg___boxed(lean_object* v_x_1837_, lean_object* v_x_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg(v_x_1837_, v_x_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
return v_res_1844_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(lean_object* v_a_1845_, lean_object* v_x_1846_){
_start:
{
if (lean_obj_tag(v_x_1846_) == 0)
{
uint8_t v___x_1847_; 
v___x_1847_ = 0;
return v___x_1847_;
}
else
{
lean_object* v_key_1848_; lean_object* v_tail_1849_; uint8_t v___x_1850_; 
v_key_1848_ = lean_ctor_get(v_x_1846_, 0);
v_tail_1849_ = lean_ctor_get(v_x_1846_, 2);
v___x_1850_ = lean_expr_eqv(v_key_1848_, v_a_1845_);
if (v___x_1850_ == 0)
{
v_x_1846_ = v_tail_1849_;
goto _start;
}
else
{
return v___x_1850_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg___boxed(lean_object* v_a_1852_, lean_object* v_x_1853_){
_start:
{
uint8_t v_res_1854_; lean_object* v_r_1855_; 
v_res_1854_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_1852_, v_x_1853_);
lean_dec(v_x_1853_);
lean_dec_ref(v_a_1852_);
v_r_1855_ = lean_box(v_res_1854_);
return v_r_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
if (lean_obj_tag(v_x_1857_) == 0)
{
return v_x_1856_;
}
else
{
lean_object* v_key_1858_; lean_object* v_value_1859_; lean_object* v_tail_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1883_; 
v_key_1858_ = lean_ctor_get(v_x_1857_, 0);
v_value_1859_ = lean_ctor_get(v_x_1857_, 1);
v_tail_1860_ = lean_ctor_get(v_x_1857_, 2);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_x_1857_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1862_ = v_x_1857_;
v_isShared_1863_ = v_isSharedCheck_1883_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_tail_1860_);
lean_inc(v_value_1859_);
lean_inc(v_key_1858_);
lean_dec(v_x_1857_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1883_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; uint64_t v___x_1865_; uint64_t v___x_1866_; uint64_t v___x_1867_; uint64_t v_fold_1868_; uint64_t v___x_1869_; uint64_t v___x_1870_; uint64_t v___x_1871_; size_t v___x_1872_; size_t v___x_1873_; size_t v___x_1874_; size_t v___x_1875_; size_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1864_ = lean_array_get_size(v_x_1856_);
v___x_1865_ = l_Lean_Expr_hash(v_key_1858_);
v___x_1866_ = 32ULL;
v___x_1867_ = lean_uint64_shift_right(v___x_1865_, v___x_1866_);
v_fold_1868_ = lean_uint64_xor(v___x_1865_, v___x_1867_);
v___x_1869_ = 16ULL;
v___x_1870_ = lean_uint64_shift_right(v_fold_1868_, v___x_1869_);
v___x_1871_ = lean_uint64_xor(v_fold_1868_, v___x_1870_);
v___x_1872_ = lean_uint64_to_usize(v___x_1871_);
v___x_1873_ = lean_usize_of_nat(v___x_1864_);
v___x_1874_ = ((size_t)1ULL);
v___x_1875_ = lean_usize_sub(v___x_1873_, v___x_1874_);
v___x_1876_ = lean_usize_land(v___x_1872_, v___x_1875_);
v___x_1877_ = lean_array_uget_borrowed(v_x_1856_, v___x_1876_);
lean_inc(v___x_1877_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 2, v___x_1877_);
v___x_1879_ = v___x_1862_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_key_1858_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_value_1859_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_array_uset(v_x_1856_, v___x_1876_, v___x_1879_);
v_x_1856_ = v___x_1880_;
v_x_1857_ = v_tail_1860_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__5___redArg(lean_object* v_i_1884_, lean_object* v_source_1885_, lean_object* v_target_1886_){
_start:
{
lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1887_ = lean_array_get_size(v_source_1885_);
v___x_1888_ = lean_nat_dec_lt(v_i_1884_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_dec_ref(v_source_1885_);
lean_dec(v_i_1884_);
return v_target_1886_;
}
else
{
lean_object* v_es_1889_; lean_object* v___x_1890_; lean_object* v_source_1891_; lean_object* v_target_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_es_1889_ = lean_array_fget(v_source_1885_, v_i_1884_);
v___x_1890_ = lean_box(0);
v_source_1891_ = lean_array_fset(v_source_1885_, v_i_1884_, v___x_1890_);
v_target_1892_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__5_spec__10___redArg(v_target_1886_, v_es_1889_);
v___x_1893_ = lean_unsigned_to_nat(1u);
v___x_1894_ = lean_nat_add(v_i_1884_, v___x_1893_);
lean_dec(v_i_1884_);
v_i_1884_ = v___x_1894_;
v_source_1885_ = v_source_1891_;
v_target_1886_ = v_target_1892_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(lean_object* v_data_1896_){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v_nbuckets_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1897_ = lean_array_get_size(v_data_1896_);
v___x_1898_ = lean_unsigned_to_nat(2u);
v_nbuckets_1899_ = lean_nat_mul(v___x_1897_, v___x_1898_);
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = lean_box(0);
v___x_1902_ = lean_mk_array(v_nbuckets_1899_, v___x_1901_);
v___x_1903_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__5___redArg(v___x_1900_, v_data_1896_, v___x_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(lean_object* v_a_1904_, lean_object* v_b_1905_, lean_object* v_x_1906_){
_start:
{
if (lean_obj_tag(v_x_1906_) == 0)
{
lean_dec(v_b_1905_);
lean_dec_ref(v_a_1904_);
return v_x_1906_;
}
else
{
lean_object* v_key_1907_; lean_object* v_value_1908_; lean_object* v_tail_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1921_; 
v_key_1907_ = lean_ctor_get(v_x_1906_, 0);
v_value_1908_ = lean_ctor_get(v_x_1906_, 1);
v_tail_1909_ = lean_ctor_get(v_x_1906_, 2);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_x_1906_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1911_ = v_x_1906_;
v_isShared_1912_ = v_isSharedCheck_1921_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_tail_1909_);
lean_inc(v_value_1908_);
lean_inc(v_key_1907_);
lean_dec(v_x_1906_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1921_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
uint8_t v___x_1913_; 
v___x_1913_ = lean_expr_eqv(v_key_1907_, v_a_1904_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_1904_, v_b_1905_, v_tail_1909_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 2, v___x_1914_);
v___x_1916_ = v___x_1911_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_key_1907_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_value_1908_);
lean_ctor_set(v_reuseFailAlloc_1917_, 2, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
else
{
lean_object* v___x_1919_; 
lean_dec(v_value_1908_);
lean_dec(v_key_1907_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 1, v_b_1905_);
lean_ctor_set(v___x_1911_, 0, v_a_1904_);
v___x_1919_ = v___x_1911_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1904_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_b_1905_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_tail_1909_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object* v_m_1922_, lean_object* v_a_1923_, lean_object* v_b_1924_){
_start:
{
lean_object* v_size_1925_; lean_object* v_buckets_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1969_; 
v_size_1925_ = lean_ctor_get(v_m_1922_, 0);
v_buckets_1926_ = lean_ctor_get(v_m_1922_, 1);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_m_1922_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1928_ = v_m_1922_;
v_isShared_1929_ = v_isSharedCheck_1969_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_buckets_1926_);
lean_inc(v_size_1925_);
lean_dec(v_m_1922_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1969_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; uint64_t v___x_1931_; uint64_t v___x_1932_; uint64_t v___x_1933_; uint64_t v_fold_1934_; uint64_t v___x_1935_; uint64_t v___x_1936_; uint64_t v___x_1937_; size_t v___x_1938_; size_t v___x_1939_; size_t v___x_1940_; size_t v___x_1941_; size_t v___x_1942_; lean_object* v_bkt_1943_; uint8_t v___x_1944_; 
v___x_1930_ = lean_array_get_size(v_buckets_1926_);
v___x_1931_ = l_Lean_Expr_hash(v_a_1923_);
v___x_1932_ = 32ULL;
v___x_1933_ = lean_uint64_shift_right(v___x_1931_, v___x_1932_);
v_fold_1934_ = lean_uint64_xor(v___x_1931_, v___x_1933_);
v___x_1935_ = 16ULL;
v___x_1936_ = lean_uint64_shift_right(v_fold_1934_, v___x_1935_);
v___x_1937_ = lean_uint64_xor(v_fold_1934_, v___x_1936_);
v___x_1938_ = lean_uint64_to_usize(v___x_1937_);
v___x_1939_ = lean_usize_of_nat(v___x_1930_);
v___x_1940_ = ((size_t)1ULL);
v___x_1941_ = lean_usize_sub(v___x_1939_, v___x_1940_);
v___x_1942_ = lean_usize_land(v___x_1938_, v___x_1941_);
v_bkt_1943_ = lean_array_uget_borrowed(v_buckets_1926_, v___x_1942_);
v___x_1944_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_1923_, v_bkt_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v_size_x27_1946_; lean_object* v___x_1947_; lean_object* v_buckets_x27_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v___x_1945_ = lean_unsigned_to_nat(1u);
v_size_x27_1946_ = lean_nat_add(v_size_1925_, v___x_1945_);
lean_dec(v_size_1925_);
lean_inc(v_bkt_1943_);
v___x_1947_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1947_, 0, v_a_1923_);
lean_ctor_set(v___x_1947_, 1, v_b_1924_);
lean_ctor_set(v___x_1947_, 2, v_bkt_1943_);
v_buckets_x27_1948_ = lean_array_uset(v_buckets_1926_, v___x_1942_, v___x_1947_);
v___x_1949_ = lean_unsigned_to_nat(4u);
v___x_1950_ = lean_nat_mul(v_size_x27_1946_, v___x_1949_);
v___x_1951_ = lean_unsigned_to_nat(3u);
v___x_1952_ = lean_nat_div(v___x_1950_, v___x_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_array_get_size(v_buckets_x27_1948_);
v___x_1954_ = lean_nat_dec_le(v___x_1952_, v___x_1953_);
lean_dec(v___x_1952_);
if (v___x_1954_ == 0)
{
lean_object* v_val_1955_; lean_object* v___x_1957_; 
v_val_1955_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_buckets_x27_1948_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v_val_1955_);
lean_ctor_set(v___x_1928_, 0, v_size_x27_1946_);
v___x_1957_ = v___x_1928_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_size_x27_1946_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_val_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
else
{
lean_object* v___x_1960_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v_buckets_x27_1948_);
lean_ctor_set(v___x_1928_, 0, v_size_x27_1946_);
v___x_1960_ = v___x_1928_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_size_x27_1946_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_buckets_x27_1948_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
else
{
lean_object* v___x_1962_; lean_object* v_buckets_x27_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
lean_inc(v_bkt_1943_);
v___x_1962_ = lean_box(0);
v_buckets_x27_1963_ = lean_array_uset(v_buckets_1926_, v___x_1942_, v___x_1962_);
v___x_1964_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_1923_, v_b_1924_, v_bkt_1943_);
v___x_1965_ = lean_array_uset(v_buckets_x27_1963_, v___x_1942_, v___x_1964_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v___x_1965_);
v___x_1967_ = v___x_1928_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_size_1925_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
if (lean_obj_tag(v_a_1970_) == 0)
{
lean_object* v___x_1972_; 
v___x_1972_ = l_List_reverse___redArg(v_a_1971_);
return v___x_1972_;
}
else
{
lean_object* v_head_1973_; lean_object* v_tail_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1983_; 
v_head_1973_ = lean_ctor_get(v_a_1970_, 0);
v_tail_1974_ = lean_ctor_get(v_a_1970_, 1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_a_1970_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1976_ = v_a_1970_;
v_isShared_1977_ = v_isSharedCheck_1983_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_tail_1974_);
lean_inc(v_head_1973_);
lean_dec(v_a_1970_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1983_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1978_ = l_Lean_MessageData_ofExpr(v_head_1973_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v_a_1971_);
lean_ctor_set(v___x_1976_, 0, v___x_1978_);
v___x_1980_ = v___x_1976_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_a_1971_);
v___x_1980_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
v_a_1970_ = v_tail_1974_;
v_a_1971_ = v___x_1980_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5_spec__9(lean_object* v_msgData_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1990_; lean_object* v_env_1991_; lean_object* v___x_1992_; lean_object* v_mctx_1993_; lean_object* v_lctx_1994_; lean_object* v_options_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1990_ = lean_st_ref_get(v___y_1988_);
v_env_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc_ref(v_env_1991_);
lean_dec(v___x_1990_);
v___x_1992_ = lean_st_ref_get(v___y_1986_);
v_mctx_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc_ref(v_mctx_1993_);
lean_dec(v___x_1992_);
v_lctx_1994_ = lean_ctor_get(v___y_1985_, 2);
v_options_1995_ = lean_ctor_get(v___y_1987_, 2);
lean_inc_ref(v_options_1995_);
lean_inc_ref(v_lctx_1994_);
v___x_1996_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1996_, 0, v_env_1991_);
lean_ctor_set(v___x_1996_, 1, v_mctx_1993_);
lean_ctor_set(v___x_1996_, 2, v_lctx_1994_);
lean_ctor_set(v___x_1996_, 3, v_options_1995_);
v___x_1997_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v_msgData_1984_);
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5_spec__9___boxed(lean_object* v_msgData_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5_spec__9(v_msgData_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
return v_res_2005_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2006_; double v___x_2007_; 
v___x_2006_ = lean_unsigned_to_nat(0u);
v___x_2007_ = lean_float_of_nat(v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(lean_object* v_cls_2011_, lean_object* v_msg_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_ref_2018_; lean_object* v___x_2019_; lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2064_; 
v_ref_2018_ = lean_ctor_get(v___y_2015_, 5);
v___x_2019_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5_spec__9(v_msg_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2064_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2064_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v_traceState_2025_; lean_object* v_env_2026_; lean_object* v_nextMacroScope_2027_; lean_object* v_ngen_2028_; lean_object* v_auxDeclNGen_2029_; lean_object* v_cache_2030_; lean_object* v_messages_2031_; lean_object* v_infoState_2032_; lean_object* v_snapshotTasks_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2063_; 
v___x_2024_ = lean_st_ref_take(v___y_2016_);
v_traceState_2025_ = lean_ctor_get(v___x_2024_, 4);
v_env_2026_ = lean_ctor_get(v___x_2024_, 0);
v_nextMacroScope_2027_ = lean_ctor_get(v___x_2024_, 1);
v_ngen_2028_ = lean_ctor_get(v___x_2024_, 2);
v_auxDeclNGen_2029_ = lean_ctor_get(v___x_2024_, 3);
v_cache_2030_ = lean_ctor_get(v___x_2024_, 5);
v_messages_2031_ = lean_ctor_get(v___x_2024_, 6);
v_infoState_2032_ = lean_ctor_get(v___x_2024_, 7);
v_snapshotTasks_2033_ = lean_ctor_get(v___x_2024_, 8);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2035_ = v___x_2024_;
v_isShared_2036_ = v_isSharedCheck_2063_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_snapshotTasks_2033_);
lean_inc(v_infoState_2032_);
lean_inc(v_messages_2031_);
lean_inc(v_cache_2030_);
lean_inc(v_traceState_2025_);
lean_inc(v_auxDeclNGen_2029_);
lean_inc(v_ngen_2028_);
lean_inc(v_nextMacroScope_2027_);
lean_inc(v_env_2026_);
lean_dec(v___x_2024_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2063_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
uint64_t v_tid_2037_; lean_object* v_traces_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2062_; 
v_tid_2037_ = lean_ctor_get_uint64(v_traceState_2025_, sizeof(void*)*1);
v_traces_2038_ = lean_ctor_get(v_traceState_2025_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_traceState_2025_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2040_ = v_traceState_2025_;
v_isShared_2041_ = v_isSharedCheck_2062_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_traces_2038_);
lean_dec(v_traceState_2025_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2062_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; double v___x_2043_; uint8_t v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2042_ = lean_box(0);
v___x_2043_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__0);
v___x_2044_ = 0;
v___x_2045_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__1));
v___x_2046_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2046_, 0, v_cls_2011_);
lean_ctor_set(v___x_2046_, 1, v___x_2042_);
lean_ctor_set(v___x_2046_, 2, v___x_2045_);
lean_ctor_set_float(v___x_2046_, sizeof(void*)*3, v___x_2043_);
lean_ctor_set_float(v___x_2046_, sizeof(void*)*3 + 8, v___x_2043_);
lean_ctor_set_uint8(v___x_2046_, sizeof(void*)*3 + 16, v___x_2044_);
v___x_2047_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___closed__2));
v___x_2048_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v_a_2020_);
lean_ctor_set(v___x_2048_, 2, v___x_2047_);
lean_inc(v_ref_2018_);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v_ref_2018_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = l_Lean_PersistentArray_push___redArg(v_traces_2038_, v___x_2049_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2050_);
v___x_2052_ = v___x_2040_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2050_);
lean_ctor_set_uint64(v_reuseFailAlloc_2061_, sizeof(void*)*1, v_tid_2037_);
v___x_2052_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2054_; 
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 4, v___x_2052_);
v___x_2054_ = v___x_2035_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_env_2026_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_nextMacroScope_2027_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_ngen_2028_);
lean_ctor_set(v_reuseFailAlloc_2060_, 3, v_auxDeclNGen_2029_);
lean_ctor_set(v_reuseFailAlloc_2060_, 4, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2060_, 5, v_cache_2030_);
lean_ctor_set(v_reuseFailAlloc_2060_, 6, v_messages_2031_);
lean_ctor_set(v_reuseFailAlloc_2060_, 7, v_infoState_2032_);
lean_ctor_set(v_reuseFailAlloc_2060_, 8, v_snapshotTasks_2033_);
v___x_2054_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2055_ = lean_st_ref_set(v___y_2016_, v___x_2054_);
v___x_2056_ = lean_box(0);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2056_);
v___x_2058_ = v___x_2022_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg___boxed(lean_object* v_cls_2065_, lean_object* v_msg_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(v_cls_2065_, v_msg_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
return v_res_2072_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__3(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__2));
v___x_2078_ = l_Lean_stringToMessageData(v___x_2077_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__5(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__4));
v___x_2081_ = l_Lean_stringToMessageData(v___x_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object* v_e_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, uint8_t v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_st_ref_get(v_a_2084_);
v___x_2094_ = l_Lean_Meta_Canonicalizer_canon(v_e_2082_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2189_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2189_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2189_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___x_2111_; 
v___x_2111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v___x_2093_, v_a_2095_);
lean_dec(v___x_2093_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v___x_2112_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; uint8_t v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___x_2164_; lean_object* v_a_2165_; uint8_t v___x_2166_; 
v___x_2112_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_lookup___closed__1));
v___x_2164_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v___x_2112_, v_a_2090_);
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref(v___x_2164_);
v___x_2166_ = lean_unbox(v_a_2165_);
lean_dec(v_a_2165_);
if (v___x_2166_ == 0)
{
v___y_2114_ = v_a_2083_;
v___y_2115_ = v_a_2084_;
v___y_2116_ = v_a_2085_;
v___y_2117_ = v_a_2086_;
v___y_2118_ = v_a_2087_;
v___y_2119_ = v_a_2088_;
v___y_2120_ = v_a_2089_;
v___y_2121_ = v_a_2090_;
v___y_2122_ = v_a_2091_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2167_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__5, &l_Lean_Elab_Tactic_Omega_lookup___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__5);
lean_inc(v_a_2095_);
v___x_2168_ = l_Lean_MessageData_ofExpr(v_a_2095_);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(v___x_2112_, v___x_2169_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_dec_ref(v___x_2170_);
v___y_2114_ = v_a_2083_;
v___y_2115_ = v_a_2084_;
v___y_2116_ = v_a_2085_;
v___y_2117_ = v_a_2086_;
v___y_2118_ = v_a_2087_;
v___y_2119_ = v_a_2088_;
v___y_2120_ = v_a_2089_;
v___y_2121_ = v_a_2090_;
v___y_2122_ = v_a_2091_;
goto v___jp_2113_;
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_del_object(v___x_2097_);
lean_dec(v_a_2095_);
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
v___jp_2113_:
{
lean_object* v___x_2123_; 
lean_inc(v_a_2095_);
v___x_2123_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(v_a_2095_, v___y_2116_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2125_; lean_object* v_a_2126_; uint8_t v___x_2127_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref(v___x_2123_);
v___x_2125_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v___x_2112_, v___y_2121_);
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref(v___x_2125_);
v___x_2127_ = lean_unbox(v_a_2126_);
lean_dec(v_a_2126_);
if (v___x_2127_ == 0)
{
v___y_2100_ = v_a_2124_;
v___y_2101_ = v___y_2115_;
goto v___jp_2099_;
}
else
{
uint8_t v___x_2128_; 
v___x_2128_ = l_List_isEmpty___redArg(v_a_2124_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; lean_object* v_a_2130_; uint8_t v___x_2131_; 
v___x_2129_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v___x_2112_, v___y_2121_);
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v___x_2129_);
v___x_2131_ = lean_unbox(v_a_2130_);
lean_dec(v_a_2130_);
if (v___x_2131_ == 0)
{
v___y_2100_ = v_a_2124_;
v___y_2101_ = v___y_2115_;
goto v___jp_2099_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = lean_box(0);
lean_inc(v_a_2124_);
v___x_2133_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg(v_a_2124_, v___x_2132_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref(v___x_2133_);
v___x_2135_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_lookup___closed__3, &l_Lean_Elab_Tactic_Omega_lookup___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_lookup___closed__3);
v___x_2136_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(v_a_2134_, v___x_2132_);
v___x_2137_ = l_Lean_MessageData_ofList(v___x_2136_);
v___x_2138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2135_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(v___x_2112_, v___x_2138_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_dec_ref(v___x_2139_);
v___y_2100_ = v_a_2124_;
v___y_2101_ = v___y_2115_;
goto v___jp_2099_;
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_a_2124_);
lean_del_object(v___x_2097_);
lean_dec(v_a_2095_);
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_a_2124_);
lean_del_object(v___x_2097_);
lean_dec(v_a_2095_);
v_a_2148_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2133_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2133_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
else
{
v___y_2100_ = v_a_2124_;
v___y_2101_ = v___y_2115_;
goto v___jp_2099_;
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_del_object(v___x_2097_);
lean_dec(v_a_2095_);
v_a_2156_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2123_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2123_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
else
{
lean_object* v_val_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2188_; 
lean_del_object(v___x_2097_);
lean_dec(v_a_2095_);
v_val_2179_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2181_ = v___x_2111_;
v_isShared_2182_ = v_isSharedCheck_2188_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_val_2179_);
lean_dec(v___x_2111_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2188_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2183_ = lean_box(0);
v___x_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2184_, 0, v_val_2179_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set_tag(v___x_2181_, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2184_);
v___x_2186_ = v___x_2181_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
v___jp_2099_:
{
lean_object* v___x_2102_; lean_object* v_size_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2102_ = lean_st_ref_take(v___y_2101_);
v_size_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_size_2103_);
lean_inc(v_size_2103_);
v___x_2104_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v___x_2102_, v_a_2095_, v_size_2103_);
v___x_2105_ = lean_st_ref_set(v___y_2101_, v___x_2104_);
v___x_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___y_2100_);
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v_size_2103_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2107_);
v___x_2109_ = v___x_2097_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v___x_2093_);
v_a_2190_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2094_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2094_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object* v_e_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
uint8_t v_a_boxed_2209_; lean_object* v_res_2210_; 
v_a_boxed_2209_ = lean_unbox(v_a_2202_);
v_res_2210_ = l_Lean_Elab_Tactic_Omega_lookup(v_e_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_boxed_2209_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec(v_a_2199_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(lean_object* v_00_u03b2_2211_, lean_object* v_m_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_2212_, v_a_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(lean_object* v_00_u03b2_2215_, lean_object* v_m_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(v_00_u03b2_2215_, v_m_2216_, v_a_2217_);
lean_dec_ref(v_a_2217_);
lean_dec_ref(v_m_2216_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object* v_00_u03b2_2219_, lean_object* v_m_2220_, lean_object* v_a_2221_, lean_object* v_b_2222_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v_m_2220_, v_a_2221_, v_b_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(lean_object* v_x_2224_, lean_object* v_x_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, uint8_t v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___redArg(v_x_2224_, v_x_2225_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3___boxed(lean_object* v_x_2237_, lean_object* v_x_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
uint8_t v___y_33848__boxed_2249_; lean_object* v_res_2250_; 
v___y_33848__boxed_2249_ = lean_unbox(v___y_2242_);
v_res_2250_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(v_x_2237_, v_x_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_33848__boxed_2249_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec(v___y_2239_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5(lean_object* v_cls_2251_, lean_object* v_msg_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, uint8_t v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(v_cls_2251_, v_msg_2252_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5___boxed(lean_object* v_cls_2264_, lean_object* v_msg_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
uint8_t v___y_33884__boxed_2276_; lean_object* v_res_2277_; 
v___y_33884__boxed_2276_ = lean_unbox(v___y_2269_);
v_res_2277_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__5(v_cls_2264_, v_msg_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_33884__boxed_2276_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec(v___y_2266_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(lean_object* v_00_u03b2_2278_, lean_object* v_a_2279_, lean_object* v_x_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_2279_, v_x_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2282_, lean_object* v_a_2283_, lean_object* v_x_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(v_00_u03b2_2282_, v_a_2283_, v_x_2284_);
lean_dec(v_x_2284_);
lean_dec_ref(v_a_2283_);
return v_res_2285_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(lean_object* v_00_u03b2_2286_, lean_object* v_a_2287_, lean_object* v_x_2288_){
_start:
{
uint8_t v___x_2289_; 
v___x_2289_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_2287_, v_x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2290_, lean_object* v_a_2291_, lean_object* v_x_2292_){
_start:
{
uint8_t v_res_2293_; lean_object* v_r_2294_; 
v_res_2293_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(v_00_u03b2_2290_, v_a_2291_, v_x_2292_);
lean_dec(v_x_2292_);
lean_dec_ref(v_a_2291_);
v_r_2294_ = lean_box(v_res_2293_);
return v_r_2294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3(lean_object* v_00_u03b2_2295_, lean_object* v_data_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_data_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4(lean_object* v_00_u03b2_2298_, lean_object* v_a_2299_, lean_object* v_b_2300_, lean_object* v_x_2301_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_2299_, v_b_2300_, v_x_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2303_, lean_object* v_i_2304_, lean_object* v_source_2305_, lean_object* v_target_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__5___redArg(v_i_2304_, v_source_2305_, v_target_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2308_, lean_object* v_x_2309_, lean_object* v_x_2310_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__5_spec__10___redArg(v_x_2309_, v_x_2310_);
return v___x_2311_;
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
