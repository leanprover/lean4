// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.Core
// Imports: public import Lean.Elab.Tactic.Omega.OmegaM public import Lean.Elab.Tactic.Omega.MinNatAbs
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
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Omega_IntList_get(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_combo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Omega_Constraint_combo(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Omega_Constraint_scale(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Omega_tidy_x3f(lean_object*);
lean_object* l_Lean_Omega_tidy(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_Omega_Constraint_isImpossible(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Omega_Constraint_isExact(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Omega_Constraint_instToString___private__1(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Omega_instBEqConstraint_beq(lean_object*, lean_object*);
lean_object* l_Lean_Omega_Constraint_exact(lean_object*);
lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Omega_Constraint_combine(lean_object*, lean_object*);
uint8_t l_Lean_Omega_instDecidableEqConstraint_decEq(lean_object*, lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_Omega_List_minNatAbs(lean_object*);
lean_object* l_Lean_Elab_Tactic_Omega_List_maxNatAbs(lean_object*);
lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Omega_bmod__coeffs(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_bmod(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Int_sign(lean_object*);
lean_object* l_List_findIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_instToExprInt;
lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_initFn___closed__0_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__0_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__0_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__0_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 155, 144, 136, 132, 122, 189, 157)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_initFn___closed__3_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__3_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__3_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_initFn___closed__5_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__3_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__5_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__5_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_initFn___closed__7_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__5_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__7_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__7_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Omega"};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_initFn___closed__9_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__7_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 53, 129, 54, 72, 225, 204, 101)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__9_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__9_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_initFn___closed__11_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__9_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 236, 185, 128, 250, 178, 8, 155)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__11_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__11_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_initFn___closed__12_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__12_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__12_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_initFn___closed__13_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__11_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__12_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(2, 90, 151, 231, 219, 103, 56, 64)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__13_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__13_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_initFn___closed__14_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__13_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 222, 68, 165, 228, 149, 16, 144)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__14_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__14_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_initFn___closed__15_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__14_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 160, 163, 157, 167, 63, 212, 36)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__15_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__15_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_initFn___closed__16_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__15_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(236, 176, 175, 134, 186, 203, 216, 139)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__16_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__16_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_initFn___closed__17_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__16_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 207, 123, 51, 186, 32, 158, 74)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__17_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__17_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_initFn___closed__18_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Core"};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__18_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__18_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_initFn___closed__19_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__17_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__18_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 105, 51, 14, 200, 107, 167, 153)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__19_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__19_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_initFn___closed__20_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__20_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_;
static const lean_string_object l_Lean_Elab_Tactic_Omega_initFn___closed__21_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__21_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__21_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_initFn___closed__22_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__22_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_;
static const lean_string_object l_Lean_Elab_Tactic_Omega_initFn___closed__23_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__23_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__23_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_initFn___closed__24_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__24_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_initFn___closed__25_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_initFn___closed__25_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "LinearCombo"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 132, 214, 18, 187, 72, 22, 121)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 33, 22, 173, 105, 76, 89, 153)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__18_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__20_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__25_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 132, 214, 18, 187, 72, 22, 121)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Constraint"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 192, 152, 239, 193, 179, 196, 197)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 129, 254, 203, 24, 254, 72, 35)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 192, 152, 239, 193, 179, 196, 197)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0_value;
static const lean_string_object l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6;
static const lean_ctor_object l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__7 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "• "};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\n  "};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1_value;
static const lean_string_object l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ∈ "};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ": assumption "};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ": tidying up:\n"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ": combination of:\n"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " * x + "};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " * y combo of:\n"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ": bmod with m="};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " and i="};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " of:\n"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_instToString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tidy_sat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 191, 70, 188, 16, 136, 82, 137)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "combine_sat'"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 192, 152, 239, 193, 179, 196, 197)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 94, 145, 248, 63, 179, 150, 35)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "combo_sat'"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 91, 1, 2, 53, 174, 185, 82)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__4_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLENat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__7_value),LEAN_SCALAR_PTR_LITERAL(211, 47, 64, 46, 87, 101, 57, 105)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Coeffs"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "length"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__10_value),LEAN_SCALAR_PTR_LITERAL(200, 12, 56, 206, 160, 32, 217, 148)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11_value),LEAN_SCALAR_PTR_LITERAL(170, 70, 58, 212, 39, 249, 136, 90)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "get"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__10_value),LEAN_SCALAR_PTR_LITERAL(200, 12, 56, 206, 160, 32, 217, 148)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__14_value),LEAN_SCALAR_PTR_LITERAL(90, 92, 99, 234, 53, 138, 153, 24)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "bmod_div_term"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__17_value),LEAN_SCALAR_PTR_LITERAL(146, 160, 30, 167, 226, 78, 110, 197)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bmod_sat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__20_value),LEAN_SCALAR_PTR_LITERAL(53, 80, 238, 64, 134, 240, 94, 90)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_instToString___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Fact_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Fact_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Fact_instToString___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Fact_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Omega_Fact_instToString = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Fact_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_tidy(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_combo(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value;
static const lean_array_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_isEmpty___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_repr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "impossible"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__6_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__1_value),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__2_value)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__9_value),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__7_value)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__1_value)} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "isImpossible"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 192, 152, 239, 193, 179, 196, 197)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 130, 136, 130, 117, 192, 112, 247)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "not_sat'_of_isImpossible"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 192, 152, 239, 193, 179, 196, 197)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__7_value),LEAN_SCALAR_PTR_LITERAL(98, 38, 67, 93, 24, 197, 229, 14)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addConstraint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality___boxed(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Invalid constraint, expected an equation."};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "When solving hard equality, new atom had been seen before!"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "When solving hard equality, there were unexpected new facts!"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "addInequality_sat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 192, 152, 239, 193, 179, 196, 197)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 20, 9, 160, 52, 15, 198, 221)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "addEquality_sat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 192, 152, 239, 193, 179, 196, 197)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 42, 95, 243, 198, 248, 249, 159)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequalities(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEqualities(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Fourier-Motzkin elimination data for variable "};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 14, .m_data = "• irrelevant: "};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 15, .m_data = "• lowerBounds: "};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 15, .m_data = "• upperBounds: "};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0___closed__0_value)} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0___closed__0_value)} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__1_value),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__2_value)} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__3_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Selected variable "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__1_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__4 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__4_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "Selecting variable to eliminate from (idx, size, exact) triples:\n"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Running Fourier-Motzkin elimination on:\n"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Running omega on:\n"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_Omega_initFn___closed__20_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_unsigned_to_nat(3193685152u);
v___x_45_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__19_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_46_ = l_Lean_Name_num___override(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_initFn___closed__22_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__21_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_49_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_initFn___closed__20_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_, &l_Lean_Elab_Tactic_Omega_initFn___closed__20_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once, _init_l_Lean_Elab_Tactic_Omega_initFn___closed__20_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_);
v___x_50_ = l_Lean_Name_str___override(v___x_49_, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_initFn___closed__24_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__23_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_53_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_initFn___closed__22_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_, &l_Lean_Elab_Tactic_Omega_initFn___closed__22_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once, _init_l_Lean_Elab_Tactic_Omega_initFn___closed__22_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_);
v___x_54_ = l_Lean_Name_str___override(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_initFn___closed__25_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_unsigned_to_nat(2u);
v___x_56_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_initFn___closed__24_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_, &l_Lean_Elab_Tactic_Omega_initFn___closed__24_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once, _init_l_Lean_Elab_Tactic_Omega_initFn___closed__24_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_);
v___x_57_ = l_Lean_Name_num___override(v___x_56_, v___x_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_59_; uint8_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_60_ = 0;
v___x_61_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_initFn___closed__25_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_, &l_Lean_Elab_Tactic_Omega_initFn___closed__25_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once, _init_l_Lean_Elab_Tactic_Omega_initFn___closed__25_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_);
v___x_62_ = l_Lean_registerTraceClass(v___x_59_, v___x_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2____boxed(lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_();
return v_res_64_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_box(0);
v___x_73_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2));
v___x_74_ = l_Lean_Expr_const___override(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v_type_80_; 
v___x_78_ = lean_box(0);
v___x_79_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__5));
v_type_80_ = l_Lean_Expr_const___override(v___x_79_, v___x_78_);
return v_type_80_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_90_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__9));
v___x_91_ = l_Lean_mkConst(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12(void){
_start:
{
lean_object* v_type_92_; lean_object* v___x_93_; lean_object* v_nil_94_; 
v_type_92_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_93_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11);
v_nil_94_ = l_Lean_Expr_app___override(v___x_93_, v_type_92_);
return v_nil_94_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_100_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__14));
v___x_101_ = l_Lean_mkConst(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16(void){
_start:
{
lean_object* v_type_102_; lean_object* v___x_103_; lean_object* v_cons_104_; 
v_type_102_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_103_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15);
v_cons_104_ = l_Lean_Expr_app___override(v___x_103_, v_type_102_);
return v_cons_104_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_nat_to_int(v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = l_Lean_Level_ofNat(v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_box(0);
v___x_115_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21);
v___x_116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_114_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22);
v___x_118_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__20));
v___x_119_ = l_Lean_Expr_const___override(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_box(0);
v___x_125_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__25));
v___x_126_ = l_Lean_Expr_const___override(v___x_125_, v___x_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0(lean_object* v___x_127_, lean_object* v_lc_128_){
_start:
{
lean_object* v_const_129_; lean_object* v_coeffs_130_; lean_object* v___x_131_; lean_object* v___y_133_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_const_129_ = lean_ctor_get(v_lc_128_, 0);
lean_inc(v_const_129_);
v_coeffs_130_ = lean_ctor_get(v_lc_128_, 1);
lean_inc(v_coeffs_130_);
lean_dec_ref(v_lc_128_);
v___x_131_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3);
v___x_139_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_140_ = lean_int_dec_le(v___x_139_, v_const_129_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_141_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_142_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_143_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_144_ = lean_int_neg(v_const_129_);
lean_dec(v_const_129_);
v___x_145_ = l_Int_toNat(v___x_144_);
lean_dec(v___x_144_);
v___x_146_ = l_Lean_instToExprInt_mkNat(v___x_145_);
v___x_147_ = l_Lean_mkApp3(v___x_141_, v___x_142_, v___x_143_, v___x_146_);
v___y_133_ = v___x_147_;
goto v___jp_132_;
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = l_Int_toNat(v_const_129_);
lean_dec(v_const_129_);
v___x_149_ = l_Lean_instToExprInt_mkNat(v___x_148_);
v___y_133_ = v___x_149_;
goto v___jp_132_;
}
v___jp_132_:
{
lean_object* v_nil_134_; lean_object* v___x_135_; lean_object* v_cons_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_nil_134_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v___x_135_ = l_Lean_Expr_app___override(v___x_131_, v___y_133_);
v_cons_136_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_137_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_127_, v_nil_134_, v_cons_136_, v_coeffs_130_);
v___x_138_ = l_Lean_Expr_app___override(v___x_135_, v___x_137_);
return v___x_138_;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0(void){
_start:
{
lean_object* v___x_150_; lean_object* v___f_151_; 
v___x_150_ = l_Lean_instToExprInt;
v___f_151_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0), 2, 1);
lean_closure_set(v___f_151_, 0, v___x_150_);
return v___f_151_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_box(0);
v___x_157_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1));
v___x_158_ = l_Lean_Expr_const___override(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3(void){
_start:
{
lean_object* v___x_159_; lean_object* v___f_160_; lean_object* v___x_161_; 
v___x_159_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2);
v___f_160_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___f_160_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo(void){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_box(0);
v___x_170_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1));
v___x_171_ = l_Lean_Expr_const___override(v___x_170_, v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_178_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__5));
v___x_179_ = l_Lean_mkConst(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7(void){
_start:
{
lean_object* v_type_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_type_180_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_181_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_182_ = l_Lean_Expr_app___override(v___x_181_, v_type_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_188_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__9));
v___x_189_ = l_Lean_mkConst(v___x_188_, v___x_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0(lean_object* v_s_190_){
_start:
{
lean_object* v_lowerBound_191_; lean_object* v_upperBound_192_; lean_object* v___x_193_; lean_object* v_type_194_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___y_198_; lean_object* v___y_202_; 
v_lowerBound_191_ = lean_ctor_get(v_s_190_, 0);
v_upperBound_192_ = lean_ctor_get(v_s_190_, 1);
v___x_193_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_194_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_191_) == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_202_ = v___x_218_;
goto v___jp_201_;
}
else
{
lean_object* v_val_219_; lean_object* v___x_220_; lean_object* v___y_222_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_val_219_ = lean_ctor_get(v_lowerBound_191_, 0);
v___x_220_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_224_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_225_ = lean_int_dec_le(v___x_224_, v_val_219_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_226_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_227_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_228_ = lean_int_neg(v_val_219_);
v___x_229_ = l_Int_toNat(v___x_228_);
lean_dec(v___x_228_);
v___x_230_ = l_Lean_instToExprInt_mkNat(v___x_229_);
v___x_231_ = l_Lean_mkApp3(v___x_226_, v_type_194_, v___x_227_, v___x_230_);
v___y_222_ = v___x_231_;
goto v___jp_221_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = l_Int_toNat(v_val_219_);
v___x_233_ = l_Lean_instToExprInt_mkNat(v___x_232_);
v___y_222_ = v___x_233_;
goto v___jp_221_;
}
v___jp_221_:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_mkAppB(v___x_220_, v_type_194_, v___y_222_);
v___y_202_ = v___x_223_;
goto v___jp_201_;
}
}
v___jp_195_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = l_Lean_mkAppB(v___y_196_, v_type_194_, v___y_198_);
v___x_200_ = l_Lean_Expr_app___override(v___y_197_, v___x_199_);
return v___x_200_;
}
v___jp_201_:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Expr_app___override(v___x_193_, v___y_202_);
if (lean_obj_tag(v_upperBound_192_) == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_205_ = l_Lean_Expr_app___override(v___x_203_, v___x_204_);
return v___x_205_;
}
else
{
lean_object* v_val_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_val_206_ = lean_ctor_get(v_upperBound_192_, 0);
v___x_207_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_208_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_209_ = lean_int_dec_le(v___x_208_, v_val_206_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_210_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_211_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_212_ = lean_int_neg(v_val_206_);
v___x_213_ = l_Int_toNat(v___x_212_);
lean_dec(v___x_212_);
v___x_214_ = l_Lean_instToExprInt_mkNat(v___x_213_);
v___x_215_ = l_Lean_mkApp3(v___x_210_, v_type_194_, v___x_211_, v___x_214_);
v___y_196_ = v___x_207_;
v___y_197_ = v___x_203_;
v___y_198_ = v___x_215_;
goto v___jp_195_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = l_Int_toNat(v_val_206_);
v___x_217_ = l_Lean_instToExprInt_mkNat(v___x_216_);
v___y_196_ = v___x_207_;
v___y_197_ = v___x_203_;
v___y_198_ = v___x_217_;
goto v___jp_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___boxed(lean_object* v_s_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0(v_s_234_);
lean_dec_ref(v_s_234_);
return v_res_235_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_box(0);
v___x_242_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__1));
v___x_243_ = l_Lean_Expr_const___override(v___x_242_, v___x_241_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3(void){
_start:
{
lean_object* v___x_244_; lean_object* v___f_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2);
v___f_245_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__0));
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___f_245_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint(void){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___redArg(lean_object* v_x_248_){
_start:
{
switch(lean_obj_tag(v_x_248_))
{
case 0:
{
lean_object* v___x_249_; 
v___x_249_ = lean_unsigned_to_nat(0u);
return v___x_249_;
}
case 1:
{
lean_object* v___x_250_; 
v___x_250_ = lean_unsigned_to_nat(1u);
return v___x_250_;
}
case 2:
{
lean_object* v___x_251_; 
v___x_251_ = lean_unsigned_to_nat(2u);
return v___x_251_;
}
case 3:
{
lean_object* v___x_252_; 
v___x_252_ = lean_unsigned_to_nat(3u);
return v___x_252_;
}
default: 
{
lean_object* v___x_253_; 
v___x_253_ = lean_unsigned_to_nat(4u);
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___redArg___boxed(lean_object* v_x_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___redArg(v_x_254_);
lean_dec_ref(v_x_254_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx(lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_x_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___redArg(v_x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___boxed(lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_x_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Elab_Tactic_Omega_Justification_ctorIdx(v_a_260_, v_a_261_, v_x_262_);
lean_dec_ref(v_x_262_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(lean_object* v_t_264_, lean_object* v_k_265_){
_start:
{
switch(lean_obj_tag(v_t_264_))
{
case 0:
{
lean_object* v_s_266_; lean_object* v_x_267_; lean_object* v_i_268_; lean_object* v___x_269_; 
v_s_266_ = lean_ctor_get(v_t_264_, 0);
lean_inc_ref(v_s_266_);
v_x_267_ = lean_ctor_get(v_t_264_, 1);
lean_inc(v_x_267_);
v_i_268_ = lean_ctor_get(v_t_264_, 2);
lean_inc(v_i_268_);
lean_dec_ref(v_t_264_);
v___x_269_ = lean_apply_3(v_k_265_, v_s_266_, v_x_267_, v_i_268_);
return v___x_269_;
}
case 1:
{
lean_object* v_s_270_; lean_object* v_c_271_; lean_object* v_j_272_; lean_object* v___x_273_; 
v_s_270_ = lean_ctor_get(v_t_264_, 0);
lean_inc_ref(v_s_270_);
v_c_271_ = lean_ctor_get(v_t_264_, 1);
lean_inc(v_c_271_);
v_j_272_ = lean_ctor_get(v_t_264_, 2);
lean_inc_ref(v_j_272_);
lean_dec_ref(v_t_264_);
v___x_273_ = lean_apply_3(v_k_265_, v_s_270_, v_c_271_, v_j_272_);
return v___x_273_;
}
case 2:
{
lean_object* v_s_274_; lean_object* v_t_275_; lean_object* v_c_276_; lean_object* v_j_277_; lean_object* v_k_278_; lean_object* v___x_279_; 
v_s_274_ = lean_ctor_get(v_t_264_, 0);
lean_inc_ref(v_s_274_);
v_t_275_ = lean_ctor_get(v_t_264_, 1);
lean_inc_ref(v_t_275_);
v_c_276_ = lean_ctor_get(v_t_264_, 2);
lean_inc(v_c_276_);
v_j_277_ = lean_ctor_get(v_t_264_, 3);
lean_inc_ref(v_j_277_);
v_k_278_ = lean_ctor_get(v_t_264_, 4);
lean_inc_ref(v_k_278_);
lean_dec_ref(v_t_264_);
v___x_279_ = lean_apply_5(v_k_265_, v_s_274_, v_t_275_, v_c_276_, v_j_277_, v_k_278_);
return v___x_279_;
}
case 3:
{
lean_object* v_s_280_; lean_object* v_t_281_; lean_object* v_x_282_; lean_object* v_y_283_; lean_object* v_a_284_; lean_object* v_j_285_; lean_object* v_b_286_; lean_object* v_k_287_; lean_object* v___x_288_; 
v_s_280_ = lean_ctor_get(v_t_264_, 0);
lean_inc_ref(v_s_280_);
v_t_281_ = lean_ctor_get(v_t_264_, 1);
lean_inc_ref(v_t_281_);
v_x_282_ = lean_ctor_get(v_t_264_, 2);
lean_inc(v_x_282_);
v_y_283_ = lean_ctor_get(v_t_264_, 3);
lean_inc(v_y_283_);
v_a_284_ = lean_ctor_get(v_t_264_, 4);
lean_inc(v_a_284_);
v_j_285_ = lean_ctor_get(v_t_264_, 5);
lean_inc_ref(v_j_285_);
v_b_286_ = lean_ctor_get(v_t_264_, 6);
lean_inc(v_b_286_);
v_k_287_ = lean_ctor_get(v_t_264_, 7);
lean_inc_ref(v_k_287_);
lean_dec_ref(v_t_264_);
v___x_288_ = lean_apply_8(v_k_265_, v_s_280_, v_t_281_, v_x_282_, v_y_283_, v_a_284_, v_j_285_, v_b_286_, v_k_287_);
return v___x_288_;
}
default: 
{
lean_object* v_m_289_; lean_object* v_r_290_; lean_object* v_i_291_; lean_object* v_x_292_; lean_object* v_j_293_; lean_object* v___x_294_; 
v_m_289_ = lean_ctor_get(v_t_264_, 0);
lean_inc(v_m_289_);
v_r_290_ = lean_ctor_get(v_t_264_, 1);
lean_inc(v_r_290_);
v_i_291_ = lean_ctor_get(v_t_264_, 2);
lean_inc(v_i_291_);
v_x_292_ = lean_ctor_get(v_t_264_, 3);
lean_inc(v_x_292_);
v_j_293_ = lean_ctor_get(v_t_264_, 4);
lean_inc_ref(v_j_293_);
lean_dec_ref(v_t_264_);
v___x_294_ = lean_apply_5(v_k_265_, v_m_289_, v_r_290_, v_i_291_, v_x_292_, v_j_293_);
return v___x_294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim(lean_object* v_motive_295_, lean_object* v_ctorIdx_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_t_299_, lean_object* v_h_300_, lean_object* v_k_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_299_, v_k_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim___boxed(lean_object* v_motive_303_, lean_object* v_ctorIdx_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_t_307_, lean_object* v_h_308_, lean_object* v_k_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim(v_motive_303_, v_ctorIdx_304_, v_a_305_, v_a_306_, v_t_307_, v_h_308_, v_k_309_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_ctorIdx_304_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim___redArg(lean_object* v_t_311_, lean_object* v_assumption_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_311_, v_assumption_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim(lean_object* v_motive_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_t_317_, lean_object* v_h_318_, lean_object* v_assumption_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_317_, v_assumption_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim___boxed(lean_object* v_motive_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_t_324_, lean_object* v_h_325_, lean_object* v_assumption_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Elab_Tactic_Omega_Justification_assumption_elim(v_motive_321_, v_a_322_, v_a_323_, v_t_324_, v_h_325_, v_assumption_326_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim___redArg(lean_object* v_t_328_, lean_object* v_tidy_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_328_, v_tidy_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim(lean_object* v_motive_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_t_334_, lean_object* v_h_335_, lean_object* v_tidy_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_334_, v_tidy_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim___boxed(lean_object* v_motive_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_t_341_, lean_object* v_h_342_, lean_object* v_tidy_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_elim(v_motive_338_, v_a_339_, v_a_340_, v_t_341_, v_h_342_, v_tidy_343_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim___redArg(lean_object* v_t_345_, lean_object* v_combine_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_345_, v_combine_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim(lean_object* v_motive_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_t_351_, lean_object* v_h_352_, lean_object* v_combine_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_351_, v_combine_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim___boxed(lean_object* v_motive_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_t_358_, lean_object* v_h_359_, lean_object* v_combine_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Elab_Tactic_Omega_Justification_combine_elim(v_motive_355_, v_a_356_, v_a_357_, v_t_358_, v_h_359_, v_combine_360_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim___redArg(lean_object* v_t_362_, lean_object* v_combo_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_362_, v_combo_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim(lean_object* v_motive_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_t_368_, lean_object* v_h_369_, lean_object* v_combo_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_368_, v_combo_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim___boxed(lean_object* v_motive_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_t_375_, lean_object* v_h_376_, lean_object* v_combo_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Elab_Tactic_Omega_Justification_combo_elim(v_motive_372_, v_a_373_, v_a_374_, v_t_375_, v_h_376_, v_combo_377_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim___redArg(lean_object* v_t_379_, lean_object* v_bmod_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_379_, v_bmod_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim(lean_object* v_motive_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_t_385_, lean_object* v_h_386_, lean_object* v_bmod_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_385_, v_bmod_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim___boxed(lean_object* v_motive_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_bmod_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Elab_Tactic_Omega_Justification_bmod_elim(v_motive_389_, v_a_390_, v_a_391_, v_t_392_, v_h_393_, v_bmod_394_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(lean_object* v_s_396_, lean_object* v_c_397_, lean_object* v_j_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_inc(v_c_397_);
lean_inc_ref(v_s_396_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_s_396_);
lean_ctor_set(v___x_399_, 1, v_c_397_);
lean_inc_ref(v___x_399_);
v___x_400_ = l_Lean_Omega_tidy_x3f(v___x_399_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; 
lean_dec_ref(v___x_399_);
lean_dec_ref(v_j_398_);
lean_dec(v_c_397_);
lean_dec_ref(v_s_396_);
v___x_401_ = lean_box(0);
return v___x_401_;
}
else
{
lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_420_; 
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v___x_400_, 0);
lean_dec(v_unused_421_);
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_420_;
goto v_resetjp_402_;
}
else
{
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_420_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v_fst_406_; lean_object* v_snd_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_419_; 
v___x_405_ = l_Lean_Omega_tidy(v___x_399_);
v_fst_406_ = lean_ctor_get(v___x_405_, 0);
v_snd_407_ = lean_ctor_get(v___x_405_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_419_ == 0)
{
v___x_409_ = v___x_405_;
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_snd_407_);
lean_inc(v_fst_406_);
lean_dec(v___x_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_411_, 0, v_s_396_);
lean_ctor_set(v___x_411_, 1, v_c_397_);
lean_ctor_set(v___x_411_, 2, v_j_398_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v___x_411_);
lean_ctor_set(v___x_409_, 0, v_snd_407_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_snd_407_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___x_411_);
v___x_413_ = v_reuseFailAlloc_418_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v_fst_406_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_414_);
v___x_416_ = v___x_403_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(lean_object* v_s_422_, lean_object* v_replacement_423_, lean_object* v_a_424_, lean_object* v_b_425_){
_start:
{
lean_object* v_it_427_; lean_object* v_startPos_428_; lean_object* v_endPos_429_; lean_object* v_it_438_; 
switch(lean_obj_tag(v_a_424_))
{
case 0:
{
lean_object* v_pos_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_456_; 
v_pos_444_ = lean_ctor_get(v_a_424_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v_a_424_);
if (v_isSharedCheck_456_ == 0)
{
v___x_446_ = v_a_424_;
v_isShared_447_ = v_isSharedCheck_456_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_pos_444_);
lean_dec(v_a_424_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_456_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_startInclusive_448_; lean_object* v_endExclusive_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_startInclusive_448_ = lean_ctor_get(v_s_422_, 1);
v_endExclusive_449_ = lean_ctor_get(v_s_422_, 2);
v___x_450_ = lean_nat_sub(v_endExclusive_449_, v_startInclusive_448_);
v___x_451_ = lean_nat_dec_eq(v_pos_444_, v___x_450_);
lean_dec(v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_453_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 1);
v___x_453_ = v___x_446_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_pos_444_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
v_it_438_ = v___x_453_;
goto v___jp_437_;
}
}
else
{
lean_object* v___x_455_; 
lean_del_object(v___x_446_);
lean_dec(v_pos_444_);
v___x_455_ = lean_box(3);
v_it_438_ = v___x_455_;
goto v___jp_437_;
}
}
}
case 1:
{
lean_object* v_pos_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_469_; 
v_pos_457_ = lean_ctor_get(v_a_424_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v_a_424_);
if (v_isSharedCheck_469_ == 0)
{
v___x_459_ = v_a_424_;
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_pos_457_);
lean_dec(v_a_424_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_str_461_; lean_object* v_startInclusive_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v_str_461_ = lean_ctor_get(v_s_422_, 0);
v_startInclusive_462_ = lean_ctor_get(v_s_422_, 1);
v___x_463_ = lean_nat_add(v_startInclusive_462_, v_pos_457_);
v___x_464_ = lean_string_utf8_next_fast(v_str_461_, v___x_463_);
lean_dec(v___x_463_);
v___x_465_ = lean_nat_sub(v___x_464_, v_startInclusive_462_);
lean_inc(v___x_465_);
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 0);
lean_ctor_set(v___x_459_, 0, v___x_465_);
v___x_467_ = v___x_459_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
v_it_427_ = v___x_467_;
v_startPos_428_ = v_pos_457_;
v_endPos_429_ = v___x_465_;
goto v___jp_426_;
}
}
}
case 2:
{
lean_object* v_needle_470_; lean_object* v_table_471_; lean_object* v_stackPos_472_; lean_object* v_needlePos_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_532_; 
v_needle_470_ = lean_ctor_get(v_a_424_, 0);
v_table_471_ = lean_ctor_get(v_a_424_, 1);
v_stackPos_472_ = lean_ctor_get(v_a_424_, 2);
v_needlePos_473_ = lean_ctor_get(v_a_424_, 3);
v_isSharedCheck_532_ = !lean_is_exclusive(v_a_424_);
if (v_isSharedCheck_532_ == 0)
{
v___x_475_ = v_a_424_;
v_isShared_476_ = v_isSharedCheck_532_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_needlePos_473_);
lean_inc(v_stackPos_472_);
lean_inc(v_table_471_);
lean_inc(v_needle_470_);
lean_dec(v_a_424_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_532_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v_str_477_; lean_object* v_startInclusive_478_; lean_object* v_endExclusive_479_; lean_object* v_str_480_; lean_object* v_startInclusive_481_; lean_object* v_endExclusive_482_; lean_object* v_basePos_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_str_477_ = lean_ctor_get(v_needle_470_, 0);
v_startInclusive_478_ = lean_ctor_get(v_needle_470_, 1);
v_endExclusive_479_ = lean_ctor_get(v_needle_470_, 2);
v_str_480_ = lean_ctor_get(v_s_422_, 0);
v_startInclusive_481_ = lean_ctor_get(v_s_422_, 1);
v_endExclusive_482_ = lean_ctor_get(v_s_422_, 2);
v_basePos_483_ = lean_nat_sub(v_stackPos_472_, v_needlePos_473_);
v___x_484_ = lean_nat_sub(v_endExclusive_479_, v_startInclusive_478_);
v___x_485_ = lean_nat_add(v_basePos_483_, v___x_484_);
v___x_486_ = lean_nat_sub(v_endExclusive_482_, v_startInclusive_481_);
v___x_487_ = lean_nat_dec_le(v___x_485_, v___x_486_);
lean_dec(v___x_485_);
if (v___x_487_ == 0)
{
uint8_t v___x_488_; 
lean_dec(v___x_484_);
lean_del_object(v___x_475_);
lean_dec(v_needlePos_473_);
lean_dec(v_stackPos_472_);
lean_dec_ref(v_table_471_);
lean_dec_ref(v_needle_470_);
v___x_488_ = lean_nat_dec_lt(v_basePos_483_, v___x_486_);
if (v___x_488_ == 0)
{
lean_dec(v___x_486_);
lean_dec(v_basePos_483_);
lean_dec_ref(v_s_422_);
return v_b_425_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = l_String_Slice_pos_x21(v_s_422_, v_basePos_483_);
lean_dec(v_basePos_483_);
v___x_490_ = lean_box(3);
v_it_427_ = v___x_490_;
v_startPos_428_ = v___x_489_;
v_endPos_429_ = v___x_486_;
goto v___jp_426_;
}
}
else
{
lean_object* v___x_491_; uint8_t v_stackByte_492_; lean_object* v___x_493_; uint8_t v_patByte_494_; uint8_t v___x_495_; 
lean_dec(v___x_486_);
v___x_491_ = lean_nat_add(v_startInclusive_481_, v_stackPos_472_);
v_stackByte_492_ = lean_string_get_byte_fast(v_str_480_, v___x_491_);
v___x_493_ = lean_nat_add(v_startInclusive_478_, v_needlePos_473_);
v_patByte_494_ = lean_string_get_byte_fast(v_str_477_, v___x_493_);
v___x_495_ = lean_uint8_dec_eq(v_stackByte_492_, v_patByte_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; uint8_t v___x_497_; 
lean_dec(v___x_484_);
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = lean_nat_dec_eq(v_needlePos_473_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_newNeedlePos_500_; uint8_t v___x_501_; 
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = lean_nat_sub(v_needlePos_473_, v___x_498_);
lean_dec(v_needlePos_473_);
v_newNeedlePos_500_ = lean_array_fget_borrowed(v_table_471_, v___x_499_);
lean_dec(v___x_499_);
v___x_501_ = lean_nat_dec_eq(v_newNeedlePos_500_, v___x_496_);
if (v___x_501_ == 0)
{
lean_object* v_oldBasePos_502_; lean_object* v___x_503_; lean_object* v_newBasePos_504_; lean_object* v___x_506_; 
lean_inc(v_newNeedlePos_500_);
v_oldBasePos_502_ = l_String_Slice_pos_x21(v_s_422_, v_basePos_483_);
lean_dec(v_basePos_483_);
v___x_503_ = lean_nat_sub(v_stackPos_472_, v_newNeedlePos_500_);
v_newBasePos_504_ = l_String_Slice_pos_x21(v_s_422_, v___x_503_);
lean_dec(v___x_503_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 3, v_newNeedlePos_500_);
v___x_506_ = v___x_475_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_needle_470_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_table_471_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_stackPos_472_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_newNeedlePos_500_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
v_it_427_ = v___x_506_;
v_startPos_428_ = v_oldBasePos_502_;
v_endPos_429_ = v_newBasePos_504_;
goto v___jp_426_;
}
}
else
{
lean_object* v_basePos_508_; lean_object* v_nextStackPos_509_; lean_object* v___x_511_; 
v_basePos_508_ = l_String_Slice_pos_x21(v_s_422_, v_basePos_483_);
lean_dec(v_basePos_483_);
v_nextStackPos_509_ = l_String_Slice_posGE___redArg(v_s_422_, v_stackPos_472_);
lean_inc(v_nextStackPos_509_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 3, v___x_496_);
lean_ctor_set(v___x_475_, 2, v_nextStackPos_509_);
v___x_511_ = v___x_475_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_needle_470_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_table_471_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_nextStackPos_509_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v___x_496_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
v_it_427_ = v___x_511_;
v_startPos_428_ = v_basePos_508_;
v_endPos_429_ = v_nextStackPos_509_;
goto v___jp_426_;
}
}
}
else
{
lean_object* v_basePos_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_nextStackPos_516_; lean_object* v___x_518_; 
lean_dec(v_basePos_483_);
lean_dec(v_needlePos_473_);
v_basePos_513_ = l_String_Slice_pos_x21(v_s_422_, v_stackPos_472_);
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_add(v_stackPos_472_, v___x_514_);
lean_dec(v_stackPos_472_);
v_nextStackPos_516_ = l_String_Slice_posGE___redArg(v_s_422_, v___x_515_);
lean_inc(v_nextStackPos_516_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 3, v___x_496_);
lean_ctor_set(v___x_475_, 2, v_nextStackPos_516_);
v___x_518_ = v___x_475_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_needle_470_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_table_471_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_nextStackPos_516_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v___x_496_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
v_it_427_ = v___x_518_;
v_startPos_428_ = v_basePos_513_;
v_endPos_429_ = v_nextStackPos_516_;
goto v___jp_426_;
}
}
}
else
{
lean_object* v___x_520_; lean_object* v_nextStackPos_521_; lean_object* v_nextNeedlePos_522_; uint8_t v___x_523_; 
lean_dec(v_basePos_483_);
v___x_520_ = lean_unsigned_to_nat(1u);
v_nextStackPos_521_ = lean_nat_add(v_stackPos_472_, v___x_520_);
lean_dec(v_stackPos_472_);
v_nextNeedlePos_522_ = lean_nat_add(v_needlePos_473_, v___x_520_);
lean_dec(v_needlePos_473_);
v___x_523_ = lean_nat_dec_eq(v_nextNeedlePos_522_, v___x_484_);
lean_dec(v___x_484_);
if (v___x_523_ == 0)
{
lean_object* v___x_525_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 3, v_nextNeedlePos_522_);
lean_ctor_set(v___x_475_, 2, v_nextStackPos_521_);
v___x_525_ = v___x_475_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_needle_470_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_table_471_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_nextStackPos_521_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_nextNeedlePos_522_);
v___x_525_ = v_reuseFailAlloc_527_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
v_a_424_ = v___x_525_;
goto _start;
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_530_; 
lean_dec(v_nextNeedlePos_522_);
v___x_528_ = lean_unsigned_to_nat(0u);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 3, v___x_528_);
lean_ctor_set(v___x_475_, 2, v_nextStackPos_521_);
v___x_530_ = v___x_475_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_needle_470_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_table_471_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_nextStackPos_521_);
lean_ctor_set(v_reuseFailAlloc_531_, 3, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
v_it_438_ = v___x_530_;
goto v___jp_437_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_422_);
return v_b_425_;
}
}
v___jp_426_:
{
lean_object* v___x_430_; lean_object* v_str_431_; lean_object* v_startInclusive_432_; lean_object* v_endExclusive_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_inc_ref(v_s_422_);
v___x_430_ = l_String_Slice_slice_x21(v_s_422_, v_startPos_428_, v_endPos_429_);
lean_dec(v_endPos_429_);
lean_dec(v_startPos_428_);
v_str_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc_ref(v_str_431_);
v_startInclusive_432_ = lean_ctor_get(v___x_430_, 1);
lean_inc(v_startInclusive_432_);
v_endExclusive_433_ = lean_ctor_get(v___x_430_, 2);
lean_inc(v_endExclusive_433_);
lean_dec_ref(v___x_430_);
v___x_434_ = lean_string_utf8_extract(v_str_431_, v_startInclusive_432_, v_endExclusive_433_);
lean_dec(v_endExclusive_433_);
lean_dec(v_startInclusive_432_);
lean_dec_ref(v_str_431_);
v___x_435_ = lean_string_append(v_b_425_, v___x_434_);
lean_dec_ref(v___x_434_);
v_a_424_ = v_it_427_;
v_b_425_ = v___x_435_;
goto _start;
}
v___jp_437_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_string_utf8_byte_size(v_replacement_423_);
v___x_441_ = lean_string_utf8_extract(v_replacement_423_, v___x_439_, v___x_440_);
v___x_442_ = lean_string_append(v_b_425_, v___x_441_);
lean_dec_ref(v___x_441_);
v_a_424_ = v_it_438_;
v_b_425_ = v___x_442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg___boxed(lean_object* v_s_533_, lean_object* v_replacement_534_, lean_object* v_a_535_, lean_object* v_b_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_533_, v_replacement_534_, v_a_535_, v_b_536_);
lean_dec_ref(v_replacement_534_);
return v_res_537_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_541_ = lean_string_utf8_byte_size(v___x_540_);
return v___x_541_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2);
v___x_544_ = lean_nat_dec_eq(v___x_543_, v___x_542_);
return v___x_544_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_545_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
lean_ctor_set(v___x_548_, 2, v___x_545_);
return v___x_548_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4);
v___x_550_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_549_);
return v___x_550_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5);
v___x_553_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4);
v___x_554_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v___x_552_);
lean_ctor_set(v___x_554_, 2, v___x_551_);
lean_ctor_set(v___x_554_, 3, v___x_551_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(lean_object* v_s_557_, lean_object* v_replacement_558_){
_start:
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_560_ = lean_uint8_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6);
v___x_562_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_557_, v_replacement_558_, v___x_561_, v___x_559_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__7));
v___x_564_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_557_, v_replacement_558_, v___x_563_, v___x_559_);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___boxed(lean_object* v_s_565_, lean_object* v_replacement_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v_s_565_, v_replacement_566_);
lean_dec_ref(v_replacement_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(lean_object* v_s_570_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__0));
v___x_572_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__1));
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_string_utf8_byte_size(v_s_570_);
v___x_575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_575_, 0, v_s_570_);
lean_ctor_set(v___x_575_, 1, v___x_573_);
lean_ctor_set(v___x_575_, 2, v___x_574_);
v___x_576_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v___x_575_, v___x_572_);
v___x_577_ = lean_string_append(v___x_571_, v___x_576_);
lean_dec_ref(v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0(lean_object* v_s_578_, lean_object* v_pattern_579_, lean_object* v_replacement_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v_s_578_, v_replacement_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___boxed(lean_object* v_s_582_, lean_object* v_pattern_583_, lean_object* v_replacement_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0(v_s_582_, v_pattern_583_, v_replacement_584_);
lean_dec_ref(v_replacement_584_);
lean_dec_ref(v_pattern_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0(lean_object* v_s_586_, lean_object* v_replacement_587_, lean_object* v_inst_588_, lean_object* v_R_589_, lean_object* v_a_590_, lean_object* v_b_591_, lean_object* v_c_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_586_, v_replacement_587_, v_a_590_, v_b_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___boxed(lean_object* v_s_594_, lean_object* v_replacement_595_, lean_object* v_inst_596_, lean_object* v_R_597_, lean_object* v_a_598_, lean_object* v_b_599_, lean_object* v_c_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0(v_s_594_, v_replacement_595_, v_inst_596_, v_R_597_, v_a_598_, v_b_599_, v_c_600_);
lean_dec_ref(v_replacement_595_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
return v_x_603_;
}
else
{
lean_object* v_head_605_; lean_object* v_tail_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_head_605_ = lean_ctor_get(v_x_604_, 0);
v_tail_606_ = lean_ctor_get(v_x_604_, 1);
v___x_607_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_608_ = lean_string_append(v_x_603_, v___x_607_);
v___x_609_ = l_Int_repr(v_head_605_);
v___x_610_ = lean_string_append(v___x_608_, v___x_609_);
lean_dec_ref(v___x_609_);
v_x_603_ = v___x_610_;
v_x_604_ = v_tail_606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___boxed(lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v_x_612_, v_x_613_);
lean_dec(v_x_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_618_) == 0)
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__0));
return v___x_619_;
}
else
{
lean_object* v_tail_620_; 
v_tail_620_ = lean_ctor_get(v_x_618_, 1);
if (lean_obj_tag(v_tail_620_) == 0)
{
lean_object* v_head_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_head_621_ = lean_ctor_get(v_x_618_, 0);
v___x_622_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v___x_623_ = l_Int_repr(v_head_621_);
v___x_624_ = lean_string_append(v___x_622_, v___x_623_);
lean_dec_ref(v___x_623_);
v___x_625_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_626_ = lean_string_append(v___x_624_, v___x_625_);
return v___x_626_;
}
else
{
lean_object* v_head_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint32_t v___x_632_; lean_object* v___x_633_; 
v_head_627_ = lean_ctor_get(v_x_618_, 0);
v___x_628_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v___x_629_ = l_Int_repr(v_head_627_);
v___x_630_ = lean_string_append(v___x_628_, v___x_629_);
lean_dec_ref(v___x_629_);
v___x_631_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v___x_630_, v_tail_620_);
v___x_632_ = 93;
v___x_633_ = lean_string_push(v___x_631_, v___x_632_);
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___boxed(lean_object* v_x_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_634_);
lean_dec(v_x_634_);
return v_res_635_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
if (lean_obj_tag(v_x_637_) == 0)
{
uint8_t v___x_638_; 
v___x_638_ = 1;
return v___x_638_;
}
else
{
uint8_t v___x_639_; 
v___x_639_ = 0;
return v___x_639_;
}
}
else
{
if (lean_obj_tag(v_x_637_) == 0)
{
uint8_t v___x_640_; 
v___x_640_ = 0;
return v___x_640_;
}
else
{
lean_object* v_head_641_; lean_object* v_tail_642_; lean_object* v_head_643_; lean_object* v_tail_644_; uint8_t v___x_645_; 
v_head_641_ = lean_ctor_get(v_x_636_, 0);
v_tail_642_ = lean_ctor_get(v_x_636_, 1);
v_head_643_ = lean_ctor_get(v_x_637_, 0);
v_tail_644_ = lean_ctor_get(v_x_637_, 1);
v___x_645_ = lean_int_dec_eq(v_head_641_, v_head_643_);
if (v___x_645_ == 0)
{
return v___x_645_;
}
else
{
v_x_636_ = v_tail_642_;
v_x_637_ = v_tail_644_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1___boxed(lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
uint8_t v_res_649_; lean_object* v_r_650_; 
v_res_649_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_647_, v_x_648_);
lean_dec(v_x_648_);
lean_dec(v_x_647_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString(lean_object* v_s_661_, lean_object* v_x_662_, lean_object* v_x_663_){
_start:
{
switch(lean_obj_tag(v_x_663_))
{
case 0:
{
lean_object* v_i_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_i_664_ = lean_ctor_get(v_x_663_, 2);
lean_inc(v_i_664_);
lean_dec_ref(v_x_663_);
v___x_665_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_662_);
lean_dec(v_x_662_);
v___x_666_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_667_ = lean_string_append(v___x_665_, v___x_666_);
v___x_668_ = l_Lean_Omega_Constraint_instToString___private__1(v_s_661_);
lean_dec_ref(v_s_661_);
v___x_669_ = lean_string_append(v___x_667_, v___x_668_);
lean_dec_ref(v___x_668_);
v___x_670_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__1));
v___x_671_ = lean_string_append(v___x_669_, v___x_670_);
v___x_672_ = l_Nat_reprFast(v_i_664_);
v___x_673_ = lean_string_append(v___x_671_, v___x_672_);
lean_dec_ref(v___x_672_);
return v___x_673_;
}
case 1:
{
lean_object* v_s_674_; lean_object* v_c_675_; lean_object* v_j_676_; uint8_t v___y_678_; uint8_t v___x_690_; 
v_s_674_ = lean_ctor_get(v_x_663_, 0);
lean_inc_ref(v_s_674_);
v_c_675_ = lean_ctor_get(v_x_663_, 1);
lean_inc(v_c_675_);
v_j_676_ = lean_ctor_get(v_x_663_, 2);
lean_inc_ref(v_j_676_);
lean_dec_ref(v_x_663_);
v___x_690_ = l_Lean_Omega_instBEqConstraint_beq(v_s_661_, v_s_674_);
if (v___x_690_ == 0)
{
v___y_678_ = v___x_690_;
goto v___jp_677_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_662_, v_c_675_);
v___y_678_ = v___x_691_;
goto v___jp_677_;
}
v___jp_677_:
{
if (v___y_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_679_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_662_);
lean_dec(v_x_662_);
v___x_680_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_681_ = lean_string_append(v___x_679_, v___x_680_);
v___x_682_ = l_Lean_Omega_Constraint_instToString___private__1(v_s_661_);
lean_dec_ref(v_s_661_);
v___x_683_ = lean_string_append(v___x_681_, v___x_682_);
lean_dec_ref(v___x_682_);
v___x_684_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_685_ = lean_string_append(v___x_683_, v___x_684_);
v___x_686_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_674_, v_c_675_, v_j_676_);
v___x_687_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_686_);
v___x_688_ = lean_string_append(v___x_685_, v___x_687_);
lean_dec_ref(v___x_687_);
return v___x_688_;
}
else
{
lean_dec(v_x_662_);
lean_dec_ref(v_s_661_);
v_s_661_ = v_s_674_;
v_x_662_ = v_c_675_;
v_x_663_ = v_j_676_;
goto _start;
}
}
}
case 2:
{
lean_object* v_s_692_; lean_object* v_t_693_; lean_object* v_j_694_; lean_object* v_k_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_s_692_ = lean_ctor_get(v_x_663_, 0);
lean_inc_ref(v_s_692_);
v_t_693_ = lean_ctor_get(v_x_663_, 1);
lean_inc_ref(v_t_693_);
v_j_694_ = lean_ctor_get(v_x_663_, 3);
lean_inc_ref(v_j_694_);
v_k_695_ = lean_ctor_get(v_x_663_, 4);
lean_inc_ref(v_k_695_);
lean_dec_ref(v_x_663_);
v___x_696_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_662_);
v___x_697_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_698_ = lean_string_append(v___x_696_, v___x_697_);
v___x_699_ = l_Lean_Omega_Constraint_instToString___private__1(v_s_661_);
lean_dec_ref(v_s_661_);
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
lean_dec_ref(v___x_699_);
v___x_701_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v___x_702_ = lean_string_append(v___x_700_, v___x_701_);
lean_inc(v_x_662_);
v___x_703_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_692_, v_x_662_, v_j_694_);
v___x_704_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_703_);
v___x_705_ = lean_string_append(v___x_702_, v___x_704_);
lean_dec_ref(v___x_704_);
v___x_706_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_707_ = lean_string_append(v___x_705_, v___x_706_);
v___x_708_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_693_, v_x_662_, v_k_695_);
v___x_709_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_708_);
v___x_710_ = lean_string_append(v___x_707_, v___x_709_);
lean_dec_ref(v___x_709_);
return v___x_710_;
}
case 3:
{
lean_object* v_s_711_; lean_object* v_t_712_; lean_object* v_x_713_; lean_object* v_y_714_; lean_object* v_a_715_; lean_object* v_j_716_; lean_object* v_b_717_; lean_object* v_k_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_s_711_ = lean_ctor_get(v_x_663_, 0);
lean_inc_ref(v_s_711_);
v_t_712_ = lean_ctor_get(v_x_663_, 1);
lean_inc_ref(v_t_712_);
v_x_713_ = lean_ctor_get(v_x_663_, 2);
lean_inc(v_x_713_);
v_y_714_ = lean_ctor_get(v_x_663_, 3);
lean_inc(v_y_714_);
v_a_715_ = lean_ctor_get(v_x_663_, 4);
lean_inc(v_a_715_);
v_j_716_ = lean_ctor_get(v_x_663_, 5);
lean_inc_ref(v_j_716_);
v_b_717_ = lean_ctor_get(v_x_663_, 6);
lean_inc(v_b_717_);
v_k_718_ = lean_ctor_get(v_x_663_, 7);
lean_inc_ref(v_k_718_);
lean_dec_ref(v_x_663_);
v___x_719_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_662_);
lean_dec(v_x_662_);
v___x_720_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_721_ = lean_string_append(v___x_719_, v___x_720_);
v___x_722_ = l_Lean_Omega_Constraint_instToString___private__1(v_s_661_);
lean_dec_ref(v_s_661_);
v___x_723_ = lean_string_append(v___x_721_, v___x_722_);
lean_dec_ref(v___x_722_);
v___x_724_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_725_ = lean_string_append(v___x_723_, v___x_724_);
v___x_726_ = l_Int_repr(v_a_715_);
lean_dec(v_a_715_);
v___x_727_ = lean_string_append(v___x_725_, v___x_726_);
lean_dec_ref(v___x_726_);
v___x_728_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_729_ = lean_string_append(v___x_727_, v___x_728_);
v___x_730_ = l_Int_repr(v_b_717_);
lean_dec(v_b_717_);
v___x_731_ = lean_string_append(v___x_729_, v___x_730_);
lean_dec_ref(v___x_730_);
v___x_732_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v___x_733_ = lean_string_append(v___x_731_, v___x_732_);
v___x_734_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_711_, v_x_713_, v_j_716_);
v___x_735_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_734_);
v___x_736_ = lean_string_append(v___x_733_, v___x_735_);
lean_dec_ref(v___x_735_);
v___x_737_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_738_ = lean_string_append(v___x_736_, v___x_737_);
v___x_739_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_712_, v_y_714_, v_k_718_);
v___x_740_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_739_);
v___x_741_ = lean_string_append(v___x_738_, v___x_740_);
lean_dec_ref(v___x_740_);
return v___x_741_;
}
default: 
{
lean_object* v_m_742_; lean_object* v_r_743_; lean_object* v_i_744_; lean_object* v_x_745_; lean_object* v_j_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_m_742_ = lean_ctor_get(v_x_663_, 0);
lean_inc(v_m_742_);
v_r_743_ = lean_ctor_get(v_x_663_, 1);
lean_inc(v_r_743_);
v_i_744_ = lean_ctor_get(v_x_663_, 2);
lean_inc(v_i_744_);
v_x_745_ = lean_ctor_get(v_x_663_, 3);
lean_inc(v_x_745_);
v_j_746_ = lean_ctor_get(v_x_663_, 4);
lean_inc_ref(v_j_746_);
lean_dec_ref(v_x_663_);
v___x_747_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_662_);
lean_dec(v_x_662_);
v___x_748_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_749_ = lean_string_append(v___x_747_, v___x_748_);
v___x_750_ = l_Lean_Omega_Constraint_instToString___private__1(v_s_661_);
lean_dec_ref(v_s_661_);
v___x_751_ = lean_string_append(v___x_749_, v___x_750_);
lean_dec_ref(v___x_750_);
v___x_752_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_753_ = lean_string_append(v___x_751_, v___x_752_);
v___x_754_ = l_Nat_reprFast(v_m_742_);
v___x_755_ = lean_string_append(v___x_753_, v___x_754_);
lean_dec_ref(v___x_754_);
v___x_756_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_757_ = lean_string_append(v___x_755_, v___x_756_);
v___x_758_ = l_Nat_reprFast(v_i_744_);
v___x_759_ = lean_string_append(v___x_757_, v___x_758_);
lean_dec_ref(v___x_758_);
v___x_760_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9));
v___x_761_ = lean_string_append(v___x_759_, v___x_760_);
v___x_762_ = l_Lean_Omega_Constraint_exact(v_r_743_);
v___x_763_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v___x_762_, v_x_745_, v_j_746_);
v___x_764_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_763_);
v___x_765_ = lean_string_append(v___x_761_, v___x_764_);
lean_dec_ref(v___x_764_);
return v___x_765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_instToString(lean_object* v_s_766_, lean_object* v_x_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Justification_toString), 3, 2);
lean_closure_set(v___x_768_, 0, v_s_766_);
lean_closure_set(v___x_768_, 1, v_x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(lean_object* v_nilFn_769_, lean_object* v_consFn_770_, lean_object* v_x_771_){
_start:
{
if (lean_obj_tag(v_x_771_) == 0)
{
lean_dec_ref(v_consFn_770_);
lean_inc_ref(v_nilFn_769_);
return v_nilFn_769_;
}
else
{
lean_object* v_head_772_; lean_object* v_tail_773_; lean_object* v___y_775_; lean_object* v___x_778_; uint8_t v___x_779_; 
v_head_772_ = lean_ctor_get(v_x_771_, 0);
v_tail_773_ = lean_ctor_get(v_x_771_, 1);
v___x_778_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_779_ = lean_int_dec_le(v___x_778_, v_head_772_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_780_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_781_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_782_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_783_ = lean_int_neg(v_head_772_);
v___x_784_ = l_Int_toNat(v___x_783_);
lean_dec(v___x_783_);
v___x_785_ = l_Lean_instToExprInt_mkNat(v___x_784_);
v___x_786_ = l_Lean_mkApp3(v___x_780_, v___x_781_, v___x_782_, v___x_785_);
v___y_775_ = v___x_786_;
goto v___jp_774_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = l_Int_toNat(v_head_772_);
v___x_788_ = l_Lean_instToExprInt_mkNat(v___x_787_);
v___y_775_ = v___x_788_;
goto v___jp_774_;
}
v___jp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
lean_inc_ref(v_consFn_770_);
v___x_776_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_769_, v_consFn_770_, v_tail_773_);
v___x_777_ = l_Lean_mkAppB(v_consFn_770_, v___y_775_, v___x_776_);
return v___x_777_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0___boxed(lean_object* v_nilFn_789_, lean_object* v_consFn_790_, lean_object* v_x_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_789_, v_consFn_790_, v_x_791_);
lean_dec(v_x_791_);
lean_dec_ref(v_nilFn_789_);
return v_res_792_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_798_ = lean_box(0);
v___x_799_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1));
v___x_800_ = l_Lean_Expr_const___override(v___x_799_, v___x_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof(lean_object* v_s_801_, lean_object* v_x_802_, lean_object* v_v_803_, lean_object* v_prf_804_){
_start:
{
lean_object* v___x_805_; lean_object* v___y_807_; lean_object* v_lowerBound_812_; lean_object* v_upperBound_813_; lean_object* v___x_814_; lean_object* v_type_815_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_823_; 
v___x_805_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2);
v_lowerBound_812_ = lean_ctor_get(v_s_801_, 0);
v_upperBound_813_ = lean_ctor_get(v_s_801_, 1);
v___x_814_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_815_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_812_) == 0)
{
lean_object* v___x_839_; 
v___x_839_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_823_ = v___x_839_;
goto v___jp_822_;
}
else
{
lean_object* v_val_840_; lean_object* v___x_841_; lean_object* v___y_843_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_val_840_ = lean_ctor_get(v_lowerBound_812_, 0);
v___x_841_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_845_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_846_ = lean_int_dec_le(v___x_845_, v_val_840_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_847_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_848_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_849_ = lean_int_neg(v_val_840_);
v___x_850_ = l_Int_toNat(v___x_849_);
lean_dec(v___x_849_);
v___x_851_ = l_Lean_instToExprInt_mkNat(v___x_850_);
v___x_852_ = l_Lean_mkApp3(v___x_847_, v_type_815_, v___x_848_, v___x_851_);
v___y_843_ = v___x_852_;
goto v___jp_842_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = l_Int_toNat(v_val_840_);
v___x_854_ = l_Lean_instToExprInt_mkNat(v___x_853_);
v___y_843_ = v___x_854_;
goto v___jp_842_;
}
v___jp_842_:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_mkAppB(v___x_841_, v_type_815_, v___y_843_);
v___y_823_ = v___x_844_;
goto v___jp_822_;
}
}
v___jp_806_:
{
lean_object* v_nil_808_; lean_object* v_cons_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_nil_808_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_809_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_810_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_808_, v_cons_809_, v_x_802_);
v___x_811_ = l_Lean_mkApp4(v___x_805_, v___y_807_, v___x_810_, v_v_803_, v_prf_804_);
return v___x_811_;
}
v___jp_816_:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = l_Lean_mkAppB(v___y_818_, v_type_815_, v___y_819_);
v___x_821_ = l_Lean_Expr_app___override(v___y_817_, v___x_820_);
v___y_807_ = v___x_821_;
goto v___jp_806_;
}
v___jp_822_:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Expr_app___override(v___x_814_, v___y_823_);
if (lean_obj_tag(v_upperBound_813_) == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_826_ = l_Lean_Expr_app___override(v___x_824_, v___x_825_);
v___y_807_ = v___x_826_;
goto v___jp_806_;
}
else
{
lean_object* v_val_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v_val_827_ = lean_ctor_get(v_upperBound_813_, 0);
v___x_828_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_829_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_830_ = lean_int_dec_le(v___x_829_, v_val_827_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_831_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_832_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_833_ = lean_int_neg(v_val_827_);
v___x_834_ = l_Int_toNat(v___x_833_);
lean_dec(v___x_833_);
v___x_835_ = l_Lean_instToExprInt_mkNat(v___x_834_);
v___x_836_ = l_Lean_mkApp3(v___x_831_, v_type_815_, v___x_832_, v___x_835_);
v___y_817_ = v___x_824_;
v___y_818_ = v___x_828_;
v___y_819_ = v___x_836_;
goto v___jp_816_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = l_Int_toNat(v_val_827_);
v___x_838_ = l_Lean_instToExprInt_mkNat(v___x_837_);
v___y_817_ = v___x_824_;
v___y_818_ = v___x_828_;
v___y_819_ = v___x_838_;
goto v___jp_816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___boxed(lean_object* v_s_855_, lean_object* v_x_856_, lean_object* v_v_857_, lean_object* v_prf_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_855_, v_x_856_, v_v_857_, v_prf_858_);
lean_dec(v_x_856_);
lean_dec_ref(v_s_855_);
return v_res_859_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = lean_box(0);
v___x_867_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1));
v___x_868_ = l_Lean_Expr_const___override(v___x_867_, v___x_866_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof(lean_object* v_s_869_, lean_object* v_t_870_, lean_object* v_x_871_, lean_object* v_v_872_, lean_object* v_ps_873_, lean_object* v_pt_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_926_; lean_object* v_lowerBound_944_; lean_object* v_upperBound_945_; lean_object* v___x_946_; lean_object* v_type_947_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_955_; 
v___x_875_ = lean_box(0);
v___x_876_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2);
v_lowerBound_944_ = lean_ctor_get(v_s_869_, 0);
v_upperBound_945_ = lean_ctor_get(v_s_869_, 1);
v___x_946_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_947_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_944_) == 0)
{
lean_object* v___x_971_; 
v___x_971_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_955_ = v___x_971_;
goto v___jp_954_;
}
else
{
lean_object* v_val_972_; lean_object* v___x_973_; lean_object* v___y_975_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_val_972_ = lean_ctor_get(v_lowerBound_944_, 0);
v___x_973_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_977_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_978_ = lean_int_dec_le(v___x_977_, v_val_972_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_979_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_980_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_981_ = lean_int_neg(v_val_972_);
v___x_982_ = l_Int_toNat(v___x_981_);
lean_dec(v___x_981_);
v___x_983_ = l_Lean_instToExprInt_mkNat(v___x_982_);
v___x_984_ = l_Lean_mkApp3(v___x_979_, v_type_947_, v___x_980_, v___x_983_);
v___y_975_ = v___x_984_;
goto v___jp_974_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = l_Int_toNat(v_val_972_);
v___x_986_ = l_Lean_instToExprInt_mkNat(v___x_985_);
v___y_975_ = v___x_986_;
goto v___jp_974_;
}
v___jp_974_:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_mkAppB(v___x_973_, v_type_947_, v___y_975_);
v___y_955_ = v___x_976_;
goto v___jp_954_;
}
}
v___jp_877_:
{
lean_object* v_nil_880_; lean_object* v_cons_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_nil_880_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_881_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_882_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_880_, v_cons_881_, v_x_871_);
v___x_883_ = l_Lean_mkApp6(v___x_876_, v___y_878_, v___y_879_, v___x_882_, v_v_872_, v_ps_873_, v_pt_874_);
return v___x_883_;
}
v___jp_884_:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = l_Lean_mkAppB(v___y_885_, v___y_886_, v___y_889_);
v___x_891_ = l_Lean_Expr_app___override(v___y_888_, v___x_890_);
v___y_878_ = v___y_887_;
v___y_879_ = v___x_891_;
goto v___jp_877_;
}
v___jp_892_:
{
lean_object* v_upperBound_898_; lean_object* v___x_899_; 
v_upperBound_898_ = lean_ctor_get(v_t_870_, 1);
v___x_899_ = l_Lean_Expr_app___override(v___y_893_, v___y_897_);
if (lean_obj_tag(v_upperBound_898_) == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
lean_dec_ref(v___y_894_);
v___x_900_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_901_ = l_Lean_Expr_app___override(v___x_900_, v___y_895_);
v___x_902_ = l_Lean_Expr_app___override(v___x_899_, v___x_901_);
v___y_878_ = v___y_896_;
v___y_879_ = v___x_902_;
goto v___jp_877_;
}
else
{
lean_object* v_val_903_; lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v_val_903_ = lean_ctor_get(v_upperBound_898_, 0);
v___x_904_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_905_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_906_ = lean_int_dec_le(v___x_905_, v_val_903_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_907_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_908_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
v___x_909_ = l_Lean_Name_mkStr2(v___y_894_, v___x_908_);
v___x_910_ = l_Lean_Expr_const___override(v___x_909_, v___x_875_);
v___x_911_ = lean_int_neg(v_val_903_);
v___x_912_ = l_Int_toNat(v___x_911_);
lean_dec(v___x_911_);
v___x_913_ = l_Lean_instToExprInt_mkNat(v___x_912_);
lean_inc_ref(v___y_895_);
v___x_914_ = l_Lean_mkApp3(v___x_907_, v___y_895_, v___x_910_, v___x_913_);
v___y_885_ = v___x_904_;
v___y_886_ = v___y_895_;
v___y_887_ = v___y_896_;
v___y_888_ = v___x_899_;
v___y_889_ = v___x_914_;
goto v___jp_884_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec_ref(v___y_894_);
v___x_915_ = l_Int_toNat(v_val_903_);
v___x_916_ = l_Lean_instToExprInt_mkNat(v___x_915_);
v___y_885_ = v___x_904_;
v___y_886_ = v___y_895_;
v___y_887_ = v___y_896_;
v___y_888_ = v___x_899_;
v___y_889_ = v___x_916_;
goto v___jp_884_;
}
}
}
v___jp_917_:
{
lean_object* v___x_924_; 
lean_inc_ref(v___y_920_);
v___x_924_ = l_Lean_mkAppB(v___y_921_, v___y_920_, v___y_923_);
v___y_893_ = v___y_918_;
v___y_894_ = v___y_919_;
v___y_895_ = v___y_920_;
v___y_896_ = v___y_922_;
v___y_897_ = v___x_924_;
goto v___jp_892_;
}
v___jp_925_:
{
lean_object* v_lowerBound_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_type_930_; 
v_lowerBound_927_ = lean_ctor_get(v_t_870_, 0);
v___x_928_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_929_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_930_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_927_) == 0)
{
lean_object* v___x_931_; 
v___x_931_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_893_ = v___x_928_;
v___y_894_ = v___x_929_;
v___y_895_ = v_type_930_;
v___y_896_ = v___y_926_;
v___y_897_ = v___x_931_;
goto v___jp_892_;
}
else
{
lean_object* v_val_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_val_932_ = lean_ctor_get(v_lowerBound_927_, 0);
v___x_933_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_934_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_935_ = lean_int_dec_le(v___x_934_, v_val_932_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_936_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_937_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_938_ = lean_int_neg(v_val_932_);
v___x_939_ = l_Int_toNat(v___x_938_);
lean_dec(v___x_938_);
v___x_940_ = l_Lean_instToExprInt_mkNat(v___x_939_);
v___x_941_ = l_Lean_mkApp3(v___x_936_, v_type_930_, v___x_937_, v___x_940_);
v___y_918_ = v___x_928_;
v___y_919_ = v___x_929_;
v___y_920_ = v_type_930_;
v___y_921_ = v___x_933_;
v___y_922_ = v___y_926_;
v___y_923_ = v___x_941_;
goto v___jp_917_;
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = l_Int_toNat(v_val_932_);
v___x_943_ = l_Lean_instToExprInt_mkNat(v___x_942_);
v___y_918_ = v___x_928_;
v___y_919_ = v___x_929_;
v___y_920_ = v_type_930_;
v___y_921_ = v___x_933_;
v___y_922_ = v___y_926_;
v___y_923_ = v___x_943_;
goto v___jp_917_;
}
}
}
v___jp_948_:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = l_Lean_mkAppB(v___y_949_, v_type_947_, v___y_951_);
v___x_953_ = l_Lean_Expr_app___override(v___y_950_, v___x_952_);
v___y_926_ = v___x_953_;
goto v___jp_925_;
}
v___jp_954_:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_Expr_app___override(v___x_946_, v___y_955_);
if (lean_obj_tag(v_upperBound_945_) == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_958_ = l_Lean_Expr_app___override(v___x_956_, v___x_957_);
v___y_926_ = v___x_958_;
goto v___jp_925_;
}
else
{
lean_object* v_val_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_val_959_ = lean_ctor_get(v_upperBound_945_, 0);
v___x_960_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_961_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_962_ = lean_int_dec_le(v___x_961_, v_val_959_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_963_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_964_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_965_ = lean_int_neg(v_val_959_);
v___x_966_ = l_Int_toNat(v___x_965_);
lean_dec(v___x_965_);
v___x_967_ = l_Lean_instToExprInt_mkNat(v___x_966_);
v___x_968_ = l_Lean_mkApp3(v___x_963_, v_type_947_, v___x_964_, v___x_967_);
v___y_949_ = v___x_960_;
v___y_950_ = v___x_956_;
v___y_951_ = v___x_968_;
goto v___jp_948_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = l_Int_toNat(v_val_959_);
v___x_970_ = l_Lean_instToExprInt_mkNat(v___x_969_);
v___y_949_ = v___x_960_;
v___y_950_ = v___x_956_;
v___y_951_ = v___x_970_;
goto v___jp_948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___boxed(lean_object* v_s_987_, lean_object* v_t_988_, lean_object* v_x_989_, lean_object* v_v_990_, lean_object* v_ps_991_, lean_object* v_pt_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_987_, v_t_988_, v_x_989_, v_v_990_, v_ps_991_, v_pt_992_);
lean_dec(v_x_989_);
lean_dec_ref(v_t_988_);
lean_dec_ref(v_s_987_);
return v_res_993_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_box(0);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1));
v___x_1001_ = l_Lean_Expr_const___override(v___x_1000_, v___x_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof(lean_object* v_s_1002_, lean_object* v_t_1003_, lean_object* v_a_1004_, lean_object* v_x_1005_, lean_object* v_b_1006_, lean_object* v_y_1007_, lean_object* v_v_1008_, lean_object* v_px_1009_, lean_object* v_py_1010_){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1097_; lean_object* v_lowerBound_1115_; lean_object* v_upperBound_1116_; lean_object* v___x_1117_; lean_object* v_type_1118_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1126_; 
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2);
v_lowerBound_1115_ = lean_ctor_get(v_s_1002_, 0);
v_upperBound_1116_ = lean_ctor_get(v_s_1002_, 1);
v___x_1117_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1118_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1115_) == 0)
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1126_ = v___x_1142_;
goto v___jp_1125_;
}
else
{
lean_object* v_val_1143_; lean_object* v___x_1144_; lean_object* v___y_1146_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v_val_1143_ = lean_ctor_get(v_lowerBound_1115_, 0);
v___x_1144_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1148_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1149_ = lean_int_dec_le(v___x_1148_, v_val_1143_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1150_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1151_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1152_ = lean_int_neg(v_val_1143_);
v___x_1153_ = l_Int_toNat(v___x_1152_);
lean_dec(v___x_1152_);
v___x_1154_ = l_Lean_instToExprInt_mkNat(v___x_1153_);
v___x_1155_ = l_Lean_mkApp3(v___x_1150_, v_type_1118_, v___x_1151_, v___x_1154_);
v___y_1146_ = v___x_1155_;
goto v___jp_1145_;
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = l_Int_toNat(v_val_1143_);
v___x_1157_ = l_Lean_instToExprInt_mkNat(v___x_1156_);
v___y_1146_ = v___x_1157_;
goto v___jp_1145_;
}
v___jp_1145_:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_mkAppB(v___x_1144_, v_type_1118_, v___y_1146_);
v___y_1126_ = v___x_1147_;
goto v___jp_1125_;
}
}
v___jp_1013_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v___y_1018_, v___y_1017_, v_y_1007_);
lean_dec_ref(v___y_1018_);
v___x_1022_ = l_Lean_mkApp9(v___x_1012_, v___y_1019_, v___y_1015_, v___y_1016_, v___y_1014_, v___y_1020_, v___x_1021_, v_v_1008_, v_px_1009_, v_py_1010_);
return v___x_1022_;
}
v___jp_1023_:
{
lean_object* v_type_1027_; lean_object* v_nil_1028_; lean_object* v_cons_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v_type_1027_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_nil_1028_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1029_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1030_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1028_, v_cons_1029_, v_x_1005_);
v___x_1031_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1032_ = lean_int_dec_le(v___x_1031_, v_b_1006_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1033_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1034_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1035_ = lean_int_neg(v_b_1006_);
v___x_1036_ = l_Int_toNat(v___x_1035_);
lean_dec(v___x_1035_);
v___x_1037_ = l_Lean_instToExprInt_mkNat(v___x_1036_);
v___x_1038_ = l_Lean_mkApp3(v___x_1033_, v_type_1027_, v___x_1034_, v___x_1037_);
v___y_1014_ = v___x_1030_;
v___y_1015_ = v___y_1024_;
v___y_1016_ = v___y_1026_;
v___y_1017_ = v_cons_1029_;
v___y_1018_ = v_nil_1028_;
v___y_1019_ = v___y_1025_;
v___y_1020_ = v___x_1038_;
goto v___jp_1013_;
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = l_Int_toNat(v_b_1006_);
v___x_1040_ = l_Lean_instToExprInt_mkNat(v___x_1039_);
v___y_1014_ = v___x_1030_;
v___y_1015_ = v___y_1024_;
v___y_1016_ = v___y_1026_;
v___y_1017_ = v_cons_1029_;
v___y_1018_ = v_nil_1028_;
v___y_1019_ = v___y_1025_;
v___y_1020_ = v___x_1040_;
goto v___jp_1013_;
}
}
v___jp_1041_:
{
lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1045_ = lean_int_dec_le(v___x_1044_, v_a_1004_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1046_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1047_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1048_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1049_ = lean_int_neg(v_a_1004_);
v___x_1050_ = l_Int_toNat(v___x_1049_);
lean_dec(v___x_1049_);
v___x_1051_ = l_Lean_instToExprInt_mkNat(v___x_1050_);
v___x_1052_ = l_Lean_mkApp3(v___x_1046_, v___x_1047_, v___x_1048_, v___x_1051_);
v___y_1024_ = v___y_1043_;
v___y_1025_ = v___y_1042_;
v___y_1026_ = v___x_1052_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = l_Int_toNat(v_a_1004_);
v___x_1054_ = l_Lean_instToExprInt_mkNat(v___x_1053_);
v___y_1024_ = v___y_1043_;
v___y_1025_ = v___y_1042_;
v___y_1026_ = v___x_1054_;
goto v___jp_1023_;
}
}
v___jp_1055_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = l_Lean_mkAppB(v___y_1059_, v___y_1056_, v___y_1060_);
v___x_1062_ = l_Lean_Expr_app___override(v___y_1058_, v___x_1061_);
v___y_1042_ = v___y_1057_;
v___y_1043_ = v___x_1062_;
goto v___jp_1041_;
}
v___jp_1063_:
{
lean_object* v_upperBound_1069_; lean_object* v___x_1070_; 
v_upperBound_1069_ = lean_ctor_get(v_t_1003_, 1);
v___x_1070_ = l_Lean_Expr_app___override(v___y_1066_, v___y_1068_);
if (lean_obj_tag(v_upperBound_1069_) == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_dec_ref(v___y_1064_);
v___x_1071_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1072_ = l_Lean_Expr_app___override(v___x_1071_, v___y_1065_);
v___x_1073_ = l_Lean_Expr_app___override(v___x_1070_, v___x_1072_);
v___y_1042_ = v___y_1067_;
v___y_1043_ = v___x_1073_;
goto v___jp_1041_;
}
else
{
lean_object* v_val_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v_val_1074_ = lean_ctor_get(v_upperBound_1069_, 0);
v___x_1075_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1076_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1077_ = lean_int_dec_le(v___x_1076_, v_val_1074_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1078_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
v___x_1080_ = l_Lean_Name_mkStr2(v___y_1064_, v___x_1079_);
v___x_1081_ = l_Lean_Expr_const___override(v___x_1080_, v___x_1011_);
v___x_1082_ = lean_int_neg(v_val_1074_);
v___x_1083_ = l_Int_toNat(v___x_1082_);
lean_dec(v___x_1082_);
v___x_1084_ = l_Lean_instToExprInt_mkNat(v___x_1083_);
lean_inc_ref(v___y_1065_);
v___x_1085_ = l_Lean_mkApp3(v___x_1078_, v___y_1065_, v___x_1081_, v___x_1084_);
v___y_1056_ = v___y_1065_;
v___y_1057_ = v___y_1067_;
v___y_1058_ = v___x_1070_;
v___y_1059_ = v___x_1075_;
v___y_1060_ = v___x_1085_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec_ref(v___y_1064_);
v___x_1086_ = l_Int_toNat(v_val_1074_);
v___x_1087_ = l_Lean_instToExprInt_mkNat(v___x_1086_);
v___y_1056_ = v___y_1065_;
v___y_1057_ = v___y_1067_;
v___y_1058_ = v___x_1070_;
v___y_1059_ = v___x_1075_;
v___y_1060_ = v___x_1087_;
goto v___jp_1055_;
}
}
}
v___jp_1088_:
{
lean_object* v___x_1095_; 
lean_inc_ref(v___y_1091_);
v___x_1095_ = l_Lean_mkAppB(v___y_1090_, v___y_1091_, v___y_1094_);
v___y_1064_ = v___y_1089_;
v___y_1065_ = v___y_1091_;
v___y_1066_ = v___y_1092_;
v___y_1067_ = v___y_1093_;
v___y_1068_ = v___x_1095_;
goto v___jp_1063_;
}
v___jp_1096_:
{
lean_object* v_lowerBound_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_type_1101_; 
v_lowerBound_1098_ = lean_ctor_get(v_t_1003_, 0);
v___x_1099_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1100_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1101_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1098_) == 0)
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1064_ = v___x_1100_;
v___y_1065_ = v_type_1101_;
v___y_1066_ = v___x_1099_;
v___y_1067_ = v___y_1097_;
v___y_1068_ = v___x_1102_;
goto v___jp_1063_;
}
else
{
lean_object* v_val_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v_val_1103_ = lean_ctor_get(v_lowerBound_1098_, 0);
v___x_1104_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1105_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1106_ = lean_int_dec_le(v___x_1105_, v_val_1103_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1107_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1108_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1109_ = lean_int_neg(v_val_1103_);
v___x_1110_ = l_Int_toNat(v___x_1109_);
lean_dec(v___x_1109_);
v___x_1111_ = l_Lean_instToExprInt_mkNat(v___x_1110_);
v___x_1112_ = l_Lean_mkApp3(v___x_1107_, v_type_1101_, v___x_1108_, v___x_1111_);
v___y_1089_ = v___x_1100_;
v___y_1090_ = v___x_1104_;
v___y_1091_ = v_type_1101_;
v___y_1092_ = v___x_1099_;
v___y_1093_ = v___y_1097_;
v___y_1094_ = v___x_1112_;
goto v___jp_1088_;
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = l_Int_toNat(v_val_1103_);
v___x_1114_ = l_Lean_instToExprInt_mkNat(v___x_1113_);
v___y_1089_ = v___x_1100_;
v___y_1090_ = v___x_1104_;
v___y_1091_ = v_type_1101_;
v___y_1092_ = v___x_1099_;
v___y_1093_ = v___y_1097_;
v___y_1094_ = v___x_1114_;
goto v___jp_1088_;
}
}
}
v___jp_1119_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = l_Lean_mkAppB(v___y_1121_, v_type_1118_, v___y_1122_);
v___x_1124_ = l_Lean_Expr_app___override(v___y_1120_, v___x_1123_);
v___y_1097_ = v___x_1124_;
goto v___jp_1096_;
}
v___jp_1125_:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_Expr_app___override(v___x_1117_, v___y_1126_);
if (lean_obj_tag(v_upperBound_1116_) == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1129_ = l_Lean_Expr_app___override(v___x_1127_, v___x_1128_);
v___y_1097_ = v___x_1129_;
goto v___jp_1096_;
}
else
{
lean_object* v_val_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_val_1130_ = lean_ctor_get(v_upperBound_1116_, 0);
v___x_1131_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1132_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1133_ = lean_int_dec_le(v___x_1132_, v_val_1130_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1134_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1135_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1136_ = lean_int_neg(v_val_1130_);
v___x_1137_ = l_Int_toNat(v___x_1136_);
lean_dec(v___x_1136_);
v___x_1138_ = l_Lean_instToExprInt_mkNat(v___x_1137_);
v___x_1139_ = l_Lean_mkApp3(v___x_1134_, v_type_1118_, v___x_1135_, v___x_1138_);
v___y_1120_ = v___x_1127_;
v___y_1121_ = v___x_1131_;
v___y_1122_ = v___x_1139_;
goto v___jp_1119_;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = l_Int_toNat(v_val_1130_);
v___x_1141_ = l_Lean_instToExprInt_mkNat(v___x_1140_);
v___y_1120_ = v___x_1127_;
v___y_1121_ = v___x_1131_;
v___y_1122_ = v___x_1141_;
goto v___jp_1119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___boxed(lean_object* v_s_1158_, lean_object* v_t_1159_, lean_object* v_a_1160_, lean_object* v_x_1161_, lean_object* v_b_1162_, lean_object* v_y_1163_, lean_object* v_v_1164_, lean_object* v_px_1165_, lean_object* v_py_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1158_, v_t_1159_, v_a_1160_, v_x_1161_, v_b_1162_, v_y_1163_, v_v_1164_, v_px_1165_, v_py_1166_);
lean_dec(v_y_1163_);
lean_dec(v_b_1162_);
lean_dec(v_x_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_t_1159_);
lean_dec_ref(v_s_1158_);
return v_res_1167_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2));
v___x_1175_ = l_Lean_Expr_const___override(v___x_1174_, v___x_1173_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1179_ = lean_box(0);
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5));
v___x_1181_ = l_Lean_Expr_const___override(v___x_1180_, v___x_1179_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_box(0);
v___x_1186_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8));
v___x_1187_ = l_Lean_Expr_const___override(v___x_1186_, v___x_1185_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = lean_box(0);
v___x_1196_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12));
v___x_1197_ = l_Lean_Expr_const___override(v___x_1196_, v___x_1195_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15));
v___x_1206_ = l_Lean_Expr_const___override(v___x_1205_, v___x_1204_);
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = lean_box(0);
v___x_1213_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18));
v___x_1214_ = l_Lean_Expr_const___override(v___x_1213_, v___x_1212_);
return v___x_1214_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21));
v___x_1222_ = l_Lean_Expr_const___override(v___x_1221_, v___x_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof(lean_object* v_m_1223_, lean_object* v_r_1224_, lean_object* v_i_1225_, lean_object* v_x_1226_, lean_object* v_v_1227_, lean_object* v_w_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_m_1234_; lean_object* v___y_1236_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_m_1234_ = l_Lean_mkNatLit(v_m_1223_);
v___x_1264_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1265_ = lean_int_dec_le(v___x_1264_, v_r_1224_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1266_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1267_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1268_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1269_ = lean_int_neg(v_r_1224_);
v___x_1270_ = l_Int_toNat(v___x_1269_);
lean_dec(v___x_1269_);
v___x_1271_ = l_Lean_instToExprInt_mkNat(v___x_1270_);
v___x_1272_ = l_Lean_mkApp3(v___x_1266_, v___x_1267_, v___x_1268_, v___x_1271_);
v___y_1236_ = v___x_1272_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = l_Int_toNat(v_r_1224_);
v___x_1274_ = l_Lean_instToExprInt_mkNat(v___x_1273_);
v___y_1236_ = v___x_1274_;
goto v___jp_1235_;
}
v___jp_1235_:
{
lean_object* v_i_1237_; lean_object* v_nil_1238_; lean_object* v_cons_1239_; lean_object* v_x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_i_1237_ = l_Lean_mkNatLit(v_i_1225_);
v_nil_1238_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1239_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v_x_1240_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1238_, v_cons_1239_, v_x_1226_);
v___x_1241_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3);
v___x_1242_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6);
v___x_1243_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9);
v___x_1244_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13);
lean_inc_ref(v_x_1240_);
v___x_1245_ = l_Lean_Expr_app___override(v___x_1244_, v_x_1240_);
lean_inc_ref(v_i_1237_);
v___x_1246_ = l_Lean_mkApp4(v___x_1241_, v___x_1242_, v___x_1243_, v___x_1245_, v_i_1237_);
lean_inc(v_a_1232_);
lean_inc_ref(v_a_1231_);
lean_inc(v_a_1230_);
lean_inc_ref(v_a_1229_);
v___x_1247_ = l_Lean_Meta_mkDecideProof(v___x_1246_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref(v___x_1247_);
v___x_1249_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16);
lean_inc_ref(v_i_1237_);
lean_inc_ref(v_v_1227_);
v___x_1250_ = l_Lean_mkAppB(v___x_1249_, v_v_1227_, v_i_1237_);
v___x_1251_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc_ref(v_v_1227_);
lean_inc_ref(v_x_1240_);
lean_inc_ref(v_m_1234_);
v___x_1252_ = l_Lean_mkApp3(v___x_1251_, v_m_1234_, v_x_1240_, v_v_1227_);
v___x_1253_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v___x_1250_, v___x_1252_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1263_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1263_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1263_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1258_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22);
v___x_1259_ = l_Lean_mkApp8(v___x_1258_, v_m_1234_, v___y_1236_, v_i_1237_, v_x_1240_, v_v_1227_, v_a_1248_, v_a_1254_, v_w_1228_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1259_);
v___x_1261_ = v___x_1256_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
else
{
lean_dec(v_a_1248_);
lean_dec_ref(v_x_1240_);
lean_dec_ref(v_i_1237_);
lean_dec_ref(v___y_1236_);
lean_dec_ref(v_m_1234_);
lean_dec_ref(v_w_1228_);
lean_dec_ref(v_v_1227_);
return v___x_1253_;
}
}
else
{
lean_dec_ref(v_x_1240_);
lean_dec_ref(v_i_1237_);
lean_dec_ref(v___y_1236_);
lean_dec_ref(v_m_1234_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec_ref(v_w_1228_);
lean_dec_ref(v_v_1227_);
return v___x_1247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___boxed(lean_object* v_m_1275_, lean_object* v_r_1276_, lean_object* v_i_1277_, lean_object* v_x_1278_, lean_object* v_v_1279_, lean_object* v_w_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1275_, v_r_1276_, v_i_1277_, v_x_1278_, v_v_1279_, v_w_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
lean_dec(v_x_1278_);
lean_dec(v_r_1276_);
return v_res_1286_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0(void){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0);
v___x_1289_ = l_ReaderT_instMonad___redArg(v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(lean_object* v_c_1294_, lean_object* v_v_1295_, lean_object* v_assumptions_1296_, lean_object* v_x_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, uint8_t v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v___x_1308_; lean_object* v_toApplicative_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1434_; 
v___x_1308_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1);
v_toApplicative_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; 
v_unused_1435_ = lean_ctor_get(v___x_1308_, 1);
lean_dec(v_unused_1435_);
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1434_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_toApplicative_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1434_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v_toFunctor_1313_; lean_object* v_toSeq_1314_; lean_object* v_toSeqLeft_1315_; lean_object* v_toSeqRight_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1432_; 
v_toFunctor_1313_ = lean_ctor_get(v_toApplicative_1309_, 0);
v_toSeq_1314_ = lean_ctor_get(v_toApplicative_1309_, 2);
v_toSeqLeft_1315_ = lean_ctor_get(v_toApplicative_1309_, 3);
v_toSeqRight_1316_ = lean_ctor_get(v_toApplicative_1309_, 4);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_toApplicative_1309_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v_toApplicative_1309_, 1);
lean_dec(v_unused_1433_);
v___x_1318_ = v_toApplicative_1309_;
v_isShared_1319_ = v_isSharedCheck_1432_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_toSeqRight_1316_);
lean_inc(v_toSeqLeft_1315_);
lean_inc(v_toSeq_1314_);
lean_inc(v_toFunctor_1313_);
lean_dec(v_toApplicative_1309_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1432_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___f_1320_; lean_object* v___f_1321_; lean_object* v___f_1322_; lean_object* v___f_1323_; lean_object* v___x_1324_; lean_object* v___f_1325_; lean_object* v___f_1326_; lean_object* v___f_1327_; lean_object* v___x_1329_; 
v___f_1320_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2));
v___f_1321_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3));
lean_inc_ref(v_toFunctor_1313_);
v___f_1322_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1322_, 0, v_toFunctor_1313_);
v___f_1323_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1323_, 0, v_toFunctor_1313_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___f_1322_);
lean_ctor_set(v___x_1324_, 1, v___f_1323_);
v___f_1325_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1325_, 0, v_toSeqRight_1316_);
v___f_1326_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1326_, 0, v_toSeqLeft_1315_);
v___f_1327_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1327_, 0, v_toSeq_1314_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 4, v___f_1325_);
lean_ctor_set(v___x_1318_, 3, v___f_1326_);
lean_ctor_set(v___x_1318_, 2, v___f_1327_);
lean_ctor_set(v___x_1318_, 1, v___f_1320_);
lean_ctor_set(v___x_1318_, 0, v___x_1324_);
v___x_1329_ = v___x_1318_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___f_1320_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v___f_1327_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v___f_1326_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v___f_1325_);
v___x_1329_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1331_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 1, v___f_1321_);
lean_ctor_set(v___x_1311_, 0, v___x_1329_);
v___x_1331_ = v___x_1311_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v___f_1321_);
v___x_1331_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; lean_object* v_toApplicative_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1428_; 
v___x_1332_ = l_ReaderT_instMonad___redArg(v___x_1331_);
v_toApplicative_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v___x_1332_, 1);
lean_dec(v_unused_1429_);
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1428_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_toApplicative_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1428_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_toFunctor_1337_; lean_object* v_toSeq_1338_; lean_object* v_toSeqLeft_1339_; lean_object* v_toSeqRight_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1426_; 
v_toFunctor_1337_ = lean_ctor_get(v_toApplicative_1333_, 0);
v_toSeq_1338_ = lean_ctor_get(v_toApplicative_1333_, 2);
v_toSeqLeft_1339_ = lean_ctor_get(v_toApplicative_1333_, 3);
v_toSeqRight_1340_ = lean_ctor_get(v_toApplicative_1333_, 4);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_toApplicative_1333_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; 
v_unused_1427_ = lean_ctor_get(v_toApplicative_1333_, 1);
lean_dec(v_unused_1427_);
v___x_1342_ = v_toApplicative_1333_;
v_isShared_1343_ = v_isSharedCheck_1426_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_toSeqRight_1340_);
lean_inc(v_toSeqLeft_1339_);
lean_inc(v_toSeq_1338_);
lean_inc(v_toFunctor_1337_);
lean_dec(v_toApplicative_1333_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1426_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___f_1344_; lean_object* v___f_1345_; lean_object* v___f_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; lean_object* v___f_1349_; lean_object* v___f_1350_; lean_object* v___f_1351_; lean_object* v___x_1353_; 
v___f_1344_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4));
v___f_1345_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5));
lean_inc_ref(v_toFunctor_1337_);
v___f_1346_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1346_, 0, v_toFunctor_1337_);
v___f_1347_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1347_, 0, v_toFunctor_1337_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___f_1346_);
lean_ctor_set(v___x_1348_, 1, v___f_1347_);
v___f_1349_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1349_, 0, v_toSeqRight_1340_);
v___f_1350_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1350_, 0, v_toSeqLeft_1339_);
v___f_1351_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1351_, 0, v_toSeq_1338_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 4, v___f_1349_);
lean_ctor_set(v___x_1342_, 3, v___f_1350_);
lean_ctor_set(v___x_1342_, 2, v___f_1351_);
lean_ctor_set(v___x_1342_, 1, v___f_1344_);
lean_ctor_set(v___x_1342_, 0, v___x_1348_);
v___x_1353_ = v___x_1342_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___f_1344_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v___f_1351_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v___f_1350_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v___f_1349_);
v___x_1353_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1355_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 1, v___f_1345_);
lean_ctor_set(v___x_1335_, 0, v___x_1353_);
v___x_1355_ = v___x_1335_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___f_1345_);
v___x_1355_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1356_ = l_ReaderT_instMonad___redArg(v___x_1355_);
v___x_1357_ = l_ReaderT_instMonad___redArg(v___x_1356_);
v___x_1358_ = l_ReaderT_instMonad___redArg(v___x_1357_);
v___x_1359_ = l_ReaderT_instMonad___redArg(v___x_1358_);
v___x_1360_ = l_ReaderT_instMonad___redArg(v___x_1359_);
switch(lean_obj_tag(v_x_1297_))
{
case 0:
{
lean_object* v_i_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_4123__overap_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec_ref(v_v_1295_);
v_i_1361_ = lean_ctor_get(v_x_1297_, 2);
lean_inc(v_i_1361_);
lean_dec_ref(v_x_1297_);
v___x_1362_ = l_Lean_instInhabitedExpr;
v___x_1363_ = l_instInhabitedOfMonad___redArg(v___x_1360_, v___x_1362_);
v___x_4123__overap_1364_ = lean_array_get_borrowed(v___x_1363_, v_assumptions_1296_, v_i_1361_);
lean_dec(v_i_1361_);
v___x_1365_ = lean_box(v_a_1301_);
lean_inc(v___x_4123__overap_1364_);
v___x_1366_ = lean_apply_10(v___x_4123__overap_1364_, v_a_1298_, v_a_1299_, v_a_1300_, v___x_1365_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, lean_box(0));
return v___x_1366_;
}
case 1:
{
lean_object* v_s_1367_; lean_object* v_c_1368_; lean_object* v_j_1369_; lean_object* v___x_1370_; 
lean_dec_ref(v___x_1360_);
v_s_1367_ = lean_ctor_get(v_x_1297_, 0);
lean_inc_ref(v_s_1367_);
v_c_1368_ = lean_ctor_get(v_x_1297_, 1);
lean_inc(v_c_1368_);
v_j_1369_ = lean_ctor_get(v_x_1297_, 2);
lean_inc_ref(v_j_1369_);
lean_dec_ref(v_x_1297_);
lean_inc_ref(v_v_1295_);
v___x_1370_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1368_, v_v_1295_, v_assumptions_1296_, v_j_1369_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1379_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1367_, v_c_1368_, v_v_1295_, v_a_1371_);
lean_dec(v_c_1368_);
lean_dec_ref(v_s_1367_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1375_);
v___x_1377_ = v___x_1373_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
else
{
lean_dec(v_c_1368_);
lean_dec_ref(v_s_1367_);
lean_dec_ref(v_v_1295_);
return v___x_1370_;
}
}
case 2:
{
lean_object* v_s_1380_; lean_object* v_t_1381_; lean_object* v_j_1382_; lean_object* v_k_1383_; lean_object* v___x_1384_; 
lean_dec_ref(v___x_1360_);
v_s_1380_ = lean_ctor_get(v_x_1297_, 0);
lean_inc_ref(v_s_1380_);
v_t_1381_ = lean_ctor_get(v_x_1297_, 1);
lean_inc_ref(v_t_1381_);
v_j_1382_ = lean_ctor_get(v_x_1297_, 3);
lean_inc_ref(v_j_1382_);
v_k_1383_ = lean_ctor_get(v_x_1297_, 4);
lean_inc_ref(v_k_1383_);
lean_dec_ref(v_x_1297_);
lean_inc(v_a_1306_);
lean_inc_ref(v_a_1305_);
lean_inc(v_a_1304_);
lean_inc_ref(v_a_1303_);
lean_inc(v_a_1302_);
lean_inc_ref(v_a_1300_);
lean_inc(v_a_1299_);
lean_inc(v_a_1298_);
lean_inc_ref(v_v_1295_);
v___x_1384_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1294_, v_v_1295_, v_assumptions_1296_, v_j_1382_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref(v___x_1384_);
lean_inc_ref(v_v_1295_);
v___x_1386_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1294_, v_v_1295_, v_assumptions_1296_, v_k_1383_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1395_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1380_, v_t_1381_, v_c_1294_, v_v_1295_, v_a_1385_, v_a_1387_);
lean_dec_ref(v_t_1381_);
lean_dec_ref(v_s_1380_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1391_);
v___x_1393_ = v___x_1389_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
else
{
lean_dec(v_a_1385_);
lean_dec_ref(v_t_1381_);
lean_dec_ref(v_s_1380_);
lean_dec_ref(v_v_1295_);
return v___x_1386_;
}
}
else
{
lean_dec_ref(v_k_1383_);
lean_dec_ref(v_t_1381_);
lean_dec_ref(v_s_1380_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_v_1295_);
return v___x_1384_;
}
}
case 3:
{
lean_object* v_s_1396_; lean_object* v_t_1397_; lean_object* v_x_1398_; lean_object* v_y_1399_; lean_object* v_a_1400_; lean_object* v_j_1401_; lean_object* v_b_1402_; lean_object* v_k_1403_; lean_object* v___x_1404_; 
lean_dec_ref(v___x_1360_);
v_s_1396_ = lean_ctor_get(v_x_1297_, 0);
lean_inc_ref(v_s_1396_);
v_t_1397_ = lean_ctor_get(v_x_1297_, 1);
lean_inc_ref(v_t_1397_);
v_x_1398_ = lean_ctor_get(v_x_1297_, 2);
lean_inc(v_x_1398_);
v_y_1399_ = lean_ctor_get(v_x_1297_, 3);
lean_inc(v_y_1399_);
v_a_1400_ = lean_ctor_get(v_x_1297_, 4);
lean_inc(v_a_1400_);
v_j_1401_ = lean_ctor_get(v_x_1297_, 5);
lean_inc_ref(v_j_1401_);
v_b_1402_ = lean_ctor_get(v_x_1297_, 6);
lean_inc(v_b_1402_);
v_k_1403_ = lean_ctor_get(v_x_1297_, 7);
lean_inc_ref(v_k_1403_);
lean_dec_ref(v_x_1297_);
lean_inc(v_a_1306_);
lean_inc_ref(v_a_1305_);
lean_inc(v_a_1304_);
lean_inc_ref(v_a_1303_);
lean_inc(v_a_1302_);
lean_inc_ref(v_a_1300_);
lean_inc(v_a_1299_);
lean_inc(v_a_1298_);
lean_inc_ref(v_v_1295_);
v___x_1404_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1398_, v_v_1295_, v_assumptions_1296_, v_j_1401_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref(v___x_1404_);
lean_inc_ref(v_v_1295_);
v___x_1406_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_y_1399_, v_v_1295_, v_assumptions_1296_, v_k_1403_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1415_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1396_, v_t_1397_, v_a_1400_, v_x_1398_, v_b_1402_, v_y_1399_, v_v_1295_, v_a_1405_, v_a_1407_);
lean_dec(v_y_1399_);
lean_dec(v_b_1402_);
lean_dec(v_x_1398_);
lean_dec(v_a_1400_);
lean_dec_ref(v_t_1397_);
lean_dec_ref(v_s_1396_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
else
{
lean_dec(v_a_1405_);
lean_dec(v_b_1402_);
lean_dec(v_a_1400_);
lean_dec(v_y_1399_);
lean_dec(v_x_1398_);
lean_dec_ref(v_t_1397_);
lean_dec_ref(v_s_1396_);
lean_dec_ref(v_v_1295_);
return v___x_1406_;
}
}
else
{
lean_dec_ref(v_k_1403_);
lean_dec(v_b_1402_);
lean_dec(v_a_1400_);
lean_dec(v_y_1399_);
lean_dec(v_x_1398_);
lean_dec_ref(v_t_1397_);
lean_dec_ref(v_s_1396_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_v_1295_);
return v___x_1404_;
}
}
default: 
{
lean_object* v_m_1416_; lean_object* v_r_1417_; lean_object* v_i_1418_; lean_object* v_x_1419_; lean_object* v_j_1420_; lean_object* v___x_1421_; 
lean_dec_ref(v___x_1360_);
v_m_1416_ = lean_ctor_get(v_x_1297_, 0);
lean_inc(v_m_1416_);
v_r_1417_ = lean_ctor_get(v_x_1297_, 1);
lean_inc(v_r_1417_);
v_i_1418_ = lean_ctor_get(v_x_1297_, 2);
lean_inc(v_i_1418_);
v_x_1419_ = lean_ctor_get(v_x_1297_, 3);
lean_inc(v_x_1419_);
v_j_1420_ = lean_ctor_get(v_x_1297_, 4);
lean_inc_ref(v_j_1420_);
lean_dec_ref(v_x_1297_);
lean_inc(v_a_1306_);
lean_inc_ref(v_a_1305_);
lean_inc(v_a_1304_);
lean_inc_ref(v_a_1303_);
lean_inc_ref(v_v_1295_);
v___x_1421_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1419_, v_v_1295_, v_assumptions_1296_, v_j_1420_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref(v___x_1421_);
v___x_1423_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1416_, v_r_1417_, v_i_1418_, v_x_1419_, v_v_1295_, v_a_1422_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_x_1419_);
lean_dec(v_r_1417_);
return v___x_1423_;
}
else
{
lean_dec(v_x_1419_);
lean_dec(v_i_1418_);
lean_dec(v_r_1417_);
lean_dec(v_m_1416_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec_ref(v_v_1295_);
return v___x_1421_;
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___boxed(lean_object* v_c_1436_, lean_object* v_v_1437_, lean_object* v_assumptions_1438_, lean_object* v_x_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
uint8_t v_a_4222__boxed_1450_; lean_object* v_res_1451_; 
v_a_4222__boxed_1450_ = lean_unbox(v_a_1443_);
v_res_1451_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1436_, v_v_1437_, v_assumptions_1438_, v_x_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_4222__boxed_1450_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec_ref(v_assumptions_1438_);
lean_dec(v_c_1436_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof(lean_object* v_s_1452_, lean_object* v_c_1453_, lean_object* v_v_1454_, lean_object* v_assumptions_1455_, lean_object* v_x_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, uint8_t v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1453_, v_v_1454_, v_assumptions_1455_, v_x_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___boxed(lean_object* v_s_1468_, lean_object* v_c_1469_, lean_object* v_v_1470_, lean_object* v_assumptions_1471_, lean_object* v_x_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
uint8_t v_a_4505__boxed_1483_; lean_object* v_res_1484_; 
v_a_4505__boxed_1483_ = lean_unbox(v_a_1476_);
v_res_1484_ = l_Lean_Elab_Tactic_Omega_Justification_proof(v_s_1468_, v_c_1469_, v_v_1470_, v_assumptions_1471_, v_x_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_4505__boxed_1483_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
lean_dec_ref(v_assumptions_1471_);
lean_dec(v_c_1469_);
lean_dec_ref(v_s_1468_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_instToString___lam__0(lean_object* v_f_1485_){
_start:
{
lean_object* v_coeffs_1486_; lean_object* v_constraint_1487_; lean_object* v_justification_1488_; lean_object* v___x_1489_; 
v_coeffs_1486_ = lean_ctor_get(v_f_1485_, 0);
lean_inc(v_coeffs_1486_);
v_constraint_1487_ = lean_ctor_get(v_f_1485_, 1);
lean_inc_ref(v_constraint_1487_);
v_justification_1488_ = lean_ctor_get(v_f_1485_, 2);
lean_inc_ref(v_justification_1488_);
lean_dec_ref(v_f_1485_);
v___x_1489_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_1487_, v_coeffs_1486_, v_justification_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_tidy(lean_object* v_f_1492_){
_start:
{
lean_object* v_coeffs_1493_; lean_object* v_constraint_1494_; lean_object* v_justification_1495_; lean_object* v___x_1496_; 
v_coeffs_1493_ = lean_ctor_get(v_f_1492_, 0);
v_constraint_1494_ = lean_ctor_get(v_f_1492_, 1);
v_justification_1495_ = lean_ctor_get(v_f_1492_, 2);
lean_inc_ref(v_justification_1495_);
lean_inc(v_coeffs_1493_);
lean_inc_ref(v_constraint_1494_);
v___x_1496_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(v_constraint_1494_, v_coeffs_1493_, v_justification_1495_);
if (lean_obj_tag(v___x_1496_) == 0)
{
return v_f_1492_;
}
else
{
lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1508_; 
v_isSharedCheck_1508_ = !lean_is_exclusive(v_f_1492_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; lean_object* v_unused_1510_; lean_object* v_unused_1511_; 
v_unused_1509_ = lean_ctor_get(v_f_1492_, 2);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_f_1492_, 1);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_f_1492_, 0);
lean_dec(v_unused_1511_);
v___x_1498_ = v_f_1492_;
v_isShared_1499_ = v_isSharedCheck_1508_;
goto v_resetjp_1497_;
}
else
{
lean_dec(v_f_1492_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1508_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_val_1500_; lean_object* v_snd_1501_; lean_object* v_fst_1502_; lean_object* v_fst_1503_; lean_object* v_snd_1504_; lean_object* v___x_1506_; 
v_val_1500_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_val_1500_);
lean_dec_ref(v___x_1496_);
v_snd_1501_ = lean_ctor_get(v_val_1500_, 1);
lean_inc(v_snd_1501_);
v_fst_1502_ = lean_ctor_get(v_val_1500_, 0);
lean_inc(v_fst_1502_);
lean_dec(v_val_1500_);
v_fst_1503_ = lean_ctor_get(v_snd_1501_, 0);
lean_inc(v_fst_1503_);
v_snd_1504_ = lean_ctor_get(v_snd_1501_, 1);
lean_inc(v_snd_1504_);
lean_dec(v_snd_1501_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 2, v_snd_1504_);
lean_ctor_set(v___x_1498_, 1, v_fst_1502_);
lean_ctor_set(v___x_1498_, 0, v_fst_1503_);
v___x_1506_ = v___x_1498_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_fst_1503_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_fst_1502_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_snd_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_combo(lean_object* v_a_1512_, lean_object* v_f_1513_, lean_object* v_b_1514_, lean_object* v_g_1515_){
_start:
{
lean_object* v_coeffs_1516_; lean_object* v_constraint_1517_; lean_object* v_justification_1518_; lean_object* v_coeffs_1519_; lean_object* v_constraint_1520_; lean_object* v_justification_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1531_; 
v_coeffs_1516_ = lean_ctor_get(v_f_1513_, 0);
lean_inc(v_coeffs_1516_);
v_constraint_1517_ = lean_ctor_get(v_f_1513_, 1);
lean_inc_ref(v_constraint_1517_);
v_justification_1518_ = lean_ctor_get(v_f_1513_, 2);
lean_inc_ref(v_justification_1518_);
lean_dec_ref(v_f_1513_);
v_coeffs_1519_ = lean_ctor_get(v_g_1515_, 0);
v_constraint_1520_ = lean_ctor_get(v_g_1515_, 1);
v_justification_1521_ = lean_ctor_get(v_g_1515_, 2);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_g_1515_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1523_ = v_g_1515_;
v_isShared_1524_ = v_isSharedCheck_1531_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_justification_1521_);
lean_inc(v_constraint_1520_);
lean_inc(v_coeffs_1519_);
lean_dec(v_g_1515_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1531_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
lean_inc(v_coeffs_1519_);
lean_inc(v_b_1514_);
lean_inc(v_coeffs_1516_);
lean_inc(v_a_1512_);
v___x_1525_ = l_Lean_Omega_IntList_combo(v_a_1512_, v_coeffs_1516_, v_b_1514_, v_coeffs_1519_);
lean_inc_ref(v_constraint_1520_);
lean_inc(v_b_1514_);
lean_inc_ref(v_constraint_1517_);
lean_inc(v_a_1512_);
v___x_1526_ = l_Lean_Omega_Constraint_combo(v_a_1512_, v_constraint_1517_, v_b_1514_, v_constraint_1520_);
v___x_1527_ = lean_alloc_ctor(3, 8, 0);
lean_ctor_set(v___x_1527_, 0, v_constraint_1517_);
lean_ctor_set(v___x_1527_, 1, v_constraint_1520_);
lean_ctor_set(v___x_1527_, 2, v_coeffs_1516_);
lean_ctor_set(v___x_1527_, 3, v_coeffs_1519_);
lean_ctor_set(v___x_1527_, 4, v_a_1512_);
lean_ctor_set(v___x_1527_, 5, v_justification_1518_);
lean_ctor_set(v___x_1527_, 6, v_b_1514_);
lean_ctor_set(v___x_1527_, 7, v_justification_1521_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 2, v___x_1527_);
lean_ctor_set(v___x_1523_, 1, v___x_1526_);
lean_ctor_set(v___x_1523_, 0, v___x_1525_);
v___x_1529_ = v___x_1523_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__10));
v___x_1558_ = l_Lean_mkAtom(v___x_1557_);
return v___x_1558_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11);
v___x_1560_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_1561_ = lean_array_push(v___x_1560_, v___x_1559_);
return v___x_1561_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1562_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12);
v___x_1563_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9));
v___x_1564_ = lean_box(2);
v___x_1565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v___x_1563_);
lean_ctor_set(v___x_1565_, 2, v___x_1562_);
return v___x_1565_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1566_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13);
v___x_1567_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_1568_ = lean_array_push(v___x_1567_, v___x_1566_);
return v___x_1568_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1569_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14);
v___x_1570_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7));
v___x_1571_ = lean_box(2);
v___x_1572_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v___x_1570_);
lean_ctor_set(v___x_1572_, 2, v___x_1569_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15);
v___x_1574_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_1575_ = lean_array_push(v___x_1574_, v___x_1573_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1576_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16);
v___x_1577_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5));
v___x_1578_ = lean_box(2);
v___x_1579_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v___x_1577_);
lean_ctor_set(v___x_1579_, 2, v___x_1576_);
return v___x_1579_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17);
v___x_1581_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_1582_ = lean_array_push(v___x_1581_, v___x_1580_);
return v___x_1582_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1583_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18);
v___x_1584_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2));
v___x_1585_ = lean_box(2);
v___x_1586_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
lean_ctor_set(v___x_1586_, 1, v___x_1584_);
lean_ctor_set(v___x_1586_, 2, v___x_1583_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam(void){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19);
return v___x_1587_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_isEmpty(lean_object* v_p_1588_){
_start:
{
lean_object* v_constraints_1589_; lean_object* v_size_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v_constraints_1589_ = lean_ctor_get(v_p_1588_, 2);
v_size_1590_ = lean_ctor_get(v_constraints_1589_, 0);
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = lean_nat_dec_eq(v_size_1590_, v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_isEmpty___boxed(lean_object* v_p_1593_){
_start:
{
uint8_t v_res_1594_; lean_object* v_r_1595_; 
v_res_1594_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_1593_);
lean_dec_ref(v_p_1593_);
v_r_1595_ = lean_box(v_res_1594_);
return v_r_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object* v_x_1597_){
_start:
{
lean_object* v_snd_1598_; lean_object* v_fst_1599_; lean_object* v_constraint_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_snd_1598_ = lean_ctor_get(v_x_1597_, 1);
lean_inc(v_snd_1598_);
v_fst_1599_ = lean_ctor_get(v_x_1597_, 0);
lean_inc(v_fst_1599_);
lean_dec_ref(v_x_1597_);
v_constraint_1600_ = lean_ctor_get(v_snd_1598_, 1);
lean_inc_ref(v_constraint_1600_);
lean_dec(v_snd_1598_);
v___x_1601_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0___closed__0));
v___x_1602_ = l_List_toString___redArg(v___x_1601_, v_fst_1599_);
v___x_1603_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1604_ = lean_string_append(v___x_1602_, v___x_1603_);
v___x_1605_ = l_Lean_Omega_Constraint_instToString___private__1(v_constraint_1600_);
lean_dec_ref(v_constraint_1600_);
v___x_1606_ = lean_string_append(v___x_1604_, v___x_1605_);
lean_dec_ref(v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object* v_a_1607_, lean_object* v_b_1608_, lean_object* v_d_1609_){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v_a_1607_);
lean_ctor_set(v___x_1610_, 1, v_b_1608_);
v___x_1611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v_d_1609_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2(lean_object* v___x_1612_, lean_object* v___f_1613_, lean_object* v_l_1614_, lean_object* v_acc_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1612_, v___f_1613_, v_acc_1615_, v_l_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3(lean_object* v___f_1638_, lean_object* v___f_1639_, lean_object* v_p_1640_){
_start:
{
uint8_t v_possible_1641_; 
v_possible_1641_ = lean_ctor_get_uint8(v_p_1640_, sizeof(void*)*7);
if (v_possible_1641_ == 0)
{
lean_object* v___x_1642_; 
lean_dec_ref(v_p_1640_);
lean_dec_ref(v___f_1639_);
lean_dec_ref(v___f_1638_);
v___x_1642_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
return v___x_1642_;
}
else
{
lean_object* v_constraints_1643_; uint8_t v___x_1644_; 
v_constraints_1643_ = lean_ctor_get(v_p_1640_, 2);
lean_inc_ref(v_constraints_1643_);
v___x_1644_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_1640_);
lean_dec_ref(v_p_1640_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v_buckets_1646_; lean_object* v___x_1647_; lean_object* v___y_1649_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1645_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10));
v_buckets_1646_ = lean_ctor_get(v_constraints_1643_, 1);
lean_inc_ref(v_buckets_1646_);
lean_dec_ref(v_constraints_1643_);
v___x_1647_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_array_get_size(v_buckets_1646_);
v___x_1655_ = lean_unsigned_to_nat(0u);
v___x_1656_ = lean_nat_dec_lt(v___x_1655_, v___x_1654_);
if (v___x_1656_ == 0)
{
lean_dec_ref(v_buckets_1646_);
lean_dec_ref(v___f_1639_);
v___y_1649_ = v___x_1653_;
goto v___jp_1648_;
}
else
{
lean_object* v___f_1657_; size_t v___x_1658_; size_t v___x_1659_; lean_object* v___x_1660_; 
v___f_1657_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2), 4, 2);
lean_closure_set(v___f_1657_, 0, v___x_1645_);
lean_closure_set(v___f_1657_, 1, v___f_1639_);
v___x_1658_ = lean_usize_of_nat(v___x_1654_);
v___x_1659_ = ((size_t)0ULL);
v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1645_, v___f_1657_, v_buckets_1646_, v___x_1658_, v___x_1659_, v___x_1653_);
v___y_1649_ = v___x_1660_;
goto v___jp_1648_;
}
v___jp_1648_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1650_ = lean_box(0);
v___x_1651_ = l_List_mapTR_loop___redArg(v___f_1638_, v___y_1649_, v___x_1650_);
v___x_1652_ = l_String_intercalate(v___x_1647_, v___x_1651_);
return v___x_1652_;
}
}
else
{
lean_object* v___x_1661_; 
lean_dec_ref(v_constraints_1643_);
lean_dec_ref(v___f_1639_);
lean_dec_ref(v___f_1638_);
v___x_1661_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
return v___x_1661_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_box(0);
v___x_1675_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1));
v___x_1676_ = l_Lean_Expr_const___override(v___x_1675_, v___x_1674_);
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_box(0);
v___x_1683_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5));
v___x_1684_ = l_Lean_Expr_const___override(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = lean_box(0);
v___x_1692_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8));
v___x_1693_ = l_Lean_Expr_const___override(v___x_1692_, v___x_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse(lean_object* v_s_1694_, lean_object* v_x_1695_, lean_object* v_j_1696_, lean_object* v_assumptions_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, uint8_t v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v___x_1708_; 
lean_inc(v_a_1706_);
lean_inc_ref(v_a_1705_);
lean_inc(v_a_1704_);
lean_inc_ref(v_a_1703_);
v___x_1708_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_1699_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1710_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref(v___x_1708_);
lean_inc(v_a_1706_);
lean_inc_ref(v_a_1705_);
lean_inc(v_a_1704_);
lean_inc_ref(v_a_1703_);
lean_inc(v_a_1709_);
v___x_1710_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1695_, v_a_1709_, v_assumptions_1697_, v_j_1696_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1712_; lean_object* v_lowerBound_1713_; lean_object* v_upperBound_1714_; lean_object* v_nil_1715_; lean_object* v_cons_1716_; lean_object* v___x_1717_; lean_object* v___y_1719_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___x_1742_; lean_object* v___y_1744_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref(v___x_1710_);
v___x_1712_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_lowerBound_1713_ = lean_ctor_get(v_s_1694_, 0);
v_upperBound_1714_ = lean_ctor_get(v_s_1694_, 1);
v_nil_1715_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1716_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1717_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1715_, v_cons_1716_, v_x_1695_);
v___x_1742_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
if (lean_obj_tag(v_lowerBound_1713_) == 0)
{
lean_object* v___x_1760_; 
v___x_1760_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1744_ = v___x_1760_;
goto v___jp_1743_;
}
else
{
lean_object* v_val_1761_; lean_object* v___x_1762_; lean_object* v___y_1764_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v_val_1761_ = lean_ctor_get(v_lowerBound_1713_, 0);
v___x_1762_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1766_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1767_ = lean_int_dec_le(v___x_1766_, v_val_1761_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1768_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1769_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1770_ = lean_int_neg(v_val_1761_);
v___x_1771_ = l_Int_toNat(v___x_1770_);
lean_dec(v___x_1770_);
v___x_1772_ = l_Lean_instToExprInt_mkNat(v___x_1771_);
v___x_1773_ = l_Lean_mkApp3(v___x_1768_, v___x_1712_, v___x_1769_, v___x_1772_);
v___y_1764_ = v___x_1773_;
goto v___jp_1763_;
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = l_Int_toNat(v_val_1761_);
v___x_1775_ = l_Lean_instToExprInt_mkNat(v___x_1774_);
v___y_1764_ = v___x_1775_;
goto v___jp_1763_;
}
v___jp_1763_:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_mkAppB(v___x_1762_, v___x_1712_, v___y_1764_);
v___y_1744_ = v___x_1765_;
goto v___jp_1743_;
}
}
v___jp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1720_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2);
lean_inc_ref(v___y_1719_);
v___x_1721_ = l_Lean_Expr_app___override(v___x_1720_, v___y_1719_);
v___x_1722_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6);
lean_inc(v_a_1706_);
lean_inc_ref(v_a_1705_);
lean_inc(v_a_1704_);
lean_inc_ref(v_a_1703_);
v___x_1723_ = l_Lean_Meta_mkEq(v___x_1721_, v___x_1722_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref(v___x_1723_);
v___x_1725_ = l_Lean_Meta_mkDecideProof(v_a_1724_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1735_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1728_ = v___x_1725_;
v_isShared_1729_ = v_isSharedCheck_1735_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1735_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1730_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9);
v___x_1731_ = l_Lean_mkApp5(v___x_1730_, v___y_1719_, v_a_1726_, v___x_1717_, v_a_1709_, v_a_1711_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1731_);
v___x_1733_ = v___x_1728_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
else
{
lean_dec_ref(v___y_1719_);
lean_dec_ref(v___x_1717_);
lean_dec(v_a_1711_);
lean_dec(v_a_1709_);
return v___x_1725_;
}
}
else
{
lean_dec_ref(v___y_1719_);
lean_dec_ref(v___x_1717_);
lean_dec(v_a_1711_);
lean_dec(v_a_1709_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
return v___x_1723_;
}
}
v___jp_1736_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = l_Lean_mkAppB(v___y_1738_, v___x_1712_, v___y_1739_);
v___x_1741_ = l_Lean_Expr_app___override(v___y_1737_, v___x_1740_);
v___y_1719_ = v___x_1741_;
goto v___jp_1718_;
}
v___jp_1743_:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Expr_app___override(v___x_1742_, v___y_1744_);
if (lean_obj_tag(v_upperBound_1714_) == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1747_ = l_Lean_Expr_app___override(v___x_1745_, v___x_1746_);
v___y_1719_ = v___x_1747_;
goto v___jp_1718_;
}
else
{
lean_object* v_val_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v_val_1748_ = lean_ctor_get(v_upperBound_1714_, 0);
v___x_1749_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1750_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1751_ = lean_int_dec_le(v___x_1750_, v_val_1748_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1752_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1753_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1754_ = lean_int_neg(v_val_1748_);
v___x_1755_ = l_Int_toNat(v___x_1754_);
lean_dec(v___x_1754_);
v___x_1756_ = l_Lean_instToExprInt_mkNat(v___x_1755_);
v___x_1757_ = l_Lean_mkApp3(v___x_1752_, v___x_1712_, v___x_1753_, v___x_1756_);
v___y_1737_ = v___x_1745_;
v___y_1738_ = v___x_1749_;
v___y_1739_ = v___x_1757_;
goto v___jp_1736_;
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = l_Int_toNat(v_val_1748_);
v___x_1759_ = l_Lean_instToExprInt_mkNat(v___x_1758_);
v___y_1737_ = v___x_1745_;
v___y_1738_ = v___x_1749_;
v___y_1739_ = v___x_1759_;
goto v___jp_1736_;
}
}
}
}
else
{
lean_dec(v_a_1709_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
return v___x_1710_;
}
}
else
{
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec(v_a_1698_);
lean_dec_ref(v_j_1696_);
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed(lean_object* v_s_1776_, lean_object* v_x_1777_, lean_object* v_j_1778_, lean_object* v_assumptions_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
uint8_t v_a_7581__boxed_1790_; lean_object* v_res_1791_; 
v_a_7581__boxed_1790_ = lean_unbox(v_a_1783_);
v_res_1791_ = l_Lean_Elab_Tactic_Omega_Problem_proveFalse(v_s_1776_, v_x_1777_, v_j_1778_, v_assumptions_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_7581__boxed_1790_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
lean_dec_ref(v_assumptions_1779_);
lean_dec(v_x_1777_);
lean_dec_ref(v_s_1776_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0(lean_object* v_constraint_1792_, lean_object* v_coeffs_1793_, lean_object* v_justification_1794_, lean_object* v_x_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_1792_, v_coeffs_1793_, v_justification_1794_);
return v___x_1796_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(lean_object* v_a_1797_, lean_object* v_x_1798_){
_start:
{
if (lean_obj_tag(v_x_1798_) == 0)
{
uint8_t v___x_1799_; 
v___x_1799_ = 0;
return v___x_1799_;
}
else
{
lean_object* v_key_1800_; lean_object* v_tail_1801_; uint8_t v___x_1802_; 
v_key_1800_ = lean_ctor_get(v_x_1798_, 0);
v_tail_1801_ = lean_ctor_get(v_x_1798_, 2);
v___x_1802_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_1800_, v_a_1797_);
if (v___x_1802_ == 0)
{
v_x_1798_ = v_tail_1801_;
goto _start;
}
else
{
return v___x_1802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg___boxed(lean_object* v_a_1804_, lean_object* v_x_1805_){
_start:
{
uint8_t v_res_1806_; lean_object* v_r_1807_; 
v_res_1806_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_1804_, v_x_1805_);
lean_dec(v_x_1805_);
lean_dec(v_a_1804_);
v_r_1807_ = lean_box(v_res_1806_);
return v_r_1807_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(uint64_t v_x_1808_, lean_object* v_x_1809_){
_start:
{
if (lean_obj_tag(v_x_1809_) == 0)
{
return v_x_1808_;
}
else
{
lean_object* v_head_1810_; lean_object* v_tail_1811_; lean_object* v_intZero_1812_; uint8_t v_isNeg_1813_; 
v_head_1810_ = lean_ctor_get(v_x_1809_, 0);
v_tail_1811_ = lean_ctor_get(v_x_1809_, 1);
v_intZero_1812_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1813_ = lean_int_dec_lt(v_head_1810_, v_intZero_1812_);
if (v_isNeg_1813_ == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint64_t v___x_1817_; uint64_t v___x_1818_; 
v_a_1814_ = lean_nat_abs(v_head_1810_);
v___x_1815_ = lean_unsigned_to_nat(2u);
v___x_1816_ = lean_nat_mul(v___x_1815_, v_a_1814_);
lean_dec(v_a_1814_);
v___x_1817_ = lean_uint64_of_nat(v___x_1816_);
lean_dec(v___x_1816_);
v___x_1818_ = lean_uint64_mix_hash(v_x_1808_, v___x_1817_);
v_x_1808_ = v___x_1818_;
v_x_1809_ = v_tail_1811_;
goto _start;
}
else
{
lean_object* v_abs_1820_; lean_object* v_one_1821_; lean_object* v_a_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; uint64_t v___x_1826_; uint64_t v___x_1827_; 
v_abs_1820_ = lean_nat_abs(v_head_1810_);
v_one_1821_ = lean_unsigned_to_nat(1u);
v_a_1822_ = lean_nat_sub(v_abs_1820_, v_one_1821_);
lean_dec(v_abs_1820_);
v___x_1823_ = lean_unsigned_to_nat(2u);
v___x_1824_ = lean_nat_mul(v___x_1823_, v_a_1822_);
lean_dec(v_a_1822_);
v___x_1825_ = lean_nat_add(v___x_1824_, v_one_1821_);
lean_dec(v___x_1824_);
v___x_1826_ = lean_uint64_of_nat(v___x_1825_);
lean_dec(v___x_1825_);
v___x_1827_ = lean_uint64_mix_hash(v_x_1808_, v___x_1826_);
v_x_1808_ = v___x_1827_;
v_x_1809_ = v_tail_1811_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0___boxed(lean_object* v_x_1829_, lean_object* v_x_1830_){
_start:
{
uint64_t v_x_980__boxed_1831_; uint64_t v_res_1832_; lean_object* v_r_1833_; 
v_x_980__boxed_1831_ = lean_unbox_uint64(v_x_1829_);
lean_dec_ref(v_x_1829_);
v_res_1832_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v_x_980__boxed_1831_, v_x_1830_);
lean_dec(v_x_1830_);
v_r_1833_ = lean_box_uint64(v_res_1832_);
return v_r_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_1834_, lean_object* v_x_1835_){
_start:
{
if (lean_obj_tag(v_x_1835_) == 0)
{
return v_x_1834_;
}
else
{
lean_object* v_key_1836_; lean_object* v_value_1837_; lean_object* v_tail_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1862_; 
v_key_1836_ = lean_ctor_get(v_x_1835_, 0);
v_value_1837_ = lean_ctor_get(v_x_1835_, 1);
v_tail_1838_ = lean_ctor_get(v_x_1835_, 2);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_x_1835_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1840_ = v_x_1835_;
v_isShared_1841_ = v_isSharedCheck_1862_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_tail_1838_);
lean_inc(v_value_1837_);
lean_inc(v_key_1836_);
lean_dec(v_x_1835_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1862_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; uint64_t v___x_1843_; uint64_t v___x_1844_; uint64_t v___x_1845_; uint64_t v___x_1846_; uint64_t v_fold_1847_; uint64_t v___x_1848_; uint64_t v___x_1849_; uint64_t v___x_1850_; size_t v___x_1851_; size_t v___x_1852_; size_t v___x_1853_; size_t v___x_1854_; size_t v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1842_ = lean_array_get_size(v_x_1834_);
v___x_1843_ = 7ULL;
v___x_1844_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_1843_, v_key_1836_);
v___x_1845_ = 32ULL;
v___x_1846_ = lean_uint64_shift_right(v___x_1844_, v___x_1845_);
v_fold_1847_ = lean_uint64_xor(v___x_1844_, v___x_1846_);
v___x_1848_ = 16ULL;
v___x_1849_ = lean_uint64_shift_right(v_fold_1847_, v___x_1848_);
v___x_1850_ = lean_uint64_xor(v_fold_1847_, v___x_1849_);
v___x_1851_ = lean_uint64_to_usize(v___x_1850_);
v___x_1852_ = lean_usize_of_nat(v___x_1842_);
v___x_1853_ = ((size_t)1ULL);
v___x_1854_ = lean_usize_sub(v___x_1852_, v___x_1853_);
v___x_1855_ = lean_usize_land(v___x_1851_, v___x_1854_);
v___x_1856_ = lean_array_uget_borrowed(v_x_1834_, v___x_1855_);
lean_inc(v___x_1856_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 2, v___x_1856_);
v___x_1858_ = v___x_1840_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_key_1836_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_value_1837_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_array_uset(v_x_1834_, v___x_1855_, v___x_1858_);
v_x_1834_ = v___x_1859_;
v_x_1835_ = v_tail_1838_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(lean_object* v_i_1863_, lean_object* v_source_1864_, lean_object* v_target_1865_){
_start:
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = lean_array_get_size(v_source_1864_);
v___x_1867_ = lean_nat_dec_lt(v_i_1863_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_dec_ref(v_source_1864_);
lean_dec(v_i_1863_);
return v_target_1865_;
}
else
{
lean_object* v_es_1868_; lean_object* v___x_1869_; lean_object* v_source_1870_; lean_object* v_target_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_es_1868_ = lean_array_fget(v_source_1864_, v_i_1863_);
v___x_1869_ = lean_box(0);
v_source_1870_ = lean_array_fset(v_source_1864_, v_i_1863_, v___x_1869_);
v_target_1871_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_target_1865_, v_es_1868_);
v___x_1872_ = lean_unsigned_to_nat(1u);
v___x_1873_ = lean_nat_add(v_i_1863_, v___x_1872_);
lean_dec(v_i_1863_);
v_i_1863_ = v___x_1873_;
v_source_1864_ = v_source_1870_;
v_target_1865_ = v_target_1871_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(lean_object* v_data_1875_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v_nbuckets_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1876_ = lean_array_get_size(v_data_1875_);
v___x_1877_ = lean_unsigned_to_nat(2u);
v_nbuckets_1878_ = lean_nat_mul(v___x_1876_, v___x_1877_);
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = lean_box(0);
v___x_1881_ = lean_mk_array(v_nbuckets_1878_, v___x_1880_);
v___x_1882_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v___x_1879_, v_data_1875_, v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(lean_object* v_m_1883_, lean_object* v_a_1884_, lean_object* v_b_1885_){
_start:
{
lean_object* v_size_1886_; lean_object* v_buckets_1887_; lean_object* v___x_1888_; uint64_t v___x_1889_; uint64_t v___x_1890_; uint64_t v___x_1891_; uint64_t v___x_1892_; uint64_t v_fold_1893_; uint64_t v___x_1894_; uint64_t v___x_1895_; uint64_t v___x_1896_; size_t v___x_1897_; size_t v___x_1898_; size_t v___x_1899_; size_t v___x_1900_; size_t v___x_1901_; lean_object* v_bkt_1902_; uint8_t v___x_1903_; 
v_size_1886_ = lean_ctor_get(v_m_1883_, 0);
v_buckets_1887_ = lean_ctor_get(v_m_1883_, 1);
v___x_1888_ = lean_array_get_size(v_buckets_1887_);
v___x_1889_ = 7ULL;
v___x_1890_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_1889_, v_a_1884_);
v___x_1891_ = 32ULL;
v___x_1892_ = lean_uint64_shift_right(v___x_1890_, v___x_1891_);
v_fold_1893_ = lean_uint64_xor(v___x_1890_, v___x_1892_);
v___x_1894_ = 16ULL;
v___x_1895_ = lean_uint64_shift_right(v_fold_1893_, v___x_1894_);
v___x_1896_ = lean_uint64_xor(v_fold_1893_, v___x_1895_);
v___x_1897_ = lean_uint64_to_usize(v___x_1896_);
v___x_1898_ = lean_usize_of_nat(v___x_1888_);
v___x_1899_ = ((size_t)1ULL);
v___x_1900_ = lean_usize_sub(v___x_1898_, v___x_1899_);
v___x_1901_ = lean_usize_land(v___x_1897_, v___x_1900_);
v_bkt_1902_ = lean_array_uget_borrowed(v_buckets_1887_, v___x_1901_);
v___x_1903_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_1884_, v_bkt_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1924_; 
lean_inc_ref(v_buckets_1887_);
lean_inc(v_size_1886_);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_m_1883_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; lean_object* v_unused_1926_; 
v_unused_1925_ = lean_ctor_get(v_m_1883_, 1);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_m_1883_, 0);
lean_dec(v_unused_1926_);
v___x_1905_ = v_m_1883_;
v_isShared_1906_ = v_isSharedCheck_1924_;
goto v_resetjp_1904_;
}
else
{
lean_dec(v_m_1883_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1924_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v_size_x27_1908_; lean_object* v___x_1909_; lean_object* v_buckets_x27_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1907_ = lean_unsigned_to_nat(1u);
v_size_x27_1908_ = lean_nat_add(v_size_1886_, v___x_1907_);
lean_dec(v_size_1886_);
lean_inc(v_bkt_1902_);
v___x_1909_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1909_, 0, v_a_1884_);
lean_ctor_set(v___x_1909_, 1, v_b_1885_);
lean_ctor_set(v___x_1909_, 2, v_bkt_1902_);
v_buckets_x27_1910_ = lean_array_uset(v_buckets_1887_, v___x_1901_, v___x_1909_);
v___x_1911_ = lean_unsigned_to_nat(4u);
v___x_1912_ = lean_nat_mul(v_size_x27_1908_, v___x_1911_);
v___x_1913_ = lean_unsigned_to_nat(3u);
v___x_1914_ = lean_nat_div(v___x_1912_, v___x_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_array_get_size(v_buckets_x27_1910_);
v___x_1916_ = lean_nat_dec_le(v___x_1914_, v___x_1915_);
lean_dec(v___x_1914_);
if (v___x_1916_ == 0)
{
lean_object* v_val_1917_; lean_object* v___x_1919_; 
v_val_1917_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_1910_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 1, v_val_1917_);
lean_ctor_set(v___x_1905_, 0, v_size_x27_1908_);
v___x_1919_ = v___x_1905_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_size_x27_1908_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_val_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
else
{
lean_object* v___x_1922_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 1, v_buckets_x27_1910_);
lean_ctor_set(v___x_1905_, 0, v_size_x27_1908_);
v___x_1922_ = v___x_1905_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_size_x27_1908_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_buckets_x27_1910_);
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
else
{
lean_dec(v_b_1885_);
lean_dec(v_a_1884_);
return v_m_1883_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(lean_object* v_a_1927_, lean_object* v_b_1928_, lean_object* v_x_1929_){
_start:
{
if (lean_obj_tag(v_x_1929_) == 0)
{
lean_dec(v_b_1928_);
lean_dec(v_a_1927_);
return v_x_1929_;
}
else
{
lean_object* v_key_1930_; lean_object* v_value_1931_; lean_object* v_tail_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1944_; 
v_key_1930_ = lean_ctor_get(v_x_1929_, 0);
v_value_1931_ = lean_ctor_get(v_x_1929_, 1);
v_tail_1932_ = lean_ctor_get(v_x_1929_, 2);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_x_1929_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1934_ = v_x_1929_;
v_isShared_1935_ = v_isSharedCheck_1944_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_tail_1932_);
lean_inc(v_value_1931_);
lean_inc(v_key_1930_);
lean_dec(v_x_1929_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1944_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
uint8_t v___x_1936_; 
v___x_1936_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_1930_, v_a_1927_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1937_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_1927_, v_b_1928_, v_tail_1932_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 2, v___x_1937_);
v___x_1939_ = v___x_1934_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_key_1930_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_value_1931_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
else
{
lean_object* v___x_1942_; 
lean_dec(v_value_1931_);
lean_dec(v_key_1930_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 1, v_b_1928_);
lean_ctor_set(v___x_1934_, 0, v_a_1927_);
v___x_1942_ = v___x_1934_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1927_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_b_1928_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v_tail_1932_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(lean_object* v_m_1945_, lean_object* v_a_1946_, lean_object* v_b_1947_){
_start:
{
lean_object* v_size_1948_; lean_object* v_buckets_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1993_; 
v_size_1948_ = lean_ctor_get(v_m_1945_, 0);
v_buckets_1949_ = lean_ctor_get(v_m_1945_, 1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_m_1945_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1951_ = v_m_1945_;
v_isShared_1952_ = v_isSharedCheck_1993_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_buckets_1949_);
lean_inc(v_size_1948_);
lean_dec(v_m_1945_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1993_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; uint64_t v___x_1954_; uint64_t v___x_1955_; uint64_t v___x_1956_; uint64_t v___x_1957_; uint64_t v_fold_1958_; uint64_t v___x_1959_; uint64_t v___x_1960_; uint64_t v___x_1961_; size_t v___x_1962_; size_t v___x_1963_; size_t v___x_1964_; size_t v___x_1965_; size_t v___x_1966_; lean_object* v_bkt_1967_; uint8_t v___x_1968_; 
v___x_1953_ = lean_array_get_size(v_buckets_1949_);
v___x_1954_ = 7ULL;
v___x_1955_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_1954_, v_a_1946_);
v___x_1956_ = 32ULL;
v___x_1957_ = lean_uint64_shift_right(v___x_1955_, v___x_1956_);
v_fold_1958_ = lean_uint64_xor(v___x_1955_, v___x_1957_);
v___x_1959_ = 16ULL;
v___x_1960_ = lean_uint64_shift_right(v_fold_1958_, v___x_1959_);
v___x_1961_ = lean_uint64_xor(v_fold_1958_, v___x_1960_);
v___x_1962_ = lean_uint64_to_usize(v___x_1961_);
v___x_1963_ = lean_usize_of_nat(v___x_1953_);
v___x_1964_ = ((size_t)1ULL);
v___x_1965_ = lean_usize_sub(v___x_1963_, v___x_1964_);
v___x_1966_ = lean_usize_land(v___x_1962_, v___x_1965_);
v_bkt_1967_ = lean_array_uget_borrowed(v_buckets_1949_, v___x_1966_);
v___x_1968_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_1946_, v_bkt_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v_size_x27_1970_; lean_object* v___x_1971_; lean_object* v_buckets_x27_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1969_ = lean_unsigned_to_nat(1u);
v_size_x27_1970_ = lean_nat_add(v_size_1948_, v___x_1969_);
lean_dec(v_size_1948_);
lean_inc(v_bkt_1967_);
v___x_1971_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1971_, 0, v_a_1946_);
lean_ctor_set(v___x_1971_, 1, v_b_1947_);
lean_ctor_set(v___x_1971_, 2, v_bkt_1967_);
v_buckets_x27_1972_ = lean_array_uset(v_buckets_1949_, v___x_1966_, v___x_1971_);
v___x_1973_ = lean_unsigned_to_nat(4u);
v___x_1974_ = lean_nat_mul(v_size_x27_1970_, v___x_1973_);
v___x_1975_ = lean_unsigned_to_nat(3u);
v___x_1976_ = lean_nat_div(v___x_1974_, v___x_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_array_get_size(v_buckets_x27_1972_);
v___x_1978_ = lean_nat_dec_le(v___x_1976_, v___x_1977_);
lean_dec(v___x_1976_);
if (v___x_1978_ == 0)
{
lean_object* v_val_1979_; lean_object* v___x_1981_; 
v_val_1979_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_1972_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 1, v_val_1979_);
lean_ctor_set(v___x_1951_, 0, v_size_x27_1970_);
v___x_1981_ = v___x_1951_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_size_x27_1970_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_val_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
else
{
lean_object* v___x_1984_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 1, v_buckets_x27_1972_);
lean_ctor_set(v___x_1951_, 0, v_size_x27_1970_);
v___x_1984_ = v___x_1951_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_size_x27_1970_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_buckets_x27_1972_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
else
{
lean_object* v___x_1986_; lean_object* v_buckets_x27_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
lean_inc(v_bkt_1967_);
v___x_1986_ = lean_box(0);
v_buckets_x27_1987_ = lean_array_uset(v_buckets_1949_, v___x_1966_, v___x_1986_);
v___x_1988_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_1946_, v_b_1947_, v_bkt_1967_);
v___x_1989_ = lean_array_uset(v_buckets_x27_1987_, v___x_1966_, v___x_1988_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 1, v___x_1989_);
v___x_1991_ = v___x_1951_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_size_1948_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(lean_object* v_p_1994_, lean_object* v_x_1995_){
_start:
{
lean_object* v_coeffs_1996_; lean_object* v_constraint_1997_; lean_object* v_justification_1998_; uint8_t v___x_1999_; 
v_coeffs_1996_ = lean_ctor_get(v_x_1995_, 0);
lean_inc(v_coeffs_1996_);
v_constraint_1997_ = lean_ctor_get(v_x_1995_, 1);
lean_inc_ref(v_constraint_1997_);
v_justification_1998_ = lean_ctor_get(v_x_1995_, 2);
v___x_1999_ = l_Lean_Omega_Constraint_isImpossible(v_constraint_1997_);
if (v___x_1999_ == 0)
{
lean_object* v_assumptions_2000_; lean_object* v_numVars_2001_; lean_object* v_constraints_2002_; lean_object* v_equalities_2003_; lean_object* v_eliminations_2004_; uint8_t v_possible_2005_; lean_object* v_proveFalse_x3f_2006_; lean_object* v_explanation_x3f_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2025_; 
v_assumptions_2000_ = lean_ctor_get(v_p_1994_, 0);
v_numVars_2001_ = lean_ctor_get(v_p_1994_, 1);
v_constraints_2002_ = lean_ctor_get(v_p_1994_, 2);
v_equalities_2003_ = lean_ctor_get(v_p_1994_, 3);
v_eliminations_2004_ = lean_ctor_get(v_p_1994_, 4);
v_possible_2005_ = lean_ctor_get_uint8(v_p_1994_, sizeof(void*)*7);
v_proveFalse_x3f_2006_ = lean_ctor_get(v_p_1994_, 5);
v_explanation_x3f_2007_ = lean_ctor_get(v_p_1994_, 6);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_p_1994_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2009_ = v_p_1994_;
v_isShared_2010_ = v_isSharedCheck_2025_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_explanation_x3f_2007_);
lean_inc(v_proveFalse_x3f_2006_);
lean_inc(v_eliminations_2004_);
lean_inc(v_equalities_2003_);
lean_inc(v_constraints_2002_);
lean_inc(v_numVars_2001_);
lean_inc(v_assumptions_2000_);
lean_dec(v_p_1994_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2025_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___y_2012_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = l_List_lengthTR___redArg(v_coeffs_1996_);
v___x_2024_ = lean_nat_dec_le(v_numVars_2001_, v___x_2023_);
if (v___x_2024_ == 0)
{
lean_dec(v___x_2023_);
v___y_2012_ = v_numVars_2001_;
goto v___jp_2011_;
}
else
{
lean_dec(v_numVars_2001_);
v___y_2012_ = v___x_2023_;
goto v___jp_2011_;
}
v___jp_2011_:
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
lean_inc(v_coeffs_1996_);
v___x_2013_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_constraints_2002_, v_coeffs_1996_, v_x_1995_);
v___x_2014_ = l_Lean_Omega_Constraint_isExact(v_constraint_1997_);
lean_dec_ref(v_constraint_1997_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2016_; 
lean_dec(v_coeffs_1996_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 2, v___x_2013_);
lean_ctor_set(v___x_2009_, 1, v___y_2012_);
v___x_2016_ = v___x_2009_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_assumptions_2000_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v___y_2012_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_equalities_2003_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v_eliminations_2004_);
lean_ctor_set(v_reuseFailAlloc_2017_, 5, v_proveFalse_x3f_2006_);
lean_ctor_set(v_reuseFailAlloc_2017_, 6, v_explanation_x3f_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*7, v_possible_2005_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2018_ = lean_box(0);
v___x_2019_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_equalities_2003_, v_coeffs_1996_, v___x_2018_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 3, v___x_2019_);
lean_ctor_set(v___x_2009_, 2, v___x_2013_);
lean_ctor_set(v___x_2009_, 1, v___y_2012_);
v___x_2021_ = v___x_2009_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_assumptions_2000_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___y_2012_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_eliminations_2004_);
lean_ctor_set(v_reuseFailAlloc_2022_, 5, v_proveFalse_x3f_2006_);
lean_ctor_set(v_reuseFailAlloc_2022_, 6, v_explanation_x3f_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*7, v_possible_2005_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
else
{
lean_object* v_assumptions_2026_; lean_object* v_numVars_2027_; lean_object* v_constraints_2028_; lean_object* v_equalities_2029_; lean_object* v_eliminations_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2042_; 
lean_inc_ref(v_justification_1998_);
lean_dec_ref(v_x_1995_);
v_assumptions_2026_ = lean_ctor_get(v_p_1994_, 0);
v_numVars_2027_ = lean_ctor_get(v_p_1994_, 1);
v_constraints_2028_ = lean_ctor_get(v_p_1994_, 2);
v_equalities_2029_ = lean_ctor_get(v_p_1994_, 3);
v_eliminations_2030_ = lean_ctor_get(v_p_1994_, 4);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_p_1994_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; lean_object* v_unused_2044_; 
v_unused_2043_ = lean_ctor_get(v_p_1994_, 6);
lean_dec(v_unused_2043_);
v_unused_2044_ = lean_ctor_get(v_p_1994_, 5);
lean_dec(v_unused_2044_);
v___x_2032_ = v_p_1994_;
v_isShared_2033_ = v_isSharedCheck_2042_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_eliminations_2030_);
lean_inc(v_equalities_2029_);
lean_inc(v_constraints_2028_);
lean_inc(v_numVars_2027_);
lean_inc(v_assumptions_2026_);
lean_dec(v_p_1994_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2042_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___f_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
lean_inc_ref(v_justification_1998_);
lean_inc(v_coeffs_1996_);
lean_inc_ref(v_constraint_1997_);
v___f_2034_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0), 4, 3);
lean_closure_set(v___f_2034_, 0, v_constraint_1997_);
lean_closure_set(v___f_2034_, 1, v_coeffs_1996_);
lean_closure_set(v___f_2034_, 2, v_justification_1998_);
v___x_2035_ = 0;
lean_inc_ref(v_assumptions_2026_);
v___x_2036_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed), 14, 4);
lean_closure_set(v___x_2036_, 0, v_constraint_1997_);
lean_closure_set(v___x_2036_, 1, v_coeffs_1996_);
lean_closure_set(v___x_2036_, 2, v_justification_1998_);
lean_closure_set(v___x_2036_, 3, v_assumptions_2026_);
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
v___x_2038_ = lean_mk_thunk(v___f_2034_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 6, v___x_2038_);
lean_ctor_set(v___x_2032_, 5, v___x_2037_);
v___x_2040_ = v___x_2032_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_assumptions_2026_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_numVars_2027_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_constraints_2028_);
lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_equalities_2029_);
lean_ctor_set(v_reuseFailAlloc_2041_, 4, v_eliminations_2030_);
lean_ctor_set(v_reuseFailAlloc_2041_, 5, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2041_, 6, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*7, v___x_2035_);
return v___x_2040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0(lean_object* v_00_u03b2_2045_, lean_object* v_m_2046_, lean_object* v_a_2047_, lean_object* v_b_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_m_2046_, v_a_2047_, v_b_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1(lean_object* v_00_u03b2_2050_, lean_object* v_m_2051_, lean_object* v_a_2052_, lean_object* v_b_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_m_2051_, v_a_2052_, v_b_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_object* v_00_u03b2_2055_, lean_object* v_a_2056_, lean_object* v_x_2057_){
_start:
{
uint8_t v___x_2058_; 
v___x_2058_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2056_, v_x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2059_, lean_object* v_a_2060_, lean_object* v_x_2061_){
_start:
{
uint8_t v_res_2062_; lean_object* v_r_2063_; 
v_res_2062_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(v_00_u03b2_2059_, v_a_2060_, v_x_2061_);
lean_dec(v_x_2061_);
lean_dec(v_a_2060_);
v_r_2063_ = lean_box(v_res_2062_);
return v_r_2063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2(lean_object* v_00_u03b2_2064_, lean_object* v_data_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_data_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3(lean_object* v_00_u03b2_2067_, lean_object* v_a_2068_, lean_object* v_b_2069_, lean_object* v_x_2070_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2068_, v_b_2069_, v_x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2072_, lean_object* v_i_2073_, lean_object* v_source_2074_, lean_object* v_target_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v_i_2073_, v_source_2074_, v_target_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2077_, lean_object* v_x_2078_, lean_object* v_x_2079_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_x_2078_, v_x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(lean_object* v_a_2081_, lean_object* v_x_2082_){
_start:
{
if (lean_obj_tag(v_x_2082_) == 0)
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_box(0);
return v___x_2083_;
}
else
{
lean_object* v_key_2084_; lean_object* v_value_2085_; lean_object* v_tail_2086_; uint8_t v___x_2087_; 
v_key_2084_ = lean_ctor_get(v_x_2082_, 0);
v_value_2085_ = lean_ctor_get(v_x_2082_, 1);
v_tail_2086_ = lean_ctor_get(v_x_2082_, 2);
v___x_2087_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2084_, v_a_2081_);
if (v___x_2087_ == 0)
{
v_x_2082_ = v_tail_2086_;
goto _start;
}
else
{
lean_object* v___x_2089_; 
lean_inc(v_value_2085_);
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_value_2085_);
return v___x_2089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg___boxed(lean_object* v_a_2090_, lean_object* v_x_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2090_, v_x_2091_);
lean_dec(v_x_2091_);
lean_dec(v_a_2090_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(lean_object* v_m_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_buckets_2095_; lean_object* v___x_2096_; uint64_t v___x_2097_; uint64_t v___x_2098_; uint64_t v___x_2099_; uint64_t v___x_2100_; uint64_t v_fold_2101_; uint64_t v___x_2102_; uint64_t v___x_2103_; uint64_t v___x_2104_; size_t v___x_2105_; size_t v___x_2106_; size_t v___x_2107_; size_t v___x_2108_; size_t v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_buckets_2095_ = lean_ctor_get(v_m_2093_, 1);
v___x_2096_ = lean_array_get_size(v_buckets_2095_);
v___x_2097_ = 7ULL;
v___x_2098_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2097_, v_a_2094_);
v___x_2099_ = 32ULL;
v___x_2100_ = lean_uint64_shift_right(v___x_2098_, v___x_2099_);
v_fold_2101_ = lean_uint64_xor(v___x_2098_, v___x_2100_);
v___x_2102_ = 16ULL;
v___x_2103_ = lean_uint64_shift_right(v_fold_2101_, v___x_2102_);
v___x_2104_ = lean_uint64_xor(v_fold_2101_, v___x_2103_);
v___x_2105_ = lean_uint64_to_usize(v___x_2104_);
v___x_2106_ = lean_usize_of_nat(v___x_2096_);
v___x_2107_ = ((size_t)1ULL);
v___x_2108_ = lean_usize_sub(v___x_2106_, v___x_2107_);
v___x_2109_ = lean_usize_land(v___x_2105_, v___x_2108_);
v___x_2110_ = lean_array_uget_borrowed(v_buckets_2095_, v___x_2109_);
v___x_2111_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2094_, v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg___boxed(lean_object* v_m_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2112_, v_a_2113_);
lean_dec(v_a_2113_);
lean_dec_ref(v_m_2112_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addConstraint(lean_object* v_p_2115_, lean_object* v_x_2116_){
_start:
{
uint8_t v_possible_2117_; 
v_possible_2117_ = lean_ctor_get_uint8(v_p_2115_, sizeof(void*)*7);
if (v_possible_2117_ == 0)
{
lean_dec_ref(v_x_2116_);
return v_p_2115_;
}
else
{
lean_object* v_coeffs_2118_; lean_object* v_constraint_2119_; lean_object* v_justification_2120_; lean_object* v_constraints_2121_; lean_object* v___x_2122_; 
v_coeffs_2118_ = lean_ctor_get(v_x_2116_, 0);
v_constraint_2119_ = lean_ctor_get(v_x_2116_, 1);
v_justification_2120_ = lean_ctor_get(v_x_2116_, 2);
v_constraints_2121_ = lean_ctor_get(v_p_2115_, 2);
v___x_2122_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2121_, v_coeffs_2118_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_lowerBound_2123_; 
v_lowerBound_2123_ = lean_ctor_get(v_constraint_2119_, 0);
if (lean_obj_tag(v_lowerBound_2123_) == 0)
{
lean_object* v_upperBound_2124_; 
v_upperBound_2124_ = lean_ctor_get(v_constraint_2119_, 1);
if (lean_obj_tag(v_upperBound_2124_) == 0)
{
lean_dec_ref(v_x_2116_);
return v_p_2115_;
}
else
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2115_, v_x_2116_);
return v___x_2125_;
}
}
else
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2115_, v_x_2116_);
return v___x_2126_;
}
}
else
{
lean_object* v_val_2127_; lean_object* v_coeffs_2128_; lean_object* v_constraint_2129_; lean_object* v_justification_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2145_; 
v_val_2127_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_val_2127_);
lean_dec_ref(v___x_2122_);
v_coeffs_2128_ = lean_ctor_get(v_val_2127_, 0);
v_constraint_2129_ = lean_ctor_get(v_val_2127_, 1);
v_justification_2130_ = lean_ctor_get(v_val_2127_, 2);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_val_2127_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2132_ = v_val_2127_;
v_isShared_2133_ = v_isSharedCheck_2145_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_justification_2130_);
lean_inc(v_constraint_2129_);
lean_inc(v_coeffs_2128_);
lean_dec(v_val_2127_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2145_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc(v_coeffs_2118_);
v___x_2135_ = l_instDecidableEqList___redArg(v___x_2134_, v_coeffs_2118_, v_coeffs_2128_);
if (v___x_2135_ == 0)
{
lean_del_object(v___x_2132_);
lean_dec_ref(v_justification_2130_);
lean_dec_ref(v_constraint_2129_);
lean_dec_ref(v_x_2116_);
return v_p_2115_;
}
else
{
lean_object* v_r_2136_; uint8_t v___x_2137_; 
lean_inc_ref(v_constraint_2129_);
lean_inc_ref(v_constraint_2119_);
v_r_2136_ = l_Lean_Omega_Constraint_combine(v_constraint_2119_, v_constraint_2129_);
lean_inc_ref(v_constraint_2129_);
lean_inc_ref(v_r_2136_);
v___x_2137_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2136_, v_constraint_2129_);
if (v___x_2137_ == 0)
{
uint8_t v___x_2138_; 
lean_inc_ref(v_constraint_2119_);
lean_inc_ref(v_r_2136_);
v___x_2138_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2136_, v_constraint_2119_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
lean_inc_ref(v_justification_2120_);
lean_inc_ref(v_constraint_2119_);
lean_inc(v_coeffs_2118_);
lean_dec_ref(v_x_2116_);
lean_inc(v_coeffs_2118_);
v___x_2139_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_2139_, 0, v_constraint_2119_);
lean_ctor_set(v___x_2139_, 1, v_constraint_2129_);
lean_ctor_set(v___x_2139_, 2, v_coeffs_2118_);
lean_ctor_set(v___x_2139_, 3, v_justification_2120_);
lean_ctor_set(v___x_2139_, 4, v_justification_2130_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 2, v___x_2139_);
lean_ctor_set(v___x_2132_, 1, v_r_2136_);
lean_ctor_set(v___x_2132_, 0, v_coeffs_2118_);
v___x_2141_ = v___x_2132_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_coeffs_2118_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_r_2136_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2115_, v___x_2141_);
return v___x_2142_;
}
}
else
{
lean_object* v___x_2144_; 
lean_dec_ref(v_r_2136_);
lean_del_object(v___x_2132_);
lean_dec_ref(v_justification_2130_);
lean_dec_ref(v_constraint_2129_);
v___x_2144_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2115_, v_x_2116_);
return v___x_2144_;
}
}
else
{
lean_dec_ref(v_r_2136_);
lean_del_object(v___x_2132_);
lean_dec_ref(v_justification_2130_);
lean_dec_ref(v_constraint_2129_);
lean_dec_ref(v_x_2116_);
return v_p_2115_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(lean_object* v_00_u03b2_2146_, lean_object* v_m_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2147_, v_a_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___boxed(lean_object* v_00_u03b2_2150_, lean_object* v_m_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(v_00_u03b2_2150_, v_m_2151_, v_a_2152_);
lean_dec(v_a_2152_);
lean_dec_ref(v_m_2151_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(lean_object* v_00_u03b2_2154_, lean_object* v_a_2155_, lean_object* v_x_2156_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2155_, v_x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2158_, lean_object* v_a_2159_, lean_object* v_x_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(v_00_u03b2_2158_, v_a_2159_, v_x_2160_);
lean_dec(v_x_2160_);
lean_dec(v_a_2159_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(lean_object* v_x_2162_, lean_object* v_x_2163_){
_start:
{
if (lean_obj_tag(v_x_2163_) == 0)
{
return v_x_2162_;
}
else
{
if (lean_obj_tag(v_x_2162_) == 0)
{
lean_object* v_key_2164_; lean_object* v_tail_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_key_2164_ = lean_ctor_get(v_x_2163_, 0);
lean_inc(v_key_2164_);
v_tail_2165_ = lean_ctor_get(v_x_2163_, 2);
lean_inc(v_tail_2165_);
lean_dec_ref(v_x_2163_);
lean_inc(v_key_2164_);
v___x_2166_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2164_);
v___x_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2167_, 0, v_key_2164_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
v_x_2162_ = v___x_2168_;
v_x_2163_ = v_tail_2165_;
goto _start;
}
else
{
lean_object* v_val_2170_; lean_object* v_key_2171_; lean_object* v_tail_2172_; lean_object* v_fst_2173_; lean_object* v_snd_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2202_; 
v_val_2170_ = lean_ctor_get(v_x_2162_, 0);
lean_inc(v_val_2170_);
v_key_2171_ = lean_ctor_get(v_x_2163_, 0);
lean_inc(v_key_2171_);
v_tail_2172_ = lean_ctor_get(v_x_2163_, 2);
lean_inc(v_tail_2172_);
lean_dec_ref(v_x_2163_);
v_fst_2173_ = lean_ctor_get(v_val_2170_, 0);
v_snd_2174_ = lean_ctor_get(v_val_2170_, 1);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_val_2170_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2176_ = v_val_2170_;
v_isShared_2177_ = v_isSharedCheck_2202_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_snd_2174_);
lean_inc(v_fst_2173_);
lean_dec(v_val_2170_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2202_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2178_ = lean_unsigned_to_nat(2u);
v___x_2179_ = lean_nat_dec_le(v___x_2178_, v_snd_2174_);
if (v___x_2179_ == 0)
{
lean_del_object(v___x_2176_);
lean_dec(v_snd_2174_);
lean_dec(v_fst_2173_);
lean_dec(v_key_2171_);
v_x_2163_ = v_tail_2172_;
goto _start;
}
else
{
lean_object* v_m_x27_2181_; uint8_t v___y_2183_; uint8_t v___x_2197_; 
lean_inc(v_key_2171_);
v_m_x27_2181_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2171_);
v___x_2197_ = lean_nat_dec_lt(v_m_x27_2181_, v_snd_2174_);
if (v___x_2197_ == 0)
{
uint8_t v___x_2198_; 
v___x_2198_ = lean_nat_dec_eq(v_m_x27_2181_, v_snd_2174_);
lean_dec(v_snd_2174_);
if (v___x_2198_ == 0)
{
lean_dec(v_fst_2173_);
v___y_2183_ = v___x_2198_;
goto v___jp_2182_;
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
lean_inc(v_key_2171_);
v___x_2199_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_key_2171_);
v___x_2200_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_fst_2173_);
v___x_2201_ = lean_nat_dec_lt(v___x_2199_, v___x_2200_);
lean_dec(v___x_2200_);
lean_dec(v___x_2199_);
v___y_2183_ = v___x_2201_;
goto v___jp_2182_;
}
}
else
{
lean_dec(v_snd_2174_);
lean_dec(v_fst_2173_);
v___y_2183_ = v___x_2197_;
goto v___jp_2182_;
}
v___jp_2182_:
{
if (v___y_2183_ == 0)
{
lean_dec(v_m_x27_2181_);
lean_del_object(v___x_2176_);
lean_dec(v_key_2171_);
v_x_2163_ = v_tail_2172_;
goto _start;
}
else
{
lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2195_; 
v_isSharedCheck_2195_ = !lean_is_exclusive(v_x_2162_);
if (v_isSharedCheck_2195_ == 0)
{
lean_object* v_unused_2196_; 
v_unused_2196_ = lean_ctor_get(v_x_2162_, 0);
lean_dec(v_unused_2196_);
v___x_2186_ = v_x_2162_;
v_isShared_2187_ = v_isSharedCheck_2195_;
goto v_resetjp_2185_;
}
else
{
lean_dec(v_x_2162_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2195_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 1, v_m_x27_2181_);
lean_ctor_set(v___x_2176_, 0, v_key_2171_);
v___x_2189_ = v___x_2176_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_key_2171_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_m_x27_2181_);
v___x_2189_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2189_);
v___x_2191_ = v___x_2186_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
v_x_2162_ = v___x_2191_;
v_x_2163_ = v_tail_2172_;
goto _start;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(lean_object* v_as_2203_, size_t v_i_2204_, size_t v_stop_2205_, lean_object* v_b_2206_){
_start:
{
uint8_t v___x_2207_; 
v___x_2207_ = lean_usize_dec_eq(v_i_2204_, v_stop_2205_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; size_t v___x_2210_; size_t v___x_2211_; 
v___x_2208_ = lean_array_uget_borrowed(v_as_2203_, v_i_2204_);
lean_inc(v___x_2208_);
v___x_2209_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(v_b_2206_, v___x_2208_);
v___x_2210_ = ((size_t)1ULL);
v___x_2211_ = lean_usize_add(v_i_2204_, v___x_2210_);
v_i_2204_ = v___x_2211_;
v_b_2206_ = v___x_2209_;
goto _start;
}
else
{
return v_b_2206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1___boxed(lean_object* v_as_2213_, lean_object* v_i_2214_, lean_object* v_stop_2215_, lean_object* v_b_2216_){
_start:
{
size_t v_i_boxed_2217_; size_t v_stop_boxed_2218_; lean_object* v_res_2219_; 
v_i_boxed_2217_ = lean_unbox_usize(v_i_2214_);
lean_dec(v_i_2214_);
v_stop_boxed_2218_ = lean_unbox_usize(v_stop_2215_);
lean_dec(v_stop_2215_);
v_res_2219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_as_2213_, v_i_boxed_2217_, v_stop_boxed_2218_, v_b_2216_);
lean_dec_ref(v_as_2213_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality(lean_object* v_p_2220_){
_start:
{
lean_object* v_equalities_2221_; lean_object* v_buckets_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; 
v_equalities_2221_ = lean_ctor_get(v_p_2220_, 3);
v_buckets_2222_ = lean_ctor_get(v_equalities_2221_, 1);
v___x_2223_ = lean_box(0);
v___x_2224_ = lean_unsigned_to_nat(0u);
v___x_2225_ = lean_array_get_size(v_buckets_2222_);
v___x_2226_ = lean_nat_dec_lt(v___x_2224_, v___x_2225_);
if (v___x_2226_ == 0)
{
return v___x_2223_;
}
else
{
uint8_t v___x_2227_; 
v___x_2227_ = lean_nat_dec_le(v___x_2225_, v___x_2225_);
if (v___x_2227_ == 0)
{
if (v___x_2226_ == 0)
{
return v___x_2223_;
}
else
{
size_t v___x_2228_; size_t v___x_2229_; lean_object* v___x_2230_; 
v___x_2228_ = ((size_t)0ULL);
v___x_2229_ = lean_usize_of_nat(v___x_2225_);
v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2222_, v___x_2228_, v___x_2229_, v___x_2223_);
return v___x_2230_;
}
}
else
{
size_t v___x_2231_; size_t v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = ((size_t)0ULL);
v___x_2232_ = lean_usize_of_nat(v___x_2225_);
v___x_2233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2222_, v___x_2231_, v___x_2232_, v___x_2223_);
return v___x_2233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality___boxed(lean_object* v_p_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_2234_);
lean_dec_ref(v_p_2234_);
return v_res_2235_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = lean_unsigned_to_nat(1u);
v___x_2237_ = lean_nat_to_int(v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2239_ = lean_int_neg(v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(lean_object* v_as_2240_, size_t v_i_2241_, size_t v_stop_2242_, lean_object* v_b_2243_){
_start:
{
uint8_t v___x_2244_; 
v___x_2244_ = lean_usize_dec_eq(v_i_2241_, v_stop_2242_);
if (v___x_2244_ == 0)
{
size_t v___x_2245_; size_t v___x_2246_; lean_object* v___x_2247_; lean_object* v_snd_2248_; lean_object* v_fst_2249_; lean_object* v_fst_2250_; lean_object* v_snd_2251_; lean_object* v_coeffs_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; 
v___x_2245_ = ((size_t)1ULL);
v___x_2246_ = lean_usize_sub(v_i_2241_, v___x_2245_);
v___x_2247_ = lean_array_uget_borrowed(v_as_2240_, v___x_2246_);
v_snd_2248_ = lean_ctor_get(v___x_2247_, 1);
v_fst_2249_ = lean_ctor_get(v___x_2247_, 0);
v_fst_2250_ = lean_ctor_get(v_snd_2248_, 0);
v_snd_2251_ = lean_ctor_get(v_snd_2248_, 1);
v_coeffs_2252_ = lean_ctor_get(v_b_2243_, 0);
lean_inc(v_fst_2250_);
v___x_2253_ = l_Lean_Omega_IntList_get(v_coeffs_2252_, v_fst_2250_);
v___x_2254_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2255_ = lean_int_dec_eq(v___x_2253_, v___x_2254_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2256_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2257_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2258_ = lean_int_mul(v___x_2257_, v_snd_2251_);
v___x_2259_ = lean_int_mul(v___x_2258_, v___x_2253_);
lean_dec(v___x_2253_);
lean_dec(v___x_2258_);
lean_inc(v_fst_2249_);
v___x_2260_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v___x_2259_, v_fst_2249_, v___x_2256_, v_b_2243_);
v_i_2241_ = v___x_2246_;
v_b_2243_ = v___x_2260_;
goto _start;
}
else
{
lean_dec(v___x_2253_);
v_i_2241_ = v___x_2246_;
goto _start;
}
}
else
{
return v_b_2243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___boxed(lean_object* v_as_2263_, lean_object* v_i_2264_, lean_object* v_stop_2265_, lean_object* v_b_2266_){
_start:
{
size_t v_i_boxed_2267_; size_t v_stop_boxed_2268_; lean_object* v_res_2269_; 
v_i_boxed_2267_ = lean_unbox_usize(v_i_2264_);
lean_dec(v_i_2264_);
v_stop_boxed_2268_ = lean_unbox_usize(v_stop_2265_);
lean_dec(v_stop_2265_);
v_res_2269_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v_as_2263_, v_i_boxed_2267_, v_stop_boxed_2268_, v_b_2266_);
lean_dec_ref(v_as_2263_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(lean_object* v_init_2270_, lean_object* v_l_2271_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v___x_2272_ = lean_array_mk(v_l_2271_);
v___x_2273_ = lean_array_get_size(v___x_2272_);
v___x_2274_ = lean_unsigned_to_nat(0u);
v___x_2275_ = lean_nat_dec_lt(v___x_2274_, v___x_2273_);
if (v___x_2275_ == 0)
{
lean_dec_ref(v___x_2272_);
return v_init_2270_;
}
else
{
size_t v___x_2276_; size_t v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = lean_usize_of_nat(v___x_2273_);
v___x_2277_ = ((size_t)0ULL);
v___x_2278_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v___x_2272_, v___x_2276_, v___x_2277_, v_init_2270_);
lean_dec_ref(v___x_2272_);
return v___x_2278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(lean_object* v_p_2279_, lean_object* v_f_2280_){
_start:
{
lean_object* v_eliminations_2281_; lean_object* v___x_2282_; 
v_eliminations_2281_ = lean_ctor_get(v_p_2279_, 4);
lean_inc(v_eliminations_2281_);
lean_dec_ref(v_p_2279_);
v___x_2282_ = l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(v_f_2280_, v_eliminations_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__0(lean_object* v_x_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
return v___x_2284_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1(lean_object* v_x_2285_){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v___x_2286_ = lean_nat_abs(v_x_2285_);
v___x_2287_ = lean_unsigned_to_nat(1u);
v___x_2288_ = lean_nat_dec_eq(v___x_2286_, v___x_2287_);
lean_dec(v___x_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1___boxed(lean_object* v_x_2289_){
_start:
{
uint8_t v_res_2290_; lean_object* v_r_2291_; 
v_res_2290_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1(v_x_2289_);
lean_dec(v_x_2289_);
v_r_2291_ = lean_box(v_res_2290_);
return v_r_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(lean_object* v___y_2292_, lean_object* v_sign_2293_, lean_object* v_val_2294_, lean_object* v_x_2295_, lean_object* v_x_2296_){
_start:
{
if (lean_obj_tag(v_x_2296_) == 0)
{
lean_dec_ref(v_val_2294_);
lean_dec(v___y_2292_);
return v_x_2295_;
}
else
{
lean_object* v_key_2297_; lean_object* v_value_2298_; lean_object* v_tail_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; 
v_key_2297_ = lean_ctor_get(v_x_2296_, 0);
lean_inc(v_key_2297_);
v_value_2298_ = lean_ctor_get(v_x_2296_, 1);
lean_inc(v_value_2298_);
v_tail_2299_ = lean_ctor_get(v_x_2296_, 2);
lean_inc(v_tail_2299_);
lean_dec_ref(v_x_2296_);
lean_inc(v___y_2292_);
v___x_2300_ = l_Lean_Omega_IntList_get(v_key_2297_, v___y_2292_);
lean_dec(v_key_2297_);
v___x_2301_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2302_ = lean_int_dec_eq(v___x_2300_, v___x_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v_k_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2303_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2304_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2305_ = lean_int_mul(v___x_2304_, v_sign_2293_);
v_k_2306_ = lean_int_mul(v___x_2305_, v___x_2300_);
lean_dec(v___x_2300_);
lean_dec(v___x_2305_);
lean_inc_ref(v_val_2294_);
v___x_2307_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_k_2306_, v_val_2294_, v___x_2303_, v_value_2298_);
v___x_2308_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_2307_);
v___x_2309_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2295_, v___x_2308_);
v_x_2295_ = v___x_2309_;
v_x_2296_ = v_tail_2299_;
goto _start;
}
else
{
lean_object* v___x_2311_; 
lean_dec(v___x_2300_);
v___x_2311_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2295_, v_value_2298_);
v_x_2295_ = v___x_2311_;
v_x_2296_ = v_tail_2299_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0___boxed(lean_object* v___y_2313_, lean_object* v_sign_2314_, lean_object* v_val_2315_, lean_object* v_x_2316_, lean_object* v_x_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2313_, v_sign_2314_, v_val_2315_, v_x_2316_, v_x_2317_);
lean_dec(v_sign_2314_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object* v___y_2319_, lean_object* v_sign_2320_, lean_object* v_val_2321_, lean_object* v_as_2322_, size_t v_i_2323_, size_t v_stop_2324_, lean_object* v_b_2325_){
_start:
{
uint8_t v___x_2326_; 
v___x_2326_ = lean_usize_dec_eq(v_i_2323_, v_stop_2324_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; size_t v___x_2329_; size_t v___x_2330_; 
v___x_2327_ = lean_array_uget_borrowed(v_as_2322_, v_i_2323_);
lean_inc(v___x_2327_);
lean_inc_ref(v_val_2321_);
lean_inc(v___y_2319_);
v___x_2328_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2319_, v_sign_2320_, v_val_2321_, v_b_2325_, v___x_2327_);
v___x_2329_ = ((size_t)1ULL);
v___x_2330_ = lean_usize_add(v_i_2323_, v___x_2329_);
v_i_2323_ = v___x_2330_;
v_b_2325_ = v___x_2328_;
goto _start;
}
else
{
lean_dec_ref(v_val_2321_);
lean_dec(v___y_2319_);
return v_b_2325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1___boxed(lean_object* v___y_2332_, lean_object* v_sign_2333_, lean_object* v_val_2334_, lean_object* v_as_2335_, lean_object* v_i_2336_, lean_object* v_stop_2337_, lean_object* v_b_2338_){
_start:
{
size_t v_i_boxed_2339_; size_t v_stop_boxed_2340_; lean_object* v_res_2341_; 
v_i_boxed_2339_ = lean_unbox_usize(v_i_2336_);
lean_dec(v_i_2336_);
v_stop_boxed_2340_ = lean_unbox_usize(v_stop_2337_);
lean_dec(v_stop_2337_);
v_res_2341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2332_, v_sign_2333_, v_val_2334_, v_as_2335_, v_i_boxed_2339_, v_stop_boxed_2340_, v_b_2338_);
lean_dec_ref(v_as_2335_);
lean_dec(v_sign_2333_);
return v_res_2341_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2343_ = lean_box(0);
v___x_2344_ = lean_unsigned_to_nat(16u);
v___x_2345_ = lean_mk_array(v___x_2344_, v___x_2343_);
return v___x_2345_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2346_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1);
v___x_2347_ = lean_unsigned_to_nat(0u);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
lean_ctor_set(v___x_2348_, 1, v___x_2346_);
return v___x_2348_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3(void){
_start:
{
lean_object* v___f_2349_; lean_object* v___x_2350_; 
v___f_2349_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0));
v___x_2350_ = lean_mk_thunk(v___f_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(lean_object* v_p_2352_, lean_object* v_c_2353_){
_start:
{
lean_object* v___y_2355_; lean_object* v___f_2402_; lean_object* v___x_2403_; 
v___f_2402_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__4));
lean_inc(v_c_2353_);
v___x_2403_ = l_List_findIdx_x3f___redArg(v___f_2402_, v_c_2353_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_unsigned_to_nat(0u);
v___y_2355_ = v___x_2404_;
goto v___jp_2354_;
}
else
{
lean_object* v_val_2405_; 
v_val_2405_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_val_2405_);
lean_dec_ref(v___x_2403_);
v___y_2355_ = v_val_2405_;
goto v___jp_2354_;
}
v___jp_2354_:
{
lean_object* v_assumptions_2356_; lean_object* v_constraints_2357_; lean_object* v_eliminations_2358_; lean_object* v___x_2359_; 
v_assumptions_2356_ = lean_ctor_get(v_p_2352_, 0);
v_constraints_2357_ = lean_ctor_get(v_p_2352_, 2);
lean_inc_ref(v_constraints_2357_);
v_eliminations_2358_ = lean_ctor_get(v_p_2352_, 4);
v___x_2359_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2357_, v_c_2353_);
if (lean_obj_tag(v___x_2359_) == 1)
{
lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2394_; 
lean_inc(v_eliminations_2358_);
lean_inc_ref(v_assumptions_2356_);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_p_2352_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; lean_object* v_unused_2396_; lean_object* v_unused_2397_; lean_object* v_unused_2398_; lean_object* v_unused_2399_; lean_object* v_unused_2400_; lean_object* v_unused_2401_; 
v_unused_2395_ = lean_ctor_get(v_p_2352_, 6);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v_p_2352_, 5);
lean_dec(v_unused_2396_);
v_unused_2397_ = lean_ctor_get(v_p_2352_, 4);
lean_dec(v_unused_2397_);
v_unused_2398_ = lean_ctor_get(v_p_2352_, 3);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_p_2352_, 2);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_p_2352_, 1);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_p_2352_, 0);
lean_dec(v_unused_2401_);
v___x_2361_ = v_p_2352_;
v_isShared_2362_ = v_isSharedCheck_2394_;
goto v_resetjp_2360_;
}
else
{
lean_dec(v_p_2352_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2394_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v_val_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v_buckets_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2392_; 
v_val_2363_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_val_2363_);
lean_dec_ref(v___x_2359_);
v___x_2364_ = lean_unsigned_to_nat(0u);
v___x_2365_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v_buckets_2366_ = lean_ctor_get(v_constraints_2357_, 1);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_constraints_2357_);
if (v_isSharedCheck_2392_ == 0)
{
lean_object* v_unused_2393_; 
v_unused_2393_ = lean_ctor_get(v_constraints_2357_, 0);
lean_dec(v_unused_2393_);
v___x_2368_ = v_constraints_2357_;
v_isShared_2369_ = v_isSharedCheck_2392_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_buckets_2366_);
lean_dec(v_constraints_2357_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2392_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v_sign_2371_; lean_object* v___x_2373_; 
lean_inc(v___y_2355_);
v___x_2370_ = l_Lean_Omega_IntList_get(v_c_2353_, v___y_2355_);
lean_dec(v_c_2353_);
v_sign_2371_ = l_Int_sign(v___x_2370_);
lean_dec(v___x_2370_);
lean_inc(v_sign_2371_);
lean_inc(v___y_2355_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 1, v_sign_2371_);
lean_ctor_set(v___x_2368_, 0, v___y_2355_);
v___x_2373_ = v___x_2368_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___y_2355_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v_sign_2371_);
v___x_2373_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v_init_2380_; 
lean_inc(v_val_2363_);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v_val_2363_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
lean_ctor_set(v___x_2375_, 1, v_eliminations_2358_);
v___x_2376_ = 1;
v___x_2377_ = lean_box(0);
v___x_2378_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 6, v___x_2378_);
lean_ctor_set(v___x_2361_, 5, v___x_2377_);
lean_ctor_set(v___x_2361_, 4, v___x_2375_);
lean_ctor_set(v___x_2361_, 3, v___x_2365_);
lean_ctor_set(v___x_2361_, 2, v___x_2365_);
lean_ctor_set(v___x_2361_, 1, v___x_2364_);
v_init_2380_ = v___x_2361_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_assumptions_2356_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2390_, 2, v___x_2365_);
lean_ctor_set(v_reuseFailAlloc_2390_, 3, v___x_2365_);
lean_ctor_set(v_reuseFailAlloc_2390_, 4, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2390_, 5, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2390_, 6, v___x_2378_);
v_init_2380_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; uint8_t v___x_2382_; 
lean_ctor_set_uint8(v_init_2380_, sizeof(void*)*7, v___x_2376_);
v___x_2381_ = lean_array_get_size(v_buckets_2366_);
v___x_2382_ = lean_nat_dec_lt(v___x_2364_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_dec(v_sign_2371_);
lean_dec_ref(v_buckets_2366_);
lean_dec(v_val_2363_);
lean_dec(v___y_2355_);
return v_init_2380_;
}
else
{
uint8_t v___x_2383_; 
v___x_2383_ = lean_nat_dec_le(v___x_2381_, v___x_2381_);
if (v___x_2383_ == 0)
{
if (v___x_2382_ == 0)
{
lean_dec(v_sign_2371_);
lean_dec_ref(v_buckets_2366_);
lean_dec(v_val_2363_);
lean_dec(v___y_2355_);
return v_init_2380_;
}
else
{
size_t v___x_2384_; size_t v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = ((size_t)0ULL);
v___x_2385_ = lean_usize_of_nat(v___x_2381_);
v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2355_, v_sign_2371_, v_val_2363_, v_buckets_2366_, v___x_2384_, v___x_2385_, v_init_2380_);
lean_dec_ref(v_buckets_2366_);
lean_dec(v_sign_2371_);
return v___x_2386_;
}
}
else
{
size_t v___x_2387_; size_t v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = ((size_t)0ULL);
v___x_2388_ = lean_usize_of_nat(v___x_2381_);
v___x_2389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2355_, v_sign_2371_, v_val_2363_, v_buckets_2366_, v___x_2387_, v___x_2388_, v_init_2380_);
lean_dec_ref(v_buckets_2366_);
lean_dec(v_sign_2371_);
return v___x_2389_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2359_);
lean_dec_ref(v_constraints_2357_);
lean_dec(v___y_2355_);
lean_dec(v_c_2353_);
return v_p_2352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(lean_object* v_msgData_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___x_2412_; lean_object* v_env_2413_; lean_object* v___x_2414_; lean_object* v_mctx_2415_; lean_object* v_lctx_2416_; lean_object* v_options_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2412_ = lean_st_ref_get(v___y_2410_);
v_env_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc_ref(v_env_2413_);
lean_dec(v___x_2412_);
v___x_2414_ = lean_st_ref_get(v___y_2408_);
v_mctx_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc_ref(v_mctx_2415_);
lean_dec(v___x_2414_);
v_lctx_2416_ = lean_ctor_get(v___y_2407_, 2);
v_options_2417_ = lean_ctor_get(v___y_2409_, 2);
lean_inc_ref(v_options_2417_);
lean_inc_ref(v_lctx_2416_);
v___x_2418_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2418_, 0, v_env_2413_);
lean_ctor_set(v___x_2418_, 1, v_mctx_2415_);
lean_ctor_set(v___x_2418_, 2, v_lctx_2416_);
lean_ctor_set(v___x_2418_, 3, v_options_2417_);
v___x_2419_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
lean_ctor_set(v___x_2419_, 1, v_msgData_2406_);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0___boxed(lean_object* v_msgData_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msgData_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(lean_object* v_msg_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_ref_2434_; lean_object* v___x_2435_; lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2444_; 
v_ref_2434_ = lean_ctor_get(v___y_2431_, 5);
v___x_2435_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2438_ = v___x_2435_;
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
lean_inc(v_ref_2434_);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v_ref_2434_);
lean_ctor_set(v___x_2440_, 1, v_a_2436_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set_tag(v___x_2438_, 1);
lean_ctor_set(v___x_2438_, 0, v___x_2440_);
v___x_2442_ = v___x_2438_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg___boxed(lean_object* v_msg_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2451_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0));
v___x_2454_ = l_Lean_stringToMessageData(v___x_2453_);
return v___x_2454_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2));
v___x_2457_ = l_Lean_stringToMessageData(v___x_2456_);
return v___x_2457_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4));
v___x_2460_ = l_Lean_stringToMessageData(v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(lean_object* v_p_2461_, lean_object* v_c_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, uint8_t v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v_constraints_2473_; lean_object* v___x_2474_; 
v_constraints_2473_ = lean_ctor_get(v_p_2461_, 2);
v___x_2474_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2473_, v_c_2462_);
if (lean_obj_tag(v___x_2474_) == 1)
{
lean_object* v_val_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2574_; 
v_val_2475_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2477_ = v___x_2474_;
v_isShared_2478_ = v_isSharedCheck_2574_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_val_2475_);
lean_dec(v___x_2474_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2574_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_constraint_2479_; lean_object* v_lowerBound_2480_; 
v_constraint_2479_ = lean_ctor_get(v_val_2475_, 1);
v_lowerBound_2480_ = lean_ctor_get(v_constraint_2479_, 0);
lean_inc(v_lowerBound_2480_);
if (lean_obj_tag(v_lowerBound_2480_) == 1)
{
lean_object* v_upperBound_2481_; 
lean_del_object(v___x_2477_);
v_upperBound_2481_ = lean_ctor_get(v_constraint_2479_, 1);
lean_inc(v_upperBound_2481_);
if (lean_obj_tag(v_upperBound_2481_) == 1)
{
lean_object* v_coeffs_2482_; lean_object* v_justification_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2561_; 
v_coeffs_2482_ = lean_ctor_get(v_val_2475_, 0);
v_justification_2483_ = lean_ctor_get(v_val_2475_, 2);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_val_2475_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; 
v_unused_2562_ = lean_ctor_get(v_val_2475_, 1);
lean_dec(v_unused_2562_);
v___x_2485_ = v_val_2475_;
v_isShared_2486_ = v_isSharedCheck_2561_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_justification_2483_);
lean_inc(v_coeffs_2482_);
lean_dec(v_val_2475_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2561_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v_val_2487_; lean_object* v_val_2488_; lean_object* v___x_2489_; 
v_val_2487_ = lean_ctor_get(v_lowerBound_2480_, 0);
lean_inc(v_val_2487_);
lean_dec_ref(v_lowerBound_2480_);
v_val_2488_ = lean_ctor_get(v_upperBound_2481_, 0);
lean_inc(v_val_2488_);
lean_dec_ref(v_upperBound_2481_);
lean_inc(v_a_2471_);
lean_inc_ref(v_a_2470_);
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
v___x_2489_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2464_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v_m_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v_nil_2496_; lean_object* v_cons_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref(v___x_2489_);
lean_inc(v_c_2462_);
v___x_2491_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_c_2462_);
v___x_2492_ = lean_unsigned_to_nat(1u);
v_m_2493_ = lean_nat_add(v___x_2491_, v___x_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc(v_m_2493_);
v___x_2495_ = l_Lean_mkNatLit(v_m_2493_);
v_nil_2496_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2497_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2498_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2496_, v_cons_2497_, v_c_2462_);
lean_dec(v_c_2462_);
v___x_2499_ = l_Lean_mkApp3(v___x_2494_, v___x_2495_, v___x_2498_, v_a_2490_);
lean_inc(v_a_2471_);
lean_inc_ref(v_a_2470_);
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
v___x_2500_ = l_Lean_Elab_Tactic_Omega_lookup(v___x_2499_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2544_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2503_ = v___x_2500_;
v_isShared_2504_ = v_isSharedCheck_2544_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2500_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2544_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v_fst_2505_; lean_object* v_snd_2506_; uint8_t v___x_2519_; 
v_fst_2505_ = lean_ctor_get(v_a_2501_, 0);
lean_inc(v_fst_2505_);
v_snd_2506_ = lean_ctor_get(v_a_2501_, 1);
lean_inc(v_snd_2506_);
lean_dec(v_a_2501_);
v___x_2519_ = lean_int_dec_eq(v_val_2488_, v_val_2487_);
lean_dec(v_val_2488_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec(v_snd_2506_);
lean_dec(v_fst_2505_);
lean_del_object(v___x_2503_);
lean_dec(v_m_2493_);
lean_dec(v_val_2487_);
lean_del_object(v___x_2485_);
lean_dec_ref(v_justification_2483_);
lean_dec(v_coeffs_2482_);
lean_dec_ref(v_p_2461_);
v___x_2520_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1);
v___x_2521_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_2520_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
return v___x_2521_;
}
else
{
if (lean_obj_tag(v_snd_2506_) == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v_fst_2505_);
lean_del_object(v___x_2503_);
lean_dec(v_m_2493_);
lean_dec(v_val_2487_);
lean_del_object(v___x_2485_);
lean_dec_ref(v_justification_2483_);
lean_dec(v_coeffs_2482_);
lean_dec_ref(v_p_2461_);
v___x_2522_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3);
v___x_2523_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_2522_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
else
{
lean_object* v_val_2532_; uint8_t v___x_2533_; 
v_val_2532_ = lean_ctor_get(v_snd_2506_, 0);
lean_inc(v_val_2532_);
lean_dec_ref(v_snd_2506_);
v___x_2533_ = l_List_isEmpty___redArg(v_val_2532_);
lean_dec(v_val_2532_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v_fst_2505_);
lean_del_object(v___x_2503_);
lean_dec(v_m_2493_);
lean_dec(v_val_2487_);
lean_del_object(v___x_2485_);
lean_dec_ref(v_justification_2483_);
lean_dec(v_coeffs_2482_);
lean_dec_ref(v_p_2461_);
v___x_2534_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5);
v___x_2535_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_2534_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
else
{
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
goto v___jp_2507_;
}
}
}
v___jp_2507_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2513_; 
lean_inc(v_coeffs_2482_);
lean_inc(v_m_2493_);
v___x_2508_ = l_Lean_Omega_bmod__coeffs(v_m_2493_, v_fst_2505_, v_coeffs_2482_);
lean_inc(v_m_2493_);
v___x_2509_ = l_Int_bmod(v_val_2487_, v_m_2493_);
v___x_2510_ = l_Lean_Omega_Constraint_exact(v___x_2509_);
v___x_2511_ = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(v___x_2511_, 0, v_m_2493_);
lean_ctor_set(v___x_2511_, 1, v_val_2487_);
lean_ctor_set(v___x_2511_, 2, v_fst_2505_);
lean_ctor_set(v___x_2511_, 3, v_coeffs_2482_);
lean_ctor_set(v___x_2511_, 4, v_justification_2483_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 2, v___x_2511_);
lean_ctor_set(v___x_2485_, 1, v___x_2510_);
lean_ctor_set(v___x_2485_, 0, v___x_2508_);
v___x_2513_ = v___x_2485_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2514_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_2461_, v___x_2513_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 0, v___x_2514_);
v___x_2516_ = v___x_2503_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_m_2493_);
lean_dec(v_val_2488_);
lean_dec(v_val_2487_);
lean_del_object(v___x_2485_);
lean_dec_ref(v_justification_2483_);
lean_dec(v_coeffs_2482_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec_ref(v_p_2461_);
v_a_2545_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2500_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2500_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v_val_2488_);
lean_dec(v_val_2487_);
lean_del_object(v___x_2485_);
lean_dec_ref(v_justification_2483_);
lean_dec(v_coeffs_2482_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_c_2462_);
lean_dec_ref(v_p_2461_);
v_a_2553_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2489_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2489_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
else
{
lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec(v_upperBound_2481_);
lean_dec(v_val_2475_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_c_2462_);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_lowerBound_2480_);
if (v_isSharedCheck_2569_ == 0)
{
lean_object* v_unused_2570_; 
v_unused_2570_ = lean_ctor_get(v_lowerBound_2480_, 0);
lean_dec(v_unused_2570_);
v___x_2564_ = v_lowerBound_2480_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_dec(v_lowerBound_2480_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
lean_ctor_set_tag(v___x_2564_, 0);
lean_ctor_set(v___x_2564_, 0, v_p_2461_);
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_p_2461_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
else
{
lean_object* v___x_2572_; 
lean_dec(v_lowerBound_2480_);
lean_dec(v_val_2475_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_c_2462_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set_tag(v___x_2477_, 0);
lean_ctor_set(v___x_2477_, 0, v_p_2461_);
v___x_2572_ = v___x_2477_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_p_2461_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
else
{
lean_object* v___x_2575_; 
lean_dec(v___x_2474_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_c_2462_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v_p_2461_);
return v___x_2575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___boxed(lean_object* v_p_2576_, lean_object* v_c_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
uint8_t v_a_14815__boxed_2588_; lean_object* v_res_2589_; 
v_a_14815__boxed_2588_ = lean_unbox(v_a_2581_);
v_res_2589_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_2576_, v_c_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_14815__boxed_2588_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2580_);
lean_dec(v_a_2579_);
lean_dec(v_a_2578_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_object* v_00_u03b1_2590_, lean_object* v_msg_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, uint8_t v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_2591_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___boxed(lean_object* v_00_u03b1_2603_, lean_object* v_msg_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
uint8_t v___y_15054__boxed_2615_; lean_object* v_res_2616_; 
v___y_15054__boxed_2615_ = lean_unbox(v___y_2608_);
v_res_2616_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(v_00_u03b1_2603_, v_msg_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_15054__boxed_2615_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec(v___y_2605_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality(lean_object* v_p_2617_, lean_object* v_c_2618_, lean_object* v_m_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, uint8_t v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v___x_2630_; uint8_t v___x_2631_; 
v___x_2630_ = lean_unsigned_to_nat(1u);
v___x_2631_ = lean_nat_dec_eq(v_m_2619_, v___x_2630_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_2617_, v_c_2618_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
return v___x_2632_;
}
else
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
v___x_2633_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_2617_, v_c_2618_);
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
return v___x_2634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality___boxed(lean_object* v_p_2635_, lean_object* v_c_2636_, lean_object* v_m_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
uint8_t v_a_388__boxed_2648_; lean_object* v_res_2649_; 
v_a_388__boxed_2648_ = lean_unbox(v_a_2641_);
v_res_2649_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_2635_, v_c_2636_, v_m_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_388__boxed_2648_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec(v_m_2637_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(lean_object* v_p_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, uint8_t v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
uint8_t v_possible_2661_; 
v_possible_2661_ = lean_ctor_get_uint8(v_p_2650_, sizeof(void*)*7);
if (v_possible_2661_ == 0)
{
lean_object* v___x_2662_; 
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v_p_2650_);
return v___x_2662_;
}
else
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_2650_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v___x_2664_; 
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v_p_2650_);
return v___x_2664_;
}
else
{
lean_object* v_val_2665_; lean_object* v_fst_2666_; lean_object* v_snd_2667_; lean_object* v___x_2668_; 
v_val_2665_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_val_2665_);
lean_dec_ref(v___x_2663_);
v_fst_2666_ = lean_ctor_get(v_val_2665_, 0);
lean_inc(v_fst_2666_);
v_snd_2667_ = lean_ctor_get(v_val_2665_, 1);
lean_inc(v_snd_2667_);
lean_dec(v_val_2665_);
lean_inc(v_a_2659_);
lean_inc_ref(v_a_2658_);
lean_inc(v_a_2657_);
lean_inc_ref(v_a_2656_);
v___x_2668_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_2650_, v_fst_2666_, v_snd_2667_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
lean_dec(v_snd_2667_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref(v___x_2668_);
v_p_2650_ = v_a_2669_;
goto _start;
}
else
{
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
return v___x_2668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities___boxed(lean_object* v_p_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
uint8_t v_a_1241__boxed_2682_; lean_object* v_res_2683_; 
v_a_1241__boxed_2682_ = lean_unbox(v_a_2675_);
v_res_2683_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_1241__boxed_2682_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec(v_a_2672_);
return v_res_2683_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = lean_box(0);
v___x_2691_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1));
v___x_2692_ = l_Lean_Expr_const___override(v___x_2691_, v___x_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object* v_c_2693_, lean_object* v_x_2694_, lean_object* v_p_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, uint8_t v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v___x_2706_; 
lean_inc(v_a_2704_);
lean_inc_ref(v_a_2703_);
lean_inc(v_a_2702_);
lean_inc_ref(v_a_2701_);
v___x_2706_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2697_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_a_2707_);
lean_dec_ref(v___x_2706_);
v___x_2708_ = lean_box(v_a_2699_);
v___x_2709_ = lean_apply_10(v_p_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v___x_2708_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, lean_box(0));
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2735_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2735_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2735_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; lean_object* v___y_2716_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2714_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2);
v___x_2724_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2725_ = lean_int_dec_le(v___x_2724_, v_c_2693_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2726_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2727_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_2728_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2729_ = lean_int_neg(v_c_2693_);
v___x_2730_ = l_Int_toNat(v___x_2729_);
lean_dec(v___x_2729_);
v___x_2731_ = l_Lean_instToExprInt_mkNat(v___x_2730_);
v___x_2732_ = l_Lean_mkApp3(v___x_2726_, v___x_2727_, v___x_2728_, v___x_2731_);
v___y_2716_ = v___x_2732_;
goto v___jp_2715_;
}
else
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = l_Int_toNat(v_c_2693_);
v___x_2734_ = l_Lean_instToExprInt_mkNat(v___x_2733_);
v___y_2716_ = v___x_2734_;
goto v___jp_2715_;
}
v___jp_2715_:
{
lean_object* v_nil_2717_; lean_object* v_cons_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; 
v_nil_2717_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2718_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2719_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2717_, v_cons_2718_, v_x_2694_);
v___x_2720_ = l_Lean_mkApp4(v___x_2714_, v___y_2716_, v___x_2719_, v_a_2707_, v_a_2710_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2720_);
v___x_2722_ = v___x_2712_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_dec(v_a_2707_);
return v___x_2709_;
}
}
else
{
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec(v_a_2700_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec_ref(v_p_2695_);
return v___x_2706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object* v_c_2736_, lean_object* v_x_2737_, lean_object* v_p_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
uint8_t v_a_3017__boxed_2749_; lean_object* v_res_2750_; 
v_a_3017__boxed_2749_ = lean_unbox(v_a_2742_);
v_res_2750_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(v_c_2736_, v_x_2737_, v_p_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_3017__boxed_2749_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
lean_dec(v_x_2737_);
lean_dec(v_c_2736_);
return v_res_2750_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2(void){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2757_ = lean_box(0);
v___x_2758_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1));
v___x_2759_ = l_Lean_Expr_const___override(v___x_2758_, v___x_2757_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(lean_object* v_c_2760_, lean_object* v_x_2761_, lean_object* v_p_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, uint8_t v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v___x_2773_; 
lean_inc(v_a_2771_);
lean_inc_ref(v_a_2770_);
lean_inc(v_a_2769_);
lean_inc_ref(v_a_2768_);
v___x_2773_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2764_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref(v___x_2773_);
v___x_2775_ = lean_box(v_a_2766_);
v___x_2776_ = lean_apply_10(v_p_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v___x_2775_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, lean_box(0));
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2802_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2802_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2802_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; lean_object* v___y_2783_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2781_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2);
v___x_2791_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2792_ = lean_int_dec_le(v___x_2791_, v_c_2760_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2793_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2794_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_2795_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2796_ = lean_int_neg(v_c_2760_);
v___x_2797_ = l_Int_toNat(v___x_2796_);
lean_dec(v___x_2796_);
v___x_2798_ = l_Lean_instToExprInt_mkNat(v___x_2797_);
v___x_2799_ = l_Lean_mkApp3(v___x_2793_, v___x_2794_, v___x_2795_, v___x_2798_);
v___y_2783_ = v___x_2799_;
goto v___jp_2782_;
}
else
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = l_Int_toNat(v_c_2760_);
v___x_2801_ = l_Lean_instToExprInt_mkNat(v___x_2800_);
v___y_2783_ = v___x_2801_;
goto v___jp_2782_;
}
v___jp_2782_:
{
lean_object* v_nil_2784_; lean_object* v_cons_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
v_nil_2784_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2785_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2786_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2784_, v_cons_2785_, v_x_2761_);
v___x_2787_ = l_Lean_mkApp4(v___x_2781_, v___y_2783_, v___x_2786_, v_a_2774_, v_a_2777_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2787_);
v___x_2789_ = v___x_2779_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
else
{
lean_dec(v_a_2774_);
return v___x_2776_;
}
}
else
{
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec(v_a_2763_);
lean_dec_ref(v_p_2762_);
return v___x_2773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed(lean_object* v_c_2803_, lean_object* v_x_2804_, lean_object* v_p_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
uint8_t v_a_3017__boxed_2816_; lean_object* v_res_2817_; 
v_a_3017__boxed_2816_ = lean_unbox(v_a_2809_);
v_res_2817_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(v_c_2803_, v_x_2804_, v_p_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_3017__boxed_2816_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_);
lean_dec(v_x_2804_);
lean_dec(v_c_2803_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(lean_object* v_prf_x3f_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, uint8_t v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
if (lean_obj_tag(v_prf_x3f_2818_) == 0)
{
lean_object* v___x_2829_; uint8_t v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec(v___y_2819_);
v___x_2829_ = lean_box(0);
v___x_2830_ = 0;
v___x_2831_ = lean_box(0);
lean_inc_ref(v___y_2824_);
v___x_2832_ = l_Lean_Meta_mkFreshExprMVar(v___x_2829_, v___x_2830_, v___x_2831_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; uint8_t v___x_2834_; lean_object* v___x_2835_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref(v___x_2832_);
v___x_2834_ = 0;
v___x_2835_ = l_Lean_Meta_mkSorry(v_a_2833_, v___x_2834_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
return v___x_2835_;
}
else
{
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
return v___x_2832_;
}
}
else
{
lean_object* v_val_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_val_2836_ = lean_ctor_get(v_prf_x3f_2818_, 0);
lean_inc(v_val_2836_);
lean_dec_ref(v_prf_x3f_2818_);
v___x_2837_ = lean_box(v___y_2822_);
v___x_2838_ = lean_apply_10(v_val_2836_, v___y_2819_, v___y_2820_, v___y_2821_, v___x_2837_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
return v___x_2838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed(lean_object* v_prf_x3f_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
uint8_t v___y_803__boxed_2850_; lean_object* v_res_2851_; 
v___y_803__boxed_2850_ = lean_unbox(v___y_2843_);
v_res_2851_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(v_prf_x3f_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_803__boxed_2850_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality(lean_object* v_p_2852_, lean_object* v_const_2853_, lean_object* v_coeffs_2854_, lean_object* v_prf_x3f_2855_){
_start:
{
lean_object* v_assumptions_2856_; lean_object* v_numVars_2857_; lean_object* v_constraints_2858_; lean_object* v_equalities_2859_; lean_object* v_eliminations_2860_; uint8_t v_possible_2861_; lean_object* v_proveFalse_x3f_2862_; lean_object* v_explanation_x3f_2863_; lean_object* v_prf_2864_; lean_object* v_i_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v_p_x27_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v_f_2874_; lean_object* v_f_2875_; lean_object* v_f_2876_; lean_object* v___x_2877_; 
v_assumptions_2856_ = lean_ctor_get(v_p_2852_, 0);
v_numVars_2857_ = lean_ctor_get(v_p_2852_, 1);
v_constraints_2858_ = lean_ctor_get(v_p_2852_, 2);
v_equalities_2859_ = lean_ctor_get(v_p_2852_, 3);
v_eliminations_2860_ = lean_ctor_get(v_p_2852_, 4);
v_possible_2861_ = lean_ctor_get_uint8(v_p_2852_, sizeof(void*)*7);
v_proveFalse_x3f_2862_ = lean_ctor_get(v_p_2852_, 5);
v_explanation_x3f_2863_ = lean_ctor_get(v_p_2852_, 6);
v_prf_2864_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_2864_, 0, v_prf_x3f_2855_);
v_i_2865_ = lean_array_get_size(v_assumptions_2856_);
lean_inc(v_coeffs_2854_);
lean_inc(v_const_2853_);
v___x_2866_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed), 13, 3);
lean_closure_set(v___x_2866_, 0, v_const_2853_);
lean_closure_set(v___x_2866_, 1, v_coeffs_2854_);
lean_closure_set(v___x_2866_, 2, v_prf_2864_);
lean_inc_ref(v_assumptions_2856_);
v___x_2867_ = lean_array_push(v_assumptions_2856_, v___x_2866_);
lean_inc_ref(v_explanation_x3f_2863_);
lean_inc(v_proveFalse_x3f_2862_);
lean_inc(v_eliminations_2860_);
lean_inc_ref(v_equalities_2859_);
lean_inc_ref(v_constraints_2858_);
lean_inc(v_numVars_2857_);
v_p_x27_2868_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_2868_, 0, v___x_2867_);
lean_ctor_set(v_p_x27_2868_, 1, v_numVars_2857_);
lean_ctor_set(v_p_x27_2868_, 2, v_constraints_2858_);
lean_ctor_set(v_p_x27_2868_, 3, v_equalities_2859_);
lean_ctor_set(v_p_x27_2868_, 4, v_eliminations_2860_);
lean_ctor_set(v_p_x27_2868_, 5, v_proveFalse_x3f_2862_);
lean_ctor_set(v_p_x27_2868_, 6, v_explanation_x3f_2863_);
lean_ctor_set_uint8(v_p_x27_2868_, sizeof(void*)*7, v_possible_2861_);
v___x_2869_ = lean_int_neg(v_const_2853_);
lean_dec(v_const_2853_);
v___x_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
v___x_2871_ = lean_box(0);
v___x_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
lean_inc(v_coeffs_2854_);
lean_inc_ref(v___x_2872_);
v___x_2873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
lean_ctor_set(v___x_2873_, 1, v_coeffs_2854_);
lean_ctor_set(v___x_2873_, 2, v_i_2865_);
v_f_2874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_2874_, 0, v_coeffs_2854_);
lean_ctor_set(v_f_2874_, 1, v___x_2872_);
lean_ctor_set(v_f_2874_, 2, v___x_2873_);
v_f_2875_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_2852_, v_f_2874_);
v_f_2876_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_2875_);
v___x_2877_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_2868_, v_f_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality(lean_object* v_p_2878_, lean_object* v_const_2879_, lean_object* v_coeffs_2880_, lean_object* v_prf_x3f_2881_){
_start:
{
lean_object* v_assumptions_2882_; lean_object* v_numVars_2883_; lean_object* v_constraints_2884_; lean_object* v_equalities_2885_; lean_object* v_eliminations_2886_; uint8_t v_possible_2887_; lean_object* v_proveFalse_x3f_2888_; lean_object* v_explanation_x3f_2889_; lean_object* v_prf_2890_; lean_object* v_i_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v_p_x27_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v_f_2899_; lean_object* v_f_2900_; lean_object* v_f_2901_; lean_object* v___x_2902_; 
v_assumptions_2882_ = lean_ctor_get(v_p_2878_, 0);
v_numVars_2883_ = lean_ctor_get(v_p_2878_, 1);
v_constraints_2884_ = lean_ctor_get(v_p_2878_, 2);
v_equalities_2885_ = lean_ctor_get(v_p_2878_, 3);
v_eliminations_2886_ = lean_ctor_get(v_p_2878_, 4);
v_possible_2887_ = lean_ctor_get_uint8(v_p_2878_, sizeof(void*)*7);
v_proveFalse_x3f_2888_ = lean_ctor_get(v_p_2878_, 5);
v_explanation_x3f_2889_ = lean_ctor_get(v_p_2878_, 6);
v_prf_2890_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_2890_, 0, v_prf_x3f_2881_);
v_i_2891_ = lean_array_get_size(v_assumptions_2882_);
lean_inc(v_coeffs_2880_);
lean_inc(v_const_2879_);
v___x_2892_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed), 13, 3);
lean_closure_set(v___x_2892_, 0, v_const_2879_);
lean_closure_set(v___x_2892_, 1, v_coeffs_2880_);
lean_closure_set(v___x_2892_, 2, v_prf_2890_);
lean_inc_ref(v_assumptions_2882_);
v___x_2893_ = lean_array_push(v_assumptions_2882_, v___x_2892_);
lean_inc_ref(v_explanation_x3f_2889_);
lean_inc(v_proveFalse_x3f_2888_);
lean_inc(v_eliminations_2886_);
lean_inc_ref(v_equalities_2885_);
lean_inc_ref(v_constraints_2884_);
lean_inc(v_numVars_2883_);
v_p_x27_2894_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_2894_, 0, v___x_2893_);
lean_ctor_set(v_p_x27_2894_, 1, v_numVars_2883_);
lean_ctor_set(v_p_x27_2894_, 2, v_constraints_2884_);
lean_ctor_set(v_p_x27_2894_, 3, v_equalities_2885_);
lean_ctor_set(v_p_x27_2894_, 4, v_eliminations_2886_);
lean_ctor_set(v_p_x27_2894_, 5, v_proveFalse_x3f_2888_);
lean_ctor_set(v_p_x27_2894_, 6, v_explanation_x3f_2889_);
lean_ctor_set_uint8(v_p_x27_2894_, sizeof(void*)*7, v_possible_2887_);
v___x_2895_ = lean_int_neg(v_const_2879_);
lean_dec(v_const_2879_);
v___x_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
lean_inc_ref(v___x_2896_);
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
lean_inc(v_coeffs_2880_);
lean_inc_ref(v___x_2897_);
v___x_2898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
lean_ctor_set(v___x_2898_, 1, v_coeffs_2880_);
lean_ctor_set(v___x_2898_, 2, v_i_2891_);
v_f_2899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_2899_, 0, v_coeffs_2880_);
lean_ctor_set(v_f_2899_, 1, v___x_2897_);
lean_ctor_set(v_f_2899_, 2, v___x_2898_);
v_f_2900_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_2878_, v_f_2899_);
v_f_2901_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_2900_);
v___x_2902_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_2894_, v_f_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(lean_object* v_x_2903_, lean_object* v_x_2904_){
_start:
{
if (lean_obj_tag(v_x_2904_) == 0)
{
return v_x_2903_;
}
else
{
lean_object* v_head_2905_; lean_object* v_snd_2906_; lean_object* v_tail_2907_; lean_object* v_fst_2908_; lean_object* v_fst_2909_; lean_object* v_snd_2910_; lean_object* v___x_2911_; 
v_head_2905_ = lean_ctor_get(v_x_2904_, 0);
lean_inc(v_head_2905_);
v_snd_2906_ = lean_ctor_get(v_head_2905_, 1);
lean_inc(v_snd_2906_);
v_tail_2907_ = lean_ctor_get(v_x_2904_, 1);
lean_inc(v_tail_2907_);
lean_dec_ref(v_x_2904_);
v_fst_2908_ = lean_ctor_get(v_head_2905_, 0);
lean_inc(v_fst_2908_);
lean_dec(v_head_2905_);
v_fst_2909_ = lean_ctor_get(v_snd_2906_, 0);
lean_inc(v_fst_2909_);
v_snd_2910_ = lean_ctor_get(v_snd_2906_, 1);
lean_inc(v_snd_2910_);
lean_dec(v_snd_2906_);
v___x_2911_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality(v_x_2903_, v_fst_2908_, v_fst_2909_, v_snd_2910_);
v_x_2903_ = v___x_2911_;
v_x_2904_ = v_tail_2907_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequalities(lean_object* v_p_2913_, lean_object* v_ineqs_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(v_p_2913_, v_ineqs_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(lean_object* v_x_2916_, lean_object* v_x_2917_){
_start:
{
if (lean_obj_tag(v_x_2917_) == 0)
{
return v_x_2916_;
}
else
{
lean_object* v_head_2918_; lean_object* v_snd_2919_; lean_object* v_tail_2920_; lean_object* v_fst_2921_; lean_object* v_fst_2922_; lean_object* v_snd_2923_; lean_object* v___x_2924_; 
v_head_2918_ = lean_ctor_get(v_x_2917_, 0);
lean_inc(v_head_2918_);
v_snd_2919_ = lean_ctor_get(v_head_2918_, 1);
lean_inc(v_snd_2919_);
v_tail_2920_ = lean_ctor_get(v_x_2917_, 1);
lean_inc(v_tail_2920_);
lean_dec_ref(v_x_2917_);
v_fst_2921_ = lean_ctor_get(v_head_2918_, 0);
lean_inc(v_fst_2921_);
lean_dec(v_head_2918_);
v_fst_2922_ = lean_ctor_get(v_snd_2919_, 0);
lean_inc(v_fst_2922_);
v_snd_2923_ = lean_ctor_get(v_snd_2919_, 1);
lean_inc(v_snd_2923_);
lean_dec(v_snd_2919_);
v___x_2924_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality(v_x_2916_, v_fst_2921_, v_fst_2922_, v_snd_2923_);
v_x_2916_ = v___x_2924_;
v_x_2917_ = v_tail_2920_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEqualities(lean_object* v_p_2926_, lean_object* v_eqs_2927_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(v_p_2926_, v_eqs_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0(lean_object* v___x_2935_, lean_object* v_x_2936_){
_start:
{
lean_object* v_coeffs_2937_; lean_object* v_constraint_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_coeffs_2937_ = lean_ctor_get(v_x_2936_, 0);
lean_inc(v_coeffs_2937_);
v_constraint_2938_ = lean_ctor_get(v_x_2936_, 1);
lean_inc_ref(v_constraint_2938_);
lean_dec_ref(v_x_2936_);
v___x_2939_ = l_List_toString___redArg(v___x_2935_, v_coeffs_2937_);
v___x_2940_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_2941_ = lean_string_append(v___x_2939_, v___x_2940_);
v___x_2942_ = l_Lean_Omega_Constraint_instToString___private__1(v_constraint_2938_);
lean_dec_ref(v_constraint_2938_);
v___x_2943_ = lean_string_append(v___x_2941_, v___x_2942_);
lean_dec_ref(v___x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1(lean_object* v___x_2944_, lean_object* v_x_2945_){
_start:
{
lean_object* v_fst_2946_; lean_object* v_coeffs_2947_; lean_object* v_constraint_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v_fst_2946_ = lean_ctor_get(v_x_2945_, 0);
lean_inc(v_fst_2946_);
lean_dec_ref(v_x_2945_);
v_coeffs_2947_ = lean_ctor_get(v_fst_2946_, 0);
lean_inc(v_coeffs_2947_);
v_constraint_2948_ = lean_ctor_get(v_fst_2946_, 1);
lean_inc_ref(v_constraint_2948_);
lean_dec(v_fst_2946_);
v___x_2949_ = l_List_toString___redArg(v___x_2944_, v_coeffs_2947_);
v___x_2950_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_2951_ = lean_string_append(v___x_2949_, v___x_2950_);
v___x_2952_ = l_Lean_Omega_Constraint_instToString___private__1(v_constraint_2948_);
lean_dec_ref(v_constraint_2948_);
v___x_2953_ = lean_string_append(v___x_2951_, v___x_2952_);
lean_dec_ref(v___x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2(lean_object* v___f_2958_, lean_object* v___f_2959_, lean_object* v___f_2960_, lean_object* v_d_2961_){
_start:
{
lean_object* v_var_2962_; lean_object* v_irrelevant_2963_; lean_object* v_lowerBounds_2964_; lean_object* v_upperBounds_2965_; lean_object* v___x_2966_; lean_object* v_irrelevant_2967_; lean_object* v_lowerBounds_2968_; lean_object* v_upperBounds_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_var_2962_ = lean_ctor_get(v_d_2961_, 0);
lean_inc(v_var_2962_);
v_irrelevant_2963_ = lean_ctor_get(v_d_2961_, 1);
lean_inc(v_irrelevant_2963_);
v_lowerBounds_2964_ = lean_ctor_get(v_d_2961_, 2);
lean_inc(v_lowerBounds_2964_);
v_upperBounds_2965_ = lean_ctor_get(v_d_2961_, 3);
lean_inc(v_upperBounds_2965_);
lean_dec_ref(v_d_2961_);
v___x_2966_ = lean_box(0);
v_irrelevant_2967_ = l_List_mapTR_loop___redArg(v___f_2958_, v_irrelevant_2963_, v___x_2966_);
lean_inc_ref(v___f_2959_);
v_lowerBounds_2968_ = l_List_mapTR_loop___redArg(v___f_2959_, v_lowerBounds_2964_, v___x_2966_);
v_upperBounds_2969_ = l_List_mapTR_loop___redArg(v___f_2959_, v_upperBounds_2965_, v___x_2966_);
v___x_2970_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0));
v___x_2971_ = l_Nat_reprFast(v_var_2962_);
v___x_2972_ = lean_string_append(v___x_2970_, v___x_2971_);
lean_dec_ref(v___x_2971_);
v___x_2973_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_2974_ = lean_string_append(v___x_2972_, v___x_2973_);
v___x_2975_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1));
lean_inc_ref(v___f_2960_);
v___x_2976_ = l_List_toString___redArg(v___f_2960_, v_irrelevant_2967_);
v___x_2977_ = lean_string_append(v___x_2975_, v___x_2976_);
lean_dec_ref(v___x_2976_);
v___x_2978_ = lean_string_append(v___x_2977_, v___x_2973_);
v___x_2979_ = lean_string_append(v___x_2974_, v___x_2978_);
lean_dec_ref(v___x_2978_);
v___x_2980_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2));
lean_inc_ref(v___f_2960_);
v___x_2981_ = l_List_toString___redArg(v___f_2960_, v_lowerBounds_2968_);
v___x_2982_ = lean_string_append(v___x_2980_, v___x_2981_);
lean_dec_ref(v___x_2981_);
v___x_2983_ = lean_string_append(v___x_2982_, v___x_2973_);
v___x_2984_ = lean_string_append(v___x_2979_, v___x_2983_);
lean_dec_ref(v___x_2983_);
v___x_2985_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3));
v___x_2986_ = l_List_toString___redArg(v___f_2960_, v_upperBounds_2969_);
v___x_2987_ = lean_string_append(v___x_2985_, v___x_2986_);
lean_dec_ref(v___x_2986_);
v___x_2988_ = lean_string_append(v___x_2984_, v___x_2987_);
lean_dec_ref(v___x_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(lean_object* v_d_2999_){
_start:
{
lean_object* v_lowerBounds_3000_; lean_object* v_upperBounds_3001_; uint8_t v___x_3002_; 
v_lowerBounds_3000_ = lean_ctor_get(v_d_2999_, 2);
v_upperBounds_3001_ = lean_ctor_get(v_d_2999_, 3);
v___x_3002_ = l_List_isEmpty___redArg(v_lowerBounds_3000_);
if (v___x_3002_ == 0)
{
return v___x_3002_;
}
else
{
uint8_t v___x_3003_; 
v___x_3003_ = l_List_isEmpty___redArg(v_upperBounds_3001_);
return v___x_3003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty___boxed(lean_object* v_d_3004_){
_start:
{
uint8_t v_res_3005_; lean_object* v_r_3006_; 
v_res_3005_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v_d_3004_);
lean_dec_ref(v_d_3004_);
v_r_3006_ = lean_box(v_res_3005_);
return v_r_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(lean_object* v_d_3007_){
_start:
{
lean_object* v_lowerBounds_3008_; lean_object* v_upperBounds_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_lowerBounds_3008_ = lean_ctor_get(v_d_3007_, 2);
v_upperBounds_3009_ = lean_ctor_get(v_d_3007_, 3);
v___x_3010_ = l_List_lengthTR___redArg(v_lowerBounds_3008_);
v___x_3011_ = l_List_lengthTR___redArg(v_upperBounds_3009_);
v___x_3012_ = lean_nat_mul(v___x_3010_, v___x_3011_);
lean_dec(v___x_3011_);
lean_dec(v___x_3010_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size___boxed(lean_object* v_d_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_d_3013_);
lean_dec_ref(v_d_3013_);
return v_res_3014_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(lean_object* v_d_3015_){
_start:
{
uint8_t v_lowerExact_3016_; 
v_lowerExact_3016_ = lean_ctor_get_uint8(v_d_3015_, sizeof(void*)*4);
if (v_lowerExact_3016_ == 0)
{
uint8_t v_upperExact_3017_; 
v_upperExact_3017_ = lean_ctor_get_uint8(v_d_3015_, sizeof(void*)*4 + 1);
return v_upperExact_3017_;
}
else
{
return v_lowerExact_3016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact___boxed(lean_object* v_d_3018_){
_start:
{
uint8_t v_res_3019_; lean_object* v_r_3020_; 
v_res_3019_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_d_3018_);
lean_dec_ref(v_d_3018_);
v_r_3020_ = lean_box(v_res_3019_);
return v_r_3020_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(lean_object* v_x_3021_, lean_object* v_x_3022_){
_start:
{
if (lean_obj_tag(v_x_3022_) == 0)
{
return v_x_3021_;
}
else
{
lean_object* v_head_3023_; lean_object* v_tail_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v_head_3023_ = lean_ctor_get(v_x_3022_, 0);
v_tail_3024_ = lean_ctor_get(v_x_3022_, 1);
v___x_3025_ = lean_box(0);
v___x_3026_ = 1;
lean_inc(v_head_3023_);
v___x_3027_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3027_, 0, v_head_3023_);
lean_ctor_set(v___x_3027_, 1, v___x_3025_);
lean_ctor_set(v___x_3027_, 2, v___x_3025_);
lean_ctor_set(v___x_3027_, 3, v___x_3025_);
lean_ctor_set_uint8(v___x_3027_, sizeof(void*)*4, v___x_3026_);
lean_ctor_set_uint8(v___x_3027_, sizeof(void*)*4 + 1, v___x_3026_);
v___x_3028_ = lean_array_push(v_x_3021_, v___x_3027_);
v_x_3021_ = v___x_3028_;
v_x_3022_ = v_tail_3024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2___boxed(lean_object* v_x_3030_, lean_object* v_x_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v_x_3030_, v_x_3031_);
lean_dec(v_x_3031_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object* v___x_3033_, lean_object* v_b_3034_, lean_object* v___x_3035_, lean_object* v_____r_3036_, lean_object* v_d_x27_3037_){
_start:
{
lean_object* v_upperBound_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3065_; 
v_upperBound_3038_ = lean_ctor_get(v___x_3033_, 1);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3065_ == 0)
{
lean_object* v_unused_3066_; 
v_unused_3066_ = lean_ctor_get(v___x_3033_, 0);
lean_dec(v_unused_3066_);
v___x_3040_ = v___x_3033_;
v_isShared_3041_ = v_isSharedCheck_3065_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_upperBound_3038_);
lean_dec(v___x_3033_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3065_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
if (lean_obj_tag(v_upperBound_3038_) == 0)
{
lean_del_object(v___x_3040_);
lean_dec(v___x_3035_);
lean_dec_ref(v_b_3034_);
return v_d_x27_3037_;
}
else
{
lean_object* v_var_3042_; lean_object* v_irrelevant_3043_; lean_object* v_lowerBounds_3044_; lean_object* v_upperBounds_3045_; uint8_t v_lowerExact_3046_; uint8_t v_upperExact_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3064_; 
lean_dec_ref(v_upperBound_3038_);
v_var_3042_ = lean_ctor_get(v_d_x27_3037_, 0);
v_irrelevant_3043_ = lean_ctor_get(v_d_x27_3037_, 1);
v_lowerBounds_3044_ = lean_ctor_get(v_d_x27_3037_, 2);
v_upperBounds_3045_ = lean_ctor_get(v_d_x27_3037_, 3);
v_lowerExact_3046_ = lean_ctor_get_uint8(v_d_x27_3037_, sizeof(void*)*4);
v_upperExact_3047_ = lean_ctor_get_uint8(v_d_x27_3037_, sizeof(void*)*4 + 1);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_d_x27_3037_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3049_ = v_d_x27_3037_;
v_isShared_3050_ = v_isSharedCheck_3064_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_upperBounds_3045_);
lean_inc(v_lowerBounds_3044_);
lean_inc(v_irrelevant_3043_);
lean_inc(v_var_3042_);
lean_dec(v_d_x27_3037_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3064_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
lean_inc(v___x_3035_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 1, v___x_3035_);
lean_ctor_set(v___x_3040_, 0, v_b_3034_);
v___x_3052_ = v___x_3040_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_b_3034_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___x_3035_);
v___x_3052_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v_upperBounds_3045_);
if (v_upperExact_3047_ == 0)
{
lean_object* v___x_3055_; 
lean_dec(v___x_3035_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 3, v___x_3053_);
v___x_3055_ = v___x_3049_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_var_3042_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_irrelevant_3043_);
lean_ctor_set(v_reuseFailAlloc_3056_, 2, v_lowerBounds_3044_);
lean_ctor_set(v_reuseFailAlloc_3056_, 3, v___x_3053_);
lean_ctor_set_uint8(v_reuseFailAlloc_3056_, sizeof(void*)*4, v_lowerExact_3046_);
lean_ctor_set_uint8(v_reuseFailAlloc_3056_, sizeof(void*)*4 + 1, v_upperExact_3047_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
else
{
lean_object* v___x_3057_; lean_object* v___x_3058_; uint8_t v___x_3059_; lean_object* v___x_3061_; 
v___x_3057_ = lean_nat_abs(v___x_3035_);
lean_dec(v___x_3035_);
v___x_3058_ = lean_unsigned_to_nat(1u);
v___x_3059_ = lean_nat_dec_eq(v___x_3057_, v___x_3058_);
lean_dec(v___x_3057_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 3, v___x_3053_);
v___x_3061_ = v___x_3049_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_var_3042_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v_irrelevant_3043_);
lean_ctor_set(v_reuseFailAlloc_3062_, 2, v_lowerBounds_3044_);
lean_ctor_set(v_reuseFailAlloc_3062_, 3, v___x_3053_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, sizeof(void*)*4, v_lowerExact_3046_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_ctor_set_uint8(v___x_3061_, sizeof(void*)*4 + 1, v___x_3059_);
return v___x_3061_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(lean_object* v_upperBound_3067_, lean_object* v_coeffs_3068_, lean_object* v_constraint_3069_, lean_object* v_b_3070_, lean_object* v_a_3071_, lean_object* v_b_3072_){
_start:
{
lean_object* v_a_3074_; uint8_t v___x_3078_; 
v___x_3078_ = lean_nat_dec_lt(v_a_3071_, v_upperBound_3067_);
if (v___x_3078_ == 0)
{
lean_dec(v_a_3071_);
lean_dec_ref(v_b_3070_);
lean_dec_ref(v_constraint_3069_);
return v_b_3072_;
}
else
{
lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = lean_array_get_size(v_b_3072_);
v___x_3080_ = lean_nat_dec_lt(v_a_3071_, v___x_3079_);
if (v___x_3080_ == 0)
{
v_a_3074_ = v_b_3072_;
goto v___jp_3073_;
}
else
{
lean_object* v___x_3081_; lean_object* v_v_3082_; lean_object* v___x_3083_; lean_object* v_xs_x27_3084_; lean_object* v___y_3086_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
lean_inc(v_a_3071_);
v___x_3081_ = l_Lean_Omega_IntList_get(v_coeffs_3068_, v_a_3071_);
v_v_3082_ = lean_array_fget(v_b_3072_, v_a_3071_);
v___x_3083_ = lean_box(0);
v_xs_x27_3084_ = lean_array_fset(v_b_3072_, v_a_3071_, v___x_3083_);
v___x_3088_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3089_ = lean_int_dec_eq(v___x_3081_, v___x_3088_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v_lowerBound_3091_; 
lean_inc_ref(v_constraint_3069_);
lean_inc(v___x_3081_);
v___x_3090_ = l_Lean_Omega_Constraint_scale(v___x_3081_, v_constraint_3069_);
v_lowerBound_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_lowerBound_3091_);
if (lean_obj_tag(v_lowerBound_3091_) == 0)
{
lean_object* v___x_3092_; 
lean_inc_ref(v_b_3070_);
v___x_3092_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3090_, v_b_3070_, v___x_3081_, v___x_3083_, v_v_3082_);
v___y_3086_ = v___x_3092_;
goto v___jp_3085_;
}
else
{
lean_object* v_var_3093_; lean_object* v_irrelevant_3094_; lean_object* v_lowerBounds_3095_; lean_object* v_upperBounds_3096_; uint8_t v_lowerExact_3097_; uint8_t v_upperExact_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3113_; 
lean_dec_ref(v_lowerBound_3091_);
v_var_3093_ = lean_ctor_get(v_v_3082_, 0);
v_irrelevant_3094_ = lean_ctor_get(v_v_3082_, 1);
v_lowerBounds_3095_ = lean_ctor_get(v_v_3082_, 2);
v_upperBounds_3096_ = lean_ctor_get(v_v_3082_, 3);
v_lowerExact_3097_ = lean_ctor_get_uint8(v_v_3082_, sizeof(void*)*4);
v_upperExact_3098_ = lean_ctor_get_uint8(v_v_3082_, sizeof(void*)*4 + 1);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_v_3082_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3100_ = v_v_3082_;
v_isShared_3101_ = v_isSharedCheck_3113_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_upperBounds_3096_);
lean_inc(v_lowerBounds_3095_);
lean_inc(v_irrelevant_3094_);
lean_inc(v_var_3093_);
lean_dec(v_v_3082_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3113_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___y_3105_; 
lean_inc(v___x_3081_);
lean_inc_ref(v_b_3070_);
v___x_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3102_, 0, v_b_3070_);
lean_ctor_set(v___x_3102_, 1, v___x_3081_);
v___x_3103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
lean_ctor_set(v___x_3103_, 1, v_lowerBounds_3095_);
if (v_lowerExact_3097_ == 0)
{
v___y_3105_ = v_lowerExact_3097_;
goto v___jp_3104_;
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; 
v___x_3110_ = lean_nat_abs(v___x_3081_);
v___x_3111_ = lean_unsigned_to_nat(1u);
v___x_3112_ = lean_nat_dec_eq(v___x_3110_, v___x_3111_);
lean_dec(v___x_3110_);
v___y_3105_ = v___x_3112_;
goto v___jp_3104_;
}
v___jp_3104_:
{
lean_object* v___x_3107_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 2, v___x_3103_);
v___x_3107_ = v___x_3100_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_var_3093_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_irrelevant_3094_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3109_, 3, v_upperBounds_3096_);
lean_ctor_set_uint8(v_reuseFailAlloc_3109_, sizeof(void*)*4 + 1, v_upperExact_3098_);
v___x_3107_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v___x_3108_; 
lean_ctor_set_uint8(v___x_3107_, sizeof(void*)*4, v___y_3105_);
lean_inc_ref(v_b_3070_);
v___x_3108_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3090_, v_b_3070_, v___x_3081_, v___x_3083_, v___x_3107_);
v___y_3086_ = v___x_3108_;
goto v___jp_3085_;
}
}
}
}
}
else
{
lean_object* v_var_3114_; lean_object* v_irrelevant_3115_; lean_object* v_lowerBounds_3116_; lean_object* v_upperBounds_3117_; uint8_t v_lowerExact_3118_; uint8_t v_upperExact_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3127_; 
lean_dec(v___x_3081_);
v_var_3114_ = lean_ctor_get(v_v_3082_, 0);
v_irrelevant_3115_ = lean_ctor_get(v_v_3082_, 1);
v_lowerBounds_3116_ = lean_ctor_get(v_v_3082_, 2);
v_upperBounds_3117_ = lean_ctor_get(v_v_3082_, 3);
v_lowerExact_3118_ = lean_ctor_get_uint8(v_v_3082_, sizeof(void*)*4);
v_upperExact_3119_ = lean_ctor_get_uint8(v_v_3082_, sizeof(void*)*4 + 1);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_v_3082_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3121_ = v_v_3082_;
v_isShared_3122_ = v_isSharedCheck_3127_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_upperBounds_3117_);
lean_inc(v_lowerBounds_3116_);
lean_inc(v_irrelevant_3115_);
lean_inc(v_var_3114_);
lean_dec(v_v_3082_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3127_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v___x_3125_; 
lean_inc_ref(v_b_3070_);
v___x_3123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3123_, 0, v_b_3070_);
lean_ctor_set(v___x_3123_, 1, v_irrelevant_3115_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 1, v___x_3123_);
v___x_3125_ = v___x_3121_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_var_3114_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___x_3123_);
lean_ctor_set(v_reuseFailAlloc_3126_, 2, v_lowerBounds_3116_);
lean_ctor_set(v_reuseFailAlloc_3126_, 3, v_upperBounds_3117_);
lean_ctor_set_uint8(v_reuseFailAlloc_3126_, sizeof(void*)*4, v_lowerExact_3118_);
lean_ctor_set_uint8(v_reuseFailAlloc_3126_, sizeof(void*)*4 + 1, v_upperExact_3119_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
v___y_3086_ = v___x_3125_;
goto v___jp_3085_;
}
}
}
v___jp_3085_:
{
lean_object* v___x_3087_; 
v___x_3087_ = lean_array_fset(v_xs_x27_3084_, v_a_3071_, v___y_3086_);
v_a_3074_ = v___x_3087_;
goto v___jp_3073_;
}
}
}
v___jp_3073_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = lean_unsigned_to_nat(1u);
v___x_3076_ = lean_nat_add(v_a_3071_, v___x_3075_);
lean_dec(v_a_3071_);
v_a_3071_ = v___x_3076_;
v_b_3072_ = v_a_3074_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___boxed(lean_object* v_upperBound_3128_, lean_object* v_coeffs_3129_, lean_object* v_constraint_3130_, lean_object* v_b_3131_, lean_object* v_a_3132_, lean_object* v_b_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3128_, v_coeffs_3129_, v_constraint_3130_, v_b_3131_, v_a_3132_, v_b_3133_);
lean_dec(v_coeffs_3129_);
lean_dec(v_upperBound_3128_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(lean_object* v_n_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_){
_start:
{
if (lean_obj_tag(v_a_3136_) == 0)
{
lean_object* v___x_3138_; 
v___x_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3138_, 0, v_a_3137_);
return v___x_3138_;
}
else
{
lean_object* v_value_3139_; lean_object* v_tail_3140_; lean_object* v_coeffs_3141_; lean_object* v_constraint_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v_value_3139_ = lean_ctor_get(v_a_3136_, 1);
lean_inc(v_value_3139_);
v_tail_3140_ = lean_ctor_get(v_a_3136_, 2);
lean_inc(v_tail_3140_);
lean_dec_ref(v_a_3136_);
v_coeffs_3141_ = lean_ctor_get(v_value_3139_, 0);
lean_inc(v_coeffs_3141_);
v_constraint_3142_ = lean_ctor_get(v_value_3139_, 1);
lean_inc_ref(v_constraint_3142_);
v___x_3143_ = lean_unsigned_to_nat(0u);
v___x_3144_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_n_3135_, v_coeffs_3141_, v_constraint_3142_, v_value_3139_, v___x_3143_, v_a_3137_);
lean_dec(v_coeffs_3141_);
v_a_3136_ = v_tail_3140_;
v_a_3137_ = v___x_3144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1___boxed(lean_object* v_n_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3146_, v_a_3147_, v_a_3148_);
lean_dec(v_n_3146_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(lean_object* v_n_3150_, lean_object* v_as_3151_, size_t v_sz_3152_, size_t v_i_3153_, lean_object* v_b_3154_){
_start:
{
uint8_t v___x_3155_; 
v___x_3155_ = lean_usize_dec_lt(v_i_3153_, v_sz_3152_);
if (v___x_3155_ == 0)
{
return v_b_3154_;
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3157_; 
v_a_3156_ = lean_array_uget_borrowed(v_as_3151_, v_i_3153_);
lean_inc(v_a_3156_);
v___x_3157_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3150_, v_a_3156_, v_b_3154_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
lean_dec_ref(v___x_3157_);
return v_a_3158_;
}
else
{
lean_object* v_a_3159_; size_t v___x_3160_; size_t v___x_3161_; 
v_a_3159_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3159_);
lean_dec_ref(v___x_3157_);
v___x_3160_ = ((size_t)1ULL);
v___x_3161_ = lean_usize_add(v_i_3153_, v___x_3160_);
v_i_3153_ = v___x_3161_;
v_b_3154_ = v_a_3159_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3___boxed(lean_object* v_n_3163_, lean_object* v_as_3164_, lean_object* v_sz_3165_, lean_object* v_i_3166_, lean_object* v_b_3167_){
_start:
{
size_t v_sz_boxed_3168_; size_t v_i_boxed_3169_; lean_object* v_res_3170_; 
v_sz_boxed_3168_ = lean_unbox_usize(v_sz_3165_);
lean_dec(v_sz_3165_);
v_i_boxed_3169_ = lean_unbox_usize(v_i_3166_);
lean_dec(v_i_3166_);
v_res_3170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_n_3163_, v_as_3164_, v_sz_boxed_3168_, v_i_boxed_3169_, v_b_3167_);
lean_dec_ref(v_as_3164_);
lean_dec(v_n_3163_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(lean_object* v_p_3173_){
_start:
{
lean_object* v_constraints_3174_; lean_object* v_numVars_3175_; lean_object* v_buckets_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v_data_3179_; size_t v_sz_3180_; size_t v___x_3181_; lean_object* v___x_3182_; 
v_constraints_3174_ = lean_ctor_get(v_p_3173_, 2);
lean_inc_ref(v_constraints_3174_);
v_numVars_3175_ = lean_ctor_get(v_p_3173_, 1);
lean_inc(v_numVars_3175_);
lean_dec_ref(v_p_3173_);
v_buckets_3176_ = lean_ctor_get(v_constraints_3174_, 1);
lean_inc_ref(v_buckets_3176_);
lean_dec_ref(v_constraints_3174_);
v___x_3177_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
lean_inc(v_numVars_3175_);
v___x_3178_ = l_List_range(v_numVars_3175_);
v_data_3179_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v___x_3177_, v___x_3178_);
lean_dec(v___x_3178_);
v_sz_3180_ = lean_array_size(v_buckets_3176_);
v___x_3181_ = ((size_t)0ULL);
v___x_3182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_numVars_3175_, v_buckets_3176_, v_sz_3180_, v___x_3181_, v_data_3179_);
lean_dec_ref(v_buckets_3176_);
lean_dec(v_numVars_3175_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(lean_object* v_upperBound_3183_, lean_object* v_coeffs_3184_, lean_object* v_constraint_3185_, lean_object* v_b_3186_, lean_object* v_inst_3187_, lean_object* v_R_3188_, lean_object* v_a_3189_, lean_object* v_b_3190_, lean_object* v_c_3191_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3183_, v_coeffs_3184_, v_constraint_3185_, v_b_3186_, v_a_3189_, v_b_3190_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___boxed(lean_object* v_upperBound_3193_, lean_object* v_coeffs_3194_, lean_object* v_constraint_3195_, lean_object* v_b_3196_, lean_object* v_inst_3197_, lean_object* v_R_3198_, lean_object* v_a_3199_, lean_object* v_b_3200_, lean_object* v_c_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(v_upperBound_3193_, v_coeffs_3194_, v_constraint_3195_, v_b_3196_, v_inst_3197_, v_R_3198_, v_a_3199_, v_b_3200_, v_c_3201_);
lean_dec(v_coeffs_3194_);
lean_dec(v_upperBound_3193_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(lean_object* v_cls_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_options_3209_; uint8_t v_hasTrace_3210_; 
v_options_3209_ = lean_ctor_get(v___y_3207_, 2);
v_hasTrace_3210_ = lean_ctor_get_uint8(v_options_3209_, sizeof(void*)*1);
if (v_hasTrace_3210_ == 0)
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
lean_dec(v_cls_3206_);
v___x_3211_ = lean_box(v_hasTrace_3210_);
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
return v___x_3212_;
}
else
{
lean_object* v_inheritedTraceOptions_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; uint8_t v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v_inheritedTraceOptions_3213_ = lean_ctor_get(v___y_3207_, 13);
v___x_3214_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___closed__1));
v___x_3215_ = l_Lean_Name_append(v___x_3214_, v_cls_3206_);
v___x_3216_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3213_, v_options_3209_, v___x_3215_);
lean_dec(v___x_3215_);
v___x_3217_ = lean_box(v___x_3216_);
v___x_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
return v___x_3218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___boxed(lean_object* v_cls_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v_cls_3219_, v___y_3220_);
lean_dec_ref(v___y_3220_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(lean_object* v_cls_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v_cls_3223_, v___y_3226_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___boxed(lean_object* v_cls_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5(lean_object* v_as_3237_, size_t v_i_3238_, size_t v_stop_3239_, lean_object* v_b_3240_){
_start:
{
lean_object* v___y_3242_; uint8_t v___x_3246_; 
v___x_3246_ = lean_usize_dec_eq(v_i_3238_, v_stop_3239_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; uint8_t v___x_3250_; 
v___x_3247_ = lean_array_uget_borrowed(v_as_3237_, v_i_3238_);
v___x_3250_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v___x_3247_);
if (v___x_3250_ == 0)
{
goto v___jp_3248_;
}
else
{
if (v___x_3246_ == 0)
{
v___y_3242_ = v_b_3240_;
goto v___jp_3241_;
}
else
{
goto v___jp_3248_;
}
}
v___jp_3248_:
{
lean_object* v___x_3249_; 
lean_inc(v___x_3247_);
v___x_3249_ = lean_array_push(v_b_3240_, v___x_3247_);
v___y_3242_ = v___x_3249_;
goto v___jp_3241_;
}
}
else
{
return v_b_3240_;
}
v___jp_3241_:
{
size_t v___x_3243_; size_t v___x_3244_; 
v___x_3243_ = ((size_t)1ULL);
v___x_3244_ = lean_usize_add(v_i_3238_, v___x_3243_);
v_i_3238_ = v___x_3244_;
v_b_3240_ = v___y_3242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5___boxed(lean_object* v_as_3251_, lean_object* v_i_3252_, lean_object* v_stop_3253_, lean_object* v_b_3254_){
_start:
{
size_t v_i_boxed_3255_; size_t v_stop_boxed_3256_; lean_object* v_res_3257_; 
v_i_boxed_3255_ = lean_unbox_usize(v_i_3252_);
lean_dec(v_i_3252_);
v_stop_boxed_3256_ = lean_unbox_usize(v_stop_3253_);
lean_dec(v_stop_3253_);
v_res_3257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5(v_as_3251_, v_i_boxed_3255_, v_stop_boxed_3256_, v_b_3254_);
lean_dec_ref(v_as_3251_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0(lean_object* v___x_3258_, lean_object* v_fst_3259_, lean_object* v_snd_3260_, lean_object* v_fst_3261_, lean_object* v_____r_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3258_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v_fst_3259_);
lean_ctor_set(v___x_3269_, 1, v_snd_3260_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v_fst_3261_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3268_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
v___x_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0___boxed(lean_object* v___x_3274_, lean_object* v_fst_3275_, lean_object* v_snd_3276_, lean_object* v_fst_3277_, lean_object* v_____r_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0(v___x_3274_, v_fst_3275_, v_snd_3276_, v_fst_3277_, v_____r_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
return v_res_3284_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3285_; double v___x_3286_; 
v___x_3285_ = lean_unsigned_to_nat(0u);
v___x_3286_ = lean_float_of_nat(v___x_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object* v_cls_3289_, lean_object* v_msg_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v_ref_3296_; lean_object* v___x_3297_; lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3342_; 
v_ref_3296_ = lean_ctor_get(v___y_3293_, 5);
v___x_3297_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3300_ = v___x_3297_;
v_isShared_3301_ = v_isSharedCheck_3342_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3297_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3342_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3302_; lean_object* v_traceState_3303_; lean_object* v_env_3304_; lean_object* v_nextMacroScope_3305_; lean_object* v_ngen_3306_; lean_object* v_auxDeclNGen_3307_; lean_object* v_cache_3308_; lean_object* v_messages_3309_; lean_object* v_infoState_3310_; lean_object* v_snapshotTasks_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3341_; 
v___x_3302_ = lean_st_ref_take(v___y_3294_);
v_traceState_3303_ = lean_ctor_get(v___x_3302_, 4);
v_env_3304_ = lean_ctor_get(v___x_3302_, 0);
v_nextMacroScope_3305_ = lean_ctor_get(v___x_3302_, 1);
v_ngen_3306_ = lean_ctor_get(v___x_3302_, 2);
v_auxDeclNGen_3307_ = lean_ctor_get(v___x_3302_, 3);
v_cache_3308_ = lean_ctor_get(v___x_3302_, 5);
v_messages_3309_ = lean_ctor_get(v___x_3302_, 6);
v_infoState_3310_ = lean_ctor_get(v___x_3302_, 7);
v_snapshotTasks_3311_ = lean_ctor_get(v___x_3302_, 8);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3313_ = v___x_3302_;
v_isShared_3314_ = v_isSharedCheck_3341_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_snapshotTasks_3311_);
lean_inc(v_infoState_3310_);
lean_inc(v_messages_3309_);
lean_inc(v_cache_3308_);
lean_inc(v_traceState_3303_);
lean_inc(v_auxDeclNGen_3307_);
lean_inc(v_ngen_3306_);
lean_inc(v_nextMacroScope_3305_);
lean_inc(v_env_3304_);
lean_dec(v___x_3302_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3341_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
uint64_t v_tid_3315_; lean_object* v_traces_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3340_; 
v_tid_3315_ = lean_ctor_get_uint64(v_traceState_3303_, sizeof(void*)*1);
v_traces_3316_ = lean_ctor_get(v_traceState_3303_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_traceState_3303_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3318_ = v_traceState_3303_;
v_isShared_3319_ = v_isSharedCheck_3340_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_traces_3316_);
lean_dec(v_traceState_3303_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3340_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3320_; double v___x_3321_; uint8_t v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3330_; 
v___x_3320_ = lean_box(0);
v___x_3321_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0);
v___x_3322_ = 0;
v___x_3323_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_3324_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3324_, 0, v_cls_3289_);
lean_ctor_set(v___x_3324_, 1, v___x_3320_);
lean_ctor_set(v___x_3324_, 2, v___x_3323_);
lean_ctor_set_float(v___x_3324_, sizeof(void*)*3, v___x_3321_);
lean_ctor_set_float(v___x_3324_, sizeof(void*)*3 + 8, v___x_3321_);
lean_ctor_set_uint8(v___x_3324_, sizeof(void*)*3 + 16, v___x_3322_);
v___x_3325_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__1));
v___x_3326_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3324_);
lean_ctor_set(v___x_3326_, 1, v_a_3298_);
lean_ctor_set(v___x_3326_, 2, v___x_3325_);
lean_inc(v_ref_3296_);
v___x_3327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3327_, 0, v_ref_3296_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = l_Lean_PersistentArray_push___redArg(v_traces_3316_, v___x_3327_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3328_);
v___x_3330_ = v___x_3318_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3328_);
lean_ctor_set_uint64(v_reuseFailAlloc_3339_, sizeof(void*)*1, v_tid_3315_);
v___x_3330_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; 
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 4, v___x_3330_);
v___x_3332_ = v___x_3313_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_env_3304_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v_nextMacroScope_3305_);
lean_ctor_set(v_reuseFailAlloc_3338_, 2, v_ngen_3306_);
lean_ctor_set(v_reuseFailAlloc_3338_, 3, v_auxDeclNGen_3307_);
lean_ctor_set(v_reuseFailAlloc_3338_, 4, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3338_, 5, v_cache_3308_);
lean_ctor_set(v_reuseFailAlloc_3338_, 6, v_messages_3309_);
lean_ctor_set(v_reuseFailAlloc_3338_, 7, v_infoState_3310_);
lean_ctor_set(v_reuseFailAlloc_3338_, 8, v_snapshotTasks_3311_);
v___x_3332_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3333_ = lean_st_ref_set(v___y_3294_, v___x_3332_);
v___x_3334_ = lean_box(0);
if (v_isShared_3301_ == 0)
{
lean_ctor_set(v___x_3300_, 0, v___x_3334_);
v___x_3336_ = v___x_3300_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object* v_cls_3343_, lean_object* v_msg_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_cls_3343_, v_msg_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
return v_res_3350_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__0));
v___x_3353_ = l_Lean_stringToMessageData(v___x_3352_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg(lean_object* v_upperBound_3354_, lean_object* v___y_3355_, lean_object* v_a_3356_, lean_object* v_b_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v_a_3364_; lean_object* v___y_3369_; uint8_t v___x_3388_; 
v___x_3388_ = lean_nat_dec_lt(v_a_3356_, v_upperBound_3354_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; 
lean_dec(v_a_3356_);
v___x_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3389_, 0, v_b_3357_);
return v___x_3389_;
}
else
{
lean_object* v_snd_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3465_; 
v_snd_3390_ = lean_ctor_get(v_b_3357_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_b_3357_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v_b_3357_, 0);
lean_dec(v_unused_3466_);
v___x_3392_ = v_b_3357_;
v_isShared_3393_ = v_isSharedCheck_3465_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_snd_3390_);
lean_dec(v_b_3357_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3465_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v_snd_3394_; lean_object* v_fst_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3464_; 
v_snd_3394_ = lean_ctor_get(v_snd_3390_, 1);
v_fst_3395_ = lean_ctor_get(v_snd_3390_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_snd_3390_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3397_ = v_snd_3390_;
v_isShared_3398_ = v_isSharedCheck_3464_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_snd_3394_);
lean_inc(v_fst_3395_);
lean_dec(v_snd_3390_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3464_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v_fst_3399_; lean_object* v_snd_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3463_; 
v_fst_3399_ = lean_ctor_get(v_snd_3394_, 0);
v_snd_3400_ = lean_ctor_get(v_snd_3394_, 1);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_snd_3394_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3402_ = v_snd_3394_;
v_isShared_3403_ = v_isSharedCheck_3463_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_snd_3400_);
lean_inc(v_fst_3399_);
lean_dec(v_snd_3394_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3463_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v_bestIdx_3404_; lean_object* v___x_3405_; lean_object* v_cls_3416_; lean_object* v___x_3417_; uint8_t v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; uint8_t v___y_3457_; uint8_t v___y_3460_; 
v_bestIdx_3404_ = lean_unsigned_to_nat(0u);
v___x_3405_ = lean_box(0);
v_cls_3416_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_3417_ = lean_array_fget_borrowed(v___y_3355_, v_a_3356_);
v___x_3418_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_3417_);
v___x_3419_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_3417_);
v___x_3420_ = lean_nat_dec_eq(v___x_3419_, v_bestIdx_3404_);
if (v___x_3420_ == 0)
{
uint8_t v___x_3462_; 
v___x_3462_ = lean_unbox(v_snd_3400_);
if (v___x_3462_ == 0)
{
v___y_3460_ = v___x_3418_;
goto v___jp_3459_;
}
else
{
if (v___x_3420_ == 0)
{
v___y_3460_ = v___x_3420_;
goto v___jp_3459_;
}
else
{
v___y_3460_ = v___x_3418_;
goto v___jp_3459_;
}
}
}
else
{
v___y_3460_ = v___x_3420_;
goto v___jp_3459_;
}
v___jp_3406_:
{
lean_object* v___x_3408_; 
if (v_isShared_3403_ == 0)
{
v___x_3408_ = v___x_3402_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_fst_3399_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_snd_3400_);
v___x_3408_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3410_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 1, v___x_3408_);
v___x_3410_ = v___x_3397_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_fst_3395_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v___x_3408_);
v___x_3410_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3412_; 
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 1, v___x_3410_);
lean_ctor_set(v___x_3392_, 0, v___x_3405_);
v___x_3412_ = v___x_3392_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
v_a_3364_ = v___x_3412_;
goto v___jp_3363_;
}
}
}
}
v___jp_3421_:
{
if (v___x_3420_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
lean_dec(v_snd_3400_);
lean_dec(v_fst_3399_);
lean_dec(v_fst_3395_);
v___x_3422_ = lean_box(v___x_3418_);
v___x_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3419_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
lean_inc(v_a_3356_);
v___x_3424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3424_, 0, v_a_3356_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3405_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v_a_3364_ = v___x_3425_;
goto v___jp_3363_;
}
else
{
lean_object* v___x_3426_; 
lean_dec(v___x_3419_);
v___x_3426_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v_cls_3416_, v___y_3360_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; uint8_t v___x_3428_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref(v___x_3426_);
v___x_3428_ = lean_unbox(v_a_3427_);
lean_dec(v_a_3427_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = lean_box(0);
lean_inc(v___x_3417_);
v___x_3430_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0(v___x_3417_, v_fst_3399_, v_snd_3400_, v_fst_3395_, v___x_3429_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
v___y_3369_ = v___x_3430_;
goto v___jp_3368_;
}
else
{
lean_object* v_var_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v_var_3431_ = lean_ctor_get(v___x_3417_, 0);
v___x_3432_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1);
lean_inc(v_var_3431_);
v___x_3433_ = l_Nat_reprFast(v_var_3431_);
v___x_3434_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
v___x_3435_ = l_Lean_MessageData_ofFormat(v___x_3434_);
v___x_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3432_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_cls_3416_, v___x_3436_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref(v___x_3437_);
lean_inc(v___x_3417_);
v___x_3439_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0(v___x_3417_, v_fst_3399_, v_snd_3400_, v_fst_3395_, v_a_3438_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
v___y_3369_ = v___x_3439_;
goto v___jp_3368_;
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v_snd_3400_);
lean_dec(v_fst_3399_);
lean_dec(v_fst_3395_);
lean_dec(v_a_3356_);
v_a_3440_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3437_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3437_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec(v_snd_3400_);
lean_dec(v_fst_3399_);
lean_dec(v_fst_3395_);
lean_dec(v_a_3356_);
v_a_3448_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3426_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3426_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
}
v___jp_3456_:
{
if (v___y_3457_ == 0)
{
lean_dec(v___x_3419_);
goto v___jp_3406_;
}
else
{
uint8_t v___x_3458_; 
v___x_3458_ = lean_nat_dec_lt(v___x_3419_, v_fst_3399_);
if (v___x_3458_ == 0)
{
lean_dec(v___x_3419_);
goto v___jp_3406_;
}
else
{
lean_del_object(v___x_3402_);
lean_del_object(v___x_3397_);
lean_del_object(v___x_3392_);
goto v___jp_3421_;
}
}
}
v___jp_3459_:
{
if (v___y_3460_ == 0)
{
uint8_t v___x_3461_; 
v___x_3461_ = lean_unbox(v_snd_3400_);
if (v___x_3461_ == 0)
{
if (v___x_3418_ == 0)
{
v___y_3457_ = v___x_3388_;
goto v___jp_3456_;
}
else
{
lean_dec(v___x_3419_);
goto v___jp_3406_;
}
}
else
{
v___y_3457_ = v___x_3418_;
goto v___jp_3456_;
}
}
else
{
lean_del_object(v___x_3402_);
lean_del_object(v___x_3397_);
lean_del_object(v___x_3392_);
goto v___jp_3421_;
}
}
}
}
}
}
v___jp_3363_:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = lean_unsigned_to_nat(1u);
v___x_3366_ = lean_nat_add(v_a_3356_, v___x_3365_);
lean_dec(v_a_3356_);
v_a_3356_ = v___x_3366_;
v_b_3357_ = v_a_3364_;
goto _start;
}
v___jp_3368_:
{
if (lean_obj_tag(v___y_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3379_; 
v_a_3370_ = lean_ctor_get(v___y_3369_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___y_3369_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3372_ = v___y_3369_;
v_isShared_3373_ = v_isSharedCheck_3379_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___y_3369_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3379_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
if (lean_obj_tag(v_a_3370_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3376_; 
lean_dec(v_a_3356_);
v_a_3374_ = lean_ctor_get(v_a_3370_, 0);
lean_inc(v_a_3374_);
lean_dec_ref(v_a_3370_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v_a_3374_);
v___x_3376_ = v___x_3372_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3374_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
else
{
lean_object* v_a_3378_; 
lean_del_object(v___x_3372_);
v_a_3378_ = lean_ctor_get(v_a_3370_, 0);
lean_inc(v_a_3378_);
lean_dec_ref(v_a_3370_);
v_a_3364_ = v_a_3378_;
goto v___jp_3363_;
}
}
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_dec(v_a_3356_);
v_a_3380_ = lean_ctor_get(v___y_3369_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___y_3369_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___y_3369_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___y_3369_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___boxed(lean_object* v_upperBound_3467_, lean_object* v___y_3468_, lean_object* v_a_3469_, lean_object* v_b_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg(v_upperBound_3467_, v___y_3468_, v_a_3469_, v_b_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec_ref(v___y_3468_);
lean_dec(v_upperBound_3467_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(size_t v_sz_3477_, size_t v_i_3478_, lean_object* v_bs_3479_){
_start:
{
uint8_t v___x_3480_; 
v___x_3480_ = lean_usize_dec_lt(v_i_3478_, v_sz_3477_);
if (v___x_3480_ == 0)
{
return v_bs_3479_;
}
else
{
lean_object* v_v_3481_; lean_object* v_var_3482_; lean_object* v___x_3483_; lean_object* v_bs_x27_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; size_t v___x_3490_; size_t v___x_3491_; lean_object* v___x_3492_; 
v_v_3481_ = lean_array_uget(v_bs_3479_, v_i_3478_);
v_var_3482_ = lean_ctor_get(v_v_3481_, 0);
lean_inc(v_var_3482_);
v___x_3483_ = lean_unsigned_to_nat(0u);
v_bs_x27_3484_ = lean_array_uset(v_bs_3479_, v_i_3478_, v___x_3483_);
v___x_3485_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_v_3481_);
v___x_3486_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_v_3481_);
lean_dec(v_v_3481_);
v___x_3487_ = lean_box(v___x_3486_);
v___x_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3485_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
v___x_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3489_, 0, v_var_3482_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = ((size_t)1ULL);
v___x_3491_ = lean_usize_add(v_i_3478_, v___x_3490_);
v___x_3492_ = lean_array_uset(v_bs_x27_3484_, v_i_3478_, v___x_3489_);
v_i_3478_ = v___x_3491_;
v_bs_3479_ = v___x_3492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___boxed(lean_object* v_sz_3494_, lean_object* v_i_3495_, lean_object* v_bs_3496_){
_start:
{
size_t v_sz_boxed_3497_; size_t v_i_boxed_3498_; lean_object* v_res_3499_; 
v_sz_boxed_3497_ = lean_unbox_usize(v_sz_3494_);
lean_dec(v_sz_3494_);
v_i_boxed_3498_ = lean_unbox_usize(v_i_3495_);
lean_dec(v_i_3495_);
v_res_3499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v_sz_boxed_3497_, v_i_boxed_3498_, v_bs_3496_);
return v_res_3499_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__1));
v___x_3504_ = l_Lean_MessageData_ofFormat(v___x_3503_);
return v___x_3504_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = lean_box(1);
v___x_3506_ = l_Lean_MessageData_ofFormat(v___x_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(lean_object* v_a_3508_, lean_object* v_a_3509_){
_start:
{
if (lean_obj_tag(v_a_3508_) == 0)
{
lean_object* v___x_3510_; 
v___x_3510_ = l_List_reverse___redArg(v_a_3509_);
return v___x_3510_;
}
else
{
lean_object* v_head_3511_; lean_object* v_snd_3512_; lean_object* v_tail_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3560_; 
v_head_3511_ = lean_ctor_get(v_a_3508_, 0);
lean_inc(v_head_3511_);
v_snd_3512_ = lean_ctor_get(v_head_3511_, 1);
lean_inc(v_snd_3512_);
v_tail_3513_ = lean_ctor_get(v_a_3508_, 1);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_a_3508_);
if (v_isSharedCheck_3560_ == 0)
{
lean_object* v_unused_3561_; 
v_unused_3561_ = lean_ctor_get(v_a_3508_, 0);
lean_dec(v_unused_3561_);
v___x_3515_ = v_a_3508_;
v_isShared_3516_ = v_isSharedCheck_3560_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_tail_3513_);
lean_dec(v_a_3508_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3560_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v_fst_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3558_; 
v_fst_3517_ = lean_ctor_get(v_head_3511_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_head_3511_);
if (v_isSharedCheck_3558_ == 0)
{
lean_object* v_unused_3559_; 
v_unused_3559_ = lean_ctor_get(v_head_3511_, 1);
lean_dec(v_unused_3559_);
v___x_3519_ = v_head_3511_;
v_isShared_3520_ = v_isSharedCheck_3558_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_fst_3517_);
lean_dec(v_head_3511_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3558_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v_fst_3521_; lean_object* v_snd_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3557_; 
v_fst_3521_ = lean_ctor_get(v_snd_3512_, 0);
v_snd_3522_ = lean_ctor_get(v_snd_3512_, 1);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_snd_3512_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3524_ = v_snd_3512_;
v_isShared_3525_ = v_isSharedCheck_3557_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_snd_3522_);
lean_inc(v_fst_3521_);
lean_dec(v_snd_3512_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3557_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3526_ = l_Nat_reprFast(v_fst_3517_);
v___x_3527_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
v___x_3528_ = l_Lean_MessageData_ofFormat(v___x_3527_);
v___x_3529_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2);
if (v_isShared_3525_ == 0)
{
lean_ctor_set_tag(v___x_3524_, 7);
lean_ctor_set(v___x_3524_, 1, v___x_3529_);
lean_ctor_set(v___x_3524_, 0, v___x_3528_);
v___x_3531_ = v___x_3524_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3532_; lean_object* v___x_3534_; 
v___x_3532_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3);
if (v_isShared_3520_ == 0)
{
lean_ctor_set_tag(v___x_3519_, 7);
lean_ctor_set(v___x_3519_, 1, v___x_3532_);
lean_ctor_set(v___x_3519_, 0, v___x_3531_);
v___x_3534_ = v___x_3519_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3531_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___y_3541_; uint8_t v___x_3552_; 
v___x_3535_ = l_Nat_reprFast(v_fst_3521_);
v___x_3536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
v___x_3537_ = l_Lean_MessageData_ofFormat(v___x_3536_);
v___x_3538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
lean_ctor_set(v___x_3538_, 1, v___x_3529_);
v___x_3539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
lean_ctor_set(v___x_3539_, 1, v___x_3532_);
v___x_3552_ = lean_unbox(v_snd_3522_);
lean_dec(v_snd_3522_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3553_; 
v___x_3553_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__4));
v___y_3541_ = v___x_3553_;
goto v___jp_3540_;
}
else
{
lean_object* v___x_3554_; 
v___x_3554_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4));
v___y_3541_ = v___x_3554_;
goto v___jp_3540_;
}
v___jp_3540_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3549_; 
v___x_3542_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3542_, 0, v___y_3541_);
v___x_3543_ = l_Lean_MessageData_ofFormat(v___x_3542_);
v___x_3544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3539_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = l_Lean_MessageData_paren(v___x_3544_);
v___x_3546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3534_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = l_Lean_MessageData_paren(v___x_3546_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 1, v_a_3509_);
lean_ctor_set(v___x_3515_, 0, v___x_3547_);
v___x_3549_ = v___x_3515_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3547_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v_a_3509_);
v___x_3549_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
v_a_3508_ = v_tail_3513_;
v_a_3509_ = v___x_3549_;
goto _start;
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0));
v___x_3564_ = l_Lean_stringToMessageData(v___x_3563_);
return v___x_3564_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2));
v___x_3567_ = l_Lean_stringToMessageData(v___x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(lean_object* v_data_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_){
_start:
{
lean_object* v___x_3574_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v_bestIdx_3580_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3698_; lean_object* v___x_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v___x_3574_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default));
v_bestIdx_3580_ = lean_unsigned_to_nat(0u);
v___x_3721_ = lean_array_get_size(v_data_3568_);
v___x_3722_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_3723_ = lean_nat_dec_lt(v_bestIdx_3580_, v___x_3721_);
if (v___x_3723_ == 0)
{
v___y_3698_ = v___x_3722_;
goto v___jp_3697_;
}
else
{
uint8_t v___x_3724_; 
v___x_3724_ = lean_nat_dec_le(v___x_3721_, v___x_3721_);
if (v___x_3724_ == 0)
{
if (v___x_3723_ == 0)
{
v___y_3698_ = v___x_3722_;
goto v___jp_3697_;
}
else
{
size_t v___x_3725_; size_t v___x_3726_; lean_object* v___x_3727_; 
v___x_3725_ = ((size_t)0ULL);
v___x_3726_ = lean_usize_of_nat(v___x_3721_);
v___x_3727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5(v_data_3568_, v___x_3725_, v___x_3726_, v___x_3722_);
v___y_3698_ = v___x_3727_;
goto v___jp_3697_;
}
}
else
{
size_t v___x_3728_; size_t v___x_3729_; lean_object* v___x_3730_; 
v___x_3728_ = ((size_t)0ULL);
v___x_3729_ = lean_usize_of_nat(v___x_3721_);
v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5(v_data_3568_, v___x_3728_, v___x_3729_, v___x_3722_);
v___y_3698_ = v___x_3730_;
goto v___jp_3697_;
}
}
v___jp_3575_:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = lean_array_get(v___x_3574_, v___y_3576_, v___y_3577_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
v___x_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3578_);
return v___x_3579_;
}
v___jp_3581_:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; 
v___x_3588_ = lean_array_get_borrowed(v___x_3574_, v___y_3582_, v_bestIdx_3580_);
v___x_3589_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_3588_);
v___x_3590_ = lean_nat_dec_eq(v___x_3589_, v_bestIdx_3580_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3591_ = lean_unsigned_to_nat(1u);
v___x_3592_ = lean_array_get_size(v___y_3582_);
v___x_3593_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_3588_);
v___x_3594_ = lean_box(0);
v___x_3595_ = lean_box(v___x_3593_);
v___x_3596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3589_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3597_, 0, v_bestIdx_3580_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3594_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg(v___x_3592_, v___y_3582_, v___x_3591_, v___x_3598_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3653_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3602_ = v___x_3599_;
v_isShared_3603_ = v_isSharedCheck_3653_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3599_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3653_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v_fst_3604_; 
v_fst_3604_ = lean_ctor_get(v_a_3600_, 0);
if (lean_obj_tag(v_fst_3604_) == 0)
{
lean_object* v_snd_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3647_; 
lean_del_object(v___x_3602_);
v_snd_3605_ = lean_ctor_get(v_a_3600_, 1);
v_isSharedCheck_3647_ = !lean_is_exclusive(v_a_3600_);
if (v_isSharedCheck_3647_ == 0)
{
lean_object* v_unused_3648_; 
v_unused_3648_ = lean_ctor_get(v_a_3600_, 0);
lean_dec(v_unused_3648_);
v___x_3607_ = v_a_3600_;
v_isShared_3608_ = v_isSharedCheck_3647_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_snd_3605_);
lean_dec(v_a_3600_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3647_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3646_; 
lean_inc(v___y_3583_);
v___x_3609_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v___y_3583_, v___y_3586_);
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3612_ = v___x_3609_;
v_isShared_3613_ = v_isSharedCheck_3646_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3609_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3646_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
uint8_t v___x_3614_; 
v___x_3614_ = lean_unbox(v_a_3610_);
lean_dec(v_a_3610_);
if (v___x_3614_ == 0)
{
lean_object* v_fst_3615_; 
lean_del_object(v___x_3612_);
lean_del_object(v___x_3607_);
lean_dec(v___y_3583_);
v_fst_3615_ = lean_ctor_get(v_snd_3605_, 0);
lean_inc(v_fst_3615_);
lean_dec(v_snd_3605_);
v___y_3576_ = v___y_3582_;
v___y_3577_ = v_fst_3615_;
goto v___jp_3575_;
}
else
{
lean_object* v_fst_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3644_; 
v_fst_3616_ = lean_ctor_get(v_snd_3605_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v_snd_3605_);
if (v_isSharedCheck_3644_ == 0)
{
lean_object* v_unused_3645_; 
v_unused_3645_ = lean_ctor_get(v_snd_3605_, 1);
lean_dec(v_unused_3645_);
v___x_3618_ = v_snd_3605_;
v_isShared_3619_ = v_isSharedCheck_3644_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_fst_3616_);
lean_dec(v_snd_3605_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3644_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3620_; lean_object* v_var_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3625_; 
v___x_3620_ = lean_array_get_borrowed(v___x_3574_, v___y_3582_, v_fst_3616_);
v_var_3621_ = lean_ctor_get(v___x_3620_, 0);
v___x_3622_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1);
lean_inc(v_var_3621_);
v___x_3623_ = l_Nat_reprFast(v_var_3621_);
if (v_isShared_3613_ == 0)
{
lean_ctor_set_tag(v___x_3612_, 3);
lean_ctor_set(v___x_3612_, 0, v___x_3623_);
v___x_3625_ = v___x_3612_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3623_);
v___x_3625_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___x_3626_; lean_object* v___x_3628_; 
v___x_3626_ = l_Lean_MessageData_ofFormat(v___x_3625_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set_tag(v___x_3618_, 7);
lean_ctor_set(v___x_3618_, 1, v___x_3626_);
lean_ctor_set(v___x_3618_, 0, v___x_3622_);
v___x_3628_ = v___x_3618_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3622_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v___x_3626_);
v___x_3628_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3629_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 7);
lean_ctor_set(v___x_3607_, 1, v___x_3629_);
lean_ctor_set(v___x_3607_, 0, v___x_3628_);
v___x_3631_ = v___x_3607_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3641_, 1, v___x_3629_);
v___x_3631_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v___y_3583_, v___x_3631_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_dec_ref(v___x_3632_);
v___y_3576_ = v___y_3582_;
v___y_3577_ = v_fst_3616_;
goto v___jp_3575_;
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v_fst_3616_);
lean_dec_ref(v___y_3582_);
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_val_3649_; lean_object* v___x_3651_; 
lean_inc_ref(v_fst_3604_);
lean_dec(v_a_3600_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
v_val_3649_ = lean_ctor_get(v_fst_3604_, 0);
lean_inc(v_val_3649_);
lean_dec_ref(v_fst_3604_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 0, v_val_3649_);
v___x_3651_ = v___x_3602_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_val_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
v_a_3654_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3599_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3599_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
else
{
lean_object* v___x_3662_; lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3696_; 
lean_inc(v___x_3588_);
lean_dec(v___x_3589_);
lean_dec_ref(v___y_3582_);
lean_inc(v___y_3583_);
v___x_3662_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v___y_3583_, v___y_3586_);
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3665_ = v___x_3662_;
v_isShared_3666_ = v_isSharedCheck_3696_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3662_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3696_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
uint8_t v___x_3667_; 
v___x_3667_ = lean_unbox(v_a_3663_);
lean_dec(v_a_3663_);
if (v___x_3667_ == 0)
{
lean_object* v___x_3669_; 
lean_dec(v___y_3583_);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v___x_3588_);
v___x_3669_ = v___x_3665_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3588_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
else
{
lean_object* v_var_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
lean_del_object(v___x_3665_);
v_var_3671_ = lean_ctor_get(v___x_3588_, 0);
v___x_3672_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1);
lean_inc(v_var_3671_);
v___x_3673_ = l_Nat_reprFast(v_var_3671_);
v___x_3674_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
v___x_3675_ = l_Lean_MessageData_ofFormat(v___x_3674_);
v___x_3676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3672_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
v___x_3677_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
v___x_3678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3676_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
v___x_3679_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v___y_3583_, v___x_3678_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3686_ == 0)
{
lean_object* v_unused_3687_; 
v_unused_3687_ = lean_ctor_get(v___x_3679_, 0);
lean_dec(v_unused_3687_);
v___x_3681_ = v___x_3679_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_dec(v___x_3679_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v___x_3588_);
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3588_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec(v___x_3588_);
v_a_3688_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3679_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3679_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
}
}
}
v___jp_3697_:
{
lean_object* v_cls_3699_; lean_object* v___x_3700_; lean_object* v_a_3701_; uint8_t v___x_3702_; 
v_cls_3699_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_3700_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v_cls_3699_, v_a_3571_);
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref(v___x_3700_);
v___x_3702_ = lean_unbox(v_a_3701_);
lean_dec(v_a_3701_);
if (v___x_3702_ == 0)
{
v___y_3582_ = v___y_3698_;
v___y_3583_ = v_cls_3699_;
v___y_3584_ = v_a_3569_;
v___y_3585_ = v_a_3570_;
v___y_3586_ = v_a_3571_;
v___y_3587_ = v_a_3572_;
goto v___jp_3581_;
}
else
{
lean_object* v___x_3703_; size_t v_sz_3704_; size_t v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3703_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3);
v_sz_3704_ = lean_array_size(v___y_3698_);
v___x_3705_ = ((size_t)0ULL);
lean_inc_ref(v___y_3698_);
v___x_3706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v_sz_3704_, v___x_3705_, v___y_3698_);
v___x_3707_ = lean_array_to_list(v___x_3706_);
v___x_3708_ = lean_box(0);
v___x_3709_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v___x_3707_, v___x_3708_);
v___x_3710_ = l_Lean_MessageData_ofList(v___x_3709_);
v___x_3711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3703_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___x_3712_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_cls_3699_, v___x_3711_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_dec_ref(v___x_3712_);
v___y_3582_ = v___y_3698_;
v___y_3583_ = v_cls_3699_;
v___y_3584_ = v_a_3569_;
v___y_3585_ = v_a_3570_;
v___y_3586_ = v_a_3571_;
v___y_3587_ = v_a_3572_;
goto v___jp_3581_;
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_dec_ref(v___y_3698_);
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object* v_data_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec_ref(v_data_3731_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(lean_object* v_upperBound_3738_, lean_object* v___y_3739_, lean_object* v_inst_3740_, lean_object* v_R_3741_, lean_object* v_a_3742_, lean_object* v_b_3743_, lean_object* v_c_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg(v_upperBound_3738_, v___y_3739_, v_a_3742_, v_b_3743_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___boxed(lean_object* v_upperBound_3751_, lean_object* v___y_3752_, lean_object* v_inst_3753_, lean_object* v_R_3754_, lean_object* v_a_3755_, lean_object* v_b_3756_, lean_object* v_c_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_upperBound_3751_, v___y_3752_, v_inst_3753_, v_R_3754_, v_a_3755_, v_b_3756_, v_c_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec_ref(v___y_3752_);
lean_dec(v_upperBound_3751_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(lean_object* v_snd_3764_, lean_object* v_fst_3765_, lean_object* v_as_x27_3766_, lean_object* v_b_3767_){
_start:
{
if (lean_obj_tag(v_as_x27_3766_) == 0)
{
lean_object* v___x_3769_; 
lean_dec_ref(v_fst_3765_);
v___x_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3769_, 0, v_b_3767_);
return v___x_3769_;
}
else
{
lean_object* v_head_3770_; lean_object* v_tail_3771_; lean_object* v_fst_3772_; lean_object* v_snd_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v_head_3770_ = lean_ctor_get(v_as_x27_3766_, 0);
lean_inc(v_head_3770_);
v_tail_3771_ = lean_ctor_get(v_as_x27_3766_, 1);
lean_inc(v_tail_3771_);
lean_dec_ref(v_as_x27_3766_);
v_fst_3772_ = lean_ctor_get(v_head_3770_, 0);
lean_inc(v_fst_3772_);
v_snd_3773_ = lean_ctor_get(v_head_3770_, 1);
lean_inc(v_snd_3773_);
lean_dec(v_head_3770_);
v___x_3774_ = lean_int_neg(v_snd_3764_);
lean_inc_ref(v_fst_3765_);
v___x_3775_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_snd_3773_, v_fst_3765_, v___x_3774_, v_fst_3772_);
v___x_3776_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_3775_);
v___x_3777_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_b_3767_, v___x_3776_);
v_as_x27_3766_ = v_tail_3771_;
v_b_3767_ = v___x_3777_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg___boxed(lean_object* v_snd_3779_, lean_object* v_fst_3780_, lean_object* v_as_x27_3781_, lean_object* v_b_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_3779_, v_fst_3780_, v_as_x27_3781_, v_b_3782_);
lean_dec(v_snd_3779_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(lean_object* v_upperBounds_3785_, lean_object* v_as_x27_3786_, lean_object* v_b_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
if (lean_obj_tag(v_as_x27_3786_) == 0)
{
lean_object* v___x_3793_; 
lean_dec(v_upperBounds_3785_);
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v_b_3787_);
return v___x_3793_;
}
else
{
lean_object* v_head_3794_; lean_object* v_tail_3795_; lean_object* v_fst_3796_; lean_object* v_snd_3797_; lean_object* v___x_3798_; lean_object* v_a_3799_; 
v_head_3794_ = lean_ctor_get(v_as_x27_3786_, 0);
lean_inc(v_head_3794_);
v_tail_3795_ = lean_ctor_get(v_as_x27_3786_, 1);
lean_inc(v_tail_3795_);
lean_dec_ref(v_as_x27_3786_);
v_fst_3796_ = lean_ctor_get(v_head_3794_, 0);
lean_inc(v_fst_3796_);
v_snd_3797_ = lean_ctor_get(v_head_3794_, 1);
lean_inc(v_snd_3797_);
lean_dec(v_head_3794_);
lean_inc(v_upperBounds_3785_);
v___x_3798_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_3797_, v_fst_3796_, v_upperBounds_3785_, v_b_3787_);
lean_dec(v_snd_3797_);
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3799_);
lean_dec_ref(v___x_3798_);
v_as_x27_3786_ = v_tail_3795_;
v_b_3787_ = v_a_3799_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg___boxed(lean_object* v_upperBounds_3801_, lean_object* v_as_x27_3802_, lean_object* v_b_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_3801_, v_as_x27_3802_, v_b_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(lean_object* v_as_x27_3810_, lean_object* v_b_3811_){
_start:
{
if (lean_obj_tag(v_as_x27_3810_) == 0)
{
lean_object* v___x_3813_; 
v___x_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3813_, 0, v_b_3811_);
return v___x_3813_;
}
else
{
lean_object* v_head_3814_; lean_object* v_tail_3815_; lean_object* v___x_3816_; 
v_head_3814_ = lean_ctor_get(v_as_x27_3810_, 0);
lean_inc(v_head_3814_);
v_tail_3815_ = lean_ctor_get(v_as_x27_3810_, 1);
lean_inc(v_tail_3815_);
lean_dec_ref(v_as_x27_3810_);
v___x_3816_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_b_3811_, v_head_3814_);
v_as_x27_3810_ = v_tail_3815_;
v_b_3811_ = v___x_3816_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg___boxed(lean_object* v_as_x27_3818_, lean_object* v_b_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_3818_, v_b_3819_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(lean_object* v_p_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_){
_start:
{
lean_object* v_data_3828_; lean_object* v___x_3829_; 
lean_inc_ref(v_p_3822_);
v_data_3828_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(v_p_3822_);
v___x_3829_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_3828_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_);
lean_dec_ref(v_data_3828_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v_irrelevant_3831_; lean_object* v_lowerBounds_3832_; lean_object* v_upperBounds_3833_; lean_object* v_assumptions_3834_; lean_object* v_eliminations_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3850_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
lean_dec_ref(v___x_3829_);
v_irrelevant_3831_ = lean_ctor_get(v_a_3830_, 1);
lean_inc(v_irrelevant_3831_);
v_lowerBounds_3832_ = lean_ctor_get(v_a_3830_, 2);
lean_inc(v_lowerBounds_3832_);
v_upperBounds_3833_ = lean_ctor_get(v_a_3830_, 3);
lean_inc(v_upperBounds_3833_);
lean_dec(v_a_3830_);
v_assumptions_3834_ = lean_ctor_get(v_p_3822_, 0);
v_eliminations_3835_ = lean_ctor_get(v_p_3822_, 4);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_p_3822_);
if (v_isSharedCheck_3850_ == 0)
{
lean_object* v_unused_3851_; lean_object* v_unused_3852_; lean_object* v_unused_3853_; lean_object* v_unused_3854_; lean_object* v_unused_3855_; 
v_unused_3851_ = lean_ctor_get(v_p_3822_, 6);
lean_dec(v_unused_3851_);
v_unused_3852_ = lean_ctor_get(v_p_3822_, 5);
lean_dec(v_unused_3852_);
v_unused_3853_ = lean_ctor_get(v_p_3822_, 3);
lean_dec(v_unused_3853_);
v_unused_3854_ = lean_ctor_get(v_p_3822_, 2);
lean_dec(v_unused_3854_);
v_unused_3855_ = lean_ctor_get(v_p_3822_, 1);
lean_dec(v_unused_3855_);
v___x_3837_ = v_p_3822_;
v_isShared_3838_ = v_isSharedCheck_3850_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_eliminations_3835_);
lean_inc(v_assumptions_3834_);
lean_dec(v_p_3822_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3850_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; uint8_t v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3839_ = lean_unsigned_to_nat(0u);
v___x_3840_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v___x_3841_ = 1;
v___x_3842_ = lean_box(0);
v___x_3843_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 6, v___x_3843_);
lean_ctor_set(v___x_3837_, 5, v___x_3842_);
lean_ctor_set(v___x_3837_, 3, v___x_3840_);
lean_ctor_set(v___x_3837_, 2, v___x_3840_);
lean_ctor_set(v___x_3837_, 1, v___x_3839_);
v___x_3845_ = v___x_3837_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_assumptions_3834_);
lean_ctor_set(v_reuseFailAlloc_3849_, 1, v___x_3839_);
lean_ctor_set(v_reuseFailAlloc_3849_, 2, v___x_3840_);
lean_ctor_set(v_reuseFailAlloc_3849_, 3, v___x_3840_);
lean_ctor_set(v_reuseFailAlloc_3849_, 4, v_eliminations_3835_);
lean_ctor_set(v_reuseFailAlloc_3849_, 5, v___x_3842_);
lean_ctor_set(v_reuseFailAlloc_3849_, 6, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; lean_object* v_a_3847_; lean_object* v___x_3848_; 
lean_ctor_set_uint8(v___x_3845_, sizeof(void*)*7, v___x_3841_);
v___x_3846_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_irrelevant_3831_, v___x_3845_);
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref(v___x_3846_);
v___x_3848_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_3833_, v_lowerBounds_3832_, v_a_3847_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_);
return v___x_3848_;
}
}
}
else
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
lean_dec_ref(v_p_3822_);
v_a_3856_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3829_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3829_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin___boxed(lean_object* v_p_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(lean_object* v_snd_3871_, lean_object* v_fst_3872_, lean_object* v_as_3873_, lean_object* v_as_x27_3874_, lean_object* v_b_3875_, lean_object* v_a_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_3871_, v_fst_3872_, v_as_x27_3874_, v_b_3875_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___boxed(lean_object* v_snd_3883_, lean_object* v_fst_3884_, lean_object* v_as_3885_, lean_object* v_as_x27_3886_, lean_object* v_b_3887_, lean_object* v_a_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(v_snd_3883_, v_fst_3884_, v_as_3885_, v_as_x27_3886_, v_b_3887_, v_a_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v_as_3885_);
lean_dec(v_snd_3883_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(lean_object* v_as_3895_, lean_object* v_as_x27_3896_, lean_object* v_b_3897_, lean_object* v_a_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_3896_, v_b_3897_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___boxed(lean_object* v_as_3905_, lean_object* v_as_x27_3906_, lean_object* v_b_3907_, lean_object* v_a_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(v_as_3905_, v_as_x27_3906_, v_b_3907_, v_a_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v_as_3905_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(lean_object* v_upperBounds_3915_, lean_object* v_as_3916_, lean_object* v_as_x27_3917_, lean_object* v_b_3918_, lean_object* v_a_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_3915_, v_as_x27_3917_, v_b_3918_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___boxed(lean_object* v_upperBounds_3926_, lean_object* v_as_3927_, lean_object* v_as_x27_3928_, lean_object* v_b_3929_, lean_object* v_a_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(v_upperBounds_3926_, v_as_3927_, v_as_x27_3928_, v_b_3929_, v_a_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v_as_3927_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object* v_cls_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_options_3940_; uint8_t v_hasTrace_3941_; 
v_options_3940_ = lean_ctor_get(v___y_3938_, 2);
v_hasTrace_3941_ = lean_ctor_get_uint8(v_options_3940_, sizeof(void*)*1);
if (v_hasTrace_3941_ == 0)
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
lean_dec(v_cls_3937_);
v___x_3942_ = lean_box(v_hasTrace_3941_);
v___x_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
return v___x_3943_;
}
else
{
lean_object* v_inheritedTraceOptions_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; uint8_t v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v_inheritedTraceOptions_3944_ = lean_ctor_get(v___y_3938_, 13);
v___x_3945_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___closed__1));
v___x_3946_ = l_Lean_Name_append(v___x_3945_, v_cls_3937_);
v___x_3947_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3944_, v_options_3940_, v___x_3946_);
lean_dec(v___x_3946_);
v___x_3948_ = lean_box(v___x_3947_);
v___x_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
return v___x_3949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg___boxed(lean_object* v_cls_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_3950_, v___y_3951_);
lean_dec_ref(v___y_3951_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(lean_object* v_cls_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, uint8_t v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_3954_, v___y_3962_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___boxed(lean_object* v_cls_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
uint8_t v___y_14583__boxed_3977_; lean_object* v_res_3978_; 
v___y_14583__boxed_3977_ = lean_unbox(v___y_3970_);
v_res_3978_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(v_cls_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_14583__boxed_3977_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec(v___y_3967_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object* v_x_3979_, lean_object* v_x_3980_){
_start:
{
if (lean_obj_tag(v_x_3980_) == 0)
{
lean_inc(v_x_3979_);
return v_x_3979_;
}
else
{
lean_object* v_key_3981_; lean_object* v_value_3982_; lean_object* v_tail_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_key_3981_ = lean_ctor_get(v_x_3980_, 0);
v_value_3982_ = lean_ctor_get(v_x_3980_, 1);
v_tail_3983_ = lean_ctor_get(v_x_3980_, 2);
v___x_3984_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_x_3979_, v_tail_3983_);
lean_inc(v_value_3982_);
lean_inc(v_key_3981_);
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v_key_3981_);
lean_ctor_set(v___x_3985_, 1, v_value_3982_);
v___x_3986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
lean_ctor_set(v___x_3986_, 1, v___x_3984_);
return v___x_3986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object* v_x_3987_, lean_object* v_x_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_x_3987_, v_x_3988_);
lean_dec(v_x_3988_);
lean_dec(v_x_3987_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4(lean_object* v_as_3990_, size_t v_i_3991_, size_t v_stop_3992_, lean_object* v_b_3993_){
_start:
{
uint8_t v___x_3994_; 
v___x_3994_ = lean_usize_dec_eq(v_i_3991_, v_stop_3992_);
if (v___x_3994_ == 0)
{
size_t v___x_3995_; size_t v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3995_ = ((size_t)1ULL);
v___x_3996_ = lean_usize_sub(v_i_3991_, v___x_3995_);
v___x_3997_ = lean_array_uget_borrowed(v_as_3990_, v___x_3996_);
v___x_3998_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_b_3993_, v___x_3997_);
lean_dec(v_b_3993_);
v_i_3991_ = v___x_3996_;
v_b_3993_ = v___x_3998_;
goto _start;
}
else
{
return v_b_3993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4___boxed(lean_object* v_as_4000_, lean_object* v_i_4001_, lean_object* v_stop_4002_, lean_object* v_b_4003_){
_start:
{
size_t v_i_boxed_4004_; size_t v_stop_boxed_4005_; lean_object* v_res_4006_; 
v_i_boxed_4004_ = lean_unbox_usize(v_i_4001_);
lean_dec(v_i_4001_);
v_stop_boxed_4005_ = lean_unbox_usize(v_stop_4002_);
lean_dec(v_stop_4002_);
v_res_4006_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4(v_as_4000_, v_i_boxed_4004_, v_stop_boxed_4005_, v_b_4003_);
lean_dec_ref(v_as_4000_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(lean_object* v_cls_4007_, lean_object* v_msg_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_ref_4014_; lean_object* v___x_4015_; lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4060_; 
v_ref_4014_ = lean_ctor_get(v___y_4011_, 5);
v___x_4015_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4018_ = v___x_4015_;
v_isShared_4019_ = v_isSharedCheck_4060_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4015_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4060_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4020_; lean_object* v_traceState_4021_; lean_object* v_env_4022_; lean_object* v_nextMacroScope_4023_; lean_object* v_ngen_4024_; lean_object* v_auxDeclNGen_4025_; lean_object* v_cache_4026_; lean_object* v_messages_4027_; lean_object* v_infoState_4028_; lean_object* v_snapshotTasks_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4059_; 
v___x_4020_ = lean_st_ref_take(v___y_4012_);
v_traceState_4021_ = lean_ctor_get(v___x_4020_, 4);
v_env_4022_ = lean_ctor_get(v___x_4020_, 0);
v_nextMacroScope_4023_ = lean_ctor_get(v___x_4020_, 1);
v_ngen_4024_ = lean_ctor_get(v___x_4020_, 2);
v_auxDeclNGen_4025_ = lean_ctor_get(v___x_4020_, 3);
v_cache_4026_ = lean_ctor_get(v___x_4020_, 5);
v_messages_4027_ = lean_ctor_get(v___x_4020_, 6);
v_infoState_4028_ = lean_ctor_get(v___x_4020_, 7);
v_snapshotTasks_4029_ = lean_ctor_get(v___x_4020_, 8);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4031_ = v___x_4020_;
v_isShared_4032_ = v_isSharedCheck_4059_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_snapshotTasks_4029_);
lean_inc(v_infoState_4028_);
lean_inc(v_messages_4027_);
lean_inc(v_cache_4026_);
lean_inc(v_traceState_4021_);
lean_inc(v_auxDeclNGen_4025_);
lean_inc(v_ngen_4024_);
lean_inc(v_nextMacroScope_4023_);
lean_inc(v_env_4022_);
lean_dec(v___x_4020_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4059_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
uint64_t v_tid_4033_; lean_object* v_traces_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4058_; 
v_tid_4033_ = lean_ctor_get_uint64(v_traceState_4021_, sizeof(void*)*1);
v_traces_4034_ = lean_ctor_get(v_traceState_4021_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v_traceState_4021_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4036_ = v_traceState_4021_;
v_isShared_4037_ = v_isSharedCheck_4058_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_traces_4034_);
lean_dec(v_traceState_4021_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4058_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4038_; double v___x_4039_; uint8_t v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4048_; 
v___x_4038_ = lean_box(0);
v___x_4039_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0);
v___x_4040_ = 0;
v___x_4041_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4042_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4042_, 0, v_cls_4007_);
lean_ctor_set(v___x_4042_, 1, v___x_4038_);
lean_ctor_set(v___x_4042_, 2, v___x_4041_);
lean_ctor_set_float(v___x_4042_, sizeof(void*)*3, v___x_4039_);
lean_ctor_set_float(v___x_4042_, sizeof(void*)*3 + 8, v___x_4039_);
lean_ctor_set_uint8(v___x_4042_, sizeof(void*)*3 + 16, v___x_4040_);
v___x_4043_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__1));
v___x_4044_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4042_);
lean_ctor_set(v___x_4044_, 1, v_a_4016_);
lean_ctor_set(v___x_4044_, 2, v___x_4043_);
lean_inc(v_ref_4014_);
v___x_4045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4045_, 0, v_ref_4014_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
v___x_4046_ = l_Lean_PersistentArray_push___redArg(v_traces_4034_, v___x_4045_);
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 0, v___x_4046_);
v___x_4048_ = v___x_4036_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4046_);
lean_ctor_set_uint64(v_reuseFailAlloc_4057_, sizeof(void*)*1, v_tid_4033_);
v___x_4048_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4050_; 
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 4, v___x_4048_);
v___x_4050_ = v___x_4031_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_env_4022_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_nextMacroScope_4023_);
lean_ctor_set(v_reuseFailAlloc_4056_, 2, v_ngen_4024_);
lean_ctor_set(v_reuseFailAlloc_4056_, 3, v_auxDeclNGen_4025_);
lean_ctor_set(v_reuseFailAlloc_4056_, 4, v___x_4048_);
lean_ctor_set(v_reuseFailAlloc_4056_, 5, v_cache_4026_);
lean_ctor_set(v_reuseFailAlloc_4056_, 6, v_messages_4027_);
lean_ctor_set(v_reuseFailAlloc_4056_, 7, v_infoState_4028_);
lean_ctor_set(v_reuseFailAlloc_4056_, 8, v_snapshotTasks_4029_);
v___x_4050_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4054_; 
v___x_4051_ = lean_st_ref_set(v___y_4012_, v___x_4050_);
v___x_4052_ = lean_box(0);
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 0, v___x_4052_);
v___x_4054_ = v___x_4018_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4052_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg___boxed(lean_object* v_cls_4061_, lean_object* v_msg_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(v_cls_4061_, v_msg_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object* v_a_4069_, lean_object* v_a_4070_){
_start:
{
if (lean_obj_tag(v_a_4069_) == 0)
{
lean_object* v___x_4071_; 
v___x_4071_ = l_List_reverse___redArg(v_a_4070_);
return v___x_4071_;
}
else
{
lean_object* v_head_4072_; lean_object* v_snd_4073_; lean_object* v_tail_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4089_; 
v_head_4072_ = lean_ctor_get(v_a_4069_, 0);
lean_inc(v_head_4072_);
v_snd_4073_ = lean_ctor_get(v_head_4072_, 1);
lean_inc(v_snd_4073_);
v_tail_4074_ = lean_ctor_get(v_a_4069_, 1);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_a_4069_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; 
v_unused_4090_ = lean_ctor_get(v_a_4069_, 0);
lean_dec(v_unused_4090_);
v___x_4076_ = v_a_4069_;
v_isShared_4077_ = v_isSharedCheck_4089_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_tail_4074_);
lean_dec(v_a_4069_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4089_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v_fst_4078_; lean_object* v_constraint_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4086_; 
v_fst_4078_ = lean_ctor_get(v_head_4072_, 0);
lean_inc(v_fst_4078_);
lean_dec(v_head_4072_);
v_constraint_4079_ = lean_ctor_get(v_snd_4073_, 1);
lean_inc_ref(v_constraint_4079_);
lean_dec(v_snd_4073_);
v___x_4080_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_fst_4078_);
lean_dec(v_fst_4078_);
v___x_4081_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_4082_ = lean_string_append(v___x_4080_, v___x_4081_);
v___x_4083_ = l_Lean_Omega_Constraint_instToString___private__1(v_constraint_4079_);
lean_dec_ref(v_constraint_4079_);
v___x_4084_ = lean_string_append(v___x_4082_, v___x_4083_);
lean_dec_ref(v___x_4083_);
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 1, v_a_4070_);
lean_ctor_set(v___x_4076_, 0, v___x_4084_);
v___x_4086_ = v___x_4076_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4084_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v_a_4070_);
v___x_4086_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
v_a_4069_ = v_tail_4074_;
v_a_4070_ = v___x_4086_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1(void){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4092_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__0));
v___x_4093_ = l_Lean_stringToMessageData(v___x_4092_);
return v___x_4093_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1(void){
_start:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__0));
v___x_4096_ = l_Lean_stringToMessageData(v___x_4095_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega(lean_object* v_p_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, uint8_t v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_){
_start:
{
lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; uint8_t v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v_cls_4123_; lean_object* v___x_4124_; 
v_cls_4123_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4124_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4123_, v_a_4105_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_a_4125_; uint8_t v___x_4126_; 
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_a_4125_);
lean_dec_ref(v___x_4124_);
v___x_4126_ = lean_unbox(v_a_4125_);
lean_dec(v_a_4125_);
if (v___x_4126_ == 0)
{
v___y_4109_ = v_a_4098_;
v___y_4110_ = v_a_4099_;
v___y_4111_ = v_a_4100_;
v___y_4112_ = v_a_4101_;
v___y_4113_ = v_a_4102_;
v___y_4114_ = v_a_4103_;
v___y_4115_ = v_a_4104_;
v___y_4116_ = v_a_4105_;
v___y_4117_ = v_a_4106_;
goto v___jp_4108_;
}
else
{
lean_object* v_constraints_4127_; uint8_t v_possible_4128_; lean_object* v___x_4129_; lean_object* v___y_4131_; 
v_constraints_4127_ = lean_ctor_get(v_p_4097_, 2);
v_possible_4128_ = lean_ctor_get_uint8(v_p_4097_, sizeof(void*)*7);
v___x_4129_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1);
if (v_possible_4128_ == 0)
{
lean_object* v___x_4144_; 
v___x_4144_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
v___y_4131_ = v___x_4144_;
goto v___jp_4130_;
}
else
{
uint8_t v___x_4145_; 
v___x_4145_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_4097_);
if (v___x_4145_ == 0)
{
lean_object* v_buckets_4146_; lean_object* v___x_4147_; lean_object* v___y_4149_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; 
v_buckets_4146_ = lean_ctor_get(v_constraints_4127_, 1);
v___x_4147_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_4153_ = lean_box(0);
v___x_4154_ = lean_array_get_size(v_buckets_4146_);
v___x_4155_ = lean_unsigned_to_nat(0u);
v___x_4156_ = lean_nat_dec_lt(v___x_4155_, v___x_4154_);
if (v___x_4156_ == 0)
{
v___y_4149_ = v___x_4153_;
goto v___jp_4148_;
}
else
{
size_t v___x_4157_; size_t v___x_4158_; lean_object* v___x_4159_; 
v___x_4157_ = lean_usize_of_nat(v___x_4154_);
v___x_4158_ = ((size_t)0ULL);
v___x_4159_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4(v_buckets_4146_, v___x_4157_, v___x_4158_, v___x_4153_);
v___y_4149_ = v___x_4159_;
goto v___jp_4148_;
}
v___jp_4148_:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4150_ = lean_box(0);
v___x_4151_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v___y_4149_, v___x_4150_);
v___x_4152_ = l_String_intercalate(v___x_4147_, v___x_4151_);
v___y_4131_ = v___x_4152_;
goto v___jp_4130_;
}
}
else
{
lean_object* v___x_4160_; 
v___x_4160_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_4131_ = v___x_4160_;
goto v___jp_4130_;
}
}
v___jp_4130_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___y_4131_);
v___x_4133_ = l_Lean_MessageData_ofFormat(v___x_4132_);
v___x_4134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4129_);
lean_ctor_set(v___x_4134_, 1, v___x_4133_);
v___x_4135_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(v_cls_4123_, v___x_4134_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_dec_ref(v___x_4135_);
v___y_4109_ = v_a_4098_;
v___y_4110_ = v_a_4099_;
v___y_4111_ = v_a_4100_;
v___y_4112_ = v_a_4101_;
v___y_4113_ = v_a_4102_;
v___y_4114_ = v_a_4103_;
v___y_4115_ = v_a_4104_;
v___y_4116_ = v_a_4105_;
v___y_4117_ = v_a_4106_;
goto v___jp_4108_;
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec(v_a_4106_);
lean_dec_ref(v_a_4105_);
lean_dec(v_a_4104_);
lean_dec_ref(v_a_4103_);
lean_dec_ref(v_p_4097_);
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4135_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4135_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
}
else
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4168_; 
lean_dec(v_a_4106_);
lean_dec_ref(v_a_4105_);
lean_dec(v_a_4104_);
lean_dec_ref(v_a_4103_);
lean_dec_ref(v_p_4097_);
v_a_4161_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4124_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4124_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4166_; 
if (v_isShared_4164_ == 0)
{
v___x_4166_ = v___x_4163_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
v___jp_4108_:
{
uint8_t v_possible_4118_; 
v_possible_4118_ = lean_ctor_get_uint8(v_p_4097_, sizeof(void*)*7);
if (v_possible_4118_ == 0)
{
lean_object* v___x_4119_; 
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
v___x_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4119_, 0, v_p_4097_);
return v___x_4119_;
}
else
{
lean_object* v___x_4120_; 
lean_inc(v___y_4117_);
lean_inc_ref(v___y_4116_);
lean_inc(v___y_4115_);
lean_inc_ref(v___y_4114_);
v___x_4120_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_4097_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; lean_object* v___x_4122_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_a_4121_);
lean_dec_ref(v___x_4120_);
v___x_4122_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_a_4121_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
return v___x_4122_;
}
else
{
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
return v___x_4120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination(lean_object* v_p_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, uint8_t v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_){
_start:
{
lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; uint8_t v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; uint8_t v_possible_4193_; 
v_possible_4193_ = lean_ctor_get_uint8(v_p_4169_, sizeof(void*)*7);
if (v_possible_4193_ == 0)
{
lean_object* v___x_4194_; 
lean_dec(v_a_4178_);
lean_dec_ref(v_a_4177_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
v___x_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4194_, 0, v_p_4169_);
return v___x_4194_;
}
else
{
lean_object* v_constraints_4195_; uint8_t v___x_4196_; 
v_constraints_4195_ = lean_ctor_get(v_p_4169_, 2);
v___x_4196_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_4169_);
if (v___x_4196_ == 0)
{
lean_object* v_cls_4197_; lean_object* v___x_4198_; 
v_cls_4197_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4198_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4197_, v_a_4177_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; uint8_t v___x_4200_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref(v___x_4198_);
v___x_4200_ = lean_unbox(v_a_4199_);
lean_dec(v_a_4199_);
if (v___x_4200_ == 0)
{
v___y_4181_ = v_a_4170_;
v___y_4182_ = v_a_4171_;
v___y_4183_ = v_a_4172_;
v___y_4184_ = v_a_4173_;
v___y_4185_ = v_a_4174_;
v___y_4186_ = v_a_4175_;
v___y_4187_ = v_a_4176_;
v___y_4188_ = v_a_4177_;
v___y_4189_ = v_a_4178_;
goto v___jp_4180_;
}
else
{
lean_object* v___x_4201_; lean_object* v___y_4203_; 
v___x_4201_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1);
if (v___x_4196_ == 0)
{
lean_object* v_buckets_4216_; lean_object* v___x_4217_; lean_object* v___y_4219_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; uint8_t v___x_4226_; 
v_buckets_4216_ = lean_ctor_get(v_constraints_4195_, 1);
v___x_4217_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_4223_ = lean_box(0);
v___x_4224_ = lean_array_get_size(v_buckets_4216_);
v___x_4225_ = lean_unsigned_to_nat(0u);
v___x_4226_ = lean_nat_dec_lt(v___x_4225_, v___x_4224_);
if (v___x_4226_ == 0)
{
v___y_4219_ = v___x_4223_;
goto v___jp_4218_;
}
else
{
size_t v___x_4227_; size_t v___x_4228_; lean_object* v___x_4229_; 
v___x_4227_ = lean_usize_of_nat(v___x_4224_);
v___x_4228_ = ((size_t)0ULL);
v___x_4229_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4(v_buckets_4216_, v___x_4227_, v___x_4228_, v___x_4223_);
v___y_4219_ = v___x_4229_;
goto v___jp_4218_;
}
v___jp_4218_:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4220_ = lean_box(0);
v___x_4221_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v___y_4219_, v___x_4220_);
v___x_4222_ = l_String_intercalate(v___x_4217_, v___x_4221_);
v___y_4203_ = v___x_4222_;
goto v___jp_4202_;
}
}
else
{
lean_object* v___x_4230_; 
v___x_4230_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_4203_ = v___x_4230_;
goto v___jp_4202_;
}
v___jp_4202_:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___y_4203_);
v___x_4205_ = l_Lean_MessageData_ofFormat(v___x_4204_);
v___x_4206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4201_);
lean_ctor_set(v___x_4206_, 1, v___x_4205_);
v___x_4207_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(v_cls_4197_, v___x_4206_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_dec_ref(v___x_4207_);
v___y_4181_ = v_a_4170_;
v___y_4182_ = v_a_4171_;
v___y_4183_ = v_a_4172_;
v___y_4184_ = v_a_4173_;
v___y_4185_ = v_a_4174_;
v___y_4186_ = v_a_4175_;
v___y_4187_ = v_a_4176_;
v___y_4188_ = v_a_4177_;
v___y_4189_ = v_a_4178_;
goto v___jp_4180_;
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
lean_dec(v_a_4178_);
lean_dec_ref(v_a_4177_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec_ref(v_p_4169_);
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4207_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4207_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
}
}
else
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
lean_dec(v_a_4178_);
lean_dec_ref(v_a_4177_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec_ref(v_p_4169_);
v_a_4231_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___x_4198_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4198_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
else
{
lean_object* v___x_4239_; 
lean_dec(v_a_4178_);
lean_dec_ref(v_a_4177_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
v___x_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4239_, 0, v_p_4169_);
return v___x_4239_;
}
}
v___jp_4180_:
{
lean_object* v___x_4190_; 
v___x_4190_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_4169_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4192_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_a_4191_);
lean_dec_ref(v___x_4190_);
v___x_4192_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_a_4191_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
return v___x_4192_;
}
else
{
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
return v___x_4190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___boxed(lean_object* v_p_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_){
_start:
{
uint8_t v_a_14804__boxed_4251_; lean_object* v_res_4252_; 
v_a_14804__boxed_4251_ = lean_unbox(v_a_4244_);
v_res_4252_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_p_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_14804__boxed_4251_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
lean_dec(v_a_4245_);
lean_dec_ref(v_a_4243_);
lean_dec(v_a_4242_);
lean_dec(v_a_4241_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___boxed(lean_object* v_p_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_){
_start:
{
uint8_t v_a_14863__boxed_4264_; lean_object* v_res_4265_; 
v_a_14863__boxed_4264_ = lean_unbox(v_a_4257_);
v_res_4265_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_p_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_14863__boxed_4264_, v_a_4258_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_);
lean_dec(v_a_4258_);
lean_dec_ref(v_a_4256_);
lean_dec(v_a_4255_);
lean_dec(v_a_4254_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object* v_cls_4266_, lean_object* v_msg_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, uint8_t v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v___x_4278_; 
v___x_4278_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(v_cls_4266_, v_msg_4267_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___boxed(lean_object* v_cls_4279_, lean_object* v_msg_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
uint8_t v___y_15105__boxed_4291_; lean_object* v_res_4292_; 
v___y_15105__boxed_4291_ = lean_unbox(v___y_4284_);
v_res_4292_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v_cls_4279_, v_msg_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_15105__boxed_4291_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec(v___y_4281_);
return v_res_4292_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Omega_Core(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Omega_instToExprLinearCombo = _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo);
l_Lean_Elab_Tactic_Omega_instToExprConstraint = _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_instToExprConstraint);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Omega_Core(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam = _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Omega_OmegaM(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Omega_MinNatAbs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Omega_Core(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Omega_MinNatAbs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Omega_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Omega_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Omega_Core(builtin);
}
#ifdef __cplusplus
}
#endif
