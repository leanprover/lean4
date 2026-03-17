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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Omega_Constraint_instToString___private__1(lean_object*);
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
lean_object* l_instToStringInt___lam__0___boxed(lean_object*);
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
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__1 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__1_value;
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
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " * y combo of:\n"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " * x + "};
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
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringInt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
return v_x_604_;
}
else
{
lean_object* v_head_606_; lean_object* v_tail_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v_intZero_610_; uint8_t v_isNeg_611_; 
v_head_606_ = lean_ctor_get(v_x_605_, 0);
v_tail_607_ = lean_ctor_get(v_x_605_, 1);
v___x_608_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_609_ = lean_string_append(v_x_604_, v___x_608_);
v_intZero_610_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_611_ = lean_int_dec_lt(v_head_606_, v_intZero_610_);
if (v_isNeg_611_ == 0)
{
lean_object* v_a_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_a_612_ = lean_nat_abs(v_head_606_);
v___x_613_ = l_Nat_reprFast(v_a_612_);
v___x_614_ = lean_string_append(v___x_609_, v___x_613_);
lean_dec_ref(v___x_613_);
v_x_604_ = v___x_614_;
v_x_605_ = v_tail_607_;
goto _start;
}
else
{
lean_object* v_abs_616_; lean_object* v_one_617_; lean_object* v_a_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_abs_616_ = lean_nat_abs(v_head_606_);
v_one_617_ = lean_unsigned_to_nat(1u);
v_a_618_ = lean_nat_sub(v_abs_616_, v_one_617_);
lean_dec(v_abs_616_);
v___x_619_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__1));
v___x_620_ = lean_nat_add(v_a_618_, v_one_617_);
lean_dec(v_a_618_);
v___x_621_ = l_Nat_reprFast(v___x_620_);
v___x_622_ = lean_string_append(v___x_619_, v___x_621_);
lean_dec_ref(v___x_621_);
v___x_623_ = lean_string_append(v___x_609_, v___x_622_);
lean_dec_ref(v___x_622_);
v_x_604_ = v___x_623_;
v_x_605_ = v_tail_607_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___boxed(lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v_x_625_, v_x_626_);
lean_dec(v_x_626_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(lean_object* v_x_631_){
_start:
{
if (lean_obj_tag(v_x_631_) == 0)
{
lean_object* v___x_632_; 
v___x_632_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__0));
return v___x_632_;
}
else
{
lean_object* v_tail_633_; 
v_tail_633_ = lean_ctor_get(v_x_631_, 1);
if (lean_obj_tag(v_tail_633_) == 0)
{
lean_object* v_head_634_; lean_object* v___x_635_; lean_object* v___y_637_; lean_object* v_intZero_641_; uint8_t v_isNeg_642_; 
v_head_634_ = lean_ctor_get(v_x_631_, 0);
v___x_635_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_641_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_642_ = lean_int_dec_lt(v_head_634_, v_intZero_641_);
if (v_isNeg_642_ == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; 
v_a_643_ = lean_nat_abs(v_head_634_);
v___x_644_ = l_Nat_reprFast(v_a_643_);
v___y_637_ = v___x_644_;
goto v___jp_636_;
}
else
{
lean_object* v_abs_645_; lean_object* v_one_646_; lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_abs_645_ = lean_nat_abs(v_head_634_);
v_one_646_ = lean_unsigned_to_nat(1u);
v_a_647_ = lean_nat_sub(v_abs_645_, v_one_646_);
lean_dec(v_abs_645_);
v___x_648_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__1));
v___x_649_ = lean_nat_add(v_a_647_, v_one_646_);
lean_dec(v_a_647_);
v___x_650_ = l_Nat_reprFast(v___x_649_);
v___x_651_ = lean_string_append(v___x_648_, v___x_650_);
lean_dec_ref(v___x_650_);
v___y_637_ = v___x_651_;
goto v___jp_636_;
}
v___jp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_string_append(v___x_635_, v___y_637_);
lean_dec_ref(v___y_637_);
v___x_639_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_640_ = lean_string_append(v___x_638_, v___x_639_);
return v___x_640_;
}
}
else
{
lean_object* v_head_652_; lean_object* v___x_653_; lean_object* v___y_655_; lean_object* v_intZero_660_; uint8_t v_isNeg_661_; 
v_head_652_ = lean_ctor_get(v_x_631_, 0);
v___x_653_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_660_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_661_ = lean_int_dec_lt(v_head_652_, v_intZero_660_);
if (v_isNeg_661_ == 0)
{
lean_object* v_a_662_; lean_object* v___x_663_; 
v_a_662_ = lean_nat_abs(v_head_652_);
v___x_663_ = l_Nat_reprFast(v_a_662_);
v___y_655_ = v___x_663_;
goto v___jp_654_;
}
else
{
lean_object* v_abs_664_; lean_object* v_one_665_; lean_object* v_a_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_abs_664_ = lean_nat_abs(v_head_652_);
v_one_665_ = lean_unsigned_to_nat(1u);
v_a_666_ = lean_nat_sub(v_abs_664_, v_one_665_);
lean_dec(v_abs_664_);
v___x_667_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__1));
v___x_668_ = lean_nat_add(v_a_666_, v_one_665_);
lean_dec(v_a_666_);
v___x_669_ = l_Nat_reprFast(v___x_668_);
v___x_670_ = lean_string_append(v___x_667_, v___x_669_);
lean_dec_ref(v___x_669_);
v___y_655_ = v___x_670_;
goto v___jp_654_;
}
v___jp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; uint32_t v___x_658_; lean_object* v___x_659_; 
v___x_656_ = lean_string_append(v___x_653_, v___y_655_);
lean_dec_ref(v___y_655_);
v___x_657_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v___x_656_, v_tail_633_);
v___x_658_ = 93;
v___x_659_ = lean_string_push(v___x_657_, v___x_658_);
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___boxed(lean_object* v_x_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_671_);
lean_dec(v_x_671_);
return v_res_672_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
if (lean_obj_tag(v_x_673_) == 0)
{
if (lean_obj_tag(v_x_674_) == 0)
{
uint8_t v___x_675_; 
v___x_675_ = 1;
return v___x_675_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = 0;
return v___x_676_;
}
}
else
{
if (lean_obj_tag(v_x_674_) == 0)
{
uint8_t v___x_677_; 
v___x_677_ = 0;
return v___x_677_;
}
else
{
lean_object* v_head_678_; lean_object* v_tail_679_; lean_object* v_head_680_; lean_object* v_tail_681_; uint8_t v___x_682_; 
v_head_678_ = lean_ctor_get(v_x_673_, 0);
v_tail_679_ = lean_ctor_get(v_x_673_, 1);
v_head_680_ = lean_ctor_get(v_x_674_, 0);
v_tail_681_ = lean_ctor_get(v_x_674_, 1);
v___x_682_ = lean_int_dec_eq(v_head_678_, v_head_680_);
if (v___x_682_ == 0)
{
return v___x_682_;
}
else
{
v_x_673_ = v_tail_679_;
v_x_674_ = v_tail_681_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1___boxed(lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
uint8_t v_res_686_; lean_object* v_r_687_; 
v_res_686_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_684_, v_x_685_);
lean_dec(v_x_685_);
lean_dec(v_x_684_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString(lean_object* v_s_698_, lean_object* v_x_699_, lean_object* v_x_700_){
_start:
{
switch(lean_obj_tag(v_x_700_))
{
case 0:
{
lean_object* v_i_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_i_701_ = lean_ctor_get(v_x_700_, 2);
lean_inc(v_i_701_);
lean_dec_ref(v_x_700_);
v___x_702_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_699_);
lean_dec(v_x_699_);
v___x_703_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_704_ = lean_string_append(v___x_702_, v___x_703_);
v___x_705_ = l_Lean_Omega_Constraint_instToString___private__1(v_s_698_);
lean_dec_ref(v_s_698_);
v___x_706_ = lean_string_append(v___x_704_, v___x_705_);
lean_dec_ref(v___x_705_);
v___x_707_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__1));
v___x_708_ = lean_string_append(v___x_706_, v___x_707_);
v___x_709_ = l_Nat_reprFast(v_i_701_);
v___x_710_ = lean_string_append(v___x_708_, v___x_709_);
lean_dec_ref(v___x_709_);
return v___x_710_;
}
case 1:
{
lean_object* v_s_711_; lean_object* v_c_712_; lean_object* v_j_713_; uint8_t v___y_715_; uint8_t v___x_727_; 
v_s_711_ = lean_ctor_get(v_x_700_, 0);
lean_inc_ref(v_s_711_);
v_c_712_ = lean_ctor_get(v_x_700_, 1);
lean_inc(v_c_712_);
v_j_713_ = lean_ctor_get(v_x_700_, 2);
lean_inc_ref(v_j_713_);
lean_dec_ref(v_x_700_);
v___x_727_ = l_Lean_Omega_instBEqConstraint_beq(v_s_698_, v_s_711_);
if (v___x_727_ == 0)
{
v___y_715_ = v___x_727_;
goto v___jp_714_;
}
else
{
uint8_t v___x_728_; 
v___x_728_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_699_, v_c_712_);
v___y_715_ = v___x_728_;
goto v___jp_714_;
}
v___jp_714_:
{
if (v___y_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_716_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_699_);
lean_dec(v_x_699_);
v___x_717_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_718_ = lean_string_append(v___x_716_, v___x_717_);
v___x_719_ = l_Lean_Omega_Constraint_instToString___private__1(v_s_698_);
lean_dec_ref(v_s_698_);
v___x_720_ = lean_string_append(v___x_718_, v___x_719_);
lean_dec_ref(v___x_719_);
v___x_721_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_722_ = lean_string_append(v___x_720_, v___x_721_);
v___x_723_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_711_, v_c_712_, v_j_713_);
v___x_724_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_723_);
v___x_725_ = lean_string_append(v___x_722_, v___x_724_);
lean_dec_ref(v___x_724_);
return v___x_725_;
}
else
{
lean_dec(v_x_699_);
lean_dec_ref(v_s_698_);
v_s_698_ = v_s_711_;
v_x_699_ = v_c_712_;
v_x_700_ = v_j_713_;
goto _start;
}
}
}
case 2:
{
lean_object* v_s_729_; lean_object* v_t_730_; lean_object* v_j_731_; lean_object* v_k_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_s_729_ = lean_ctor_get(v_x_700_, 0);
lean_inc_ref(v_s_729_);
v_t_730_ = lean_ctor_get(v_x_700_, 1);
lean_inc_ref(v_t_730_);
v_j_731_ = lean_ctor_get(v_x_700_, 3);
lean_inc_ref(v_j_731_);
v_k_732_ = lean_ctor_get(v_x_700_, 4);
lean_inc_ref(v_k_732_);
lean_dec_ref(v_x_700_);
v___x_733_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_699_);
v___x_734_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_735_ = lean_string_append(v___x_733_, v___x_734_);
v___x_736_ = l_Lean_Omega_Constraint_instToString___private__1(v_s_698_);
lean_dec_ref(v_s_698_);
v___x_737_ = lean_string_append(v___x_735_, v___x_736_);
lean_dec_ref(v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v___x_739_ = lean_string_append(v___x_737_, v___x_738_);
lean_inc(v_x_699_);
v___x_740_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_729_, v_x_699_, v_j_731_);
v___x_741_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_740_);
v___x_742_ = lean_string_append(v___x_739_, v___x_741_);
lean_dec_ref(v___x_741_);
v___x_743_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_744_ = lean_string_append(v___x_742_, v___x_743_);
v___x_745_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_730_, v_x_699_, v_k_732_);
v___x_746_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_745_);
v___x_747_ = lean_string_append(v___x_744_, v___x_746_);
lean_dec_ref(v___x_746_);
return v___x_747_;
}
case 3:
{
lean_object* v_s_748_; lean_object* v_t_749_; lean_object* v_x_750_; lean_object* v_y_751_; lean_object* v_a_752_; lean_object* v_j_753_; lean_object* v_b_754_; lean_object* v_k_755_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___y_778_; lean_object* v_intZero_793_; uint8_t v_isNeg_794_; 
v_s_748_ = lean_ctor_get(v_x_700_, 0);
lean_inc_ref(v_s_748_);
v_t_749_ = lean_ctor_get(v_x_700_, 1);
lean_inc_ref(v_t_749_);
v_x_750_ = lean_ctor_get(v_x_700_, 2);
lean_inc(v_x_750_);
v_y_751_ = lean_ctor_get(v_x_700_, 3);
lean_inc(v_y_751_);
v_a_752_ = lean_ctor_get(v_x_700_, 4);
lean_inc(v_a_752_);
v_j_753_ = lean_ctor_get(v_x_700_, 5);
lean_inc_ref(v_j_753_);
v_b_754_ = lean_ctor_get(v_x_700_, 6);
lean_inc(v_b_754_);
v_k_755_ = lean_ctor_get(v_x_700_, 7);
lean_inc_ref(v_k_755_);
lean_dec_ref(v_x_700_);
v___x_770_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_699_);
lean_dec(v_x_699_);
v___x_771_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_772_ = lean_string_append(v___x_770_, v___x_771_);
v___x_773_ = l_Lean_Omega_Constraint_instToString___private__1(v_s_698_);
lean_dec_ref(v_s_698_);
v___x_774_ = lean_string_append(v___x_772_, v___x_773_);
lean_dec_ref(v___x_773_);
v___x_775_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_776_ = lean_string_append(v___x_774_, v___x_775_);
v_intZero_793_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_794_ = lean_int_dec_lt(v_a_752_, v_intZero_793_);
if (v_isNeg_794_ == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; 
v_a_795_ = lean_nat_abs(v_a_752_);
lean_dec(v_a_752_);
v___x_796_ = l_Nat_reprFast(v_a_795_);
v___y_778_ = v___x_796_;
goto v___jp_777_;
}
else
{
lean_object* v_abs_797_; lean_object* v_one_798_; lean_object* v_a_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_abs_797_ = lean_nat_abs(v_a_752_);
lean_dec(v_a_752_);
v_one_798_ = lean_unsigned_to_nat(1u);
v_a_799_ = lean_nat_sub(v_abs_797_, v_one_798_);
lean_dec(v_abs_797_);
v___x_800_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__1));
v___x_801_ = lean_nat_add(v_a_799_, v_one_798_);
lean_dec(v_a_799_);
v___x_802_ = l_Nat_reprFast(v___x_801_);
v___x_803_ = lean_string_append(v___x_800_, v___x_802_);
lean_dec_ref(v___x_802_);
v___y_778_ = v___x_803_;
goto v___jp_777_;
}
v___jp_756_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_759_ = lean_string_append(v___y_757_, v___y_758_);
lean_dec_ref(v___y_758_);
v___x_760_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_761_ = lean_string_append(v___x_759_, v___x_760_);
v___x_762_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_748_, v_x_750_, v_j_753_);
v___x_763_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_762_);
v___x_764_ = lean_string_append(v___x_761_, v___x_763_);
lean_dec_ref(v___x_763_);
v___x_765_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_766_ = lean_string_append(v___x_764_, v___x_765_);
v___x_767_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_749_, v_y_751_, v_k_755_);
v___x_768_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_767_);
v___x_769_ = lean_string_append(v___x_766_, v___x_768_);
lean_dec_ref(v___x_768_);
return v___x_769_;
}
v___jp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v_intZero_782_; uint8_t v_isNeg_783_; 
v___x_779_ = lean_string_append(v___x_776_, v___y_778_);
lean_dec_ref(v___y_778_);
v___x_780_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v___x_781_ = lean_string_append(v___x_779_, v___x_780_);
v_intZero_782_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_783_ = lean_int_dec_lt(v_b_754_, v_intZero_782_);
if (v_isNeg_783_ == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; 
v_a_784_ = lean_nat_abs(v_b_754_);
lean_dec(v_b_754_);
v___x_785_ = l_Nat_reprFast(v_a_784_);
v___y_757_ = v___x_781_;
v___y_758_ = v___x_785_;
goto v___jp_756_;
}
else
{
lean_object* v_abs_786_; lean_object* v_one_787_; lean_object* v_a_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_abs_786_ = lean_nat_abs(v_b_754_);
lean_dec(v_b_754_);
v_one_787_ = lean_unsigned_to_nat(1u);
v_a_788_ = lean_nat_sub(v_abs_786_, v_one_787_);
lean_dec(v_abs_786_);
v___x_789_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__1));
v___x_790_ = lean_nat_add(v_a_788_, v_one_787_);
lean_dec(v_a_788_);
v___x_791_ = l_Nat_reprFast(v___x_790_);
v___x_792_ = lean_string_append(v___x_789_, v___x_791_);
lean_dec_ref(v___x_791_);
v___y_757_ = v___x_781_;
v___y_758_ = v___x_792_;
goto v___jp_756_;
}
}
}
default: 
{
lean_object* v_m_804_; lean_object* v_r_805_; lean_object* v_i_806_; lean_object* v_x_807_; lean_object* v_j_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_m_804_ = lean_ctor_get(v_x_700_, 0);
lean_inc(v_m_804_);
v_r_805_ = lean_ctor_get(v_x_700_, 1);
lean_inc(v_r_805_);
v_i_806_ = lean_ctor_get(v_x_700_, 2);
lean_inc(v_i_806_);
v_x_807_ = lean_ctor_get(v_x_700_, 3);
lean_inc(v_x_807_);
v_j_808_ = lean_ctor_get(v_x_700_, 4);
lean_inc_ref(v_j_808_);
lean_dec_ref(v_x_700_);
v___x_809_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_699_);
lean_dec(v_x_699_);
v___x_810_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_811_ = lean_string_append(v___x_809_, v___x_810_);
v___x_812_ = l_Lean_Omega_Constraint_instToString___private__1(v_s_698_);
lean_dec_ref(v_s_698_);
v___x_813_ = lean_string_append(v___x_811_, v___x_812_);
lean_dec_ref(v___x_812_);
v___x_814_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_815_ = lean_string_append(v___x_813_, v___x_814_);
v___x_816_ = l_Nat_reprFast(v_m_804_);
v___x_817_ = lean_string_append(v___x_815_, v___x_816_);
lean_dec_ref(v___x_816_);
v___x_818_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_819_ = lean_string_append(v___x_817_, v___x_818_);
v___x_820_ = l_Nat_reprFast(v_i_806_);
v___x_821_ = lean_string_append(v___x_819_, v___x_820_);
lean_dec_ref(v___x_820_);
v___x_822_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9));
v___x_823_ = lean_string_append(v___x_821_, v___x_822_);
v___x_824_ = l_Lean_Omega_Constraint_exact(v_r_805_);
v___x_825_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v___x_824_, v_x_807_, v_j_808_);
v___x_826_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_825_);
v___x_827_ = lean_string_append(v___x_823_, v___x_826_);
lean_dec_ref(v___x_826_);
return v___x_827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_instToString(lean_object* v_s_828_, lean_object* v_x_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Justification_toString), 3, 2);
lean_closure_set(v___x_830_, 0, v_s_828_);
lean_closure_set(v___x_830_, 1, v_x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(lean_object* v_nilFn_831_, lean_object* v_consFn_832_, lean_object* v_x_833_){
_start:
{
if (lean_obj_tag(v_x_833_) == 0)
{
lean_dec_ref(v_consFn_832_);
lean_inc_ref(v_nilFn_831_);
return v_nilFn_831_;
}
else
{
lean_object* v_head_834_; lean_object* v_tail_835_; lean_object* v___y_837_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_head_834_ = lean_ctor_get(v_x_833_, 0);
v_tail_835_ = lean_ctor_get(v_x_833_, 1);
v___x_840_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_841_ = lean_int_dec_le(v___x_840_, v_head_834_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_842_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_843_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_844_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_845_ = lean_int_neg(v_head_834_);
v___x_846_ = l_Int_toNat(v___x_845_);
lean_dec(v___x_845_);
v___x_847_ = l_Lean_instToExprInt_mkNat(v___x_846_);
v___x_848_ = l_Lean_mkApp3(v___x_842_, v___x_843_, v___x_844_, v___x_847_);
v___y_837_ = v___x_848_;
goto v___jp_836_;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = l_Int_toNat(v_head_834_);
v___x_850_ = l_Lean_instToExprInt_mkNat(v___x_849_);
v___y_837_ = v___x_850_;
goto v___jp_836_;
}
v___jp_836_:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_inc_ref(v_consFn_832_);
v___x_838_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_831_, v_consFn_832_, v_tail_835_);
v___x_839_ = l_Lean_mkAppB(v_consFn_832_, v___y_837_, v___x_838_);
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0___boxed(lean_object* v_nilFn_851_, lean_object* v_consFn_852_, lean_object* v_x_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_851_, v_consFn_852_, v_x_853_);
lean_dec(v_x_853_);
lean_dec_ref(v_nilFn_851_);
return v_res_854_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = lean_box(0);
v___x_861_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1));
v___x_862_ = l_Lean_Expr_const___override(v___x_861_, v___x_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof(lean_object* v_s_863_, lean_object* v_x_864_, lean_object* v_v_865_, lean_object* v_prf_866_){
_start:
{
lean_object* v___x_867_; lean_object* v___y_869_; lean_object* v_lowerBound_874_; lean_object* v_upperBound_875_; lean_object* v___x_876_; lean_object* v_type_877_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_885_; 
v___x_867_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2);
v_lowerBound_874_ = lean_ctor_get(v_s_863_, 0);
v_upperBound_875_ = lean_ctor_get(v_s_863_, 1);
v___x_876_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_877_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_874_) == 0)
{
lean_object* v___x_901_; 
v___x_901_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_885_ = v___x_901_;
goto v___jp_884_;
}
else
{
lean_object* v_val_902_; lean_object* v___x_903_; lean_object* v___y_905_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_val_902_ = lean_ctor_get(v_lowerBound_874_, 0);
v___x_903_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_907_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_908_ = lean_int_dec_le(v___x_907_, v_val_902_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_909_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_910_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_911_ = lean_int_neg(v_val_902_);
v___x_912_ = l_Int_toNat(v___x_911_);
lean_dec(v___x_911_);
v___x_913_ = l_Lean_instToExprInt_mkNat(v___x_912_);
v___x_914_ = l_Lean_mkApp3(v___x_909_, v_type_877_, v___x_910_, v___x_913_);
v___y_905_ = v___x_914_;
goto v___jp_904_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = l_Int_toNat(v_val_902_);
v___x_916_ = l_Lean_instToExprInt_mkNat(v___x_915_);
v___y_905_ = v___x_916_;
goto v___jp_904_;
}
v___jp_904_:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_mkAppB(v___x_903_, v_type_877_, v___y_905_);
v___y_885_ = v___x_906_;
goto v___jp_884_;
}
}
v___jp_868_:
{
lean_object* v_nil_870_; lean_object* v_cons_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_nil_870_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_871_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_872_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_870_, v_cons_871_, v_x_864_);
v___x_873_ = l_Lean_mkApp4(v___x_867_, v___y_869_, v___x_872_, v_v_865_, v_prf_866_);
return v___x_873_;
}
v___jp_878_:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = l_Lean_mkAppB(v___y_879_, v_type_877_, v___y_881_);
v___x_883_ = l_Lean_Expr_app___override(v___y_880_, v___x_882_);
v___y_869_ = v___x_883_;
goto v___jp_868_;
}
v___jp_884_:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Expr_app___override(v___x_876_, v___y_885_);
if (lean_obj_tag(v_upperBound_875_) == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_888_ = l_Lean_Expr_app___override(v___x_886_, v___x_887_);
v___y_869_ = v___x_888_;
goto v___jp_868_;
}
else
{
lean_object* v_val_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v_val_889_ = lean_ctor_get(v_upperBound_875_, 0);
v___x_890_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_891_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_892_ = lean_int_dec_le(v___x_891_, v_val_889_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_893_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_894_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_895_ = lean_int_neg(v_val_889_);
v___x_896_ = l_Int_toNat(v___x_895_);
lean_dec(v___x_895_);
v___x_897_ = l_Lean_instToExprInt_mkNat(v___x_896_);
v___x_898_ = l_Lean_mkApp3(v___x_893_, v_type_877_, v___x_894_, v___x_897_);
v___y_879_ = v___x_890_;
v___y_880_ = v___x_886_;
v___y_881_ = v___x_898_;
goto v___jp_878_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = l_Int_toNat(v_val_889_);
v___x_900_ = l_Lean_instToExprInt_mkNat(v___x_899_);
v___y_879_ = v___x_890_;
v___y_880_ = v___x_886_;
v___y_881_ = v___x_900_;
goto v___jp_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___boxed(lean_object* v_s_917_, lean_object* v_x_918_, lean_object* v_v_919_, lean_object* v_prf_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_917_, v_x_918_, v_v_919_, v_prf_920_);
lean_dec(v_x_918_);
lean_dec_ref(v_s_917_);
return v_res_921_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_box(0);
v___x_929_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1));
v___x_930_ = l_Lean_Expr_const___override(v___x_929_, v___x_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof(lean_object* v_s_931_, lean_object* v_t_932_, lean_object* v_x_933_, lean_object* v_v_934_, lean_object* v_ps_935_, lean_object* v_pt_936_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_988_; lean_object* v_lowerBound_1006_; lean_object* v_upperBound_1007_; lean_object* v___x_1008_; lean_object* v_type_1009_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1017_; 
v___x_937_ = lean_box(0);
v___x_938_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2);
v_lowerBound_1006_ = lean_ctor_get(v_s_931_, 0);
v_upperBound_1007_ = lean_ctor_get(v_s_931_, 1);
v___x_1008_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1009_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1006_) == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1017_ = v___x_1033_;
goto v___jp_1016_;
}
else
{
lean_object* v_val_1034_; lean_object* v___x_1035_; lean_object* v___y_1037_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_val_1034_ = lean_ctor_get(v_lowerBound_1006_, 0);
v___x_1035_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1039_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1040_ = lean_int_dec_le(v___x_1039_, v_val_1034_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1041_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1042_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1043_ = lean_int_neg(v_val_1034_);
v___x_1044_ = l_Int_toNat(v___x_1043_);
lean_dec(v___x_1043_);
v___x_1045_ = l_Lean_instToExprInt_mkNat(v___x_1044_);
v___x_1046_ = l_Lean_mkApp3(v___x_1041_, v_type_1009_, v___x_1042_, v___x_1045_);
v___y_1037_ = v___x_1046_;
goto v___jp_1036_;
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = l_Int_toNat(v_val_1034_);
v___x_1048_ = l_Lean_instToExprInt_mkNat(v___x_1047_);
v___y_1037_ = v___x_1048_;
goto v___jp_1036_;
}
v___jp_1036_:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_mkAppB(v___x_1035_, v_type_1009_, v___y_1037_);
v___y_1017_ = v___x_1038_;
goto v___jp_1016_;
}
}
v___jp_939_:
{
lean_object* v_nil_942_; lean_object* v_cons_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_nil_942_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_943_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_944_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_942_, v_cons_943_, v_x_933_);
v___x_945_ = l_Lean_mkApp6(v___x_938_, v___y_940_, v___y_941_, v___x_944_, v_v_934_, v_ps_935_, v_pt_936_);
return v___x_945_;
}
v___jp_946_:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = l_Lean_mkAppB(v___y_949_, v___y_947_, v___y_951_);
v___x_953_ = l_Lean_Expr_app___override(v___y_950_, v___x_952_);
v___y_940_ = v___y_948_;
v___y_941_ = v___x_953_;
goto v___jp_939_;
}
v___jp_954_:
{
lean_object* v_upperBound_960_; lean_object* v___x_961_; 
v_upperBound_960_ = lean_ctor_get(v_t_932_, 1);
v___x_961_ = l_Lean_Expr_app___override(v___y_955_, v___y_959_);
if (lean_obj_tag(v_upperBound_960_) == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec_ref(v___y_958_);
v___x_962_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_963_ = l_Lean_Expr_app___override(v___x_962_, v___y_956_);
v___x_964_ = l_Lean_Expr_app___override(v___x_961_, v___x_963_);
v___y_940_ = v___y_957_;
v___y_941_ = v___x_964_;
goto v___jp_939_;
}
else
{
lean_object* v_val_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_val_965_ = lean_ctor_get(v_upperBound_960_, 0);
v___x_966_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_967_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_968_ = lean_int_dec_le(v___x_967_, v_val_965_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_969_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_970_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
v___x_971_ = l_Lean_Name_mkStr2(v___y_958_, v___x_970_);
v___x_972_ = l_Lean_Expr_const___override(v___x_971_, v___x_937_);
v___x_973_ = lean_int_neg(v_val_965_);
v___x_974_ = l_Int_toNat(v___x_973_);
lean_dec(v___x_973_);
v___x_975_ = l_Lean_instToExprInt_mkNat(v___x_974_);
lean_inc_ref(v___y_956_);
v___x_976_ = l_Lean_mkApp3(v___x_969_, v___y_956_, v___x_972_, v___x_975_);
v___y_947_ = v___y_956_;
v___y_948_ = v___y_957_;
v___y_949_ = v___x_966_;
v___y_950_ = v___x_961_;
v___y_951_ = v___x_976_;
goto v___jp_946_;
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec_ref(v___y_958_);
v___x_977_ = l_Int_toNat(v_val_965_);
v___x_978_ = l_Lean_instToExprInt_mkNat(v___x_977_);
v___y_947_ = v___y_956_;
v___y_948_ = v___y_957_;
v___y_949_ = v___x_966_;
v___y_950_ = v___x_961_;
v___y_951_ = v___x_978_;
goto v___jp_946_;
}
}
}
v___jp_979_:
{
lean_object* v___x_986_; 
lean_inc_ref(v___y_982_);
v___x_986_ = l_Lean_mkAppB(v___y_981_, v___y_982_, v___y_985_);
v___y_955_ = v___y_980_;
v___y_956_ = v___y_982_;
v___y_957_ = v___y_983_;
v___y_958_ = v___y_984_;
v___y_959_ = v___x_986_;
goto v___jp_954_;
}
v___jp_987_:
{
lean_object* v_lowerBound_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v_type_992_; 
v_lowerBound_989_ = lean_ctor_get(v_t_932_, 0);
v___x_990_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_991_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_992_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_989_) == 0)
{
lean_object* v___x_993_; 
v___x_993_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_955_ = v___x_990_;
v___y_956_ = v_type_992_;
v___y_957_ = v___y_988_;
v___y_958_ = v___x_991_;
v___y_959_ = v___x_993_;
goto v___jp_954_;
}
else
{
lean_object* v_val_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v_val_994_ = lean_ctor_get(v_lowerBound_989_, 0);
v___x_995_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_996_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_997_ = lean_int_dec_le(v___x_996_, v_val_994_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_998_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_999_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1000_ = lean_int_neg(v_val_994_);
v___x_1001_ = l_Int_toNat(v___x_1000_);
lean_dec(v___x_1000_);
v___x_1002_ = l_Lean_instToExprInt_mkNat(v___x_1001_);
v___x_1003_ = l_Lean_mkApp3(v___x_998_, v_type_992_, v___x_999_, v___x_1002_);
v___y_980_ = v___x_990_;
v___y_981_ = v___x_995_;
v___y_982_ = v_type_992_;
v___y_983_ = v___y_988_;
v___y_984_ = v___x_991_;
v___y_985_ = v___x_1003_;
goto v___jp_979_;
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = l_Int_toNat(v_val_994_);
v___x_1005_ = l_Lean_instToExprInt_mkNat(v___x_1004_);
v___y_980_ = v___x_990_;
v___y_981_ = v___x_995_;
v___y_982_ = v_type_992_;
v___y_983_ = v___y_988_;
v___y_984_ = v___x_991_;
v___y_985_ = v___x_1005_;
goto v___jp_979_;
}
}
}
v___jp_1010_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = l_Lean_mkAppB(v___y_1012_, v_type_1009_, v___y_1013_);
v___x_1015_ = l_Lean_Expr_app___override(v___y_1011_, v___x_1014_);
v___y_988_ = v___x_1015_;
goto v___jp_987_;
}
v___jp_1016_:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_Expr_app___override(v___x_1008_, v___y_1017_);
if (lean_obj_tag(v_upperBound_1007_) == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1020_ = l_Lean_Expr_app___override(v___x_1018_, v___x_1019_);
v___y_988_ = v___x_1020_;
goto v___jp_987_;
}
else
{
lean_object* v_val_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_val_1021_ = lean_ctor_get(v_upperBound_1007_, 0);
v___x_1022_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1023_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1024_ = lean_int_dec_le(v___x_1023_, v_val_1021_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1025_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1026_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1027_ = lean_int_neg(v_val_1021_);
v___x_1028_ = l_Int_toNat(v___x_1027_);
lean_dec(v___x_1027_);
v___x_1029_ = l_Lean_instToExprInt_mkNat(v___x_1028_);
v___x_1030_ = l_Lean_mkApp3(v___x_1025_, v_type_1009_, v___x_1026_, v___x_1029_);
v___y_1011_ = v___x_1018_;
v___y_1012_ = v___x_1022_;
v___y_1013_ = v___x_1030_;
goto v___jp_1010_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = l_Int_toNat(v_val_1021_);
v___x_1032_ = l_Lean_instToExprInt_mkNat(v___x_1031_);
v___y_1011_ = v___x_1018_;
v___y_1012_ = v___x_1022_;
v___y_1013_ = v___x_1032_;
goto v___jp_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___boxed(lean_object* v_s_1049_, lean_object* v_t_1050_, lean_object* v_x_1051_, lean_object* v_v_1052_, lean_object* v_ps_1053_, lean_object* v_pt_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1049_, v_t_1050_, v_x_1051_, v_v_1052_, v_ps_1053_, v_pt_1054_);
lean_dec(v_x_1051_);
lean_dec_ref(v_t_1050_);
lean_dec_ref(v_s_1049_);
return v_res_1055_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = lean_box(0);
v___x_1062_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1));
v___x_1063_ = l_Lean_Expr_const___override(v___x_1062_, v___x_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof(lean_object* v_s_1064_, lean_object* v_t_1065_, lean_object* v_a_1066_, lean_object* v_x_1067_, lean_object* v_b_1068_, lean_object* v_y_1069_, lean_object* v_v_1070_, lean_object* v_px_1071_, lean_object* v_py_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1159_; lean_object* v_lowerBound_1177_; lean_object* v_upperBound_1178_; lean_object* v___x_1179_; lean_object* v_type_1180_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1188_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2);
v_lowerBound_1177_ = lean_ctor_get(v_s_1064_, 0);
v_upperBound_1178_ = lean_ctor_get(v_s_1064_, 1);
v___x_1179_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1180_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1177_) == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1188_ = v___x_1204_;
goto v___jp_1187_;
}
else
{
lean_object* v_val_1205_; lean_object* v___x_1206_; lean_object* v___y_1208_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_val_1205_ = lean_ctor_get(v_lowerBound_1177_, 0);
v___x_1206_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1210_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1211_ = lean_int_dec_le(v___x_1210_, v_val_1205_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1212_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1213_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1214_ = lean_int_neg(v_val_1205_);
v___x_1215_ = l_Int_toNat(v___x_1214_);
lean_dec(v___x_1214_);
v___x_1216_ = l_Lean_instToExprInt_mkNat(v___x_1215_);
v___x_1217_ = l_Lean_mkApp3(v___x_1212_, v_type_1180_, v___x_1213_, v___x_1216_);
v___y_1208_ = v___x_1217_;
goto v___jp_1207_;
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = l_Int_toNat(v_val_1205_);
v___x_1219_ = l_Lean_instToExprInt_mkNat(v___x_1218_);
v___y_1208_ = v___x_1219_;
goto v___jp_1207_;
}
v___jp_1207_:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_mkAppB(v___x_1206_, v_type_1180_, v___y_1208_);
v___y_1188_ = v___x_1209_;
goto v___jp_1187_;
}
}
v___jp_1075_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v___y_1077_, v___y_1079_, v_y_1069_);
lean_dec_ref(v___y_1077_);
v___x_1084_ = l_Lean_mkApp9(v___x_1074_, v___y_1076_, v___y_1080_, v___y_1078_, v___y_1081_, v___y_1082_, v___x_1083_, v_v_1070_, v_px_1071_, v_py_1072_);
return v___x_1084_;
}
v___jp_1085_:
{
lean_object* v_type_1089_; lean_object* v_nil_1090_; lean_object* v_cons_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v_type_1089_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_nil_1090_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1091_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1092_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1090_, v_cons_1091_, v_x_1067_);
v___x_1093_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1094_ = lean_int_dec_le(v___x_1093_, v_b_1068_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1095_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1096_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1097_ = lean_int_neg(v_b_1068_);
v___x_1098_ = l_Int_toNat(v___x_1097_);
lean_dec(v___x_1097_);
v___x_1099_ = l_Lean_instToExprInt_mkNat(v___x_1098_);
v___x_1100_ = l_Lean_mkApp3(v___x_1095_, v_type_1089_, v___x_1096_, v___x_1099_);
v___y_1076_ = v___y_1086_;
v___y_1077_ = v_nil_1090_;
v___y_1078_ = v___y_1088_;
v___y_1079_ = v_cons_1091_;
v___y_1080_ = v___y_1087_;
v___y_1081_ = v___x_1092_;
v___y_1082_ = v___x_1100_;
goto v___jp_1075_;
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = l_Int_toNat(v_b_1068_);
v___x_1102_ = l_Lean_instToExprInt_mkNat(v___x_1101_);
v___y_1076_ = v___y_1086_;
v___y_1077_ = v_nil_1090_;
v___y_1078_ = v___y_1088_;
v___y_1079_ = v_cons_1091_;
v___y_1080_ = v___y_1087_;
v___y_1081_ = v___x_1092_;
v___y_1082_ = v___x_1102_;
goto v___jp_1075_;
}
}
v___jp_1103_:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1107_ = lean_int_dec_le(v___x_1106_, v_a_1066_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1108_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1109_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1110_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1111_ = lean_int_neg(v_a_1066_);
v___x_1112_ = l_Int_toNat(v___x_1111_);
lean_dec(v___x_1111_);
v___x_1113_ = l_Lean_instToExprInt_mkNat(v___x_1112_);
v___x_1114_ = l_Lean_mkApp3(v___x_1108_, v___x_1109_, v___x_1110_, v___x_1113_);
v___y_1086_ = v___y_1104_;
v___y_1087_ = v___y_1105_;
v___y_1088_ = v___x_1114_;
goto v___jp_1085_;
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = l_Int_toNat(v_a_1066_);
v___x_1116_ = l_Lean_instToExprInt_mkNat(v___x_1115_);
v___y_1086_ = v___y_1104_;
v___y_1087_ = v___y_1105_;
v___y_1088_ = v___x_1116_;
goto v___jp_1085_;
}
}
v___jp_1117_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = l_Lean_mkAppB(v___y_1121_, v___y_1119_, v___y_1122_);
v___x_1124_ = l_Lean_Expr_app___override(v___y_1120_, v___x_1123_);
v___y_1104_ = v___y_1118_;
v___y_1105_ = v___x_1124_;
goto v___jp_1103_;
}
v___jp_1125_:
{
lean_object* v_upperBound_1131_; lean_object* v___x_1132_; 
v_upperBound_1131_ = lean_ctor_get(v_t_1065_, 1);
v___x_1132_ = l_Lean_Expr_app___override(v___y_1129_, v___y_1130_);
if (lean_obj_tag(v_upperBound_1131_) == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec_ref(v___y_1127_);
v___x_1133_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1134_ = l_Lean_Expr_app___override(v___x_1133_, v___y_1128_);
v___x_1135_ = l_Lean_Expr_app___override(v___x_1132_, v___x_1134_);
v___y_1104_ = v___y_1126_;
v___y_1105_ = v___x_1135_;
goto v___jp_1103_;
}
else
{
lean_object* v_val_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_val_1136_ = lean_ctor_get(v_upperBound_1131_, 0);
v___x_1137_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1138_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1139_ = lean_int_dec_le(v___x_1138_, v_val_1136_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1140_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
v___x_1142_ = l_Lean_Name_mkStr2(v___y_1127_, v___x_1141_);
v___x_1143_ = l_Lean_Expr_const___override(v___x_1142_, v___x_1073_);
v___x_1144_ = lean_int_neg(v_val_1136_);
v___x_1145_ = l_Int_toNat(v___x_1144_);
lean_dec(v___x_1144_);
v___x_1146_ = l_Lean_instToExprInt_mkNat(v___x_1145_);
lean_inc_ref(v___y_1128_);
v___x_1147_ = l_Lean_mkApp3(v___x_1140_, v___y_1128_, v___x_1143_, v___x_1146_);
v___y_1118_ = v___y_1126_;
v___y_1119_ = v___y_1128_;
v___y_1120_ = v___x_1132_;
v___y_1121_ = v___x_1137_;
v___y_1122_ = v___x_1147_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec_ref(v___y_1127_);
v___x_1148_ = l_Int_toNat(v_val_1136_);
v___x_1149_ = l_Lean_instToExprInt_mkNat(v___x_1148_);
v___y_1118_ = v___y_1126_;
v___y_1119_ = v___y_1128_;
v___y_1120_ = v___x_1132_;
v___y_1121_ = v___x_1137_;
v___y_1122_ = v___x_1149_;
goto v___jp_1117_;
}
}
}
v___jp_1150_:
{
lean_object* v___x_1157_; 
lean_inc_ref(v___y_1153_);
v___x_1157_ = l_Lean_mkAppB(v___y_1154_, v___y_1153_, v___y_1156_);
v___y_1126_ = v___y_1151_;
v___y_1127_ = v___y_1152_;
v___y_1128_ = v___y_1153_;
v___y_1129_ = v___y_1155_;
v___y_1130_ = v___x_1157_;
goto v___jp_1125_;
}
v___jp_1158_:
{
lean_object* v_lowerBound_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v_type_1163_; 
v_lowerBound_1160_ = lean_ctor_get(v_t_1065_, 0);
v___x_1161_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1162_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1163_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1160_) == 0)
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1126_ = v___y_1159_;
v___y_1127_ = v___x_1162_;
v___y_1128_ = v_type_1163_;
v___y_1129_ = v___x_1161_;
v___y_1130_ = v___x_1164_;
goto v___jp_1125_;
}
else
{
lean_object* v_val_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v_val_1165_ = lean_ctor_get(v_lowerBound_1160_, 0);
v___x_1166_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1167_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1168_ = lean_int_dec_le(v___x_1167_, v_val_1165_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1169_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1170_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1171_ = lean_int_neg(v_val_1165_);
v___x_1172_ = l_Int_toNat(v___x_1171_);
lean_dec(v___x_1171_);
v___x_1173_ = l_Lean_instToExprInt_mkNat(v___x_1172_);
v___x_1174_ = l_Lean_mkApp3(v___x_1169_, v_type_1163_, v___x_1170_, v___x_1173_);
v___y_1151_ = v___y_1159_;
v___y_1152_ = v___x_1162_;
v___y_1153_ = v_type_1163_;
v___y_1154_ = v___x_1166_;
v___y_1155_ = v___x_1161_;
v___y_1156_ = v___x_1174_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = l_Int_toNat(v_val_1165_);
v___x_1176_ = l_Lean_instToExprInt_mkNat(v___x_1175_);
v___y_1151_ = v___y_1159_;
v___y_1152_ = v___x_1162_;
v___y_1153_ = v_type_1163_;
v___y_1154_ = v___x_1166_;
v___y_1155_ = v___x_1161_;
v___y_1156_ = v___x_1176_;
goto v___jp_1150_;
}
}
}
v___jp_1181_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = l_Lean_mkAppB(v___y_1183_, v_type_1180_, v___y_1184_);
v___x_1186_ = l_Lean_Expr_app___override(v___y_1182_, v___x_1185_);
v___y_1159_ = v___x_1186_;
goto v___jp_1158_;
}
v___jp_1187_:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Expr_app___override(v___x_1179_, v___y_1188_);
if (lean_obj_tag(v_upperBound_1178_) == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1191_ = l_Lean_Expr_app___override(v___x_1189_, v___x_1190_);
v___y_1159_ = v___x_1191_;
goto v___jp_1158_;
}
else
{
lean_object* v_val_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v_val_1192_ = lean_ctor_get(v_upperBound_1178_, 0);
v___x_1193_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1194_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1195_ = lean_int_dec_le(v___x_1194_, v_val_1192_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1196_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1197_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1198_ = lean_int_neg(v_val_1192_);
v___x_1199_ = l_Int_toNat(v___x_1198_);
lean_dec(v___x_1198_);
v___x_1200_ = l_Lean_instToExprInt_mkNat(v___x_1199_);
v___x_1201_ = l_Lean_mkApp3(v___x_1196_, v_type_1180_, v___x_1197_, v___x_1200_);
v___y_1182_ = v___x_1189_;
v___y_1183_ = v___x_1193_;
v___y_1184_ = v___x_1201_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = l_Int_toNat(v_val_1192_);
v___x_1203_ = l_Lean_instToExprInt_mkNat(v___x_1202_);
v___y_1182_ = v___x_1189_;
v___y_1183_ = v___x_1193_;
v___y_1184_ = v___x_1203_;
goto v___jp_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___boxed(lean_object* v_s_1220_, lean_object* v_t_1221_, lean_object* v_a_1222_, lean_object* v_x_1223_, lean_object* v_b_1224_, lean_object* v_y_1225_, lean_object* v_v_1226_, lean_object* v_px_1227_, lean_object* v_py_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1220_, v_t_1221_, v_a_1222_, v_x_1223_, v_b_1224_, v_y_1225_, v_v_1226_, v_px_1227_, v_py_1228_);
lean_dec(v_y_1225_);
lean_dec(v_b_1224_);
lean_dec(v_x_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_t_1221_);
lean_dec_ref(v_s_1220_);
return v_res_1229_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_1236_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2));
v___x_1237_ = l_Lean_Expr_const___override(v___x_1236_, v___x_1235_);
return v___x_1237_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_box(0);
v___x_1242_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5));
v___x_1243_ = l_Lean_Expr_const___override(v___x_1242_, v___x_1241_);
return v___x_1243_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = lean_box(0);
v___x_1248_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8));
v___x_1249_ = l_Lean_Expr_const___override(v___x_1248_, v___x_1247_);
return v___x_1249_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_box(0);
v___x_1258_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12));
v___x_1259_ = l_Lean_Expr_const___override(v___x_1258_, v___x_1257_);
return v___x_1259_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = lean_box(0);
v___x_1267_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15));
v___x_1268_ = l_Lean_Expr_const___override(v___x_1267_, v___x_1266_);
return v___x_1268_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_box(0);
v___x_1275_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18));
v___x_1276_ = l_Lean_Expr_const___override(v___x_1275_, v___x_1274_);
return v___x_1276_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_box(0);
v___x_1283_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21));
v___x_1284_ = l_Lean_Expr_const___override(v___x_1283_, v___x_1282_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof(lean_object* v_m_1285_, lean_object* v_r_1286_, lean_object* v_i_1287_, lean_object* v_x_1288_, lean_object* v_v_1289_, lean_object* v_w_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_m_1296_; lean_object* v___y_1298_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v_m_1296_ = l_Lean_mkNatLit(v_m_1285_);
v___x_1326_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1327_ = lean_int_dec_le(v___x_1326_, v_r_1286_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1328_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1329_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1330_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1331_ = lean_int_neg(v_r_1286_);
v___x_1332_ = l_Int_toNat(v___x_1331_);
lean_dec(v___x_1331_);
v___x_1333_ = l_Lean_instToExprInt_mkNat(v___x_1332_);
v___x_1334_ = l_Lean_mkApp3(v___x_1328_, v___x_1329_, v___x_1330_, v___x_1333_);
v___y_1298_ = v___x_1334_;
goto v___jp_1297_;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = l_Int_toNat(v_r_1286_);
v___x_1336_ = l_Lean_instToExprInt_mkNat(v___x_1335_);
v___y_1298_ = v___x_1336_;
goto v___jp_1297_;
}
v___jp_1297_:
{
lean_object* v_i_1299_; lean_object* v_nil_1300_; lean_object* v_cons_1301_; lean_object* v_x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_i_1299_ = l_Lean_mkNatLit(v_i_1287_);
v_nil_1300_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1301_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v_x_1302_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1300_, v_cons_1301_, v_x_1288_);
v___x_1303_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3);
v___x_1304_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6);
v___x_1305_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9);
v___x_1306_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13);
lean_inc_ref(v_x_1302_);
v___x_1307_ = l_Lean_Expr_app___override(v___x_1306_, v_x_1302_);
lean_inc_ref(v_i_1299_);
v___x_1308_ = l_Lean_mkApp4(v___x_1303_, v___x_1304_, v___x_1305_, v___x_1307_, v_i_1299_);
lean_inc(v_a_1294_);
lean_inc_ref(v_a_1293_);
lean_inc(v_a_1292_);
lean_inc_ref(v_a_1291_);
v___x_1309_ = l_Lean_Meta_mkDecideProof(v___x_1308_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref(v___x_1309_);
v___x_1311_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16);
lean_inc_ref(v_i_1299_);
lean_inc_ref(v_v_1289_);
v___x_1312_ = l_Lean_mkAppB(v___x_1311_, v_v_1289_, v_i_1299_);
v___x_1313_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc_ref(v_v_1289_);
lean_inc_ref(v_x_1302_);
lean_inc_ref(v_m_1296_);
v___x_1314_ = l_Lean_mkApp3(v___x_1313_, v_m_1296_, v_x_1302_, v_v_1289_);
v___x_1315_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v___x_1312_, v___x_1314_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1325_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1325_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1325_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1320_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22);
v___x_1321_ = l_Lean_mkApp8(v___x_1320_, v_m_1296_, v___y_1298_, v_i_1299_, v_x_1302_, v_v_1289_, v_a_1310_, v_a_1316_, v_w_1290_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1321_);
v___x_1323_ = v___x_1318_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
else
{
lean_dec(v_a_1310_);
lean_dec_ref(v_x_1302_);
lean_dec_ref(v_i_1299_);
lean_dec_ref(v___y_1298_);
lean_dec_ref(v_m_1296_);
lean_dec_ref(v_w_1290_);
lean_dec_ref(v_v_1289_);
return v___x_1315_;
}
}
else
{
lean_dec_ref(v_x_1302_);
lean_dec_ref(v_i_1299_);
lean_dec_ref(v___y_1298_);
lean_dec_ref(v_m_1296_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec_ref(v_w_1290_);
lean_dec_ref(v_v_1289_);
return v___x_1309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___boxed(lean_object* v_m_1337_, lean_object* v_r_1338_, lean_object* v_i_1339_, lean_object* v_x_1340_, lean_object* v_v_1341_, lean_object* v_w_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1337_, v_r_1338_, v_i_1339_, v_x_1340_, v_v_1341_, v_w_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_);
lean_dec(v_x_1340_);
lean_dec(v_r_1338_);
return v_res_1348_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0(void){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0);
v___x_1351_ = l_ReaderT_instMonad___redArg(v___x_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(lean_object* v_c_1356_, lean_object* v_v_1357_, lean_object* v_assumptions_1358_, lean_object* v_x_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, uint8_t v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v_toApplicative_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1496_; 
v___x_1370_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1);
v_toApplicative_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v___x_1370_, 1);
lean_dec(v_unused_1497_);
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1496_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_toApplicative_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1496_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_toFunctor_1375_; lean_object* v_toSeq_1376_; lean_object* v_toSeqLeft_1377_; lean_object* v_toSeqRight_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1494_; 
v_toFunctor_1375_ = lean_ctor_get(v_toApplicative_1371_, 0);
v_toSeq_1376_ = lean_ctor_get(v_toApplicative_1371_, 2);
v_toSeqLeft_1377_ = lean_ctor_get(v_toApplicative_1371_, 3);
v_toSeqRight_1378_ = lean_ctor_get(v_toApplicative_1371_, 4);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_toApplicative_1371_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; 
v_unused_1495_ = lean_ctor_get(v_toApplicative_1371_, 1);
lean_dec(v_unused_1495_);
v___x_1380_ = v_toApplicative_1371_;
v_isShared_1381_ = v_isSharedCheck_1494_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_toSeqRight_1378_);
lean_inc(v_toSeqLeft_1377_);
lean_inc(v_toSeq_1376_);
lean_inc(v_toFunctor_1375_);
lean_dec(v_toApplicative_1371_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1494_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___f_1382_; lean_object* v___f_1383_; lean_object* v___f_1384_; lean_object* v___f_1385_; lean_object* v___x_1386_; lean_object* v___f_1387_; lean_object* v___f_1388_; lean_object* v___f_1389_; lean_object* v___x_1391_; 
v___f_1382_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2));
v___f_1383_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3));
lean_inc_ref(v_toFunctor_1375_);
v___f_1384_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1384_, 0, v_toFunctor_1375_);
v___f_1385_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1385_, 0, v_toFunctor_1375_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___f_1384_);
lean_ctor_set(v___x_1386_, 1, v___f_1385_);
v___f_1387_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1387_, 0, v_toSeqRight_1378_);
v___f_1388_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1388_, 0, v_toSeqLeft_1377_);
v___f_1389_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1389_, 0, v_toSeq_1376_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 4, v___f_1387_);
lean_ctor_set(v___x_1380_, 3, v___f_1388_);
lean_ctor_set(v___x_1380_, 2, v___f_1389_);
lean_ctor_set(v___x_1380_, 1, v___f_1382_);
lean_ctor_set(v___x_1380_, 0, v___x_1386_);
v___x_1391_ = v___x_1380_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___f_1382_);
lean_ctor_set(v_reuseFailAlloc_1493_, 2, v___f_1389_);
lean_ctor_set(v_reuseFailAlloc_1493_, 3, v___f_1388_);
lean_ctor_set(v_reuseFailAlloc_1493_, 4, v___f_1387_);
v___x_1391_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1393_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v___f_1383_);
lean_ctor_set(v___x_1373_, 0, v___x_1391_);
v___x_1393_ = v___x_1373_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___f_1383_);
v___x_1393_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; lean_object* v_toApplicative_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1490_; 
v___x_1394_ = l_ReaderT_instMonad___redArg(v___x_1393_);
v_toApplicative_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; 
v_unused_1491_ = lean_ctor_get(v___x_1394_, 1);
lean_dec(v_unused_1491_);
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1490_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_toApplicative_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1490_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_toFunctor_1399_; lean_object* v_toSeq_1400_; lean_object* v_toSeqLeft_1401_; lean_object* v_toSeqRight_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1488_; 
v_toFunctor_1399_ = lean_ctor_get(v_toApplicative_1395_, 0);
v_toSeq_1400_ = lean_ctor_get(v_toApplicative_1395_, 2);
v_toSeqLeft_1401_ = lean_ctor_get(v_toApplicative_1395_, 3);
v_toSeqRight_1402_ = lean_ctor_get(v_toApplicative_1395_, 4);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_toApplicative_1395_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v_toApplicative_1395_, 1);
lean_dec(v_unused_1489_);
v___x_1404_ = v_toApplicative_1395_;
v_isShared_1405_ = v_isSharedCheck_1488_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_toSeqRight_1402_);
lean_inc(v_toSeqLeft_1401_);
lean_inc(v_toSeq_1400_);
lean_inc(v_toFunctor_1399_);
lean_dec(v_toApplicative_1395_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1488_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___f_1406_; lean_object* v___f_1407_; lean_object* v___f_1408_; lean_object* v___f_1409_; lean_object* v___x_1410_; lean_object* v___f_1411_; lean_object* v___f_1412_; lean_object* v___f_1413_; lean_object* v___x_1415_; 
v___f_1406_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4));
v___f_1407_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5));
lean_inc_ref(v_toFunctor_1399_);
v___f_1408_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1408_, 0, v_toFunctor_1399_);
v___f_1409_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1409_, 0, v_toFunctor_1399_);
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___f_1408_);
lean_ctor_set(v___x_1410_, 1, v___f_1409_);
v___f_1411_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1411_, 0, v_toSeqRight_1402_);
v___f_1412_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1412_, 0, v_toSeqLeft_1401_);
v___f_1413_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1413_, 0, v_toSeq_1400_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v___f_1411_);
lean_ctor_set(v___x_1404_, 3, v___f_1412_);
lean_ctor_set(v___x_1404_, 2, v___f_1413_);
lean_ctor_set(v___x_1404_, 1, v___f_1406_);
lean_ctor_set(v___x_1404_, 0, v___x_1410_);
v___x_1415_ = v___x_1404_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___f_1406_);
lean_ctor_set(v_reuseFailAlloc_1487_, 2, v___f_1413_);
lean_ctor_set(v_reuseFailAlloc_1487_, 3, v___f_1412_);
lean_ctor_set(v_reuseFailAlloc_1487_, 4, v___f_1411_);
v___x_1415_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v___f_1407_);
lean_ctor_set(v___x_1397_, 0, v___x_1415_);
v___x_1417_ = v___x_1397_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___f_1407_);
v___x_1417_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1418_ = l_ReaderT_instMonad___redArg(v___x_1417_);
v___x_1419_ = l_ReaderT_instMonad___redArg(v___x_1418_);
v___x_1420_ = l_ReaderT_instMonad___redArg(v___x_1419_);
v___x_1421_ = l_ReaderT_instMonad___redArg(v___x_1420_);
v___x_1422_ = l_ReaderT_instMonad___redArg(v___x_1421_);
switch(lean_obj_tag(v_x_1359_))
{
case 0:
{
lean_object* v_i_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_4123__overap_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_dec_ref(v_v_1357_);
v_i_1423_ = lean_ctor_get(v_x_1359_, 2);
lean_inc(v_i_1423_);
lean_dec_ref(v_x_1359_);
v___x_1424_ = l_Lean_instInhabitedExpr;
v___x_1425_ = l_instInhabitedOfMonad___redArg(v___x_1422_, v___x_1424_);
v___x_4123__overap_1426_ = lean_array_get_borrowed(v___x_1425_, v_assumptions_1358_, v_i_1423_);
lean_dec(v_i_1423_);
v___x_1427_ = lean_box(v_a_1363_);
lean_inc(v___x_4123__overap_1426_);
v___x_1428_ = lean_apply_10(v___x_4123__overap_1426_, v_a_1360_, v_a_1361_, v_a_1362_, v___x_1427_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, lean_box(0));
return v___x_1428_;
}
case 1:
{
lean_object* v_s_1429_; lean_object* v_c_1430_; lean_object* v_j_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v___x_1422_);
v_s_1429_ = lean_ctor_get(v_x_1359_, 0);
lean_inc_ref(v_s_1429_);
v_c_1430_ = lean_ctor_get(v_x_1359_, 1);
lean_inc(v_c_1430_);
v_j_1431_ = lean_ctor_get(v_x_1359_, 2);
lean_inc_ref(v_j_1431_);
lean_dec_ref(v_x_1359_);
lean_inc_ref(v_v_1357_);
v___x_1432_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1430_, v_v_1357_, v_assumptions_1358_, v_j_1431_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1441_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1441_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1441_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1437_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1429_, v_c_1430_, v_v_1357_, v_a_1433_);
lean_dec(v_c_1430_);
lean_dec_ref(v_s_1429_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1437_);
v___x_1439_ = v___x_1435_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
else
{
lean_dec(v_c_1430_);
lean_dec_ref(v_s_1429_);
lean_dec_ref(v_v_1357_);
return v___x_1432_;
}
}
case 2:
{
lean_object* v_s_1442_; lean_object* v_t_1443_; lean_object* v_j_1444_; lean_object* v_k_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v___x_1422_);
v_s_1442_ = lean_ctor_get(v_x_1359_, 0);
lean_inc_ref(v_s_1442_);
v_t_1443_ = lean_ctor_get(v_x_1359_, 1);
lean_inc_ref(v_t_1443_);
v_j_1444_ = lean_ctor_get(v_x_1359_, 3);
lean_inc_ref(v_j_1444_);
v_k_1445_ = lean_ctor_get(v_x_1359_, 4);
lean_inc_ref(v_k_1445_);
lean_dec_ref(v_x_1359_);
lean_inc(v_a_1368_);
lean_inc_ref(v_a_1367_);
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
lean_inc(v_a_1364_);
lean_inc_ref(v_a_1362_);
lean_inc(v_a_1361_);
lean_inc(v_a_1360_);
lean_inc_ref(v_v_1357_);
v___x_1446_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1356_, v_v_1357_, v_assumptions_1358_, v_j_1444_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1448_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref(v___x_1446_);
lean_inc_ref(v_v_1357_);
v___x_1448_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1356_, v_v_1357_, v_assumptions_1358_, v_k_1445_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1457_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1442_, v_t_1443_, v_c_1356_, v_v_1357_, v_a_1447_, v_a_1449_);
lean_dec_ref(v_t_1443_);
lean_dec_ref(v_s_1442_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1453_);
v___x_1455_ = v___x_1451_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
else
{
lean_dec(v_a_1447_);
lean_dec_ref(v_t_1443_);
lean_dec_ref(v_s_1442_);
lean_dec_ref(v_v_1357_);
return v___x_1448_;
}
}
else
{
lean_dec_ref(v_k_1445_);
lean_dec_ref(v_t_1443_);
lean_dec_ref(v_s_1442_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_v_1357_);
return v___x_1446_;
}
}
case 3:
{
lean_object* v_s_1458_; lean_object* v_t_1459_; lean_object* v_x_1460_; lean_object* v_y_1461_; lean_object* v_a_1462_; lean_object* v_j_1463_; lean_object* v_b_1464_; lean_object* v_k_1465_; lean_object* v___x_1466_; 
lean_dec_ref(v___x_1422_);
v_s_1458_ = lean_ctor_get(v_x_1359_, 0);
lean_inc_ref(v_s_1458_);
v_t_1459_ = lean_ctor_get(v_x_1359_, 1);
lean_inc_ref(v_t_1459_);
v_x_1460_ = lean_ctor_get(v_x_1359_, 2);
lean_inc(v_x_1460_);
v_y_1461_ = lean_ctor_get(v_x_1359_, 3);
lean_inc(v_y_1461_);
v_a_1462_ = lean_ctor_get(v_x_1359_, 4);
lean_inc(v_a_1462_);
v_j_1463_ = lean_ctor_get(v_x_1359_, 5);
lean_inc_ref(v_j_1463_);
v_b_1464_ = lean_ctor_get(v_x_1359_, 6);
lean_inc(v_b_1464_);
v_k_1465_ = lean_ctor_get(v_x_1359_, 7);
lean_inc_ref(v_k_1465_);
lean_dec_ref(v_x_1359_);
lean_inc(v_a_1368_);
lean_inc_ref(v_a_1367_);
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
lean_inc(v_a_1364_);
lean_inc_ref(v_a_1362_);
lean_inc(v_a_1361_);
lean_inc(v_a_1360_);
lean_inc_ref(v_v_1357_);
v___x_1466_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1460_, v_v_1357_, v_assumptions_1358_, v_j_1463_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref(v___x_1466_);
lean_inc_ref(v_v_1357_);
v___x_1468_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_y_1461_, v_v_1357_, v_assumptions_1358_, v_k_1465_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1477_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1458_, v_t_1459_, v_a_1462_, v_x_1460_, v_b_1464_, v_y_1461_, v_v_1357_, v_a_1467_, v_a_1469_);
lean_dec(v_y_1461_);
lean_dec(v_b_1464_);
lean_dec(v_x_1460_);
lean_dec(v_a_1462_);
lean_dec_ref(v_t_1459_);
lean_dec_ref(v_s_1458_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1473_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
else
{
lean_dec(v_a_1467_);
lean_dec(v_b_1464_);
lean_dec(v_a_1462_);
lean_dec(v_y_1461_);
lean_dec(v_x_1460_);
lean_dec_ref(v_t_1459_);
lean_dec_ref(v_s_1458_);
lean_dec_ref(v_v_1357_);
return v___x_1468_;
}
}
else
{
lean_dec_ref(v_k_1465_);
lean_dec(v_b_1464_);
lean_dec(v_a_1462_);
lean_dec(v_y_1461_);
lean_dec(v_x_1460_);
lean_dec_ref(v_t_1459_);
lean_dec_ref(v_s_1458_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_v_1357_);
return v___x_1466_;
}
}
default: 
{
lean_object* v_m_1478_; lean_object* v_r_1479_; lean_object* v_i_1480_; lean_object* v_x_1481_; lean_object* v_j_1482_; lean_object* v___x_1483_; 
lean_dec_ref(v___x_1422_);
v_m_1478_ = lean_ctor_get(v_x_1359_, 0);
lean_inc(v_m_1478_);
v_r_1479_ = lean_ctor_get(v_x_1359_, 1);
lean_inc(v_r_1479_);
v_i_1480_ = lean_ctor_get(v_x_1359_, 2);
lean_inc(v_i_1480_);
v_x_1481_ = lean_ctor_get(v_x_1359_, 3);
lean_inc(v_x_1481_);
v_j_1482_ = lean_ctor_get(v_x_1359_, 4);
lean_inc_ref(v_j_1482_);
lean_dec_ref(v_x_1359_);
lean_inc(v_a_1368_);
lean_inc_ref(v_a_1367_);
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
lean_inc_ref(v_v_1357_);
v___x_1483_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1481_, v_v_1357_, v_assumptions_1358_, v_j_1482_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1478_, v_r_1479_, v_i_1480_, v_x_1481_, v_v_1357_, v_a_1484_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
lean_dec(v_x_1481_);
lean_dec(v_r_1479_);
return v___x_1485_;
}
else
{
lean_dec(v_x_1481_);
lean_dec(v_i_1480_);
lean_dec(v_r_1479_);
lean_dec(v_m_1478_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec_ref(v_v_1357_);
return v___x_1483_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___boxed(lean_object* v_c_1498_, lean_object* v_v_1499_, lean_object* v_assumptions_1500_, lean_object* v_x_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
uint8_t v_a_4222__boxed_1512_; lean_object* v_res_1513_; 
v_a_4222__boxed_1512_ = lean_unbox(v_a_1505_);
v_res_1513_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1498_, v_v_1499_, v_assumptions_1500_, v_x_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_4222__boxed_1512_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
lean_dec_ref(v_assumptions_1500_);
lean_dec(v_c_1498_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof(lean_object* v_s_1514_, lean_object* v_c_1515_, lean_object* v_v_1516_, lean_object* v_assumptions_1517_, lean_object* v_x_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, uint8_t v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1515_, v_v_1516_, v_assumptions_1517_, v_x_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___boxed(lean_object* v_s_1530_, lean_object* v_c_1531_, lean_object* v_v_1532_, lean_object* v_assumptions_1533_, lean_object* v_x_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
uint8_t v_a_4505__boxed_1545_; lean_object* v_res_1546_; 
v_a_4505__boxed_1545_ = lean_unbox(v_a_1538_);
v_res_1546_ = l_Lean_Elab_Tactic_Omega_Justification_proof(v_s_1530_, v_c_1531_, v_v_1532_, v_assumptions_1533_, v_x_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_4505__boxed_1545_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
lean_dec_ref(v_assumptions_1533_);
lean_dec(v_c_1531_);
lean_dec_ref(v_s_1530_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_instToString___lam__0(lean_object* v_f_1547_){
_start:
{
lean_object* v_coeffs_1548_; lean_object* v_constraint_1549_; lean_object* v_justification_1550_; lean_object* v___x_1551_; 
v_coeffs_1548_ = lean_ctor_get(v_f_1547_, 0);
lean_inc(v_coeffs_1548_);
v_constraint_1549_ = lean_ctor_get(v_f_1547_, 1);
lean_inc_ref(v_constraint_1549_);
v_justification_1550_ = lean_ctor_get(v_f_1547_, 2);
lean_inc_ref(v_justification_1550_);
lean_dec_ref(v_f_1547_);
v___x_1551_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_1549_, v_coeffs_1548_, v_justification_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_tidy(lean_object* v_f_1554_){
_start:
{
lean_object* v_coeffs_1555_; lean_object* v_constraint_1556_; lean_object* v_justification_1557_; lean_object* v___x_1558_; 
v_coeffs_1555_ = lean_ctor_get(v_f_1554_, 0);
v_constraint_1556_ = lean_ctor_get(v_f_1554_, 1);
v_justification_1557_ = lean_ctor_get(v_f_1554_, 2);
lean_inc_ref(v_justification_1557_);
lean_inc(v_coeffs_1555_);
lean_inc_ref(v_constraint_1556_);
v___x_1558_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(v_constraint_1556_, v_coeffs_1555_, v_justification_1557_);
if (lean_obj_tag(v___x_1558_) == 0)
{
return v_f_1554_;
}
else
{
lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1570_; 
v_isSharedCheck_1570_ = !lean_is_exclusive(v_f_1554_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; lean_object* v_unused_1572_; lean_object* v_unused_1573_; 
v_unused_1571_ = lean_ctor_get(v_f_1554_, 2);
lean_dec(v_unused_1571_);
v_unused_1572_ = lean_ctor_get(v_f_1554_, 1);
lean_dec(v_unused_1572_);
v_unused_1573_ = lean_ctor_get(v_f_1554_, 0);
lean_dec(v_unused_1573_);
v___x_1560_ = v_f_1554_;
v_isShared_1561_ = v_isSharedCheck_1570_;
goto v_resetjp_1559_;
}
else
{
lean_dec(v_f_1554_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1570_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v_val_1562_; lean_object* v_snd_1563_; lean_object* v_fst_1564_; lean_object* v_fst_1565_; lean_object* v_snd_1566_; lean_object* v___x_1568_; 
v_val_1562_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_val_1562_);
lean_dec_ref(v___x_1558_);
v_snd_1563_ = lean_ctor_get(v_val_1562_, 1);
lean_inc(v_snd_1563_);
v_fst_1564_ = lean_ctor_get(v_val_1562_, 0);
lean_inc(v_fst_1564_);
lean_dec(v_val_1562_);
v_fst_1565_ = lean_ctor_get(v_snd_1563_, 0);
lean_inc(v_fst_1565_);
v_snd_1566_ = lean_ctor_get(v_snd_1563_, 1);
lean_inc(v_snd_1566_);
lean_dec(v_snd_1563_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 2, v_snd_1566_);
lean_ctor_set(v___x_1560_, 1, v_fst_1564_);
lean_ctor_set(v___x_1560_, 0, v_fst_1565_);
v___x_1568_ = v___x_1560_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_fst_1565_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_fst_1564_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_snd_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_combo(lean_object* v_a_1574_, lean_object* v_f_1575_, lean_object* v_b_1576_, lean_object* v_g_1577_){
_start:
{
lean_object* v_coeffs_1578_; lean_object* v_constraint_1579_; lean_object* v_justification_1580_; lean_object* v_coeffs_1581_; lean_object* v_constraint_1582_; lean_object* v_justification_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1593_; 
v_coeffs_1578_ = lean_ctor_get(v_f_1575_, 0);
lean_inc(v_coeffs_1578_);
v_constraint_1579_ = lean_ctor_get(v_f_1575_, 1);
lean_inc_ref(v_constraint_1579_);
v_justification_1580_ = lean_ctor_get(v_f_1575_, 2);
lean_inc_ref(v_justification_1580_);
lean_dec_ref(v_f_1575_);
v_coeffs_1581_ = lean_ctor_get(v_g_1577_, 0);
v_constraint_1582_ = lean_ctor_get(v_g_1577_, 1);
v_justification_1583_ = lean_ctor_get(v_g_1577_, 2);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_g_1577_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1585_ = v_g_1577_;
v_isShared_1586_ = v_isSharedCheck_1593_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_justification_1583_);
lean_inc(v_constraint_1582_);
lean_inc(v_coeffs_1581_);
lean_dec(v_g_1577_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1593_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
lean_inc(v_coeffs_1581_);
lean_inc(v_b_1576_);
lean_inc(v_coeffs_1578_);
lean_inc(v_a_1574_);
v___x_1587_ = l_Lean_Omega_IntList_combo(v_a_1574_, v_coeffs_1578_, v_b_1576_, v_coeffs_1581_);
lean_inc_ref(v_constraint_1582_);
lean_inc(v_b_1576_);
lean_inc_ref(v_constraint_1579_);
lean_inc(v_a_1574_);
v___x_1588_ = l_Lean_Omega_Constraint_combo(v_a_1574_, v_constraint_1579_, v_b_1576_, v_constraint_1582_);
v___x_1589_ = lean_alloc_ctor(3, 8, 0);
lean_ctor_set(v___x_1589_, 0, v_constraint_1579_);
lean_ctor_set(v___x_1589_, 1, v_constraint_1582_);
lean_ctor_set(v___x_1589_, 2, v_coeffs_1578_);
lean_ctor_set(v___x_1589_, 3, v_coeffs_1581_);
lean_ctor_set(v___x_1589_, 4, v_a_1574_);
lean_ctor_set(v___x_1589_, 5, v_justification_1580_);
lean_ctor_set(v___x_1589_, 6, v_b_1576_);
lean_ctor_set(v___x_1589_, 7, v_justification_1583_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 2, v___x_1589_);
lean_ctor_set(v___x_1585_, 1, v___x_1588_);
lean_ctor_set(v___x_1585_, 0, v___x_1587_);
v___x_1591_ = v___x_1585_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__10));
v___x_1620_ = l_Lean_mkAtom(v___x_1619_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1621_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11);
v___x_1622_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_1623_ = lean_array_push(v___x_1622_, v___x_1621_);
return v___x_1623_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1624_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12);
v___x_1625_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9));
v___x_1626_ = lean_box(2);
v___x_1627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v___x_1625_);
lean_ctor_set(v___x_1627_, 2, v___x_1624_);
return v___x_1627_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13);
v___x_1629_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_1630_ = lean_array_push(v___x_1629_, v___x_1628_);
return v___x_1630_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1631_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14);
v___x_1632_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7));
v___x_1633_ = lean_box(2);
v___x_1634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
lean_ctor_set(v___x_1634_, 1, v___x_1632_);
lean_ctor_set(v___x_1634_, 2, v___x_1631_);
return v___x_1634_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15);
v___x_1636_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_1637_ = lean_array_push(v___x_1636_, v___x_1635_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1638_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16);
v___x_1639_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5));
v___x_1640_ = lean_box(2);
v___x_1641_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_ctor_set(v___x_1641_, 1, v___x_1639_);
lean_ctor_set(v___x_1641_, 2, v___x_1638_);
return v___x_1641_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1642_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17);
v___x_1643_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_1644_ = lean_array_push(v___x_1643_, v___x_1642_);
return v___x_1644_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1645_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18);
v___x_1646_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2));
v___x_1647_ = lean_box(2);
v___x_1648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v___x_1646_);
lean_ctor_set(v___x_1648_, 2, v___x_1645_);
return v___x_1648_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam(void){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19);
return v___x_1649_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_isEmpty(lean_object* v_p_1650_){
_start:
{
lean_object* v_constraints_1651_; lean_object* v_size_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v_constraints_1651_ = lean_ctor_get(v_p_1650_, 2);
v_size_1652_ = lean_ctor_get(v_constraints_1651_, 0);
v___x_1653_ = lean_unsigned_to_nat(0u);
v___x_1654_ = lean_nat_dec_eq(v_size_1652_, v___x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_isEmpty___boxed(lean_object* v_p_1655_){
_start:
{
uint8_t v_res_1656_; lean_object* v_r_1657_; 
v_res_1656_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_1655_);
lean_dec_ref(v_p_1655_);
v_r_1657_ = lean_box(v_res_1656_);
return v_r_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object* v_x_1659_){
_start:
{
lean_object* v_snd_1660_; lean_object* v_fst_1661_; lean_object* v_constraint_1662_; lean_object* v___f_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_snd_1660_ = lean_ctor_get(v_x_1659_, 1);
lean_inc(v_snd_1660_);
v_fst_1661_ = lean_ctor_get(v_x_1659_, 0);
lean_inc(v_fst_1661_);
lean_dec_ref(v_x_1659_);
v_constraint_1662_ = lean_ctor_get(v_snd_1660_, 1);
lean_inc_ref(v_constraint_1662_);
lean_dec(v_snd_1660_);
v___f_1663_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0___closed__0));
v___x_1664_ = l_List_toString___redArg(v___f_1663_, v_fst_1661_);
v___x_1665_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1666_ = lean_string_append(v___x_1664_, v___x_1665_);
v___x_1667_ = l_Lean_Omega_Constraint_instToString___private__1(v_constraint_1662_);
lean_dec_ref(v_constraint_1662_);
v___x_1668_ = lean_string_append(v___x_1666_, v___x_1667_);
lean_dec_ref(v___x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object* v_a_1669_, lean_object* v_b_1670_, lean_object* v_d_1671_){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v_a_1669_);
lean_ctor_set(v___x_1672_, 1, v_b_1670_);
v___x_1673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set(v___x_1673_, 1, v_d_1671_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2(lean_object* v___x_1674_, lean_object* v___f_1675_, lean_object* v_l_1676_, lean_object* v_acc_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1674_, v___f_1675_, v_acc_1677_, v_l_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3(lean_object* v___f_1700_, lean_object* v___f_1701_, lean_object* v_p_1702_){
_start:
{
uint8_t v_possible_1703_; 
v_possible_1703_ = lean_ctor_get_uint8(v_p_1702_, sizeof(void*)*7);
if (v_possible_1703_ == 0)
{
lean_object* v___x_1704_; 
lean_dec_ref(v_p_1702_);
lean_dec_ref(v___f_1701_);
lean_dec_ref(v___f_1700_);
v___x_1704_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
return v___x_1704_;
}
else
{
lean_object* v_constraints_1705_; uint8_t v___x_1706_; 
v_constraints_1705_ = lean_ctor_get(v_p_1702_, 2);
lean_inc_ref(v_constraints_1705_);
v___x_1706_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_1702_);
lean_dec_ref(v_p_1702_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; lean_object* v_buckets_1708_; lean_object* v___x_1709_; lean_object* v___y_1711_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1707_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10));
v_buckets_1708_ = lean_ctor_get(v_constraints_1705_, 1);
lean_inc_ref(v_buckets_1708_);
lean_dec_ref(v_constraints_1705_);
v___x_1709_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_1715_ = lean_box(0);
v___x_1716_ = lean_array_get_size(v_buckets_1708_);
v___x_1717_ = lean_unsigned_to_nat(0u);
v___x_1718_ = lean_nat_dec_lt(v___x_1717_, v___x_1716_);
if (v___x_1718_ == 0)
{
lean_dec_ref(v_buckets_1708_);
lean_dec_ref(v___f_1701_);
v___y_1711_ = v___x_1715_;
goto v___jp_1710_;
}
else
{
lean_object* v___f_1719_; size_t v___x_1720_; size_t v___x_1721_; lean_object* v___x_1722_; 
v___f_1719_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2), 4, 2);
lean_closure_set(v___f_1719_, 0, v___x_1707_);
lean_closure_set(v___f_1719_, 1, v___f_1701_);
v___x_1720_ = lean_usize_of_nat(v___x_1716_);
v___x_1721_ = ((size_t)0ULL);
v___x_1722_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1707_, v___f_1719_, v_buckets_1708_, v___x_1720_, v___x_1721_, v___x_1715_);
v___y_1711_ = v___x_1722_;
goto v___jp_1710_;
}
v___jp_1710_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_box(0);
v___x_1713_ = l_List_mapTR_loop___redArg(v___f_1700_, v___y_1711_, v___x_1712_);
v___x_1714_ = l_String_intercalate(v___x_1709_, v___x_1713_);
return v___x_1714_;
}
}
else
{
lean_object* v___x_1723_; 
lean_dec_ref(v_constraints_1705_);
lean_dec_ref(v___f_1701_);
lean_dec_ref(v___f_1700_);
v___x_1723_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
return v___x_1723_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_box(0);
v___x_1737_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1));
v___x_1738_ = l_Lean_Expr_const___override(v___x_1737_, v___x_1736_);
return v___x_1738_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_box(0);
v___x_1745_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5));
v___x_1746_ = l_Lean_Expr_const___override(v___x_1745_, v___x_1744_);
return v___x_1746_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_box(0);
v___x_1754_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8));
v___x_1755_ = l_Lean_Expr_const___override(v___x_1754_, v___x_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse(lean_object* v_s_1756_, lean_object* v_x_1757_, lean_object* v_j_1758_, lean_object* v_assumptions_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, uint8_t v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v___x_1770_; 
lean_inc(v_a_1768_);
lean_inc_ref(v_a_1767_);
lean_inc(v_a_1766_);
lean_inc_ref(v_a_1765_);
v___x_1770_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_1761_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1770_);
lean_inc(v_a_1768_);
lean_inc_ref(v_a_1767_);
lean_inc(v_a_1766_);
lean_inc_ref(v_a_1765_);
lean_inc(v_a_1771_);
v___x_1772_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1757_, v_a_1771_, v_assumptions_1759_, v_j_1758_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; lean_object* v_lowerBound_1775_; lean_object* v_upperBound_1776_; lean_object* v_nil_1777_; lean_object* v_cons_1778_; lean_object* v___x_1779_; lean_object* v___y_1781_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___x_1804_; lean_object* v___y_1806_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_lowerBound_1775_ = lean_ctor_get(v_s_1756_, 0);
v_upperBound_1776_ = lean_ctor_get(v_s_1756_, 1);
v_nil_1777_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1778_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1779_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1777_, v_cons_1778_, v_x_1757_);
v___x_1804_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
if (lean_obj_tag(v_lowerBound_1775_) == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1806_ = v___x_1822_;
goto v___jp_1805_;
}
else
{
lean_object* v_val_1823_; lean_object* v___x_1824_; lean_object* v___y_1826_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v_val_1823_ = lean_ctor_get(v_lowerBound_1775_, 0);
v___x_1824_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1828_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1829_ = lean_int_dec_le(v___x_1828_, v_val_1823_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1830_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1831_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1832_ = lean_int_neg(v_val_1823_);
v___x_1833_ = l_Int_toNat(v___x_1832_);
lean_dec(v___x_1832_);
v___x_1834_ = l_Lean_instToExprInt_mkNat(v___x_1833_);
v___x_1835_ = l_Lean_mkApp3(v___x_1830_, v___x_1774_, v___x_1831_, v___x_1834_);
v___y_1826_ = v___x_1835_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = l_Int_toNat(v_val_1823_);
v___x_1837_ = l_Lean_instToExprInt_mkNat(v___x_1836_);
v___y_1826_ = v___x_1837_;
goto v___jp_1825_;
}
v___jp_1825_:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_mkAppB(v___x_1824_, v___x_1774_, v___y_1826_);
v___y_1806_ = v___x_1827_;
goto v___jp_1805_;
}
}
v___jp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1782_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2);
lean_inc_ref(v___y_1781_);
v___x_1783_ = l_Lean_Expr_app___override(v___x_1782_, v___y_1781_);
v___x_1784_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6);
lean_inc(v_a_1768_);
lean_inc_ref(v_a_1767_);
lean_inc(v_a_1766_);
lean_inc_ref(v_a_1765_);
v___x_1785_ = l_Lean_Meta_mkEq(v___x_1783_, v___x_1784_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1787_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref(v___x_1785_);
v___x_1787_ = l_Lean_Meta_mkDecideProof(v_a_1786_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1797_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1797_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1797_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1792_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9);
v___x_1793_ = l_Lean_mkApp5(v___x_1792_, v___y_1781_, v_a_1788_, v___x_1779_, v_a_1771_, v_a_1773_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1793_);
v___x_1795_ = v___x_1790_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
else
{
lean_dec_ref(v___y_1781_);
lean_dec_ref(v___x_1779_);
lean_dec(v_a_1773_);
lean_dec(v_a_1771_);
return v___x_1787_;
}
}
else
{
lean_dec_ref(v___y_1781_);
lean_dec_ref(v___x_1779_);
lean_dec(v_a_1773_);
lean_dec(v_a_1771_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
return v___x_1785_;
}
}
v___jp_1798_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = l_Lean_mkAppB(v___y_1800_, v___x_1774_, v___y_1801_);
v___x_1803_ = l_Lean_Expr_app___override(v___y_1799_, v___x_1802_);
v___y_1781_ = v___x_1803_;
goto v___jp_1780_;
}
v___jp_1805_:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_Expr_app___override(v___x_1804_, v___y_1806_);
if (lean_obj_tag(v_upperBound_1776_) == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1809_ = l_Lean_Expr_app___override(v___x_1807_, v___x_1808_);
v___y_1781_ = v___x_1809_;
goto v___jp_1780_;
}
else
{
lean_object* v_val_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; 
v_val_1810_ = lean_ctor_get(v_upperBound_1776_, 0);
v___x_1811_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1812_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1813_ = lean_int_dec_le(v___x_1812_, v_val_1810_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1814_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1815_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1816_ = lean_int_neg(v_val_1810_);
v___x_1817_ = l_Int_toNat(v___x_1816_);
lean_dec(v___x_1816_);
v___x_1818_ = l_Lean_instToExprInt_mkNat(v___x_1817_);
v___x_1819_ = l_Lean_mkApp3(v___x_1814_, v___x_1774_, v___x_1815_, v___x_1818_);
v___y_1799_ = v___x_1807_;
v___y_1800_ = v___x_1811_;
v___y_1801_ = v___x_1819_;
goto v___jp_1798_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = l_Int_toNat(v_val_1810_);
v___x_1821_ = l_Lean_instToExprInt_mkNat(v___x_1820_);
v___y_1799_ = v___x_1807_;
v___y_1800_ = v___x_1811_;
v___y_1801_ = v___x_1821_;
goto v___jp_1798_;
}
}
}
}
else
{
lean_dec(v_a_1771_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
return v___x_1772_;
}
}
else
{
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec(v_a_1760_);
lean_dec_ref(v_j_1758_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed(lean_object* v_s_1838_, lean_object* v_x_1839_, lean_object* v_j_1840_, lean_object* v_assumptions_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
uint8_t v_a_7581__boxed_1852_; lean_object* v_res_1853_; 
v_a_7581__boxed_1852_ = lean_unbox(v_a_1845_);
v_res_1853_ = l_Lean_Elab_Tactic_Omega_Problem_proveFalse(v_s_1838_, v_x_1839_, v_j_1840_, v_assumptions_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_7581__boxed_1852_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
lean_dec_ref(v_assumptions_1841_);
lean_dec(v_x_1839_);
lean_dec_ref(v_s_1838_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0(lean_object* v_constraint_1854_, lean_object* v_coeffs_1855_, lean_object* v_justification_1856_, lean_object* v_x_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_1854_, v_coeffs_1855_, v_justification_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(lean_object* v_a_1859_, lean_object* v_x_1860_){
_start:
{
if (lean_obj_tag(v_x_1860_) == 0)
{
uint8_t v___x_1861_; 
v___x_1861_ = 0;
return v___x_1861_;
}
else
{
lean_object* v_key_1862_; lean_object* v_tail_1863_; uint8_t v___x_1864_; 
v_key_1862_ = lean_ctor_get(v_x_1860_, 0);
v_tail_1863_ = lean_ctor_get(v_x_1860_, 2);
v___x_1864_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_1862_, v_a_1859_);
if (v___x_1864_ == 0)
{
v_x_1860_ = v_tail_1863_;
goto _start;
}
else
{
return v___x_1864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg___boxed(lean_object* v_a_1866_, lean_object* v_x_1867_){
_start:
{
uint8_t v_res_1868_; lean_object* v_r_1869_; 
v_res_1868_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_1866_, v_x_1867_);
lean_dec(v_x_1867_);
lean_dec(v_a_1866_);
v_r_1869_ = lean_box(v_res_1868_);
return v_r_1869_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(uint64_t v_x_1870_, lean_object* v_x_1871_){
_start:
{
if (lean_obj_tag(v_x_1871_) == 0)
{
return v_x_1870_;
}
else
{
lean_object* v_head_1872_; lean_object* v_tail_1873_; lean_object* v_intZero_1874_; uint8_t v_isNeg_1875_; 
v_head_1872_ = lean_ctor_get(v_x_1871_, 0);
v_tail_1873_ = lean_ctor_get(v_x_1871_, 1);
v_intZero_1874_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1875_ = lean_int_dec_lt(v_head_1872_, v_intZero_1874_);
if (v_isNeg_1875_ == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; uint64_t v___x_1879_; uint64_t v___x_1880_; 
v_a_1876_ = lean_nat_abs(v_head_1872_);
v___x_1877_ = lean_unsigned_to_nat(2u);
v___x_1878_ = lean_nat_mul(v___x_1877_, v_a_1876_);
lean_dec(v_a_1876_);
v___x_1879_ = lean_uint64_of_nat(v___x_1878_);
lean_dec(v___x_1878_);
v___x_1880_ = lean_uint64_mix_hash(v_x_1870_, v___x_1879_);
v_x_1870_ = v___x_1880_;
v_x_1871_ = v_tail_1873_;
goto _start;
}
else
{
lean_object* v_abs_1882_; lean_object* v_one_1883_; lean_object* v_a_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; uint64_t v___x_1888_; uint64_t v___x_1889_; 
v_abs_1882_ = lean_nat_abs(v_head_1872_);
v_one_1883_ = lean_unsigned_to_nat(1u);
v_a_1884_ = lean_nat_sub(v_abs_1882_, v_one_1883_);
lean_dec(v_abs_1882_);
v___x_1885_ = lean_unsigned_to_nat(2u);
v___x_1886_ = lean_nat_mul(v___x_1885_, v_a_1884_);
lean_dec(v_a_1884_);
v___x_1887_ = lean_nat_add(v___x_1886_, v_one_1883_);
lean_dec(v___x_1886_);
v___x_1888_ = lean_uint64_of_nat(v___x_1887_);
lean_dec(v___x_1887_);
v___x_1889_ = lean_uint64_mix_hash(v_x_1870_, v___x_1888_);
v_x_1870_ = v___x_1889_;
v_x_1871_ = v_tail_1873_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0___boxed(lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
uint64_t v_x_980__boxed_1893_; uint64_t v_res_1894_; lean_object* v_r_1895_; 
v_x_980__boxed_1893_ = lean_unbox_uint64(v_x_1891_);
lean_dec_ref(v_x_1891_);
v_res_1894_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v_x_980__boxed_1893_, v_x_1892_);
lean_dec(v_x_1892_);
v_r_1895_ = lean_box_uint64(v_res_1894_);
return v_r_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_1896_, lean_object* v_x_1897_){
_start:
{
if (lean_obj_tag(v_x_1897_) == 0)
{
return v_x_1896_;
}
else
{
lean_object* v_key_1898_; lean_object* v_value_1899_; lean_object* v_tail_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1924_; 
v_key_1898_ = lean_ctor_get(v_x_1897_, 0);
v_value_1899_ = lean_ctor_get(v_x_1897_, 1);
v_tail_1900_ = lean_ctor_get(v_x_1897_, 2);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_x_1897_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1902_ = v_x_1897_;
v_isShared_1903_ = v_isSharedCheck_1924_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_tail_1900_);
lean_inc(v_value_1899_);
lean_inc(v_key_1898_);
lean_dec(v_x_1897_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1924_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; uint64_t v___x_1905_; uint64_t v___x_1906_; uint64_t v___x_1907_; uint64_t v___x_1908_; uint64_t v_fold_1909_; uint64_t v___x_1910_; uint64_t v___x_1911_; uint64_t v___x_1912_; size_t v___x_1913_; size_t v___x_1914_; size_t v___x_1915_; size_t v___x_1916_; size_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1904_ = lean_array_get_size(v_x_1896_);
v___x_1905_ = 7ULL;
v___x_1906_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_1905_, v_key_1898_);
v___x_1907_ = 32ULL;
v___x_1908_ = lean_uint64_shift_right(v___x_1906_, v___x_1907_);
v_fold_1909_ = lean_uint64_xor(v___x_1906_, v___x_1908_);
v___x_1910_ = 16ULL;
v___x_1911_ = lean_uint64_shift_right(v_fold_1909_, v___x_1910_);
v___x_1912_ = lean_uint64_xor(v_fold_1909_, v___x_1911_);
v___x_1913_ = lean_uint64_to_usize(v___x_1912_);
v___x_1914_ = lean_usize_of_nat(v___x_1904_);
v___x_1915_ = ((size_t)1ULL);
v___x_1916_ = lean_usize_sub(v___x_1914_, v___x_1915_);
v___x_1917_ = lean_usize_land(v___x_1913_, v___x_1916_);
v___x_1918_ = lean_array_uget_borrowed(v_x_1896_, v___x_1917_);
lean_inc(v___x_1918_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 2, v___x_1918_);
v___x_1920_ = v___x_1902_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_key_1898_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_value_1899_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_array_uset(v_x_1896_, v___x_1917_, v___x_1920_);
v_x_1896_ = v___x_1921_;
v_x_1897_ = v_tail_1900_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(lean_object* v_i_1925_, lean_object* v_source_1926_, lean_object* v_target_1927_){
_start:
{
lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = lean_array_get_size(v_source_1926_);
v___x_1929_ = lean_nat_dec_lt(v_i_1925_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_dec_ref(v_source_1926_);
lean_dec(v_i_1925_);
return v_target_1927_;
}
else
{
lean_object* v_es_1930_; lean_object* v___x_1931_; lean_object* v_source_1932_; lean_object* v_target_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v_es_1930_ = lean_array_fget(v_source_1926_, v_i_1925_);
v___x_1931_ = lean_box(0);
v_source_1932_ = lean_array_fset(v_source_1926_, v_i_1925_, v___x_1931_);
v_target_1933_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_target_1927_, v_es_1930_);
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1935_ = lean_nat_add(v_i_1925_, v___x_1934_);
lean_dec(v_i_1925_);
v_i_1925_ = v___x_1935_;
v_source_1926_ = v_source_1932_;
v_target_1927_ = v_target_1933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(lean_object* v_data_1937_){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v_nbuckets_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1938_ = lean_array_get_size(v_data_1937_);
v___x_1939_ = lean_unsigned_to_nat(2u);
v_nbuckets_1940_ = lean_nat_mul(v___x_1938_, v___x_1939_);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_box(0);
v___x_1943_ = lean_mk_array(v_nbuckets_1940_, v___x_1942_);
v___x_1944_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v___x_1941_, v_data_1937_, v___x_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(lean_object* v_m_1945_, lean_object* v_a_1946_, lean_object* v_b_1947_){
_start:
{
lean_object* v_size_1948_; lean_object* v_buckets_1949_; lean_object* v___x_1950_; uint64_t v___x_1951_; uint64_t v___x_1952_; uint64_t v___x_1953_; uint64_t v___x_1954_; uint64_t v_fold_1955_; uint64_t v___x_1956_; uint64_t v___x_1957_; uint64_t v___x_1958_; size_t v___x_1959_; size_t v___x_1960_; size_t v___x_1961_; size_t v___x_1962_; size_t v___x_1963_; lean_object* v_bkt_1964_; uint8_t v___x_1965_; 
v_size_1948_ = lean_ctor_get(v_m_1945_, 0);
v_buckets_1949_ = lean_ctor_get(v_m_1945_, 1);
v___x_1950_ = lean_array_get_size(v_buckets_1949_);
v___x_1951_ = 7ULL;
v___x_1952_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_1951_, v_a_1946_);
v___x_1953_ = 32ULL;
v___x_1954_ = lean_uint64_shift_right(v___x_1952_, v___x_1953_);
v_fold_1955_ = lean_uint64_xor(v___x_1952_, v___x_1954_);
v___x_1956_ = 16ULL;
v___x_1957_ = lean_uint64_shift_right(v_fold_1955_, v___x_1956_);
v___x_1958_ = lean_uint64_xor(v_fold_1955_, v___x_1957_);
v___x_1959_ = lean_uint64_to_usize(v___x_1958_);
v___x_1960_ = lean_usize_of_nat(v___x_1950_);
v___x_1961_ = ((size_t)1ULL);
v___x_1962_ = lean_usize_sub(v___x_1960_, v___x_1961_);
v___x_1963_ = lean_usize_land(v___x_1959_, v___x_1962_);
v_bkt_1964_ = lean_array_uget_borrowed(v_buckets_1949_, v___x_1963_);
v___x_1965_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_1946_, v_bkt_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1986_; 
lean_inc_ref(v_buckets_1949_);
lean_inc(v_size_1948_);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_m_1945_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; lean_object* v_unused_1988_; 
v_unused_1987_ = lean_ctor_get(v_m_1945_, 1);
lean_dec(v_unused_1987_);
v_unused_1988_ = lean_ctor_get(v_m_1945_, 0);
lean_dec(v_unused_1988_);
v___x_1967_ = v_m_1945_;
v_isShared_1968_ = v_isSharedCheck_1986_;
goto v_resetjp_1966_;
}
else
{
lean_dec(v_m_1945_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1986_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v_size_x27_1970_; lean_object* v___x_1971_; lean_object* v_buckets_x27_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1969_ = lean_unsigned_to_nat(1u);
v_size_x27_1970_ = lean_nat_add(v_size_1948_, v___x_1969_);
lean_dec(v_size_1948_);
lean_inc(v_bkt_1964_);
v___x_1971_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1971_, 0, v_a_1946_);
lean_ctor_set(v___x_1971_, 1, v_b_1947_);
lean_ctor_set(v___x_1971_, 2, v_bkt_1964_);
v_buckets_x27_1972_ = lean_array_uset(v_buckets_1949_, v___x_1963_, v___x_1971_);
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
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v_val_1979_);
lean_ctor_set(v___x_1967_, 0, v_size_x27_1970_);
v___x_1981_ = v___x_1967_;
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
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v_buckets_x27_1972_);
lean_ctor_set(v___x_1967_, 0, v_size_x27_1970_);
v___x_1984_ = v___x_1967_;
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
}
else
{
lean_dec(v_b_1947_);
lean_dec(v_a_1946_);
return v_m_1945_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(lean_object* v_a_1989_, lean_object* v_b_1990_, lean_object* v_x_1991_){
_start:
{
if (lean_obj_tag(v_x_1991_) == 0)
{
lean_dec(v_b_1990_);
lean_dec(v_a_1989_);
return v_x_1991_;
}
else
{
lean_object* v_key_1992_; lean_object* v_value_1993_; lean_object* v_tail_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2006_; 
v_key_1992_ = lean_ctor_get(v_x_1991_, 0);
v_value_1993_ = lean_ctor_get(v_x_1991_, 1);
v_tail_1994_ = lean_ctor_get(v_x_1991_, 2);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_x_1991_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1996_ = v_x_1991_;
v_isShared_1997_ = v_isSharedCheck_2006_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_tail_1994_);
lean_inc(v_value_1993_);
lean_inc(v_key_1992_);
lean_dec(v_x_1991_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2006_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
uint8_t v___x_1998_; 
v___x_1998_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_1992_, v_a_1989_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_1989_, v_b_1990_, v_tail_1994_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 2, v___x_1999_);
v___x_2001_ = v___x_1996_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_key_1992_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_value_1993_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
else
{
lean_object* v___x_2004_; 
lean_dec(v_value_1993_);
lean_dec(v_key_1992_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 1, v_b_1990_);
lean_ctor_set(v___x_1996_, 0, v_a_1989_);
v___x_2004_ = v___x_1996_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1989_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_b_1990_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_tail_1994_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(lean_object* v_m_2007_, lean_object* v_a_2008_, lean_object* v_b_2009_){
_start:
{
lean_object* v_size_2010_; lean_object* v_buckets_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2055_; 
v_size_2010_ = lean_ctor_get(v_m_2007_, 0);
v_buckets_2011_ = lean_ctor_get(v_m_2007_, 1);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_m_2007_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2013_ = v_m_2007_;
v_isShared_2014_ = v_isSharedCheck_2055_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_buckets_2011_);
lean_inc(v_size_2010_);
lean_dec(v_m_2007_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2055_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; uint64_t v___x_2016_; uint64_t v___x_2017_; uint64_t v___x_2018_; uint64_t v___x_2019_; uint64_t v_fold_2020_; uint64_t v___x_2021_; uint64_t v___x_2022_; uint64_t v___x_2023_; size_t v___x_2024_; size_t v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; lean_object* v_bkt_2029_; uint8_t v___x_2030_; 
v___x_2015_ = lean_array_get_size(v_buckets_2011_);
v___x_2016_ = 7ULL;
v___x_2017_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2016_, v_a_2008_);
v___x_2018_ = 32ULL;
v___x_2019_ = lean_uint64_shift_right(v___x_2017_, v___x_2018_);
v_fold_2020_ = lean_uint64_xor(v___x_2017_, v___x_2019_);
v___x_2021_ = 16ULL;
v___x_2022_ = lean_uint64_shift_right(v_fold_2020_, v___x_2021_);
v___x_2023_ = lean_uint64_xor(v_fold_2020_, v___x_2022_);
v___x_2024_ = lean_uint64_to_usize(v___x_2023_);
v___x_2025_ = lean_usize_of_nat(v___x_2015_);
v___x_2026_ = ((size_t)1ULL);
v___x_2027_ = lean_usize_sub(v___x_2025_, v___x_2026_);
v___x_2028_ = lean_usize_land(v___x_2024_, v___x_2027_);
v_bkt_2029_ = lean_array_uget_borrowed(v_buckets_2011_, v___x_2028_);
v___x_2030_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2008_, v_bkt_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; lean_object* v_size_x27_2032_; lean_object* v___x_2033_; lean_object* v_buckets_x27_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2031_ = lean_unsigned_to_nat(1u);
v_size_x27_2032_ = lean_nat_add(v_size_2010_, v___x_2031_);
lean_dec(v_size_2010_);
lean_inc(v_bkt_2029_);
v___x_2033_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2033_, 0, v_a_2008_);
lean_ctor_set(v___x_2033_, 1, v_b_2009_);
lean_ctor_set(v___x_2033_, 2, v_bkt_2029_);
v_buckets_x27_2034_ = lean_array_uset(v_buckets_2011_, v___x_2028_, v___x_2033_);
v___x_2035_ = lean_unsigned_to_nat(4u);
v___x_2036_ = lean_nat_mul(v_size_x27_2032_, v___x_2035_);
v___x_2037_ = lean_unsigned_to_nat(3u);
v___x_2038_ = lean_nat_div(v___x_2036_, v___x_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_array_get_size(v_buckets_x27_2034_);
v___x_2040_ = lean_nat_dec_le(v___x_2038_, v___x_2039_);
lean_dec(v___x_2038_);
if (v___x_2040_ == 0)
{
lean_object* v_val_2041_; lean_object* v___x_2043_; 
v_val_2041_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2034_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 1, v_val_2041_);
lean_ctor_set(v___x_2013_, 0, v_size_x27_2032_);
v___x_2043_ = v___x_2013_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_size_x27_2032_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_val_2041_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
else
{
lean_object* v___x_2046_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 1, v_buckets_x27_2034_);
lean_ctor_set(v___x_2013_, 0, v_size_x27_2032_);
v___x_2046_ = v___x_2013_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_size_x27_2032_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_buckets_x27_2034_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
else
{
lean_object* v___x_2048_; lean_object* v_buckets_x27_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
lean_inc(v_bkt_2029_);
v___x_2048_ = lean_box(0);
v_buckets_x27_2049_ = lean_array_uset(v_buckets_2011_, v___x_2028_, v___x_2048_);
v___x_2050_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2008_, v_b_2009_, v_bkt_2029_);
v___x_2051_ = lean_array_uset(v_buckets_x27_2049_, v___x_2028_, v___x_2050_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 1, v___x_2051_);
v___x_2053_ = v___x_2013_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_size_2010_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(lean_object* v_p_2056_, lean_object* v_x_2057_){
_start:
{
lean_object* v_coeffs_2058_; lean_object* v_constraint_2059_; lean_object* v_justification_2060_; uint8_t v___x_2061_; 
v_coeffs_2058_ = lean_ctor_get(v_x_2057_, 0);
lean_inc(v_coeffs_2058_);
v_constraint_2059_ = lean_ctor_get(v_x_2057_, 1);
lean_inc_ref(v_constraint_2059_);
v_justification_2060_ = lean_ctor_get(v_x_2057_, 2);
v___x_2061_ = l_Lean_Omega_Constraint_isImpossible(v_constraint_2059_);
if (v___x_2061_ == 0)
{
lean_object* v_assumptions_2062_; lean_object* v_numVars_2063_; lean_object* v_constraints_2064_; lean_object* v_equalities_2065_; lean_object* v_eliminations_2066_; uint8_t v_possible_2067_; lean_object* v_proveFalse_x3f_2068_; lean_object* v_explanation_x3f_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2087_; 
v_assumptions_2062_ = lean_ctor_get(v_p_2056_, 0);
v_numVars_2063_ = lean_ctor_get(v_p_2056_, 1);
v_constraints_2064_ = lean_ctor_get(v_p_2056_, 2);
v_equalities_2065_ = lean_ctor_get(v_p_2056_, 3);
v_eliminations_2066_ = lean_ctor_get(v_p_2056_, 4);
v_possible_2067_ = lean_ctor_get_uint8(v_p_2056_, sizeof(void*)*7);
v_proveFalse_x3f_2068_ = lean_ctor_get(v_p_2056_, 5);
v_explanation_x3f_2069_ = lean_ctor_get(v_p_2056_, 6);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_p_2056_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2071_ = v_p_2056_;
v_isShared_2072_ = v_isSharedCheck_2087_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_explanation_x3f_2069_);
lean_inc(v_proveFalse_x3f_2068_);
lean_inc(v_eliminations_2066_);
lean_inc(v_equalities_2065_);
lean_inc(v_constraints_2064_);
lean_inc(v_numVars_2063_);
lean_inc(v_assumptions_2062_);
lean_dec(v_p_2056_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2087_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___y_2074_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = l_List_lengthTR___redArg(v_coeffs_2058_);
v___x_2086_ = lean_nat_dec_le(v_numVars_2063_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_dec(v___x_2085_);
v___y_2074_ = v_numVars_2063_;
goto v___jp_2073_;
}
else
{
lean_dec(v_numVars_2063_);
v___y_2074_ = v___x_2085_;
goto v___jp_2073_;
}
v___jp_2073_:
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
lean_inc(v_coeffs_2058_);
v___x_2075_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_constraints_2064_, v_coeffs_2058_, v_x_2057_);
v___x_2076_ = l_Lean_Omega_Constraint_isExact(v_constraint_2059_);
lean_dec_ref(v_constraint_2059_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2078_; 
lean_dec(v_coeffs_2058_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 2, v___x_2075_);
lean_ctor_set(v___x_2071_, 1, v___y_2074_);
v___x_2078_ = v___x_2071_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_assumptions_2062_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___y_2074_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_equalities_2065_);
lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_eliminations_2066_);
lean_ctor_set(v_reuseFailAlloc_2079_, 5, v_proveFalse_x3f_2068_);
lean_ctor_set(v_reuseFailAlloc_2079_, 6, v_explanation_x3f_2069_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, sizeof(void*)*7, v_possible_2067_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2080_ = lean_box(0);
v___x_2081_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_equalities_2065_, v_coeffs_2058_, v___x_2080_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 3, v___x_2081_);
lean_ctor_set(v___x_2071_, 2, v___x_2075_);
lean_ctor_set(v___x_2071_, 1, v___y_2074_);
v___x_2083_ = v___x_2071_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_assumptions_2062_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___y_2074_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_eliminations_2066_);
lean_ctor_set(v_reuseFailAlloc_2084_, 5, v_proveFalse_x3f_2068_);
lean_ctor_set(v_reuseFailAlloc_2084_, 6, v_explanation_x3f_2069_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*7, v_possible_2067_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
else
{
lean_object* v_assumptions_2088_; lean_object* v_numVars_2089_; lean_object* v_constraints_2090_; lean_object* v_equalities_2091_; lean_object* v_eliminations_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2104_; 
lean_inc_ref(v_justification_2060_);
lean_dec_ref(v_x_2057_);
v_assumptions_2088_ = lean_ctor_get(v_p_2056_, 0);
v_numVars_2089_ = lean_ctor_get(v_p_2056_, 1);
v_constraints_2090_ = lean_ctor_get(v_p_2056_, 2);
v_equalities_2091_ = lean_ctor_get(v_p_2056_, 3);
v_eliminations_2092_ = lean_ctor_get(v_p_2056_, 4);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_p_2056_);
if (v_isSharedCheck_2104_ == 0)
{
lean_object* v_unused_2105_; lean_object* v_unused_2106_; 
v_unused_2105_ = lean_ctor_get(v_p_2056_, 6);
lean_dec(v_unused_2105_);
v_unused_2106_ = lean_ctor_get(v_p_2056_, 5);
lean_dec(v_unused_2106_);
v___x_2094_ = v_p_2056_;
v_isShared_2095_ = v_isSharedCheck_2104_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_eliminations_2092_);
lean_inc(v_equalities_2091_);
lean_inc(v_constraints_2090_);
lean_inc(v_numVars_2089_);
lean_inc(v_assumptions_2088_);
lean_dec(v_p_2056_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2104_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___f_2096_; uint8_t v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
lean_inc_ref(v_justification_2060_);
lean_inc(v_coeffs_2058_);
lean_inc_ref(v_constraint_2059_);
v___f_2096_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0), 4, 3);
lean_closure_set(v___f_2096_, 0, v_constraint_2059_);
lean_closure_set(v___f_2096_, 1, v_coeffs_2058_);
lean_closure_set(v___f_2096_, 2, v_justification_2060_);
v___x_2097_ = 0;
lean_inc_ref(v_assumptions_2088_);
v___x_2098_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed), 14, 4);
lean_closure_set(v___x_2098_, 0, v_constraint_2059_);
lean_closure_set(v___x_2098_, 1, v_coeffs_2058_);
lean_closure_set(v___x_2098_, 2, v_justification_2060_);
lean_closure_set(v___x_2098_, 3, v_assumptions_2088_);
v___x_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
v___x_2100_ = lean_mk_thunk(v___f_2096_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 6, v___x_2100_);
lean_ctor_set(v___x_2094_, 5, v___x_2099_);
v___x_2102_ = v___x_2094_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_assumptions_2088_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_numVars_2089_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_constraints_2090_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_equalities_2091_);
lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_eliminations_2092_);
lean_ctor_set(v_reuseFailAlloc_2103_, 5, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2103_, 6, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_ctor_set_uint8(v___x_2102_, sizeof(void*)*7, v___x_2097_);
return v___x_2102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0(lean_object* v_00_u03b2_2107_, lean_object* v_m_2108_, lean_object* v_a_2109_, lean_object* v_b_2110_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_m_2108_, v_a_2109_, v_b_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1(lean_object* v_00_u03b2_2112_, lean_object* v_m_2113_, lean_object* v_a_2114_, lean_object* v_b_2115_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_m_2113_, v_a_2114_, v_b_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_object* v_00_u03b2_2117_, lean_object* v_a_2118_, lean_object* v_x_2119_){
_start:
{
uint8_t v___x_2120_; 
v___x_2120_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2118_, v_x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2121_, lean_object* v_a_2122_, lean_object* v_x_2123_){
_start:
{
uint8_t v_res_2124_; lean_object* v_r_2125_; 
v_res_2124_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(v_00_u03b2_2121_, v_a_2122_, v_x_2123_);
lean_dec(v_x_2123_);
lean_dec(v_a_2122_);
v_r_2125_ = lean_box(v_res_2124_);
return v_r_2125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2(lean_object* v_00_u03b2_2126_, lean_object* v_data_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_data_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3(lean_object* v_00_u03b2_2129_, lean_object* v_a_2130_, lean_object* v_b_2131_, lean_object* v_x_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2130_, v_b_2131_, v_x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2134_, lean_object* v_i_2135_, lean_object* v_source_2136_, lean_object* v_target_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v_i_2135_, v_source_2136_, v_target_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2139_, lean_object* v_x_2140_, lean_object* v_x_2141_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_x_2140_, v_x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(lean_object* v_a_2143_, lean_object* v_x_2144_){
_start:
{
if (lean_obj_tag(v_x_2144_) == 0)
{
lean_object* v___x_2145_; 
v___x_2145_ = lean_box(0);
return v___x_2145_;
}
else
{
lean_object* v_key_2146_; lean_object* v_value_2147_; lean_object* v_tail_2148_; uint8_t v___x_2149_; 
v_key_2146_ = lean_ctor_get(v_x_2144_, 0);
v_value_2147_ = lean_ctor_get(v_x_2144_, 1);
v_tail_2148_ = lean_ctor_get(v_x_2144_, 2);
v___x_2149_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2146_, v_a_2143_);
if (v___x_2149_ == 0)
{
v_x_2144_ = v_tail_2148_;
goto _start;
}
else
{
lean_object* v___x_2151_; 
lean_inc(v_value_2147_);
v___x_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2151_, 0, v_value_2147_);
return v___x_2151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg___boxed(lean_object* v_a_2152_, lean_object* v_x_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2152_, v_x_2153_);
lean_dec(v_x_2153_);
lean_dec(v_a_2152_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(lean_object* v_m_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v_buckets_2157_; lean_object* v___x_2158_; uint64_t v___x_2159_; uint64_t v___x_2160_; uint64_t v___x_2161_; uint64_t v___x_2162_; uint64_t v_fold_2163_; uint64_t v___x_2164_; uint64_t v___x_2165_; uint64_t v___x_2166_; size_t v___x_2167_; size_t v___x_2168_; size_t v___x_2169_; size_t v___x_2170_; size_t v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_buckets_2157_ = lean_ctor_get(v_m_2155_, 1);
v___x_2158_ = lean_array_get_size(v_buckets_2157_);
v___x_2159_ = 7ULL;
v___x_2160_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2159_, v_a_2156_);
v___x_2161_ = 32ULL;
v___x_2162_ = lean_uint64_shift_right(v___x_2160_, v___x_2161_);
v_fold_2163_ = lean_uint64_xor(v___x_2160_, v___x_2162_);
v___x_2164_ = 16ULL;
v___x_2165_ = lean_uint64_shift_right(v_fold_2163_, v___x_2164_);
v___x_2166_ = lean_uint64_xor(v_fold_2163_, v___x_2165_);
v___x_2167_ = lean_uint64_to_usize(v___x_2166_);
v___x_2168_ = lean_usize_of_nat(v___x_2158_);
v___x_2169_ = ((size_t)1ULL);
v___x_2170_ = lean_usize_sub(v___x_2168_, v___x_2169_);
v___x_2171_ = lean_usize_land(v___x_2167_, v___x_2170_);
v___x_2172_ = lean_array_uget_borrowed(v_buckets_2157_, v___x_2171_);
v___x_2173_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2156_, v___x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg___boxed(lean_object* v_m_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2174_, v_a_2175_);
lean_dec(v_a_2175_);
lean_dec_ref(v_m_2174_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addConstraint(lean_object* v_p_2177_, lean_object* v_x_2178_){
_start:
{
uint8_t v_possible_2179_; 
v_possible_2179_ = lean_ctor_get_uint8(v_p_2177_, sizeof(void*)*7);
if (v_possible_2179_ == 0)
{
lean_dec_ref(v_x_2178_);
return v_p_2177_;
}
else
{
lean_object* v_coeffs_2180_; lean_object* v_constraint_2181_; lean_object* v_justification_2182_; lean_object* v_constraints_2183_; lean_object* v___x_2184_; 
v_coeffs_2180_ = lean_ctor_get(v_x_2178_, 0);
v_constraint_2181_ = lean_ctor_get(v_x_2178_, 1);
v_justification_2182_ = lean_ctor_get(v_x_2178_, 2);
v_constraints_2183_ = lean_ctor_get(v_p_2177_, 2);
v___x_2184_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2183_, v_coeffs_2180_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_lowerBound_2185_; 
v_lowerBound_2185_ = lean_ctor_get(v_constraint_2181_, 0);
if (lean_obj_tag(v_lowerBound_2185_) == 0)
{
lean_object* v_upperBound_2186_; 
v_upperBound_2186_ = lean_ctor_get(v_constraint_2181_, 1);
if (lean_obj_tag(v_upperBound_2186_) == 0)
{
lean_dec_ref(v_x_2178_);
return v_p_2177_;
}
else
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2177_, v_x_2178_);
return v___x_2187_;
}
}
else
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2177_, v_x_2178_);
return v___x_2188_;
}
}
else
{
lean_object* v_val_2189_; lean_object* v_coeffs_2190_; lean_object* v_constraint_2191_; lean_object* v_justification_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2207_; 
v_val_2189_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_val_2189_);
lean_dec_ref(v___x_2184_);
v_coeffs_2190_ = lean_ctor_get(v_val_2189_, 0);
v_constraint_2191_ = lean_ctor_get(v_val_2189_, 1);
v_justification_2192_ = lean_ctor_get(v_val_2189_, 2);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_val_2189_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2194_ = v_val_2189_;
v_isShared_2195_ = v_isSharedCheck_2207_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_justification_2192_);
lean_inc(v_constraint_2191_);
lean_inc(v_coeffs_2190_);
lean_dec(v_val_2189_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2207_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2196_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc(v_coeffs_2180_);
v___x_2197_ = l_instDecidableEqList___redArg(v___x_2196_, v_coeffs_2180_, v_coeffs_2190_);
if (v___x_2197_ == 0)
{
lean_del_object(v___x_2194_);
lean_dec_ref(v_justification_2192_);
lean_dec_ref(v_constraint_2191_);
lean_dec_ref(v_x_2178_);
return v_p_2177_;
}
else
{
lean_object* v_r_2198_; uint8_t v___x_2199_; 
lean_inc_ref(v_constraint_2191_);
lean_inc_ref(v_constraint_2181_);
v_r_2198_ = l_Lean_Omega_Constraint_combine(v_constraint_2181_, v_constraint_2191_);
lean_inc_ref(v_constraint_2191_);
lean_inc_ref(v_r_2198_);
v___x_2199_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2198_, v_constraint_2191_);
if (v___x_2199_ == 0)
{
uint8_t v___x_2200_; 
lean_inc_ref(v_constraint_2181_);
lean_inc_ref(v_r_2198_);
v___x_2200_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2198_, v_constraint_2181_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2203_; 
lean_inc_ref(v_justification_2182_);
lean_inc_ref(v_constraint_2181_);
lean_inc(v_coeffs_2180_);
lean_dec_ref(v_x_2178_);
lean_inc(v_coeffs_2180_);
v___x_2201_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_2201_, 0, v_constraint_2181_);
lean_ctor_set(v___x_2201_, 1, v_constraint_2191_);
lean_ctor_set(v___x_2201_, 2, v_coeffs_2180_);
lean_ctor_set(v___x_2201_, 3, v_justification_2182_);
lean_ctor_set(v___x_2201_, 4, v_justification_2192_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 2, v___x_2201_);
lean_ctor_set(v___x_2194_, 1, v_r_2198_);
lean_ctor_set(v___x_2194_, 0, v_coeffs_2180_);
v___x_2203_ = v___x_2194_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_coeffs_2180_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_r_2198_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2177_, v___x_2203_);
return v___x_2204_;
}
}
else
{
lean_object* v___x_2206_; 
lean_dec_ref(v_r_2198_);
lean_del_object(v___x_2194_);
lean_dec_ref(v_justification_2192_);
lean_dec_ref(v_constraint_2191_);
v___x_2206_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2177_, v_x_2178_);
return v___x_2206_;
}
}
else
{
lean_dec_ref(v_r_2198_);
lean_del_object(v___x_2194_);
lean_dec_ref(v_justification_2192_);
lean_dec_ref(v_constraint_2191_);
lean_dec_ref(v_x_2178_);
return v_p_2177_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(lean_object* v_00_u03b2_2208_, lean_object* v_m_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2209_, v_a_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___boxed(lean_object* v_00_u03b2_2212_, lean_object* v_m_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(v_00_u03b2_2212_, v_m_2213_, v_a_2214_);
lean_dec(v_a_2214_);
lean_dec_ref(v_m_2213_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(lean_object* v_00_u03b2_2216_, lean_object* v_a_2217_, lean_object* v_x_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2217_, v_x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2220_, lean_object* v_a_2221_, lean_object* v_x_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(v_00_u03b2_2220_, v_a_2221_, v_x_2222_);
lean_dec(v_x_2222_);
lean_dec(v_a_2221_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
if (lean_obj_tag(v_x_2225_) == 0)
{
return v_x_2224_;
}
else
{
if (lean_obj_tag(v_x_2224_) == 0)
{
lean_object* v_key_2226_; lean_object* v_tail_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v_key_2226_ = lean_ctor_get(v_x_2225_, 0);
lean_inc(v_key_2226_);
v_tail_2227_ = lean_ctor_get(v_x_2225_, 2);
lean_inc(v_tail_2227_);
lean_dec_ref(v_x_2225_);
lean_inc(v_key_2226_);
v___x_2228_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2226_);
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v_key_2226_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
v_x_2224_ = v___x_2230_;
v_x_2225_ = v_tail_2227_;
goto _start;
}
else
{
lean_object* v_val_2232_; lean_object* v_key_2233_; lean_object* v_tail_2234_; lean_object* v_fst_2235_; lean_object* v_snd_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2264_; 
v_val_2232_ = lean_ctor_get(v_x_2224_, 0);
lean_inc(v_val_2232_);
v_key_2233_ = lean_ctor_get(v_x_2225_, 0);
lean_inc(v_key_2233_);
v_tail_2234_ = lean_ctor_get(v_x_2225_, 2);
lean_inc(v_tail_2234_);
lean_dec_ref(v_x_2225_);
v_fst_2235_ = lean_ctor_get(v_val_2232_, 0);
v_snd_2236_ = lean_ctor_get(v_val_2232_, 1);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_val_2232_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2238_ = v_val_2232_;
v_isShared_2239_ = v_isSharedCheck_2264_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_snd_2236_);
lean_inc(v_fst_2235_);
lean_dec(v_val_2232_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2264_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = lean_unsigned_to_nat(2u);
v___x_2241_ = lean_nat_dec_le(v___x_2240_, v_snd_2236_);
if (v___x_2241_ == 0)
{
lean_del_object(v___x_2238_);
lean_dec(v_snd_2236_);
lean_dec(v_fst_2235_);
lean_dec(v_key_2233_);
v_x_2225_ = v_tail_2234_;
goto _start;
}
else
{
lean_object* v_m_x27_2243_; uint8_t v___y_2245_; uint8_t v___x_2259_; 
lean_inc(v_key_2233_);
v_m_x27_2243_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2233_);
v___x_2259_ = lean_nat_dec_lt(v_m_x27_2243_, v_snd_2236_);
if (v___x_2259_ == 0)
{
uint8_t v___x_2260_; 
v___x_2260_ = lean_nat_dec_eq(v_m_x27_2243_, v_snd_2236_);
lean_dec(v_snd_2236_);
if (v___x_2260_ == 0)
{
lean_dec(v_fst_2235_);
v___y_2245_ = v___x_2260_;
goto v___jp_2244_;
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
lean_inc(v_key_2233_);
v___x_2261_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_key_2233_);
v___x_2262_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_fst_2235_);
v___x_2263_ = lean_nat_dec_lt(v___x_2261_, v___x_2262_);
lean_dec(v___x_2262_);
lean_dec(v___x_2261_);
v___y_2245_ = v___x_2263_;
goto v___jp_2244_;
}
}
else
{
lean_dec(v_snd_2236_);
lean_dec(v_fst_2235_);
v___y_2245_ = v___x_2259_;
goto v___jp_2244_;
}
v___jp_2244_:
{
if (v___y_2245_ == 0)
{
lean_dec(v_m_x27_2243_);
lean_del_object(v___x_2238_);
lean_dec(v_key_2233_);
v_x_2225_ = v_tail_2234_;
goto _start;
}
else
{
lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2257_; 
v_isSharedCheck_2257_ = !lean_is_exclusive(v_x_2224_);
if (v_isSharedCheck_2257_ == 0)
{
lean_object* v_unused_2258_; 
v_unused_2258_ = lean_ctor_get(v_x_2224_, 0);
lean_dec(v_unused_2258_);
v___x_2248_ = v_x_2224_;
v_isShared_2249_ = v_isSharedCheck_2257_;
goto v_resetjp_2247_;
}
else
{
lean_dec(v_x_2224_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2257_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 1, v_m_x27_2243_);
lean_ctor_set(v___x_2238_, 0, v_key_2233_);
v___x_2251_ = v___x_2238_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_key_2233_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_m_x27_2243_);
v___x_2251_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2251_);
v___x_2253_ = v___x_2248_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
v_x_2224_ = v___x_2253_;
v_x_2225_ = v_tail_2234_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(lean_object* v_as_2265_, size_t v_i_2266_, size_t v_stop_2267_, lean_object* v_b_2268_){
_start:
{
uint8_t v___x_2269_; 
v___x_2269_ = lean_usize_dec_eq(v_i_2266_, v_stop_2267_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; lean_object* v___x_2271_; size_t v___x_2272_; size_t v___x_2273_; 
v___x_2270_ = lean_array_uget_borrowed(v_as_2265_, v_i_2266_);
lean_inc(v___x_2270_);
v___x_2271_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(v_b_2268_, v___x_2270_);
v___x_2272_ = ((size_t)1ULL);
v___x_2273_ = lean_usize_add(v_i_2266_, v___x_2272_);
v_i_2266_ = v___x_2273_;
v_b_2268_ = v___x_2271_;
goto _start;
}
else
{
return v_b_2268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1___boxed(lean_object* v_as_2275_, lean_object* v_i_2276_, lean_object* v_stop_2277_, lean_object* v_b_2278_){
_start:
{
size_t v_i_boxed_2279_; size_t v_stop_boxed_2280_; lean_object* v_res_2281_; 
v_i_boxed_2279_ = lean_unbox_usize(v_i_2276_);
lean_dec(v_i_2276_);
v_stop_boxed_2280_ = lean_unbox_usize(v_stop_2277_);
lean_dec(v_stop_2277_);
v_res_2281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_as_2275_, v_i_boxed_2279_, v_stop_boxed_2280_, v_b_2278_);
lean_dec_ref(v_as_2275_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality(lean_object* v_p_2282_){
_start:
{
lean_object* v_equalities_2283_; lean_object* v_buckets_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v_equalities_2283_ = lean_ctor_get(v_p_2282_, 3);
v_buckets_2284_ = lean_ctor_get(v_equalities_2283_, 1);
v___x_2285_ = lean_box(0);
v___x_2286_ = lean_unsigned_to_nat(0u);
v___x_2287_ = lean_array_get_size(v_buckets_2284_);
v___x_2288_ = lean_nat_dec_lt(v___x_2286_, v___x_2287_);
if (v___x_2288_ == 0)
{
return v___x_2285_;
}
else
{
uint8_t v___x_2289_; 
v___x_2289_ = lean_nat_dec_le(v___x_2287_, v___x_2287_);
if (v___x_2289_ == 0)
{
if (v___x_2288_ == 0)
{
return v___x_2285_;
}
else
{
size_t v___x_2290_; size_t v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = ((size_t)0ULL);
v___x_2291_ = lean_usize_of_nat(v___x_2287_);
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2284_, v___x_2290_, v___x_2291_, v___x_2285_);
return v___x_2292_;
}
}
else
{
size_t v___x_2293_; size_t v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = ((size_t)0ULL);
v___x_2294_ = lean_usize_of_nat(v___x_2287_);
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2284_, v___x_2293_, v___x_2294_, v___x_2285_);
return v___x_2295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality___boxed(lean_object* v_p_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_2296_);
lean_dec_ref(v_p_2296_);
return v_res_2297_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2299_ = lean_nat_to_int(v___x_2298_);
return v___x_2299_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2301_ = lean_int_neg(v___x_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(lean_object* v_as_2302_, size_t v_i_2303_, size_t v_stop_2304_, lean_object* v_b_2305_){
_start:
{
uint8_t v___x_2306_; 
v___x_2306_ = lean_usize_dec_eq(v_i_2303_, v_stop_2304_);
if (v___x_2306_ == 0)
{
size_t v___x_2307_; size_t v___x_2308_; lean_object* v___x_2309_; lean_object* v_snd_2310_; lean_object* v_fst_2311_; lean_object* v_fst_2312_; lean_object* v_snd_2313_; lean_object* v_coeffs_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; uint8_t v___x_2317_; 
v___x_2307_ = ((size_t)1ULL);
v___x_2308_ = lean_usize_sub(v_i_2303_, v___x_2307_);
v___x_2309_ = lean_array_uget_borrowed(v_as_2302_, v___x_2308_);
v_snd_2310_ = lean_ctor_get(v___x_2309_, 1);
v_fst_2311_ = lean_ctor_get(v___x_2309_, 0);
v_fst_2312_ = lean_ctor_get(v_snd_2310_, 0);
v_snd_2313_ = lean_ctor_get(v_snd_2310_, 1);
v_coeffs_2314_ = lean_ctor_get(v_b_2305_, 0);
lean_inc(v_fst_2312_);
v___x_2315_ = l_Lean_Omega_IntList_get(v_coeffs_2314_, v_fst_2312_);
v___x_2316_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2317_ = lean_int_dec_eq(v___x_2315_, v___x_2316_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2318_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2319_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2320_ = lean_int_mul(v___x_2319_, v_snd_2313_);
v___x_2321_ = lean_int_mul(v___x_2320_, v___x_2315_);
lean_dec(v___x_2315_);
lean_dec(v___x_2320_);
lean_inc(v_fst_2311_);
v___x_2322_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v___x_2321_, v_fst_2311_, v___x_2318_, v_b_2305_);
v_i_2303_ = v___x_2308_;
v_b_2305_ = v___x_2322_;
goto _start;
}
else
{
lean_dec(v___x_2315_);
v_i_2303_ = v___x_2308_;
goto _start;
}
}
else
{
return v_b_2305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___boxed(lean_object* v_as_2325_, lean_object* v_i_2326_, lean_object* v_stop_2327_, lean_object* v_b_2328_){
_start:
{
size_t v_i_boxed_2329_; size_t v_stop_boxed_2330_; lean_object* v_res_2331_; 
v_i_boxed_2329_ = lean_unbox_usize(v_i_2326_);
lean_dec(v_i_2326_);
v_stop_boxed_2330_ = lean_unbox_usize(v_stop_2327_);
lean_dec(v_stop_2327_);
v_res_2331_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v_as_2325_, v_i_boxed_2329_, v_stop_boxed_2330_, v_b_2328_);
lean_dec_ref(v_as_2325_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(lean_object* v_init_2332_, lean_object* v_l_2333_){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2334_ = lean_array_mk(v_l_2333_);
v___x_2335_ = lean_array_get_size(v___x_2334_);
v___x_2336_ = lean_unsigned_to_nat(0u);
v___x_2337_ = lean_nat_dec_lt(v___x_2336_, v___x_2335_);
if (v___x_2337_ == 0)
{
lean_dec_ref(v___x_2334_);
return v_init_2332_;
}
else
{
size_t v___x_2338_; size_t v___x_2339_; lean_object* v___x_2340_; 
v___x_2338_ = lean_usize_of_nat(v___x_2335_);
v___x_2339_ = ((size_t)0ULL);
v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v___x_2334_, v___x_2338_, v___x_2339_, v_init_2332_);
lean_dec_ref(v___x_2334_);
return v___x_2340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(lean_object* v_p_2341_, lean_object* v_f_2342_){
_start:
{
lean_object* v_eliminations_2343_; lean_object* v___x_2344_; 
v_eliminations_2343_ = lean_ctor_get(v_p_2341_, 4);
lean_inc(v_eliminations_2343_);
lean_dec_ref(v_p_2341_);
v___x_2344_ = l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(v_f_2342_, v_eliminations_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__0(lean_object* v_x_2345_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
return v___x_2346_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1(lean_object* v_x_2347_){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; uint8_t v___x_2350_; 
v___x_2348_ = lean_nat_abs(v_x_2347_);
v___x_2349_ = lean_unsigned_to_nat(1u);
v___x_2350_ = lean_nat_dec_eq(v___x_2348_, v___x_2349_);
lean_dec(v___x_2348_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1___boxed(lean_object* v_x_2351_){
_start:
{
uint8_t v_res_2352_; lean_object* v_r_2353_; 
v_res_2352_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1(v_x_2351_);
lean_dec(v_x_2351_);
v_r_2353_ = lean_box(v_res_2352_);
return v_r_2353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(lean_object* v___y_2354_, lean_object* v_sign_2355_, lean_object* v_val_2356_, lean_object* v_x_2357_, lean_object* v_x_2358_){
_start:
{
if (lean_obj_tag(v_x_2358_) == 0)
{
lean_dec_ref(v_val_2356_);
lean_dec(v___y_2354_);
return v_x_2357_;
}
else
{
lean_object* v_key_2359_; lean_object* v_value_2360_; lean_object* v_tail_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v_key_2359_ = lean_ctor_get(v_x_2358_, 0);
lean_inc(v_key_2359_);
v_value_2360_ = lean_ctor_get(v_x_2358_, 1);
lean_inc(v_value_2360_);
v_tail_2361_ = lean_ctor_get(v_x_2358_, 2);
lean_inc(v_tail_2361_);
lean_dec_ref(v_x_2358_);
lean_inc(v___y_2354_);
v___x_2362_ = l_Lean_Omega_IntList_get(v_key_2359_, v___y_2354_);
lean_dec(v_key_2359_);
v___x_2363_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2364_ = lean_int_dec_eq(v___x_2362_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v_k_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2365_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2366_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2367_ = lean_int_mul(v___x_2366_, v_sign_2355_);
v_k_2368_ = lean_int_mul(v___x_2367_, v___x_2362_);
lean_dec(v___x_2362_);
lean_dec(v___x_2367_);
lean_inc_ref(v_val_2356_);
v___x_2369_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_k_2368_, v_val_2356_, v___x_2365_, v_value_2360_);
v___x_2370_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_2369_);
v___x_2371_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2357_, v___x_2370_);
v_x_2357_ = v___x_2371_;
v_x_2358_ = v_tail_2361_;
goto _start;
}
else
{
lean_object* v___x_2373_; 
lean_dec(v___x_2362_);
v___x_2373_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2357_, v_value_2360_);
v_x_2357_ = v___x_2373_;
v_x_2358_ = v_tail_2361_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0___boxed(lean_object* v___y_2375_, lean_object* v_sign_2376_, lean_object* v_val_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2375_, v_sign_2376_, v_val_2377_, v_x_2378_, v_x_2379_);
lean_dec(v_sign_2376_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object* v___y_2381_, lean_object* v_sign_2382_, lean_object* v_val_2383_, lean_object* v_as_2384_, size_t v_i_2385_, size_t v_stop_2386_, lean_object* v_b_2387_){
_start:
{
uint8_t v___x_2388_; 
v___x_2388_ = lean_usize_dec_eq(v_i_2385_, v_stop_2386_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; lean_object* v___x_2390_; size_t v___x_2391_; size_t v___x_2392_; 
v___x_2389_ = lean_array_uget_borrowed(v_as_2384_, v_i_2385_);
lean_inc(v___x_2389_);
lean_inc_ref(v_val_2383_);
lean_inc(v___y_2381_);
v___x_2390_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2381_, v_sign_2382_, v_val_2383_, v_b_2387_, v___x_2389_);
v___x_2391_ = ((size_t)1ULL);
v___x_2392_ = lean_usize_add(v_i_2385_, v___x_2391_);
v_i_2385_ = v___x_2392_;
v_b_2387_ = v___x_2390_;
goto _start;
}
else
{
lean_dec_ref(v_val_2383_);
lean_dec(v___y_2381_);
return v_b_2387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1___boxed(lean_object* v___y_2394_, lean_object* v_sign_2395_, lean_object* v_val_2396_, lean_object* v_as_2397_, lean_object* v_i_2398_, lean_object* v_stop_2399_, lean_object* v_b_2400_){
_start:
{
size_t v_i_boxed_2401_; size_t v_stop_boxed_2402_; lean_object* v_res_2403_; 
v_i_boxed_2401_ = lean_unbox_usize(v_i_2398_);
lean_dec(v_i_2398_);
v_stop_boxed_2402_ = lean_unbox_usize(v_stop_2399_);
lean_dec(v_stop_2399_);
v_res_2403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2394_, v_sign_2395_, v_val_2396_, v_as_2397_, v_i_boxed_2401_, v_stop_boxed_2402_, v_b_2400_);
lean_dec_ref(v_as_2397_);
lean_dec(v_sign_2395_);
return v_res_2403_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = lean_box(0);
v___x_2406_ = lean_unsigned_to_nat(16u);
v___x_2407_ = lean_mk_array(v___x_2406_, v___x_2405_);
return v___x_2407_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1);
v___x_2409_ = lean_unsigned_to_nat(0u);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
lean_ctor_set(v___x_2410_, 1, v___x_2408_);
return v___x_2410_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3(void){
_start:
{
lean_object* v___f_2411_; lean_object* v___x_2412_; 
v___f_2411_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0));
v___x_2412_ = lean_mk_thunk(v___f_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(lean_object* v_p_2414_, lean_object* v_c_2415_){
_start:
{
lean_object* v___y_2417_; lean_object* v___f_2464_; lean_object* v___x_2465_; 
v___f_2464_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__4));
lean_inc(v_c_2415_);
v___x_2465_ = l_List_findIdx_x3f___redArg(v___f_2464_, v_c_2415_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_unsigned_to_nat(0u);
v___y_2417_ = v___x_2466_;
goto v___jp_2416_;
}
else
{
lean_object* v_val_2467_; 
v_val_2467_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_val_2467_);
lean_dec_ref(v___x_2465_);
v___y_2417_ = v_val_2467_;
goto v___jp_2416_;
}
v___jp_2416_:
{
lean_object* v_assumptions_2418_; lean_object* v_constraints_2419_; lean_object* v_eliminations_2420_; lean_object* v___x_2421_; 
v_assumptions_2418_ = lean_ctor_get(v_p_2414_, 0);
v_constraints_2419_ = lean_ctor_get(v_p_2414_, 2);
lean_inc_ref(v_constraints_2419_);
v_eliminations_2420_ = lean_ctor_get(v_p_2414_, 4);
v___x_2421_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2419_, v_c_2415_);
if (lean_obj_tag(v___x_2421_) == 1)
{
lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2456_; 
lean_inc(v_eliminations_2420_);
lean_inc_ref(v_assumptions_2418_);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_p_2414_);
if (v_isSharedCheck_2456_ == 0)
{
lean_object* v_unused_2457_; lean_object* v_unused_2458_; lean_object* v_unused_2459_; lean_object* v_unused_2460_; lean_object* v_unused_2461_; lean_object* v_unused_2462_; lean_object* v_unused_2463_; 
v_unused_2457_ = lean_ctor_get(v_p_2414_, 6);
lean_dec(v_unused_2457_);
v_unused_2458_ = lean_ctor_get(v_p_2414_, 5);
lean_dec(v_unused_2458_);
v_unused_2459_ = lean_ctor_get(v_p_2414_, 4);
lean_dec(v_unused_2459_);
v_unused_2460_ = lean_ctor_get(v_p_2414_, 3);
lean_dec(v_unused_2460_);
v_unused_2461_ = lean_ctor_get(v_p_2414_, 2);
lean_dec(v_unused_2461_);
v_unused_2462_ = lean_ctor_get(v_p_2414_, 1);
lean_dec(v_unused_2462_);
v_unused_2463_ = lean_ctor_get(v_p_2414_, 0);
lean_dec(v_unused_2463_);
v___x_2423_ = v_p_2414_;
v_isShared_2424_ = v_isSharedCheck_2456_;
goto v_resetjp_2422_;
}
else
{
lean_dec(v_p_2414_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2456_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v_val_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v_buckets_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2454_; 
v_val_2425_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_val_2425_);
lean_dec_ref(v___x_2421_);
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v_buckets_2428_ = lean_ctor_get(v_constraints_2419_, 1);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_constraints_2419_);
if (v_isSharedCheck_2454_ == 0)
{
lean_object* v_unused_2455_; 
v_unused_2455_ = lean_ctor_get(v_constraints_2419_, 0);
lean_dec(v_unused_2455_);
v___x_2430_ = v_constraints_2419_;
v_isShared_2431_ = v_isSharedCheck_2454_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_buckets_2428_);
lean_dec(v_constraints_2419_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2454_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; lean_object* v_sign_2433_; lean_object* v___x_2435_; 
lean_inc(v___y_2417_);
v___x_2432_ = l_Lean_Omega_IntList_get(v_c_2415_, v___y_2417_);
lean_dec(v_c_2415_);
v_sign_2433_ = l_Int_sign(v___x_2432_);
lean_dec(v___x_2432_);
lean_inc(v_sign_2433_);
lean_inc(v___y_2417_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 1, v_sign_2433_);
lean_ctor_set(v___x_2430_, 0, v___y_2417_);
v___x_2435_ = v___x_2430_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___y_2417_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_sign_2433_);
v___x_2435_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v_init_2442_; 
lean_inc(v_val_2425_);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v_val_2425_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
lean_ctor_set(v___x_2437_, 1, v_eliminations_2420_);
v___x_2438_ = 1;
v___x_2439_ = lean_box(0);
v___x_2440_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 6, v___x_2440_);
lean_ctor_set(v___x_2423_, 5, v___x_2439_);
lean_ctor_set(v___x_2423_, 4, v___x_2437_);
lean_ctor_set(v___x_2423_, 3, v___x_2427_);
lean_ctor_set(v___x_2423_, 2, v___x_2427_);
lean_ctor_set(v___x_2423_, 1, v___x_2426_);
v_init_2442_ = v___x_2423_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_assumptions_2418_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2452_, 5, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2452_, 6, v___x_2440_);
v_init_2442_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2443_; uint8_t v___x_2444_; 
lean_ctor_set_uint8(v_init_2442_, sizeof(void*)*7, v___x_2438_);
v___x_2443_ = lean_array_get_size(v_buckets_2428_);
v___x_2444_ = lean_nat_dec_lt(v___x_2426_, v___x_2443_);
if (v___x_2444_ == 0)
{
lean_dec(v_sign_2433_);
lean_dec_ref(v_buckets_2428_);
lean_dec(v_val_2425_);
lean_dec(v___y_2417_);
return v_init_2442_;
}
else
{
uint8_t v___x_2445_; 
v___x_2445_ = lean_nat_dec_le(v___x_2443_, v___x_2443_);
if (v___x_2445_ == 0)
{
if (v___x_2444_ == 0)
{
lean_dec(v_sign_2433_);
lean_dec_ref(v_buckets_2428_);
lean_dec(v_val_2425_);
lean_dec(v___y_2417_);
return v_init_2442_;
}
else
{
size_t v___x_2446_; size_t v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = ((size_t)0ULL);
v___x_2447_ = lean_usize_of_nat(v___x_2443_);
v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2417_, v_sign_2433_, v_val_2425_, v_buckets_2428_, v___x_2446_, v___x_2447_, v_init_2442_);
lean_dec_ref(v_buckets_2428_);
lean_dec(v_sign_2433_);
return v___x_2448_;
}
}
else
{
size_t v___x_2449_; size_t v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = ((size_t)0ULL);
v___x_2450_ = lean_usize_of_nat(v___x_2443_);
v___x_2451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2417_, v_sign_2433_, v_val_2425_, v_buckets_2428_, v___x_2449_, v___x_2450_, v_init_2442_);
lean_dec_ref(v_buckets_2428_);
lean_dec(v_sign_2433_);
return v___x_2451_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2421_);
lean_dec_ref(v_constraints_2419_);
lean_dec(v___y_2417_);
lean_dec(v_c_2415_);
return v_p_2414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(lean_object* v_msgData_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v___x_2474_; lean_object* v_env_2475_; lean_object* v___x_2476_; lean_object* v_mctx_2477_; lean_object* v_lctx_2478_; lean_object* v_options_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2474_ = lean_st_ref_get(v___y_2472_);
v_env_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc_ref(v_env_2475_);
lean_dec(v___x_2474_);
v___x_2476_ = lean_st_ref_get(v___y_2470_);
v_mctx_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc_ref(v_mctx_2477_);
lean_dec(v___x_2476_);
v_lctx_2478_ = lean_ctor_get(v___y_2469_, 2);
v_options_2479_ = lean_ctor_get(v___y_2471_, 2);
lean_inc_ref(v_options_2479_);
lean_inc_ref(v_lctx_2478_);
v___x_2480_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2480_, 0, v_env_2475_);
lean_ctor_set(v___x_2480_, 1, v_mctx_2477_);
lean_ctor_set(v___x_2480_, 2, v_lctx_2478_);
lean_ctor_set(v___x_2480_, 3, v_options_2479_);
v___x_2481_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v_msgData_2468_);
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0___boxed(lean_object* v_msgData_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msgData_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(lean_object* v_msg_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_ref_2496_; lean_object* v___x_2497_; lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2506_; 
v_ref_2496_ = lean_ctor_get(v___y_2493_, 5);
v___x_2497_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2506_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2506_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
lean_inc(v_ref_2496_);
v___x_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2502_, 0, v_ref_2496_);
lean_ctor_set(v___x_2502_, 1, v_a_2498_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set_tag(v___x_2500_, 1);
lean_ctor_set(v___x_2500_, 0, v___x_2502_);
v___x_2504_ = v___x_2500_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg___boxed(lean_object* v_msg_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
return v_res_2513_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0));
v___x_2516_ = l_Lean_stringToMessageData(v___x_2515_);
return v___x_2516_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2));
v___x_2519_ = l_Lean_stringToMessageData(v___x_2518_);
return v___x_2519_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4));
v___x_2522_ = l_Lean_stringToMessageData(v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(lean_object* v_p_2523_, lean_object* v_c_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, uint8_t v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v_constraints_2535_; lean_object* v___x_2536_; 
v_constraints_2535_ = lean_ctor_get(v_p_2523_, 2);
v___x_2536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2535_, v_c_2524_);
if (lean_obj_tag(v___x_2536_) == 1)
{
lean_object* v_val_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2636_; 
v_val_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2636_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_val_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2636_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v_constraint_2541_; lean_object* v_lowerBound_2542_; 
v_constraint_2541_ = lean_ctor_get(v_val_2537_, 1);
v_lowerBound_2542_ = lean_ctor_get(v_constraint_2541_, 0);
lean_inc(v_lowerBound_2542_);
if (lean_obj_tag(v_lowerBound_2542_) == 1)
{
lean_object* v_upperBound_2543_; 
lean_del_object(v___x_2539_);
v_upperBound_2543_ = lean_ctor_get(v_constraint_2541_, 1);
lean_inc(v_upperBound_2543_);
if (lean_obj_tag(v_upperBound_2543_) == 1)
{
lean_object* v_coeffs_2544_; lean_object* v_justification_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2623_; 
v_coeffs_2544_ = lean_ctor_get(v_val_2537_, 0);
v_justification_2545_ = lean_ctor_get(v_val_2537_, 2);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_val_2537_);
if (v_isSharedCheck_2623_ == 0)
{
lean_object* v_unused_2624_; 
v_unused_2624_ = lean_ctor_get(v_val_2537_, 1);
lean_dec(v_unused_2624_);
v___x_2547_ = v_val_2537_;
v_isShared_2548_ = v_isSharedCheck_2623_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_justification_2545_);
lean_inc(v_coeffs_2544_);
lean_dec(v_val_2537_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2623_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_val_2549_; lean_object* v_val_2550_; lean_object* v___x_2551_; 
v_val_2549_ = lean_ctor_get(v_lowerBound_2542_, 0);
lean_inc(v_val_2549_);
lean_dec_ref(v_lowerBound_2542_);
v_val_2550_ = lean_ctor_get(v_upperBound_2543_, 0);
lean_inc(v_val_2550_);
lean_dec_ref(v_upperBound_2543_);
lean_inc(v_a_2533_);
lean_inc_ref(v_a_2532_);
lean_inc(v_a_2531_);
lean_inc_ref(v_a_2530_);
v___x_2551_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2526_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_m_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v_nil_2558_; lean_object* v_cons_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref(v___x_2551_);
lean_inc(v_c_2524_);
v___x_2553_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_c_2524_);
v___x_2554_ = lean_unsigned_to_nat(1u);
v_m_2555_ = lean_nat_add(v___x_2553_, v___x_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc(v_m_2555_);
v___x_2557_ = l_Lean_mkNatLit(v_m_2555_);
v_nil_2558_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2559_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2560_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2558_, v_cons_2559_, v_c_2524_);
lean_dec(v_c_2524_);
v___x_2561_ = l_Lean_mkApp3(v___x_2556_, v___x_2557_, v___x_2560_, v_a_2552_);
lean_inc(v_a_2533_);
lean_inc_ref(v_a_2532_);
lean_inc(v_a_2531_);
lean_inc_ref(v_a_2530_);
v___x_2562_ = l_Lean_Elab_Tactic_Omega_lookup(v___x_2561_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2606_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2606_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2606_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v_fst_2567_; lean_object* v_snd_2568_; uint8_t v___x_2581_; 
v_fst_2567_ = lean_ctor_get(v_a_2563_, 0);
lean_inc(v_fst_2567_);
v_snd_2568_ = lean_ctor_get(v_a_2563_, 1);
lean_inc(v_snd_2568_);
lean_dec(v_a_2563_);
v___x_2581_ = lean_int_dec_eq(v_val_2550_, v_val_2549_);
lean_dec(v_val_2550_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_dec(v_snd_2568_);
lean_dec(v_fst_2567_);
lean_del_object(v___x_2565_);
lean_dec(v_m_2555_);
lean_dec(v_val_2549_);
lean_del_object(v___x_2547_);
lean_dec_ref(v_justification_2545_);
lean_dec(v_coeffs_2544_);
lean_dec_ref(v_p_2523_);
v___x_2582_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1);
v___x_2583_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_2582_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
return v___x_2583_;
}
else
{
if (lean_obj_tag(v_snd_2568_) == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v_fst_2567_);
lean_del_object(v___x_2565_);
lean_dec(v_m_2555_);
lean_dec(v_val_2549_);
lean_del_object(v___x_2547_);
lean_dec_ref(v_justification_2545_);
lean_dec(v_coeffs_2544_);
lean_dec_ref(v_p_2523_);
v___x_2584_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3);
v___x_2585_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_2584_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
else
{
lean_object* v_val_2594_; uint8_t v___x_2595_; 
v_val_2594_ = lean_ctor_get(v_snd_2568_, 0);
lean_inc(v_val_2594_);
lean_dec_ref(v_snd_2568_);
v___x_2595_ = l_List_isEmpty___redArg(v_val_2594_);
lean_dec(v_val_2594_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec(v_fst_2567_);
lean_del_object(v___x_2565_);
lean_dec(v_m_2555_);
lean_dec(v_val_2549_);
lean_del_object(v___x_2547_);
lean_dec_ref(v_justification_2545_);
lean_dec(v_coeffs_2544_);
lean_dec_ref(v_p_2523_);
v___x_2596_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5);
v___x_2597_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_2596_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
else
{
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
goto v___jp_2569_;
}
}
}
v___jp_2569_:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
lean_inc(v_coeffs_2544_);
lean_inc(v_m_2555_);
v___x_2570_ = l_Lean_Omega_bmod__coeffs(v_m_2555_, v_fst_2567_, v_coeffs_2544_);
lean_inc(v_m_2555_);
v___x_2571_ = l_Int_bmod(v_val_2549_, v_m_2555_);
v___x_2572_ = l_Lean_Omega_Constraint_exact(v___x_2571_);
v___x_2573_ = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(v___x_2573_, 0, v_m_2555_);
lean_ctor_set(v___x_2573_, 1, v_val_2549_);
lean_ctor_set(v___x_2573_, 2, v_fst_2567_);
lean_ctor_set(v___x_2573_, 3, v_coeffs_2544_);
lean_ctor_set(v___x_2573_, 4, v_justification_2545_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 2, v___x_2573_);
lean_ctor_set(v___x_2547_, 1, v___x_2572_);
lean_ctor_set(v___x_2547_, 0, v___x_2570_);
v___x_2575_ = v___x_2547_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2570_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2580_, 2, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_2523_, v___x_2575_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2576_);
v___x_2578_ = v___x_2565_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v_m_2555_);
lean_dec(v_val_2550_);
lean_dec(v_val_2549_);
lean_del_object(v___x_2547_);
lean_dec_ref(v_justification_2545_);
lean_dec(v_coeffs_2544_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec_ref(v_p_2523_);
v_a_2607_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2562_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2562_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec(v_val_2550_);
lean_dec(v_val_2549_);
lean_del_object(v___x_2547_);
lean_dec_ref(v_justification_2545_);
lean_dec(v_coeffs_2544_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec(v_c_2524_);
lean_dec_ref(v_p_2523_);
v_a_2615_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2551_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2551_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
else
{
lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec(v_upperBound_2543_);
lean_dec(v_val_2537_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec(v_c_2524_);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_lowerBound_2542_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; 
v_unused_2632_ = lean_ctor_get(v_lowerBound_2542_, 0);
lean_dec(v_unused_2632_);
v___x_2626_ = v_lowerBound_2542_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_dec(v_lowerBound_2542_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
lean_ctor_set_tag(v___x_2626_, 0);
lean_ctor_set(v___x_2626_, 0, v_p_2523_);
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_p_2523_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
else
{
lean_object* v___x_2634_; 
lean_dec(v_lowerBound_2542_);
lean_dec(v_val_2537_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec(v_c_2524_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set_tag(v___x_2539_, 0);
lean_ctor_set(v___x_2539_, 0, v_p_2523_);
v___x_2634_ = v___x_2539_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_p_2523_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v___x_2637_; 
lean_dec(v___x_2536_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec(v_c_2524_);
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v_p_2523_);
return v___x_2637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___boxed(lean_object* v_p_2638_, lean_object* v_c_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
uint8_t v_a_14815__boxed_2650_; lean_object* v_res_2651_; 
v_a_14815__boxed_2650_ = lean_unbox(v_a_2643_);
v_res_2651_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_2638_, v_c_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_14815__boxed_2650_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec(v_a_2640_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_object* v_00_u03b1_2652_, lean_object* v_msg_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, uint8_t v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_2653_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___boxed(lean_object* v_00_u03b1_2665_, lean_object* v_msg_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
uint8_t v___y_15054__boxed_2677_; lean_object* v_res_2678_; 
v___y_15054__boxed_2677_ = lean_unbox(v___y_2670_);
v_res_2678_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(v_00_u03b1_2665_, v_msg_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_15054__boxed_2677_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec(v___y_2667_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality(lean_object* v_p_2679_, lean_object* v_c_2680_, lean_object* v_m_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, uint8_t v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2692_ = lean_unsigned_to_nat(1u);
v___x_2693_ = lean_nat_dec_eq(v_m_2681_, v___x_2692_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; 
v___x_2694_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_2679_, v_c_2680_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_);
return v___x_2694_;
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
v___x_2695_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_2679_, v_c_2680_);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
return v___x_2696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality___boxed(lean_object* v_p_2697_, lean_object* v_c_2698_, lean_object* v_m_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
uint8_t v_a_388__boxed_2710_; lean_object* v_res_2711_; 
v_a_388__boxed_2710_ = lean_unbox(v_a_2703_);
v_res_2711_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_2697_, v_c_2698_, v_m_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_388__boxed_2710_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec(v_a_2700_);
lean_dec(v_m_2699_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(lean_object* v_p_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, uint8_t v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_){
_start:
{
uint8_t v_possible_2723_; 
v_possible_2723_ = lean_ctor_get_uint8(v_p_2712_, sizeof(void*)*7);
if (v_possible_2723_ == 0)
{
lean_object* v___x_2724_; 
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
v___x_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2724_, 0, v_p_2712_);
return v___x_2724_;
}
else
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_2712_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v___x_2726_; 
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v_p_2712_);
return v___x_2726_;
}
else
{
lean_object* v_val_2727_; lean_object* v_fst_2728_; lean_object* v_snd_2729_; lean_object* v___x_2730_; 
v_val_2727_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_val_2727_);
lean_dec_ref(v___x_2725_);
v_fst_2728_ = lean_ctor_get(v_val_2727_, 0);
lean_inc(v_fst_2728_);
v_snd_2729_ = lean_ctor_get(v_val_2727_, 1);
lean_inc(v_snd_2729_);
lean_dec(v_val_2727_);
lean_inc(v_a_2721_);
lean_inc_ref(v_a_2720_);
lean_inc(v_a_2719_);
lean_inc_ref(v_a_2718_);
v___x_2730_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_2712_, v_fst_2728_, v_snd_2729_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
lean_dec(v_snd_2729_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref(v___x_2730_);
v_p_2712_ = v_a_2731_;
goto _start;
}
else
{
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
return v___x_2730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities___boxed(lean_object* v_p_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
uint8_t v_a_1241__boxed_2744_; lean_object* v_res_2745_; 
v_a_1241__boxed_2744_ = lean_unbox(v_a_2737_);
v_res_2745_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_1241__boxed_2744_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec(v_a_2734_);
return v_res_2745_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2752_ = lean_box(0);
v___x_2753_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1));
v___x_2754_ = l_Lean_Expr_const___override(v___x_2753_, v___x_2752_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object* v_c_2755_, lean_object* v_x_2756_, lean_object* v_p_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, uint8_t v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v___x_2768_; 
lean_inc(v_a_2766_);
lean_inc_ref(v_a_2765_);
lean_inc(v_a_2764_);
lean_inc_ref(v_a_2763_);
v___x_2768_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2759_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref(v___x_2768_);
v___x_2770_ = lean_box(v_a_2761_);
v___x_2771_ = lean_apply_10(v_p_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v___x_2770_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, lean_box(0));
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2797_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2797_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2797_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___y_2778_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
v___x_2776_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2);
v___x_2786_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2787_ = lean_int_dec_le(v___x_2786_, v_c_2755_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2788_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2789_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_2790_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2791_ = lean_int_neg(v_c_2755_);
v___x_2792_ = l_Int_toNat(v___x_2791_);
lean_dec(v___x_2791_);
v___x_2793_ = l_Lean_instToExprInt_mkNat(v___x_2792_);
v___x_2794_ = l_Lean_mkApp3(v___x_2788_, v___x_2789_, v___x_2790_, v___x_2793_);
v___y_2778_ = v___x_2794_;
goto v___jp_2777_;
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = l_Int_toNat(v_c_2755_);
v___x_2796_ = l_Lean_instToExprInt_mkNat(v___x_2795_);
v___y_2778_ = v___x_2796_;
goto v___jp_2777_;
}
v___jp_2777_:
{
lean_object* v_nil_2779_; lean_object* v_cons_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2784_; 
v_nil_2779_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2780_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2781_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2779_, v_cons_2780_, v_x_2756_);
v___x_2782_ = l_Lean_mkApp4(v___x_2776_, v___y_2778_, v___x_2781_, v_a_2769_, v_a_2772_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2782_);
v___x_2784_ = v___x_2774_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2782_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
else
{
lean_dec(v_a_2769_);
return v___x_2771_;
}
}
else
{
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2760_);
lean_dec(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_p_2757_);
return v___x_2768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object* v_c_2798_, lean_object* v_x_2799_, lean_object* v_p_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
uint8_t v_a_3017__boxed_2811_; lean_object* v_res_2812_; 
v_a_3017__boxed_2811_ = lean_unbox(v_a_2804_);
v_res_2812_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(v_c_2798_, v_x_2799_, v_p_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_3017__boxed_2811_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
lean_dec(v_x_2799_);
lean_dec(v_c_2798_);
return v_res_2812_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2(void){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2819_ = lean_box(0);
v___x_2820_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1));
v___x_2821_ = l_Lean_Expr_const___override(v___x_2820_, v___x_2819_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(lean_object* v_c_2822_, lean_object* v_x_2823_, lean_object* v_p_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, uint8_t v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v___x_2835_; 
lean_inc(v_a_2833_);
lean_inc_ref(v_a_2832_);
lean_inc(v_a_2831_);
lean_inc_ref(v_a_2830_);
v___x_2835_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2826_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref(v___x_2835_);
v___x_2837_ = lean_box(v_a_2828_);
v___x_2838_ = lean_apply_10(v_p_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v___x_2837_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, lean_box(0));
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2864_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2864_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2864_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___y_2845_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v___x_2843_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2);
v___x_2853_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2854_ = lean_int_dec_le(v___x_2853_, v_c_2822_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2855_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2856_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_2857_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2858_ = lean_int_neg(v_c_2822_);
v___x_2859_ = l_Int_toNat(v___x_2858_);
lean_dec(v___x_2858_);
v___x_2860_ = l_Lean_instToExprInt_mkNat(v___x_2859_);
v___x_2861_ = l_Lean_mkApp3(v___x_2855_, v___x_2856_, v___x_2857_, v___x_2860_);
v___y_2845_ = v___x_2861_;
goto v___jp_2844_;
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2862_ = l_Int_toNat(v_c_2822_);
v___x_2863_ = l_Lean_instToExprInt_mkNat(v___x_2862_);
v___y_2845_ = v___x_2863_;
goto v___jp_2844_;
}
v___jp_2844_:
{
lean_object* v_nil_2846_; lean_object* v_cons_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2851_; 
v_nil_2846_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2847_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2848_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2846_, v_cons_2847_, v_x_2823_);
v___x_2849_ = l_Lean_mkApp4(v___x_2843_, v___y_2845_, v___x_2848_, v_a_2836_, v_a_2839_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2849_);
v___x_2851_ = v___x_2841_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
else
{
lean_dec(v_a_2836_);
return v___x_2838_;
}
}
else
{
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_p_2824_);
return v___x_2835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed(lean_object* v_c_2865_, lean_object* v_x_2866_, lean_object* v_p_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
uint8_t v_a_3017__boxed_2878_; lean_object* v_res_2879_; 
v_a_3017__boxed_2878_ = lean_unbox(v_a_2871_);
v_res_2879_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(v_c_2865_, v_x_2866_, v_p_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_3017__boxed_2878_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
lean_dec(v_x_2866_);
lean_dec(v_c_2865_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(lean_object* v_prf_x3f_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, uint8_t v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
if (lean_obj_tag(v_prf_x3f_2880_) == 0)
{
lean_object* v___x_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec(v___y_2881_);
v___x_2891_ = lean_box(0);
v___x_2892_ = 0;
v___x_2893_ = lean_box(0);
lean_inc_ref(v___y_2886_);
v___x_2894_ = l_Lean_Meta_mkFreshExprMVar(v___x_2891_, v___x_2892_, v___x_2893_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; uint8_t v___x_2896_; lean_object* v___x_2897_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref(v___x_2894_);
v___x_2896_ = 0;
v___x_2897_ = l_Lean_Meta_mkSorry(v_a_2895_, v___x_2896_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
return v___x_2897_;
}
else
{
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
return v___x_2894_;
}
}
else
{
lean_object* v_val_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v_val_2898_ = lean_ctor_get(v_prf_x3f_2880_, 0);
lean_inc(v_val_2898_);
lean_dec_ref(v_prf_x3f_2880_);
v___x_2899_ = lean_box(v___y_2884_);
v___x_2900_ = lean_apply_10(v_val_2898_, v___y_2881_, v___y_2882_, v___y_2883_, v___x_2899_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, lean_box(0));
return v___x_2900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed(lean_object* v_prf_x3f_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
uint8_t v___y_803__boxed_2912_; lean_object* v_res_2913_; 
v___y_803__boxed_2912_ = lean_unbox(v___y_2905_);
v_res_2913_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(v_prf_x3f_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_803__boxed_2912_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality(lean_object* v_p_2914_, lean_object* v_const_2915_, lean_object* v_coeffs_2916_, lean_object* v_prf_x3f_2917_){
_start:
{
lean_object* v_assumptions_2918_; lean_object* v_numVars_2919_; lean_object* v_constraints_2920_; lean_object* v_equalities_2921_; lean_object* v_eliminations_2922_; uint8_t v_possible_2923_; lean_object* v_proveFalse_x3f_2924_; lean_object* v_explanation_x3f_2925_; lean_object* v_prf_2926_; lean_object* v_i_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v_p_x27_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v_f_2936_; lean_object* v_f_2937_; lean_object* v_f_2938_; lean_object* v___x_2939_; 
v_assumptions_2918_ = lean_ctor_get(v_p_2914_, 0);
v_numVars_2919_ = lean_ctor_get(v_p_2914_, 1);
v_constraints_2920_ = lean_ctor_get(v_p_2914_, 2);
v_equalities_2921_ = lean_ctor_get(v_p_2914_, 3);
v_eliminations_2922_ = lean_ctor_get(v_p_2914_, 4);
v_possible_2923_ = lean_ctor_get_uint8(v_p_2914_, sizeof(void*)*7);
v_proveFalse_x3f_2924_ = lean_ctor_get(v_p_2914_, 5);
v_explanation_x3f_2925_ = lean_ctor_get(v_p_2914_, 6);
v_prf_2926_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_2926_, 0, v_prf_x3f_2917_);
v_i_2927_ = lean_array_get_size(v_assumptions_2918_);
lean_inc(v_coeffs_2916_);
lean_inc(v_const_2915_);
v___x_2928_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed), 13, 3);
lean_closure_set(v___x_2928_, 0, v_const_2915_);
lean_closure_set(v___x_2928_, 1, v_coeffs_2916_);
lean_closure_set(v___x_2928_, 2, v_prf_2926_);
lean_inc_ref(v_assumptions_2918_);
v___x_2929_ = lean_array_push(v_assumptions_2918_, v___x_2928_);
lean_inc_ref(v_explanation_x3f_2925_);
lean_inc(v_proveFalse_x3f_2924_);
lean_inc(v_eliminations_2922_);
lean_inc_ref(v_equalities_2921_);
lean_inc_ref(v_constraints_2920_);
lean_inc(v_numVars_2919_);
v_p_x27_2930_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_2930_, 0, v___x_2929_);
lean_ctor_set(v_p_x27_2930_, 1, v_numVars_2919_);
lean_ctor_set(v_p_x27_2930_, 2, v_constraints_2920_);
lean_ctor_set(v_p_x27_2930_, 3, v_equalities_2921_);
lean_ctor_set(v_p_x27_2930_, 4, v_eliminations_2922_);
lean_ctor_set(v_p_x27_2930_, 5, v_proveFalse_x3f_2924_);
lean_ctor_set(v_p_x27_2930_, 6, v_explanation_x3f_2925_);
lean_ctor_set_uint8(v_p_x27_2930_, sizeof(void*)*7, v_possible_2923_);
v___x_2931_ = lean_int_neg(v_const_2915_);
lean_dec(v_const_2915_);
v___x_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
v___x_2933_ = lean_box(0);
v___x_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2932_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
lean_inc(v_coeffs_2916_);
lean_inc_ref(v___x_2934_);
v___x_2935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
lean_ctor_set(v___x_2935_, 1, v_coeffs_2916_);
lean_ctor_set(v___x_2935_, 2, v_i_2927_);
v_f_2936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_2936_, 0, v_coeffs_2916_);
lean_ctor_set(v_f_2936_, 1, v___x_2934_);
lean_ctor_set(v_f_2936_, 2, v___x_2935_);
v_f_2937_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_2914_, v_f_2936_);
v_f_2938_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_2937_);
v___x_2939_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_2930_, v_f_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality(lean_object* v_p_2940_, lean_object* v_const_2941_, lean_object* v_coeffs_2942_, lean_object* v_prf_x3f_2943_){
_start:
{
lean_object* v_assumptions_2944_; lean_object* v_numVars_2945_; lean_object* v_constraints_2946_; lean_object* v_equalities_2947_; lean_object* v_eliminations_2948_; uint8_t v_possible_2949_; lean_object* v_proveFalse_x3f_2950_; lean_object* v_explanation_x3f_2951_; lean_object* v_prf_2952_; lean_object* v_i_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v_p_x27_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v_f_2961_; lean_object* v_f_2962_; lean_object* v_f_2963_; lean_object* v___x_2964_; 
v_assumptions_2944_ = lean_ctor_get(v_p_2940_, 0);
v_numVars_2945_ = lean_ctor_get(v_p_2940_, 1);
v_constraints_2946_ = lean_ctor_get(v_p_2940_, 2);
v_equalities_2947_ = lean_ctor_get(v_p_2940_, 3);
v_eliminations_2948_ = lean_ctor_get(v_p_2940_, 4);
v_possible_2949_ = lean_ctor_get_uint8(v_p_2940_, sizeof(void*)*7);
v_proveFalse_x3f_2950_ = lean_ctor_get(v_p_2940_, 5);
v_explanation_x3f_2951_ = lean_ctor_get(v_p_2940_, 6);
v_prf_2952_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_2952_, 0, v_prf_x3f_2943_);
v_i_2953_ = lean_array_get_size(v_assumptions_2944_);
lean_inc(v_coeffs_2942_);
lean_inc(v_const_2941_);
v___x_2954_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed), 13, 3);
lean_closure_set(v___x_2954_, 0, v_const_2941_);
lean_closure_set(v___x_2954_, 1, v_coeffs_2942_);
lean_closure_set(v___x_2954_, 2, v_prf_2952_);
lean_inc_ref(v_assumptions_2944_);
v___x_2955_ = lean_array_push(v_assumptions_2944_, v___x_2954_);
lean_inc_ref(v_explanation_x3f_2951_);
lean_inc(v_proveFalse_x3f_2950_);
lean_inc(v_eliminations_2948_);
lean_inc_ref(v_equalities_2947_);
lean_inc_ref(v_constraints_2946_);
lean_inc(v_numVars_2945_);
v_p_x27_2956_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_2956_, 0, v___x_2955_);
lean_ctor_set(v_p_x27_2956_, 1, v_numVars_2945_);
lean_ctor_set(v_p_x27_2956_, 2, v_constraints_2946_);
lean_ctor_set(v_p_x27_2956_, 3, v_equalities_2947_);
lean_ctor_set(v_p_x27_2956_, 4, v_eliminations_2948_);
lean_ctor_set(v_p_x27_2956_, 5, v_proveFalse_x3f_2950_);
lean_ctor_set(v_p_x27_2956_, 6, v_explanation_x3f_2951_);
lean_ctor_set_uint8(v_p_x27_2956_, sizeof(void*)*7, v_possible_2949_);
v___x_2957_ = lean_int_neg(v_const_2941_);
lean_dec(v_const_2941_);
v___x_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
lean_inc_ref(v___x_2958_);
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
lean_inc(v_coeffs_2942_);
lean_inc_ref(v___x_2959_);
v___x_2960_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v_coeffs_2942_);
lean_ctor_set(v___x_2960_, 2, v_i_2953_);
v_f_2961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_2961_, 0, v_coeffs_2942_);
lean_ctor_set(v_f_2961_, 1, v___x_2959_);
lean_ctor_set(v_f_2961_, 2, v___x_2960_);
v_f_2962_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_2940_, v_f_2961_);
v_f_2963_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_2962_);
v___x_2964_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_2956_, v_f_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(lean_object* v_x_2965_, lean_object* v_x_2966_){
_start:
{
if (lean_obj_tag(v_x_2966_) == 0)
{
return v_x_2965_;
}
else
{
lean_object* v_head_2967_; lean_object* v_snd_2968_; lean_object* v_tail_2969_; lean_object* v_fst_2970_; lean_object* v_fst_2971_; lean_object* v_snd_2972_; lean_object* v___x_2973_; 
v_head_2967_ = lean_ctor_get(v_x_2966_, 0);
lean_inc(v_head_2967_);
v_snd_2968_ = lean_ctor_get(v_head_2967_, 1);
lean_inc(v_snd_2968_);
v_tail_2969_ = lean_ctor_get(v_x_2966_, 1);
lean_inc(v_tail_2969_);
lean_dec_ref(v_x_2966_);
v_fst_2970_ = lean_ctor_get(v_head_2967_, 0);
lean_inc(v_fst_2970_);
lean_dec(v_head_2967_);
v_fst_2971_ = lean_ctor_get(v_snd_2968_, 0);
lean_inc(v_fst_2971_);
v_snd_2972_ = lean_ctor_get(v_snd_2968_, 1);
lean_inc(v_snd_2972_);
lean_dec(v_snd_2968_);
v___x_2973_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality(v_x_2965_, v_fst_2970_, v_fst_2971_, v_snd_2972_);
v_x_2965_ = v___x_2973_;
v_x_2966_ = v_tail_2969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequalities(lean_object* v_p_2975_, lean_object* v_ineqs_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(v_p_2975_, v_ineqs_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(lean_object* v_x_2978_, lean_object* v_x_2979_){
_start:
{
if (lean_obj_tag(v_x_2979_) == 0)
{
return v_x_2978_;
}
else
{
lean_object* v_head_2980_; lean_object* v_snd_2981_; lean_object* v_tail_2982_; lean_object* v_fst_2983_; lean_object* v_fst_2984_; lean_object* v_snd_2985_; lean_object* v___x_2986_; 
v_head_2980_ = lean_ctor_get(v_x_2979_, 0);
lean_inc(v_head_2980_);
v_snd_2981_ = lean_ctor_get(v_head_2980_, 1);
lean_inc(v_snd_2981_);
v_tail_2982_ = lean_ctor_get(v_x_2979_, 1);
lean_inc(v_tail_2982_);
lean_dec_ref(v_x_2979_);
v_fst_2983_ = lean_ctor_get(v_head_2980_, 0);
lean_inc(v_fst_2983_);
lean_dec(v_head_2980_);
v_fst_2984_ = lean_ctor_get(v_snd_2981_, 0);
lean_inc(v_fst_2984_);
v_snd_2985_ = lean_ctor_get(v_snd_2981_, 1);
lean_inc(v_snd_2985_);
lean_dec(v_snd_2981_);
v___x_2986_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality(v_x_2978_, v_fst_2983_, v_fst_2984_, v_snd_2985_);
v_x_2978_ = v___x_2986_;
v_x_2979_ = v_tail_2982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEqualities(lean_object* v_p_2988_, lean_object* v_eqs_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(v_p_2988_, v_eqs_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0(lean_object* v___f_2997_, lean_object* v_x_2998_){
_start:
{
lean_object* v_coeffs_2999_; lean_object* v_constraint_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v_coeffs_2999_ = lean_ctor_get(v_x_2998_, 0);
lean_inc(v_coeffs_2999_);
v_constraint_3000_ = lean_ctor_get(v_x_2998_, 1);
lean_inc_ref(v_constraint_3000_);
lean_dec_ref(v_x_2998_);
v___x_3001_ = l_List_toString___redArg(v___f_2997_, v_coeffs_2999_);
v___x_3002_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3003_ = lean_string_append(v___x_3001_, v___x_3002_);
v___x_3004_ = l_Lean_Omega_Constraint_instToString___private__1(v_constraint_3000_);
lean_dec_ref(v_constraint_3000_);
v___x_3005_ = lean_string_append(v___x_3003_, v___x_3004_);
lean_dec_ref(v___x_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1(lean_object* v___f_3006_, lean_object* v_x_3007_){
_start:
{
lean_object* v_fst_3008_; lean_object* v_coeffs_3009_; lean_object* v_constraint_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_fst_3008_ = lean_ctor_get(v_x_3007_, 0);
lean_inc(v_fst_3008_);
lean_dec_ref(v_x_3007_);
v_coeffs_3009_ = lean_ctor_get(v_fst_3008_, 0);
lean_inc(v_coeffs_3009_);
v_constraint_3010_ = lean_ctor_get(v_fst_3008_, 1);
lean_inc_ref(v_constraint_3010_);
lean_dec(v_fst_3008_);
v___x_3011_ = l_List_toString___redArg(v___f_3006_, v_coeffs_3009_);
v___x_3012_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3013_ = lean_string_append(v___x_3011_, v___x_3012_);
v___x_3014_ = l_Lean_Omega_Constraint_instToString___private__1(v_constraint_3010_);
lean_dec_ref(v_constraint_3010_);
v___x_3015_ = lean_string_append(v___x_3013_, v___x_3014_);
lean_dec_ref(v___x_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2(lean_object* v___f_3020_, lean_object* v___f_3021_, lean_object* v___f_3022_, lean_object* v_d_3023_){
_start:
{
lean_object* v_var_3024_; lean_object* v_irrelevant_3025_; lean_object* v_lowerBounds_3026_; lean_object* v_upperBounds_3027_; lean_object* v___x_3028_; lean_object* v_irrelevant_3029_; lean_object* v_lowerBounds_3030_; lean_object* v_upperBounds_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v_var_3024_ = lean_ctor_get(v_d_3023_, 0);
lean_inc(v_var_3024_);
v_irrelevant_3025_ = lean_ctor_get(v_d_3023_, 1);
lean_inc(v_irrelevant_3025_);
v_lowerBounds_3026_ = lean_ctor_get(v_d_3023_, 2);
lean_inc(v_lowerBounds_3026_);
v_upperBounds_3027_ = lean_ctor_get(v_d_3023_, 3);
lean_inc(v_upperBounds_3027_);
lean_dec_ref(v_d_3023_);
v___x_3028_ = lean_box(0);
v_irrelevant_3029_ = l_List_mapTR_loop___redArg(v___f_3020_, v_irrelevant_3025_, v___x_3028_);
lean_inc_ref(v___f_3021_);
v_lowerBounds_3030_ = l_List_mapTR_loop___redArg(v___f_3021_, v_lowerBounds_3026_, v___x_3028_);
v_upperBounds_3031_ = l_List_mapTR_loop___redArg(v___f_3021_, v_upperBounds_3027_, v___x_3028_);
v___x_3032_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0));
v___x_3033_ = l_Nat_reprFast(v_var_3024_);
v___x_3034_ = lean_string_append(v___x_3032_, v___x_3033_);
lean_dec_ref(v___x_3033_);
v___x_3035_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_3036_ = lean_string_append(v___x_3034_, v___x_3035_);
v___x_3037_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1));
lean_inc_ref(v___f_3022_);
v___x_3038_ = l_List_toString___redArg(v___f_3022_, v_irrelevant_3029_);
v___x_3039_ = lean_string_append(v___x_3037_, v___x_3038_);
lean_dec_ref(v___x_3038_);
v___x_3040_ = lean_string_append(v___x_3039_, v___x_3035_);
v___x_3041_ = lean_string_append(v___x_3036_, v___x_3040_);
lean_dec_ref(v___x_3040_);
v___x_3042_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2));
lean_inc_ref(v___f_3022_);
v___x_3043_ = l_List_toString___redArg(v___f_3022_, v_lowerBounds_3030_);
v___x_3044_ = lean_string_append(v___x_3042_, v___x_3043_);
lean_dec_ref(v___x_3043_);
v___x_3045_ = lean_string_append(v___x_3044_, v___x_3035_);
v___x_3046_ = lean_string_append(v___x_3041_, v___x_3045_);
lean_dec_ref(v___x_3045_);
v___x_3047_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3));
v___x_3048_ = l_List_toString___redArg(v___f_3022_, v_upperBounds_3031_);
v___x_3049_ = lean_string_append(v___x_3047_, v___x_3048_);
lean_dec_ref(v___x_3048_);
v___x_3050_ = lean_string_append(v___x_3046_, v___x_3049_);
lean_dec_ref(v___x_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(lean_object* v_d_3061_){
_start:
{
lean_object* v_lowerBounds_3062_; lean_object* v_upperBounds_3063_; uint8_t v___x_3064_; 
v_lowerBounds_3062_ = lean_ctor_get(v_d_3061_, 2);
v_upperBounds_3063_ = lean_ctor_get(v_d_3061_, 3);
v___x_3064_ = l_List_isEmpty___redArg(v_lowerBounds_3062_);
if (v___x_3064_ == 0)
{
return v___x_3064_;
}
else
{
uint8_t v___x_3065_; 
v___x_3065_ = l_List_isEmpty___redArg(v_upperBounds_3063_);
return v___x_3065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty___boxed(lean_object* v_d_3066_){
_start:
{
uint8_t v_res_3067_; lean_object* v_r_3068_; 
v_res_3067_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v_d_3066_);
lean_dec_ref(v_d_3066_);
v_r_3068_ = lean_box(v_res_3067_);
return v_r_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(lean_object* v_d_3069_){
_start:
{
lean_object* v_lowerBounds_3070_; lean_object* v_upperBounds_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v_lowerBounds_3070_ = lean_ctor_get(v_d_3069_, 2);
v_upperBounds_3071_ = lean_ctor_get(v_d_3069_, 3);
v___x_3072_ = l_List_lengthTR___redArg(v_lowerBounds_3070_);
v___x_3073_ = l_List_lengthTR___redArg(v_upperBounds_3071_);
v___x_3074_ = lean_nat_mul(v___x_3072_, v___x_3073_);
lean_dec(v___x_3073_);
lean_dec(v___x_3072_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size___boxed(lean_object* v_d_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_d_3075_);
lean_dec_ref(v_d_3075_);
return v_res_3076_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(lean_object* v_d_3077_){
_start:
{
uint8_t v_lowerExact_3078_; 
v_lowerExact_3078_ = lean_ctor_get_uint8(v_d_3077_, sizeof(void*)*4);
if (v_lowerExact_3078_ == 0)
{
uint8_t v_upperExact_3079_; 
v_upperExact_3079_ = lean_ctor_get_uint8(v_d_3077_, sizeof(void*)*4 + 1);
return v_upperExact_3079_;
}
else
{
return v_lowerExact_3078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact___boxed(lean_object* v_d_3080_){
_start:
{
uint8_t v_res_3081_; lean_object* v_r_3082_; 
v_res_3081_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_d_3080_);
lean_dec_ref(v_d_3080_);
v_r_3082_ = lean_box(v_res_3081_);
return v_r_3082_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(lean_object* v_x_3083_, lean_object* v_x_3084_){
_start:
{
if (lean_obj_tag(v_x_3084_) == 0)
{
return v_x_3083_;
}
else
{
lean_object* v_head_3085_; lean_object* v_tail_3086_; lean_object* v___x_3087_; uint8_t v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v_head_3085_ = lean_ctor_get(v_x_3084_, 0);
v_tail_3086_ = lean_ctor_get(v_x_3084_, 1);
v___x_3087_ = lean_box(0);
v___x_3088_ = 1;
lean_inc(v_head_3085_);
v___x_3089_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3089_, 0, v_head_3085_);
lean_ctor_set(v___x_3089_, 1, v___x_3087_);
lean_ctor_set(v___x_3089_, 2, v___x_3087_);
lean_ctor_set(v___x_3089_, 3, v___x_3087_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*4, v___x_3088_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*4 + 1, v___x_3088_);
v___x_3090_ = lean_array_push(v_x_3083_, v___x_3089_);
v_x_3083_ = v___x_3090_;
v_x_3084_ = v_tail_3086_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2___boxed(lean_object* v_x_3092_, lean_object* v_x_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v_x_3092_, v_x_3093_);
lean_dec(v_x_3093_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object* v___x_3095_, lean_object* v_b_3096_, lean_object* v___x_3097_, lean_object* v_____r_3098_, lean_object* v_d_x27_3099_){
_start:
{
lean_object* v_upperBound_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3127_; 
v_upperBound_3100_ = lean_ctor_get(v___x_3095_, 1);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v___x_3095_, 0);
lean_dec(v_unused_3128_);
v___x_3102_ = v___x_3095_;
v_isShared_3103_ = v_isSharedCheck_3127_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_upperBound_3100_);
lean_dec(v___x_3095_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3127_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
if (lean_obj_tag(v_upperBound_3100_) == 0)
{
lean_del_object(v___x_3102_);
lean_dec(v___x_3097_);
lean_dec_ref(v_b_3096_);
return v_d_x27_3099_;
}
else
{
lean_object* v_var_3104_; lean_object* v_irrelevant_3105_; lean_object* v_lowerBounds_3106_; lean_object* v_upperBounds_3107_; uint8_t v_lowerExact_3108_; uint8_t v_upperExact_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v_upperBound_3100_);
v_var_3104_ = lean_ctor_get(v_d_x27_3099_, 0);
v_irrelevant_3105_ = lean_ctor_get(v_d_x27_3099_, 1);
v_lowerBounds_3106_ = lean_ctor_get(v_d_x27_3099_, 2);
v_upperBounds_3107_ = lean_ctor_get(v_d_x27_3099_, 3);
v_lowerExact_3108_ = lean_ctor_get_uint8(v_d_x27_3099_, sizeof(void*)*4);
v_upperExact_3109_ = lean_ctor_get_uint8(v_d_x27_3099_, sizeof(void*)*4 + 1);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_d_x27_3099_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3111_ = v_d_x27_3099_;
v_isShared_3112_ = v_isSharedCheck_3126_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_upperBounds_3107_);
lean_inc(v_lowerBounds_3106_);
lean_inc(v_irrelevant_3105_);
lean_inc(v_var_3104_);
lean_dec(v_d_x27_3099_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3126_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
lean_inc(v___x_3097_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 1, v___x_3097_);
lean_ctor_set(v___x_3102_, 0, v_b_3096_);
v___x_3114_ = v___x_3102_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_b_3096_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v___x_3097_);
v___x_3114_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3115_; 
v___x_3115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
lean_ctor_set(v___x_3115_, 1, v_upperBounds_3107_);
if (v_upperExact_3109_ == 0)
{
lean_object* v___x_3117_; 
lean_dec(v___x_3097_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 3, v___x_3115_);
v___x_3117_ = v___x_3111_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_var_3104_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_irrelevant_3105_);
lean_ctor_set(v_reuseFailAlloc_3118_, 2, v_lowerBounds_3106_);
lean_ctor_set(v_reuseFailAlloc_3118_, 3, v___x_3115_);
lean_ctor_set_uint8(v_reuseFailAlloc_3118_, sizeof(void*)*4, v_lowerExact_3108_);
lean_ctor_set_uint8(v_reuseFailAlloc_3118_, sizeof(void*)*4 + 1, v_upperExact_3109_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; lean_object* v___x_3123_; 
v___x_3119_ = lean_nat_abs(v___x_3097_);
lean_dec(v___x_3097_);
v___x_3120_ = lean_unsigned_to_nat(1u);
v___x_3121_ = lean_nat_dec_eq(v___x_3119_, v___x_3120_);
lean_dec(v___x_3119_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 3, v___x_3115_);
v___x_3123_ = v___x_3111_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_var_3104_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v_irrelevant_3105_);
lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_lowerBounds_3106_);
lean_ctor_set(v_reuseFailAlloc_3124_, 3, v___x_3115_);
lean_ctor_set_uint8(v_reuseFailAlloc_3124_, sizeof(void*)*4, v_lowerExact_3108_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_ctor_set_uint8(v___x_3123_, sizeof(void*)*4 + 1, v___x_3121_);
return v___x_3123_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(lean_object* v_upperBound_3129_, lean_object* v_coeffs_3130_, lean_object* v_constraint_3131_, lean_object* v_b_3132_, lean_object* v_a_3133_, lean_object* v_b_3134_){
_start:
{
lean_object* v_a_3136_; uint8_t v___x_3140_; 
v___x_3140_ = lean_nat_dec_lt(v_a_3133_, v_upperBound_3129_);
if (v___x_3140_ == 0)
{
lean_dec(v_a_3133_);
lean_dec_ref(v_b_3132_);
lean_dec_ref(v_constraint_3131_);
return v_b_3134_;
}
else
{
lean_object* v___x_3141_; uint8_t v___x_3142_; 
v___x_3141_ = lean_array_get_size(v_b_3134_);
v___x_3142_ = lean_nat_dec_lt(v_a_3133_, v___x_3141_);
if (v___x_3142_ == 0)
{
v_a_3136_ = v_b_3134_;
goto v___jp_3135_;
}
else
{
lean_object* v___x_3143_; lean_object* v_v_3144_; lean_object* v___x_3145_; lean_object* v_xs_x27_3146_; lean_object* v___y_3148_; lean_object* v___x_3150_; uint8_t v___x_3151_; 
lean_inc(v_a_3133_);
v___x_3143_ = l_Lean_Omega_IntList_get(v_coeffs_3130_, v_a_3133_);
v_v_3144_ = lean_array_fget(v_b_3134_, v_a_3133_);
v___x_3145_ = lean_box(0);
v_xs_x27_3146_ = lean_array_fset(v_b_3134_, v_a_3133_, v___x_3145_);
v___x_3150_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3151_ = lean_int_dec_eq(v___x_3143_, v___x_3150_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; lean_object* v_lowerBound_3153_; 
lean_inc_ref(v_constraint_3131_);
lean_inc(v___x_3143_);
v___x_3152_ = l_Lean_Omega_Constraint_scale(v___x_3143_, v_constraint_3131_);
v_lowerBound_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_lowerBound_3153_);
if (lean_obj_tag(v_lowerBound_3153_) == 0)
{
lean_object* v___x_3154_; 
lean_inc_ref(v_b_3132_);
v___x_3154_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3152_, v_b_3132_, v___x_3143_, v___x_3145_, v_v_3144_);
v___y_3148_ = v___x_3154_;
goto v___jp_3147_;
}
else
{
lean_object* v_var_3155_; lean_object* v_irrelevant_3156_; lean_object* v_lowerBounds_3157_; lean_object* v_upperBounds_3158_; uint8_t v_lowerExact_3159_; uint8_t v_upperExact_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3175_; 
lean_dec_ref(v_lowerBound_3153_);
v_var_3155_ = lean_ctor_get(v_v_3144_, 0);
v_irrelevant_3156_ = lean_ctor_get(v_v_3144_, 1);
v_lowerBounds_3157_ = lean_ctor_get(v_v_3144_, 2);
v_upperBounds_3158_ = lean_ctor_get(v_v_3144_, 3);
v_lowerExact_3159_ = lean_ctor_get_uint8(v_v_3144_, sizeof(void*)*4);
v_upperExact_3160_ = lean_ctor_get_uint8(v_v_3144_, sizeof(void*)*4 + 1);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_v_3144_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3162_ = v_v_3144_;
v_isShared_3163_ = v_isSharedCheck_3175_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_upperBounds_3158_);
lean_inc(v_lowerBounds_3157_);
lean_inc(v_irrelevant_3156_);
lean_inc(v_var_3155_);
lean_dec(v_v_3144_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3175_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; uint8_t v___y_3167_; 
lean_inc(v___x_3143_);
lean_inc_ref(v_b_3132_);
v___x_3164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3164_, 0, v_b_3132_);
lean_ctor_set(v___x_3164_, 1, v___x_3143_);
v___x_3165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
lean_ctor_set(v___x_3165_, 1, v_lowerBounds_3157_);
if (v_lowerExact_3159_ == 0)
{
v___y_3167_ = v_lowerExact_3159_;
goto v___jp_3166_;
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v___x_3172_ = lean_nat_abs(v___x_3143_);
v___x_3173_ = lean_unsigned_to_nat(1u);
v___x_3174_ = lean_nat_dec_eq(v___x_3172_, v___x_3173_);
lean_dec(v___x_3172_);
v___y_3167_ = v___x_3174_;
goto v___jp_3166_;
}
v___jp_3166_:
{
lean_object* v___x_3169_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 2, v___x_3165_);
v___x_3169_ = v___x_3162_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_var_3155_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_irrelevant_3156_);
lean_ctor_set(v_reuseFailAlloc_3171_, 2, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3171_, 3, v_upperBounds_3158_);
lean_ctor_set_uint8(v_reuseFailAlloc_3171_, sizeof(void*)*4 + 1, v_upperExact_3160_);
v___x_3169_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; 
lean_ctor_set_uint8(v___x_3169_, sizeof(void*)*4, v___y_3167_);
lean_inc_ref(v_b_3132_);
v___x_3170_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3152_, v_b_3132_, v___x_3143_, v___x_3145_, v___x_3169_);
v___y_3148_ = v___x_3170_;
goto v___jp_3147_;
}
}
}
}
}
else
{
lean_object* v_var_3176_; lean_object* v_irrelevant_3177_; lean_object* v_lowerBounds_3178_; lean_object* v_upperBounds_3179_; uint8_t v_lowerExact_3180_; uint8_t v_upperExact_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3189_; 
lean_dec(v___x_3143_);
v_var_3176_ = lean_ctor_get(v_v_3144_, 0);
v_irrelevant_3177_ = lean_ctor_get(v_v_3144_, 1);
v_lowerBounds_3178_ = lean_ctor_get(v_v_3144_, 2);
v_upperBounds_3179_ = lean_ctor_get(v_v_3144_, 3);
v_lowerExact_3180_ = lean_ctor_get_uint8(v_v_3144_, sizeof(void*)*4);
v_upperExact_3181_ = lean_ctor_get_uint8(v_v_3144_, sizeof(void*)*4 + 1);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_v_3144_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3183_ = v_v_3144_;
v_isShared_3184_ = v_isSharedCheck_3189_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_upperBounds_3179_);
lean_inc(v_lowerBounds_3178_);
lean_inc(v_irrelevant_3177_);
lean_inc(v_var_3176_);
lean_dec(v_v_3144_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3189_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
lean_inc_ref(v_b_3132_);
v___x_3185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3185_, 0, v_b_3132_);
lean_ctor_set(v___x_3185_, 1, v_irrelevant_3177_);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 1, v___x_3185_);
v___x_3187_ = v___x_3183_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_var_3176_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v___x_3185_);
lean_ctor_set(v_reuseFailAlloc_3188_, 2, v_lowerBounds_3178_);
lean_ctor_set(v_reuseFailAlloc_3188_, 3, v_upperBounds_3179_);
lean_ctor_set_uint8(v_reuseFailAlloc_3188_, sizeof(void*)*4, v_lowerExact_3180_);
lean_ctor_set_uint8(v_reuseFailAlloc_3188_, sizeof(void*)*4 + 1, v_upperExact_3181_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
v___y_3148_ = v___x_3187_;
goto v___jp_3147_;
}
}
}
v___jp_3147_:
{
lean_object* v___x_3149_; 
v___x_3149_ = lean_array_fset(v_xs_x27_3146_, v_a_3133_, v___y_3148_);
v_a_3136_ = v___x_3149_;
goto v___jp_3135_;
}
}
}
v___jp_3135_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = lean_unsigned_to_nat(1u);
v___x_3138_ = lean_nat_add(v_a_3133_, v___x_3137_);
lean_dec(v_a_3133_);
v_a_3133_ = v___x_3138_;
v_b_3134_ = v_a_3136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___boxed(lean_object* v_upperBound_3190_, lean_object* v_coeffs_3191_, lean_object* v_constraint_3192_, lean_object* v_b_3193_, lean_object* v_a_3194_, lean_object* v_b_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3190_, v_coeffs_3191_, v_constraint_3192_, v_b_3193_, v_a_3194_, v_b_3195_);
lean_dec(v_coeffs_3191_);
lean_dec(v_upperBound_3190_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(lean_object* v_n_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
if (lean_obj_tag(v_a_3198_) == 0)
{
lean_object* v___x_3200_; 
v___x_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3200_, 0, v_a_3199_);
return v___x_3200_;
}
else
{
lean_object* v_value_3201_; lean_object* v_tail_3202_; lean_object* v_coeffs_3203_; lean_object* v_constraint_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v_value_3201_ = lean_ctor_get(v_a_3198_, 1);
lean_inc(v_value_3201_);
v_tail_3202_ = lean_ctor_get(v_a_3198_, 2);
lean_inc(v_tail_3202_);
lean_dec_ref(v_a_3198_);
v_coeffs_3203_ = lean_ctor_get(v_value_3201_, 0);
lean_inc(v_coeffs_3203_);
v_constraint_3204_ = lean_ctor_get(v_value_3201_, 1);
lean_inc_ref(v_constraint_3204_);
v___x_3205_ = lean_unsigned_to_nat(0u);
v___x_3206_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_n_3197_, v_coeffs_3203_, v_constraint_3204_, v_value_3201_, v___x_3205_, v_a_3199_);
lean_dec(v_coeffs_3203_);
v_a_3198_ = v_tail_3202_;
v_a_3199_ = v___x_3206_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1___boxed(lean_object* v_n_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3208_, v_a_3209_, v_a_3210_);
lean_dec(v_n_3208_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(lean_object* v_n_3212_, lean_object* v_as_3213_, size_t v_sz_3214_, size_t v_i_3215_, lean_object* v_b_3216_){
_start:
{
uint8_t v___x_3217_; 
v___x_3217_ = lean_usize_dec_lt(v_i_3215_, v_sz_3214_);
if (v___x_3217_ == 0)
{
return v_b_3216_;
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3219_; 
v_a_3218_ = lean_array_uget_borrowed(v_as_3213_, v_i_3215_);
lean_inc(v_a_3218_);
v___x_3219_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3212_, v_a_3218_, v_b_3216_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref(v___x_3219_);
return v_a_3220_;
}
else
{
lean_object* v_a_3221_; size_t v___x_3222_; size_t v___x_3223_; 
v_a_3221_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3221_);
lean_dec_ref(v___x_3219_);
v___x_3222_ = ((size_t)1ULL);
v___x_3223_ = lean_usize_add(v_i_3215_, v___x_3222_);
v_i_3215_ = v___x_3223_;
v_b_3216_ = v_a_3221_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3___boxed(lean_object* v_n_3225_, lean_object* v_as_3226_, lean_object* v_sz_3227_, lean_object* v_i_3228_, lean_object* v_b_3229_){
_start:
{
size_t v_sz_boxed_3230_; size_t v_i_boxed_3231_; lean_object* v_res_3232_; 
v_sz_boxed_3230_ = lean_unbox_usize(v_sz_3227_);
lean_dec(v_sz_3227_);
v_i_boxed_3231_ = lean_unbox_usize(v_i_3228_);
lean_dec(v_i_3228_);
v_res_3232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_n_3225_, v_as_3226_, v_sz_boxed_3230_, v_i_boxed_3231_, v_b_3229_);
lean_dec_ref(v_as_3226_);
lean_dec(v_n_3225_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(lean_object* v_p_3235_){
_start:
{
lean_object* v_constraints_3236_; lean_object* v_numVars_3237_; lean_object* v_buckets_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v_data_3241_; size_t v_sz_3242_; size_t v___x_3243_; lean_object* v___x_3244_; 
v_constraints_3236_ = lean_ctor_get(v_p_3235_, 2);
lean_inc_ref(v_constraints_3236_);
v_numVars_3237_ = lean_ctor_get(v_p_3235_, 1);
lean_inc(v_numVars_3237_);
lean_dec_ref(v_p_3235_);
v_buckets_3238_ = lean_ctor_get(v_constraints_3236_, 1);
lean_inc_ref(v_buckets_3238_);
lean_dec_ref(v_constraints_3236_);
v___x_3239_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
lean_inc(v_numVars_3237_);
v___x_3240_ = l_List_range(v_numVars_3237_);
v_data_3241_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v___x_3239_, v___x_3240_);
lean_dec(v___x_3240_);
v_sz_3242_ = lean_array_size(v_buckets_3238_);
v___x_3243_ = ((size_t)0ULL);
v___x_3244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_numVars_3237_, v_buckets_3238_, v_sz_3242_, v___x_3243_, v_data_3241_);
lean_dec_ref(v_buckets_3238_);
lean_dec(v_numVars_3237_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(lean_object* v_upperBound_3245_, lean_object* v_coeffs_3246_, lean_object* v_constraint_3247_, lean_object* v_b_3248_, lean_object* v_inst_3249_, lean_object* v_R_3250_, lean_object* v_a_3251_, lean_object* v_b_3252_, lean_object* v_c_3253_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3245_, v_coeffs_3246_, v_constraint_3247_, v_b_3248_, v_a_3251_, v_b_3252_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___boxed(lean_object* v_upperBound_3255_, lean_object* v_coeffs_3256_, lean_object* v_constraint_3257_, lean_object* v_b_3258_, lean_object* v_inst_3259_, lean_object* v_R_3260_, lean_object* v_a_3261_, lean_object* v_b_3262_, lean_object* v_c_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(v_upperBound_3255_, v_coeffs_3256_, v_constraint_3257_, v_b_3258_, v_inst_3259_, v_R_3260_, v_a_3261_, v_b_3262_, v_c_3263_);
lean_dec(v_coeffs_3256_);
lean_dec(v_upperBound_3255_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(lean_object* v_cls_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v_options_3271_; uint8_t v_hasTrace_3272_; 
v_options_3271_ = lean_ctor_get(v___y_3269_, 2);
v_hasTrace_3272_ = lean_ctor_get_uint8(v_options_3271_, sizeof(void*)*1);
if (v_hasTrace_3272_ == 0)
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
lean_dec(v_cls_3268_);
v___x_3273_ = lean_box(v_hasTrace_3272_);
v___x_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
return v___x_3274_;
}
else
{
lean_object* v_inheritedTraceOptions_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v_inheritedTraceOptions_3275_ = lean_ctor_get(v___y_3269_, 13);
v___x_3276_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___closed__1));
v___x_3277_ = l_Lean_Name_append(v___x_3276_, v_cls_3268_);
v___x_3278_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3275_, v_options_3271_, v___x_3277_);
lean_dec(v___x_3277_);
v___x_3279_ = lean_box(v___x_3278_);
v___x_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
return v___x_3280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___boxed(lean_object* v_cls_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v_cls_3281_, v___y_3282_);
lean_dec_ref(v___y_3282_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(lean_object* v_cls_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v_cls_3285_, v___y_3288_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___boxed(lean_object* v_cls_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5(lean_object* v_as_3299_, size_t v_i_3300_, size_t v_stop_3301_, lean_object* v_b_3302_){
_start:
{
lean_object* v___y_3304_; uint8_t v___x_3308_; 
v___x_3308_ = lean_usize_dec_eq(v_i_3300_, v_stop_3301_);
if (v___x_3308_ == 0)
{
lean_object* v___x_3309_; uint8_t v___x_3312_; 
v___x_3309_ = lean_array_uget_borrowed(v_as_3299_, v_i_3300_);
v___x_3312_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v___x_3309_);
if (v___x_3312_ == 0)
{
goto v___jp_3310_;
}
else
{
if (v___x_3308_ == 0)
{
v___y_3304_ = v_b_3302_;
goto v___jp_3303_;
}
else
{
goto v___jp_3310_;
}
}
v___jp_3310_:
{
lean_object* v___x_3311_; 
lean_inc(v___x_3309_);
v___x_3311_ = lean_array_push(v_b_3302_, v___x_3309_);
v___y_3304_ = v___x_3311_;
goto v___jp_3303_;
}
}
else
{
return v_b_3302_;
}
v___jp_3303_:
{
size_t v___x_3305_; size_t v___x_3306_; 
v___x_3305_ = ((size_t)1ULL);
v___x_3306_ = lean_usize_add(v_i_3300_, v___x_3305_);
v_i_3300_ = v___x_3306_;
v_b_3302_ = v___y_3304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5___boxed(lean_object* v_as_3313_, lean_object* v_i_3314_, lean_object* v_stop_3315_, lean_object* v_b_3316_){
_start:
{
size_t v_i_boxed_3317_; size_t v_stop_boxed_3318_; lean_object* v_res_3319_; 
v_i_boxed_3317_ = lean_unbox_usize(v_i_3314_);
lean_dec(v_i_3314_);
v_stop_boxed_3318_ = lean_unbox_usize(v_stop_3315_);
lean_dec(v_stop_3315_);
v_res_3319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5(v_as_3313_, v_i_boxed_3317_, v_stop_boxed_3318_, v_b_3316_);
lean_dec_ref(v_as_3313_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0(lean_object* v___x_3320_, lean_object* v_fst_3321_, lean_object* v_snd_3322_, lean_object* v_fst_3323_, lean_object* v_____r_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3320_);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v_fst_3321_);
lean_ctor_set(v___x_3331_, 1, v_snd_3322_);
v___x_3332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3332_, 0, v_fst_3323_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3330_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
v___x_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0___boxed(lean_object* v___x_3336_, lean_object* v_fst_3337_, lean_object* v_snd_3338_, lean_object* v_fst_3339_, lean_object* v_____r_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0(v___x_3336_, v_fst_3337_, v_snd_3338_, v_fst_3339_, v_____r_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
return v_res_3346_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3347_; double v___x_3348_; 
v___x_3347_ = lean_unsigned_to_nat(0u);
v___x_3348_ = lean_float_of_nat(v___x_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object* v_cls_3351_, lean_object* v_msg_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v_ref_3358_; lean_object* v___x_3359_; lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3404_; 
v_ref_3358_ = lean_ctor_get(v___y_3355_, 5);
v___x_3359_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3362_ = v___x_3359_;
v_isShared_3363_ = v_isSharedCheck_3404_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3404_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3364_; lean_object* v_traceState_3365_; lean_object* v_env_3366_; lean_object* v_nextMacroScope_3367_; lean_object* v_ngen_3368_; lean_object* v_auxDeclNGen_3369_; lean_object* v_cache_3370_; lean_object* v_messages_3371_; lean_object* v_infoState_3372_; lean_object* v_snapshotTasks_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3403_; 
v___x_3364_ = lean_st_ref_take(v___y_3356_);
v_traceState_3365_ = lean_ctor_get(v___x_3364_, 4);
v_env_3366_ = lean_ctor_get(v___x_3364_, 0);
v_nextMacroScope_3367_ = lean_ctor_get(v___x_3364_, 1);
v_ngen_3368_ = lean_ctor_get(v___x_3364_, 2);
v_auxDeclNGen_3369_ = lean_ctor_get(v___x_3364_, 3);
v_cache_3370_ = lean_ctor_get(v___x_3364_, 5);
v_messages_3371_ = lean_ctor_get(v___x_3364_, 6);
v_infoState_3372_ = lean_ctor_get(v___x_3364_, 7);
v_snapshotTasks_3373_ = lean_ctor_get(v___x_3364_, 8);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3375_ = v___x_3364_;
v_isShared_3376_ = v_isSharedCheck_3403_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_snapshotTasks_3373_);
lean_inc(v_infoState_3372_);
lean_inc(v_messages_3371_);
lean_inc(v_cache_3370_);
lean_inc(v_traceState_3365_);
lean_inc(v_auxDeclNGen_3369_);
lean_inc(v_ngen_3368_);
lean_inc(v_nextMacroScope_3367_);
lean_inc(v_env_3366_);
lean_dec(v___x_3364_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3403_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
uint64_t v_tid_3377_; lean_object* v_traces_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3402_; 
v_tid_3377_ = lean_ctor_get_uint64(v_traceState_3365_, sizeof(void*)*1);
v_traces_3378_ = lean_ctor_get(v_traceState_3365_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_traceState_3365_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3380_ = v_traceState_3365_;
v_isShared_3381_ = v_isSharedCheck_3402_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_traces_3378_);
lean_dec(v_traceState_3365_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3402_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; double v___x_3383_; uint8_t v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3382_ = lean_box(0);
v___x_3383_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0);
v___x_3384_ = 0;
v___x_3385_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_3386_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3386_, 0, v_cls_3351_);
lean_ctor_set(v___x_3386_, 1, v___x_3382_);
lean_ctor_set(v___x_3386_, 2, v___x_3385_);
lean_ctor_set_float(v___x_3386_, sizeof(void*)*3, v___x_3383_);
lean_ctor_set_float(v___x_3386_, sizeof(void*)*3 + 8, v___x_3383_);
lean_ctor_set_uint8(v___x_3386_, sizeof(void*)*3 + 16, v___x_3384_);
v___x_3387_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__1));
v___x_3388_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3386_);
lean_ctor_set(v___x_3388_, 1, v_a_3360_);
lean_ctor_set(v___x_3388_, 2, v___x_3387_);
lean_inc(v_ref_3358_);
v___x_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3389_, 0, v_ref_3358_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = l_Lean_PersistentArray_push___redArg(v_traces_3378_, v___x_3389_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v___x_3390_);
v___x_3392_ = v___x_3380_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3390_);
lean_ctor_set_uint64(v_reuseFailAlloc_3401_, sizeof(void*)*1, v_tid_3377_);
v___x_3392_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3394_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 4, v___x_3392_);
v___x_3394_ = v___x_3375_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_env_3366_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v_nextMacroScope_3367_);
lean_ctor_set(v_reuseFailAlloc_3400_, 2, v_ngen_3368_);
lean_ctor_set(v_reuseFailAlloc_3400_, 3, v_auxDeclNGen_3369_);
lean_ctor_set(v_reuseFailAlloc_3400_, 4, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3400_, 5, v_cache_3370_);
lean_ctor_set(v_reuseFailAlloc_3400_, 6, v_messages_3371_);
lean_ctor_set(v_reuseFailAlloc_3400_, 7, v_infoState_3372_);
lean_ctor_set(v_reuseFailAlloc_3400_, 8, v_snapshotTasks_3373_);
v___x_3394_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3395_ = lean_st_ref_set(v___y_3356_, v___x_3394_);
v___x_3396_ = lean_box(0);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 0, v___x_3396_);
v___x_3398_ = v___x_3362_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object* v_cls_3405_, lean_object* v_msg_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_cls_3405_, v_msg_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3412_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__0));
v___x_3415_ = l_Lean_stringToMessageData(v___x_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg(lean_object* v_upperBound_3416_, lean_object* v___y_3417_, lean_object* v_a_3418_, lean_object* v_b_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v_a_3426_; lean_object* v___y_3431_; uint8_t v___x_3450_; 
v___x_3450_ = lean_nat_dec_lt(v_a_3418_, v_upperBound_3416_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; 
lean_dec(v_a_3418_);
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v_b_3419_);
return v___x_3451_;
}
else
{
lean_object* v_snd_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3527_; 
v_snd_3452_ = lean_ctor_get(v_b_3419_, 1);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_b_3419_);
if (v_isSharedCheck_3527_ == 0)
{
lean_object* v_unused_3528_; 
v_unused_3528_ = lean_ctor_get(v_b_3419_, 0);
lean_dec(v_unused_3528_);
v___x_3454_ = v_b_3419_;
v_isShared_3455_ = v_isSharedCheck_3527_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_snd_3452_);
lean_dec(v_b_3419_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3527_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v_snd_3456_; lean_object* v_fst_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3526_; 
v_snd_3456_ = lean_ctor_get(v_snd_3452_, 1);
v_fst_3457_ = lean_ctor_get(v_snd_3452_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_snd_3452_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3459_ = v_snd_3452_;
v_isShared_3460_ = v_isSharedCheck_3526_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_snd_3456_);
lean_inc(v_fst_3457_);
lean_dec(v_snd_3452_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3526_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v_fst_3461_; lean_object* v_snd_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3525_; 
v_fst_3461_ = lean_ctor_get(v_snd_3456_, 0);
v_snd_3462_ = lean_ctor_get(v_snd_3456_, 1);
v_isSharedCheck_3525_ = !lean_is_exclusive(v_snd_3456_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3464_ = v_snd_3456_;
v_isShared_3465_ = v_isSharedCheck_3525_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_snd_3462_);
lean_inc(v_fst_3461_);
lean_dec(v_snd_3456_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3525_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_bestIdx_3466_; lean_object* v___x_3467_; lean_object* v_cls_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; lean_object* v___x_3481_; uint8_t v___x_3482_; uint8_t v___y_3519_; uint8_t v___y_3522_; 
v_bestIdx_3466_ = lean_unsigned_to_nat(0u);
v___x_3467_ = lean_box(0);
v_cls_3478_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_3479_ = lean_array_fget_borrowed(v___y_3417_, v_a_3418_);
v___x_3480_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_3479_);
v___x_3481_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_3479_);
v___x_3482_ = lean_nat_dec_eq(v___x_3481_, v_bestIdx_3466_);
if (v___x_3482_ == 0)
{
uint8_t v___x_3524_; 
v___x_3524_ = lean_unbox(v_snd_3462_);
if (v___x_3524_ == 0)
{
v___y_3522_ = v___x_3480_;
goto v___jp_3521_;
}
else
{
if (v___x_3482_ == 0)
{
v___y_3522_ = v___x_3482_;
goto v___jp_3521_;
}
else
{
v___y_3522_ = v___x_3480_;
goto v___jp_3521_;
}
}
}
else
{
v___y_3522_ = v___x_3482_;
goto v___jp_3521_;
}
v___jp_3468_:
{
lean_object* v___x_3470_; 
if (v_isShared_3465_ == 0)
{
v___x_3470_ = v___x_3464_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_fst_3461_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_snd_3462_);
v___x_3470_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3472_; 
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 1, v___x_3470_);
v___x_3472_ = v___x_3459_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_fst_3457_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
lean_object* v___x_3474_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 1, v___x_3472_);
lean_ctor_set(v___x_3454_, 0, v___x_3467_);
v___x_3474_ = v___x_3454_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3467_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v___x_3472_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
v_a_3426_ = v___x_3474_;
goto v___jp_3425_;
}
}
}
}
v___jp_3483_:
{
if (v___x_3482_ == 0)
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_fst_3457_);
v___x_3484_ = lean_box(v___x_3480_);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3481_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
lean_inc(v_a_3418_);
v___x_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3486_, 0, v_a_3418_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3467_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v_a_3426_ = v___x_3487_;
goto v___jp_3425_;
}
else
{
lean_object* v___x_3488_; 
lean_dec(v___x_3481_);
v___x_3488_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v_cls_3478_, v___y_3422_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; uint8_t v___x_3490_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref(v___x_3488_);
v___x_3490_ = lean_unbox(v_a_3489_);
lean_dec(v_a_3489_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = lean_box(0);
lean_inc(v___x_3479_);
v___x_3492_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0(v___x_3479_, v_fst_3461_, v_snd_3462_, v_fst_3457_, v___x_3491_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
v___y_3431_ = v___x_3492_;
goto v___jp_3430_;
}
else
{
lean_object* v_var_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v_var_3493_ = lean_ctor_get(v___x_3479_, 0);
v___x_3494_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1);
lean_inc(v_var_3493_);
v___x_3495_ = l_Nat_reprFast(v_var_3493_);
v___x_3496_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
v___x_3497_ = l_Lean_MessageData_ofFormat(v___x_3496_);
v___x_3498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3494_);
lean_ctor_set(v___x_3498_, 1, v___x_3497_);
v___x_3499_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_cls_3478_, v___x_3498_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3501_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref(v___x_3499_);
lean_inc(v___x_3479_);
v___x_3501_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0(v___x_3479_, v_fst_3461_, v_snd_3462_, v_fst_3457_, v_a_3500_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
v___y_3431_ = v___x_3501_;
goto v___jp_3430_;
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_fst_3457_);
lean_dec(v_a_3418_);
v_a_3502_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3499_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3499_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec(v_fst_3457_);
lean_dec(v_a_3418_);
v_a_3510_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3488_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3488_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
v___jp_3518_:
{
if (v___y_3519_ == 0)
{
lean_dec(v___x_3481_);
goto v___jp_3468_;
}
else
{
uint8_t v___x_3520_; 
v___x_3520_ = lean_nat_dec_lt(v___x_3481_, v_fst_3461_);
if (v___x_3520_ == 0)
{
lean_dec(v___x_3481_);
goto v___jp_3468_;
}
else
{
lean_del_object(v___x_3464_);
lean_del_object(v___x_3459_);
lean_del_object(v___x_3454_);
goto v___jp_3483_;
}
}
}
v___jp_3521_:
{
if (v___y_3522_ == 0)
{
uint8_t v___x_3523_; 
v___x_3523_ = lean_unbox(v_snd_3462_);
if (v___x_3523_ == 0)
{
if (v___x_3480_ == 0)
{
v___y_3519_ = v___x_3450_;
goto v___jp_3518_;
}
else
{
lean_dec(v___x_3481_);
goto v___jp_3468_;
}
}
else
{
v___y_3519_ = v___x_3480_;
goto v___jp_3518_;
}
}
else
{
lean_del_object(v___x_3464_);
lean_del_object(v___x_3459_);
lean_del_object(v___x_3454_);
goto v___jp_3483_;
}
}
}
}
}
}
v___jp_3425_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = lean_unsigned_to_nat(1u);
v___x_3428_ = lean_nat_add(v_a_3418_, v___x_3427_);
lean_dec(v_a_3418_);
v_a_3418_ = v___x_3428_;
v_b_3419_ = v_a_3426_;
goto _start;
}
v___jp_3430_:
{
if (lean_obj_tag(v___y_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3441_; 
v_a_3432_ = lean_ctor_get(v___y_3431_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___y_3431_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3434_ = v___y_3431_;
v_isShared_3435_ = v_isSharedCheck_3441_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___y_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3441_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
if (lean_obj_tag(v_a_3432_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3438_; 
lean_dec(v_a_3418_);
v_a_3436_ = lean_ctor_get(v_a_3432_, 0);
lean_inc(v_a_3436_);
lean_dec_ref(v_a_3432_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v_a_3436_);
v___x_3438_ = v___x_3434_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3436_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
else
{
lean_object* v_a_3440_; 
lean_del_object(v___x_3434_);
v_a_3440_ = lean_ctor_get(v_a_3432_, 0);
lean_inc(v_a_3440_);
lean_dec_ref(v_a_3432_);
v_a_3426_ = v_a_3440_;
goto v___jp_3425_;
}
}
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec(v_a_3418_);
v_a_3442_ = lean_ctor_get(v___y_3431_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___y_3431_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___y_3431_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___y_3431_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___boxed(lean_object* v_upperBound_3529_, lean_object* v___y_3530_, lean_object* v_a_3531_, lean_object* v_b_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg(v_upperBound_3529_, v___y_3530_, v_a_3531_, v_b_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3530_);
lean_dec(v_upperBound_3529_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(size_t v_sz_3539_, size_t v_i_3540_, lean_object* v_bs_3541_){
_start:
{
uint8_t v___x_3542_; 
v___x_3542_ = lean_usize_dec_lt(v_i_3540_, v_sz_3539_);
if (v___x_3542_ == 0)
{
return v_bs_3541_;
}
else
{
lean_object* v_v_3543_; lean_object* v_var_3544_; lean_object* v___x_3545_; lean_object* v_bs_x27_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; size_t v___x_3552_; size_t v___x_3553_; lean_object* v___x_3554_; 
v_v_3543_ = lean_array_uget(v_bs_3541_, v_i_3540_);
v_var_3544_ = lean_ctor_get(v_v_3543_, 0);
lean_inc(v_var_3544_);
v___x_3545_ = lean_unsigned_to_nat(0u);
v_bs_x27_3546_ = lean_array_uset(v_bs_3541_, v_i_3540_, v___x_3545_);
v___x_3547_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_v_3543_);
v___x_3548_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_v_3543_);
lean_dec(v_v_3543_);
v___x_3549_ = lean_box(v___x_3548_);
v___x_3550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3547_);
lean_ctor_set(v___x_3550_, 1, v___x_3549_);
v___x_3551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3551_, 0, v_var_3544_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
v___x_3552_ = ((size_t)1ULL);
v___x_3553_ = lean_usize_add(v_i_3540_, v___x_3552_);
v___x_3554_ = lean_array_uset(v_bs_x27_3546_, v_i_3540_, v___x_3551_);
v_i_3540_ = v___x_3553_;
v_bs_3541_ = v___x_3554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___boxed(lean_object* v_sz_3556_, lean_object* v_i_3557_, lean_object* v_bs_3558_){
_start:
{
size_t v_sz_boxed_3559_; size_t v_i_boxed_3560_; lean_object* v_res_3561_; 
v_sz_boxed_3559_ = lean_unbox_usize(v_sz_3556_);
lean_dec(v_sz_3556_);
v_i_boxed_3560_ = lean_unbox_usize(v_i_3557_);
lean_dec(v_i_3557_);
v_res_3561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v_sz_boxed_3559_, v_i_boxed_3560_, v_bs_3558_);
return v_res_3561_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__1));
v___x_3566_ = l_Lean_MessageData_ofFormat(v___x_3565_);
return v___x_3566_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = lean_box(1);
v___x_3568_ = l_Lean_MessageData_ofFormat(v___x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
if (lean_obj_tag(v_a_3570_) == 0)
{
lean_object* v___x_3572_; 
v___x_3572_ = l_List_reverse___redArg(v_a_3571_);
return v___x_3572_;
}
else
{
lean_object* v_head_3573_; lean_object* v_snd_3574_; lean_object* v_tail_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3622_; 
v_head_3573_ = lean_ctor_get(v_a_3570_, 0);
lean_inc(v_head_3573_);
v_snd_3574_ = lean_ctor_get(v_head_3573_, 1);
lean_inc(v_snd_3574_);
v_tail_3575_ = lean_ctor_get(v_a_3570_, 1);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_a_3570_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; 
v_unused_3623_ = lean_ctor_get(v_a_3570_, 0);
lean_dec(v_unused_3623_);
v___x_3577_ = v_a_3570_;
v_isShared_3578_ = v_isSharedCheck_3622_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_tail_3575_);
lean_dec(v_a_3570_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3622_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v_fst_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3620_; 
v_fst_3579_ = lean_ctor_get(v_head_3573_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_head_3573_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; 
v_unused_3621_ = lean_ctor_get(v_head_3573_, 1);
lean_dec(v_unused_3621_);
v___x_3581_ = v_head_3573_;
v_isShared_3582_ = v_isSharedCheck_3620_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_fst_3579_);
lean_dec(v_head_3573_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3620_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v_fst_3583_; lean_object* v_snd_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3619_; 
v_fst_3583_ = lean_ctor_get(v_snd_3574_, 0);
v_snd_3584_ = lean_ctor_get(v_snd_3574_, 1);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_snd_3574_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3586_ = v_snd_3574_;
v_isShared_3587_ = v_isSharedCheck_3619_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_snd_3584_);
lean_inc(v_fst_3583_);
lean_dec(v_snd_3574_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3619_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3588_ = l_Nat_reprFast(v_fst_3579_);
v___x_3589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
v___x_3590_ = l_Lean_MessageData_ofFormat(v___x_3589_);
v___x_3591_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2);
if (v_isShared_3587_ == 0)
{
lean_ctor_set_tag(v___x_3586_, 7);
lean_ctor_set(v___x_3586_, 1, v___x_3591_);
lean_ctor_set(v___x_3586_, 0, v___x_3590_);
v___x_3593_ = v___x_3586_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3594_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3);
if (v_isShared_3582_ == 0)
{
lean_ctor_set_tag(v___x_3581_, 7);
lean_ctor_set(v___x_3581_, 1, v___x_3594_);
lean_ctor_set(v___x_3581_, 0, v___x_3593_);
v___x_3596_ = v___x_3581_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3593_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___y_3603_; uint8_t v___x_3614_; 
v___x_3597_ = l_Nat_reprFast(v_fst_3583_);
v___x_3598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
v___x_3599_ = l_Lean_MessageData_ofFormat(v___x_3598_);
v___x_3600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
lean_ctor_set(v___x_3600_, 1, v___x_3591_);
v___x_3601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
lean_ctor_set(v___x_3601_, 1, v___x_3594_);
v___x_3614_ = lean_unbox(v_snd_3584_);
lean_dec(v_snd_3584_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; 
v___x_3615_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__4));
v___y_3603_ = v___x_3615_;
goto v___jp_3602_;
}
else
{
lean_object* v___x_3616_; 
v___x_3616_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4));
v___y_3603_ = v___x_3616_;
goto v___jp_3602_;
}
v___jp_3602_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3611_; 
v___x_3604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3604_, 0, v___y_3603_);
v___x_3605_ = l_Lean_MessageData_ofFormat(v___x_3604_);
v___x_3606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3601_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = l_Lean_MessageData_paren(v___x_3606_);
v___x_3608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3596_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = l_Lean_MessageData_paren(v___x_3608_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 1, v_a_3571_);
lean_ctor_set(v___x_3577_, 0, v___x_3609_);
v___x_3611_ = v___x_3577_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_a_3571_);
v___x_3611_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
v_a_3570_ = v_tail_3575_;
v_a_3571_ = v___x_3611_;
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
lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0));
v___x_3626_ = l_Lean_stringToMessageData(v___x_3625_);
return v___x_3626_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3(void){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2));
v___x_3629_ = l_Lean_stringToMessageData(v___x_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(lean_object* v_data_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v___x_3636_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v_bestIdx_3642_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3760_; lean_object* v___x_3783_; lean_object* v___x_3784_; uint8_t v___x_3785_; 
v___x_3636_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default));
v_bestIdx_3642_ = lean_unsigned_to_nat(0u);
v___x_3783_ = lean_array_get_size(v_data_3630_);
v___x_3784_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_3785_ = lean_nat_dec_lt(v_bestIdx_3642_, v___x_3783_);
if (v___x_3785_ == 0)
{
v___y_3760_ = v___x_3784_;
goto v___jp_3759_;
}
else
{
uint8_t v___x_3786_; 
v___x_3786_ = lean_nat_dec_le(v___x_3783_, v___x_3783_);
if (v___x_3786_ == 0)
{
if (v___x_3785_ == 0)
{
v___y_3760_ = v___x_3784_;
goto v___jp_3759_;
}
else
{
size_t v___x_3787_; size_t v___x_3788_; lean_object* v___x_3789_; 
v___x_3787_ = ((size_t)0ULL);
v___x_3788_ = lean_usize_of_nat(v___x_3783_);
v___x_3789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5(v_data_3630_, v___x_3787_, v___x_3788_, v___x_3784_);
v___y_3760_ = v___x_3789_;
goto v___jp_3759_;
}
}
else
{
size_t v___x_3790_; size_t v___x_3791_; lean_object* v___x_3792_; 
v___x_3790_ = ((size_t)0ULL);
v___x_3791_ = lean_usize_of_nat(v___x_3783_);
v___x_3792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5(v_data_3630_, v___x_3790_, v___x_3791_, v___x_3784_);
v___y_3760_ = v___x_3792_;
goto v___jp_3759_;
}
}
v___jp_3637_:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = lean_array_get(v___x_3636_, v___y_3638_, v___y_3639_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
v___x_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3640_);
return v___x_3641_;
}
v___jp_3643_:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; uint8_t v___x_3652_; 
v___x_3650_ = lean_array_get_borrowed(v___x_3636_, v___y_3644_, v_bestIdx_3642_);
v___x_3651_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_3650_);
v___x_3652_ = lean_nat_dec_eq(v___x_3651_, v_bestIdx_3642_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3653_ = lean_unsigned_to_nat(1u);
v___x_3654_ = lean_array_get_size(v___y_3644_);
v___x_3655_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_3650_);
v___x_3656_ = lean_box(0);
v___x_3657_ = lean_box(v___x_3655_);
v___x_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3651_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
v___x_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3659_, 0, v_bestIdx_3642_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3656_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg(v___x_3654_, v___y_3644_, v___x_3653_, v___x_3660_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3715_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3664_ = v___x_3661_;
v_isShared_3665_ = v_isSharedCheck_3715_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3661_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3715_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v_fst_3666_; 
v_fst_3666_ = lean_ctor_get(v_a_3662_, 0);
if (lean_obj_tag(v_fst_3666_) == 0)
{
lean_object* v_snd_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3709_; 
lean_del_object(v___x_3664_);
v_snd_3667_ = lean_ctor_get(v_a_3662_, 1);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_a_3662_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; 
v_unused_3710_ = lean_ctor_get(v_a_3662_, 0);
lean_dec(v_unused_3710_);
v___x_3669_ = v_a_3662_;
v_isShared_3670_ = v_isSharedCheck_3709_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_snd_3667_);
lean_dec(v_a_3662_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3709_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3671_; lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3708_; 
lean_inc(v___y_3645_);
v___x_3671_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v___y_3645_, v___y_3648_);
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3674_ = v___x_3671_;
v_isShared_3675_ = v_isSharedCheck_3708_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3671_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3708_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
uint8_t v___x_3676_; 
v___x_3676_ = lean_unbox(v_a_3672_);
lean_dec(v_a_3672_);
if (v___x_3676_ == 0)
{
lean_object* v_fst_3677_; 
lean_del_object(v___x_3674_);
lean_del_object(v___x_3669_);
lean_dec(v___y_3645_);
v_fst_3677_ = lean_ctor_get(v_snd_3667_, 0);
lean_inc(v_fst_3677_);
lean_dec(v_snd_3667_);
v___y_3638_ = v___y_3644_;
v___y_3639_ = v_fst_3677_;
goto v___jp_3637_;
}
else
{
lean_object* v_fst_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3706_; 
v_fst_3678_ = lean_ctor_get(v_snd_3667_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_snd_3667_);
if (v_isSharedCheck_3706_ == 0)
{
lean_object* v_unused_3707_; 
v_unused_3707_ = lean_ctor_get(v_snd_3667_, 1);
lean_dec(v_unused_3707_);
v___x_3680_ = v_snd_3667_;
v_isShared_3681_ = v_isSharedCheck_3706_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_fst_3678_);
lean_dec(v_snd_3667_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3706_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; lean_object* v_var_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3687_; 
v___x_3682_ = lean_array_get_borrowed(v___x_3636_, v___y_3644_, v_fst_3678_);
v_var_3683_ = lean_ctor_get(v___x_3682_, 0);
v___x_3684_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1);
lean_inc(v_var_3683_);
v___x_3685_ = l_Nat_reprFast(v_var_3683_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set_tag(v___x_3674_, 3);
lean_ctor_set(v___x_3674_, 0, v___x_3685_);
v___x_3687_ = v___x_3674_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3688_ = l_Lean_MessageData_ofFormat(v___x_3687_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set_tag(v___x_3680_, 7);
lean_ctor_set(v___x_3680_, 1, v___x_3688_);
lean_ctor_set(v___x_3680_, 0, v___x_3684_);
v___x_3690_ = v___x_3680_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3691_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
if (v_isShared_3670_ == 0)
{
lean_ctor_set_tag(v___x_3669_, 7);
lean_ctor_set(v___x_3669_, 1, v___x_3691_);
lean_ctor_set(v___x_3669_, 0, v___x_3690_);
v___x_3693_ = v___x_3669_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v___y_3645_, v___x_3693_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_dec_ref(v___x_3694_);
v___y_3638_ = v___y_3644_;
v___y_3639_ = v_fst_3678_;
goto v___jp_3637_;
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec(v_fst_3678_);
lean_dec_ref(v___y_3644_);
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3694_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
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
lean_object* v_val_3711_; lean_object* v___x_3713_; 
lean_inc_ref(v_fst_3666_);
lean_dec(v_a_3662_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
v_val_3711_ = lean_ctor_get(v_fst_3666_, 0);
lean_inc(v_val_3711_);
lean_dec_ref(v_fst_3666_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v_val_3711_);
v___x_3713_ = v___x_3664_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_val_3711_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
v_a_3716_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3661_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3661_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_object* v___x_3724_; lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3758_; 
lean_inc(v___x_3650_);
lean_dec(v___x_3651_);
lean_dec_ref(v___y_3644_);
lean_inc(v___y_3645_);
v___x_3724_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v___y_3645_, v___y_3648_);
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3727_ = v___x_3724_;
v_isShared_3728_ = v_isSharedCheck_3758_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3724_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3758_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
uint8_t v___x_3729_; 
v___x_3729_ = lean_unbox(v_a_3725_);
lean_dec(v_a_3725_);
if (v___x_3729_ == 0)
{
lean_object* v___x_3731_; 
lean_dec(v___y_3645_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v___x_3650_);
v___x_3731_ = v___x_3727_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3650_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
else
{
lean_object* v_var_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_del_object(v___x_3727_);
v_var_3733_ = lean_ctor_get(v___x_3650_, 0);
v___x_3734_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1);
lean_inc(v_var_3733_);
v___x_3735_ = l_Nat_reprFast(v_var_3733_);
v___x_3736_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
v___x_3737_ = l_Lean_MessageData_ofFormat(v___x_3736_);
v___x_3738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3734_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
v___x_3740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3738_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v___y_3645_, v___x_3740_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3748_ == 0)
{
lean_object* v_unused_3749_; 
v_unused_3749_ = lean_ctor_get(v___x_3741_, 0);
lean_dec(v_unused_3749_);
v___x_3743_ = v___x_3741_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_dec(v___x_3741_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v___x_3650_);
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3650_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec(v___x_3650_);
v_a_3750_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3741_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3741_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
}
}
v___jp_3759_:
{
lean_object* v_cls_3761_; lean_object* v___x_3762_; lean_object* v_a_3763_; uint8_t v___x_3764_; 
v_cls_3761_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_3762_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v_cls_3761_, v_a_3633_);
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref(v___x_3762_);
v___x_3764_ = lean_unbox(v_a_3763_);
lean_dec(v_a_3763_);
if (v___x_3764_ == 0)
{
v___y_3644_ = v___y_3760_;
v___y_3645_ = v_cls_3761_;
v___y_3646_ = v_a_3631_;
v___y_3647_ = v_a_3632_;
v___y_3648_ = v_a_3633_;
v___y_3649_ = v_a_3634_;
goto v___jp_3643_;
}
else
{
lean_object* v___x_3765_; size_t v_sz_3766_; size_t v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3765_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3);
v_sz_3766_ = lean_array_size(v___y_3760_);
v___x_3767_ = ((size_t)0ULL);
lean_inc_ref(v___y_3760_);
v___x_3768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v_sz_3766_, v___x_3767_, v___y_3760_);
v___x_3769_ = lean_array_to_list(v___x_3768_);
v___x_3770_ = lean_box(0);
v___x_3771_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v___x_3769_, v___x_3770_);
v___x_3772_ = l_Lean_MessageData_ofList(v___x_3771_);
v___x_3773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3765_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_cls_3761_, v___x_3773_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_dec_ref(v___x_3774_);
v___y_3644_ = v___y_3760_;
v___y_3645_ = v_cls_3761_;
v___y_3646_ = v_a_3631_;
v___y_3647_ = v_a_3632_;
v___y_3648_ = v_a_3633_;
v___y_3649_ = v_a_3634_;
goto v___jp_3643_;
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec_ref(v___y_3760_);
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3774_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3774_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object* v_data_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_);
lean_dec(v_a_3797_);
lean_dec_ref(v_a_3796_);
lean_dec(v_a_3795_);
lean_dec_ref(v_a_3794_);
lean_dec_ref(v_data_3793_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(lean_object* v_upperBound_3800_, lean_object* v___y_3801_, lean_object* v_inst_3802_, lean_object* v_R_3803_, lean_object* v_a_3804_, lean_object* v_b_3805_, lean_object* v_c_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg(v_upperBound_3800_, v___y_3801_, v_a_3804_, v_b_3805_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___boxed(lean_object* v_upperBound_3813_, lean_object* v___y_3814_, lean_object* v_inst_3815_, lean_object* v_R_3816_, lean_object* v_a_3817_, lean_object* v_b_3818_, lean_object* v_c_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_upperBound_3813_, v___y_3814_, v_inst_3815_, v_R_3816_, v_a_3817_, v_b_3818_, v_c_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec_ref(v___y_3814_);
lean_dec(v_upperBound_3813_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(lean_object* v_snd_3826_, lean_object* v_fst_3827_, lean_object* v_as_x27_3828_, lean_object* v_b_3829_){
_start:
{
if (lean_obj_tag(v_as_x27_3828_) == 0)
{
lean_object* v___x_3831_; 
lean_dec_ref(v_fst_3827_);
v___x_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3831_, 0, v_b_3829_);
return v___x_3831_;
}
else
{
lean_object* v_head_3832_; lean_object* v_tail_3833_; lean_object* v_fst_3834_; lean_object* v_snd_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v_head_3832_ = lean_ctor_get(v_as_x27_3828_, 0);
lean_inc(v_head_3832_);
v_tail_3833_ = lean_ctor_get(v_as_x27_3828_, 1);
lean_inc(v_tail_3833_);
lean_dec_ref(v_as_x27_3828_);
v_fst_3834_ = lean_ctor_get(v_head_3832_, 0);
lean_inc(v_fst_3834_);
v_snd_3835_ = lean_ctor_get(v_head_3832_, 1);
lean_inc(v_snd_3835_);
lean_dec(v_head_3832_);
v___x_3836_ = lean_int_neg(v_snd_3826_);
lean_inc_ref(v_fst_3827_);
v___x_3837_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_snd_3835_, v_fst_3827_, v___x_3836_, v_fst_3834_);
v___x_3838_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_3837_);
v___x_3839_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_b_3829_, v___x_3838_);
v_as_x27_3828_ = v_tail_3833_;
v_b_3829_ = v___x_3839_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg___boxed(lean_object* v_snd_3841_, lean_object* v_fst_3842_, lean_object* v_as_x27_3843_, lean_object* v_b_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_3841_, v_fst_3842_, v_as_x27_3843_, v_b_3844_);
lean_dec(v_snd_3841_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(lean_object* v_upperBounds_3847_, lean_object* v_as_x27_3848_, lean_object* v_b_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
if (lean_obj_tag(v_as_x27_3848_) == 0)
{
lean_object* v___x_3855_; 
lean_dec(v_upperBounds_3847_);
v___x_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3855_, 0, v_b_3849_);
return v___x_3855_;
}
else
{
lean_object* v_head_3856_; lean_object* v_tail_3857_; lean_object* v_fst_3858_; lean_object* v_snd_3859_; lean_object* v___x_3860_; lean_object* v_a_3861_; 
v_head_3856_ = lean_ctor_get(v_as_x27_3848_, 0);
lean_inc(v_head_3856_);
v_tail_3857_ = lean_ctor_get(v_as_x27_3848_, 1);
lean_inc(v_tail_3857_);
lean_dec_ref(v_as_x27_3848_);
v_fst_3858_ = lean_ctor_get(v_head_3856_, 0);
lean_inc(v_fst_3858_);
v_snd_3859_ = lean_ctor_get(v_head_3856_, 1);
lean_inc(v_snd_3859_);
lean_dec(v_head_3856_);
lean_inc(v_upperBounds_3847_);
v___x_3860_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_3859_, v_fst_3858_, v_upperBounds_3847_, v_b_3849_);
lean_dec(v_snd_3859_);
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref(v___x_3860_);
v_as_x27_3848_ = v_tail_3857_;
v_b_3849_ = v_a_3861_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg___boxed(lean_object* v_upperBounds_3863_, lean_object* v_as_x27_3864_, lean_object* v_b_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_3863_, v_as_x27_3864_, v_b_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(lean_object* v_as_x27_3872_, lean_object* v_b_3873_){
_start:
{
if (lean_obj_tag(v_as_x27_3872_) == 0)
{
lean_object* v___x_3875_; 
v___x_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3875_, 0, v_b_3873_);
return v___x_3875_;
}
else
{
lean_object* v_head_3876_; lean_object* v_tail_3877_; lean_object* v___x_3878_; 
v_head_3876_ = lean_ctor_get(v_as_x27_3872_, 0);
lean_inc(v_head_3876_);
v_tail_3877_ = lean_ctor_get(v_as_x27_3872_, 1);
lean_inc(v_tail_3877_);
lean_dec_ref(v_as_x27_3872_);
v___x_3878_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_b_3873_, v_head_3876_);
v_as_x27_3872_ = v_tail_3877_;
v_b_3873_ = v___x_3878_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg___boxed(lean_object* v_as_x27_3880_, lean_object* v_b_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_3880_, v_b_3881_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(lean_object* v_p_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_){
_start:
{
lean_object* v_data_3890_; lean_object* v___x_3891_; 
lean_inc_ref(v_p_3884_);
v_data_3890_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(v_p_3884_);
v___x_3891_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_3890_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
lean_dec_ref(v_data_3890_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v_irrelevant_3893_; lean_object* v_lowerBounds_3894_; lean_object* v_upperBounds_3895_; lean_object* v_assumptions_3896_; lean_object* v_eliminations_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3912_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref(v___x_3891_);
v_irrelevant_3893_ = lean_ctor_get(v_a_3892_, 1);
lean_inc(v_irrelevant_3893_);
v_lowerBounds_3894_ = lean_ctor_get(v_a_3892_, 2);
lean_inc(v_lowerBounds_3894_);
v_upperBounds_3895_ = lean_ctor_get(v_a_3892_, 3);
lean_inc(v_upperBounds_3895_);
lean_dec(v_a_3892_);
v_assumptions_3896_ = lean_ctor_get(v_p_3884_, 0);
v_eliminations_3897_ = lean_ctor_get(v_p_3884_, 4);
v_isSharedCheck_3912_ = !lean_is_exclusive(v_p_3884_);
if (v_isSharedCheck_3912_ == 0)
{
lean_object* v_unused_3913_; lean_object* v_unused_3914_; lean_object* v_unused_3915_; lean_object* v_unused_3916_; lean_object* v_unused_3917_; 
v_unused_3913_ = lean_ctor_get(v_p_3884_, 6);
lean_dec(v_unused_3913_);
v_unused_3914_ = lean_ctor_get(v_p_3884_, 5);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_p_3884_, 3);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_p_3884_, 2);
lean_dec(v_unused_3916_);
v_unused_3917_ = lean_ctor_get(v_p_3884_, 1);
lean_dec(v_unused_3917_);
v___x_3899_ = v_p_3884_;
v_isShared_3900_ = v_isSharedCheck_3912_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_eliminations_3897_);
lean_inc(v_assumptions_3896_);
lean_dec(v_p_3884_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3912_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; uint8_t v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3901_ = lean_unsigned_to_nat(0u);
v___x_3902_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v___x_3903_ = 1;
v___x_3904_ = lean_box(0);
v___x_3905_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 6, v___x_3905_);
lean_ctor_set(v___x_3899_, 5, v___x_3904_);
lean_ctor_set(v___x_3899_, 3, v___x_3902_);
lean_ctor_set(v___x_3899_, 2, v___x_3902_);
lean_ctor_set(v___x_3899_, 1, v___x_3901_);
v___x_3907_ = v___x_3899_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_assumptions_3896_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v___x_3901_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v___x_3902_);
lean_ctor_set(v_reuseFailAlloc_3911_, 3, v___x_3902_);
lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_eliminations_3897_);
lean_ctor_set(v_reuseFailAlloc_3911_, 5, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3911_, 6, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3908_; lean_object* v_a_3909_; lean_object* v___x_3910_; 
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*7, v___x_3903_);
v___x_3908_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_irrelevant_3893_, v___x_3907_);
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref(v___x_3908_);
v___x_3910_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_3895_, v_lowerBounds_3894_, v_a_3909_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
return v___x_3910_;
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec_ref(v_p_3884_);
v_a_3918_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3891_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3891_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin___boxed(lean_object* v_p_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
lean_dec(v_a_3930_);
lean_dec_ref(v_a_3929_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(lean_object* v_snd_3933_, lean_object* v_fst_3934_, lean_object* v_as_3935_, lean_object* v_as_x27_3936_, lean_object* v_b_3937_, lean_object* v_a_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_3933_, v_fst_3934_, v_as_x27_3936_, v_b_3937_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___boxed(lean_object* v_snd_3945_, lean_object* v_fst_3946_, lean_object* v_as_3947_, lean_object* v_as_x27_3948_, lean_object* v_b_3949_, lean_object* v_a_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(v_snd_3945_, v_fst_3946_, v_as_3947_, v_as_x27_3948_, v_b_3949_, v_a_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v_as_3947_);
lean_dec(v_snd_3945_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(lean_object* v_as_3957_, lean_object* v_as_x27_3958_, lean_object* v_b_3959_, lean_object* v_a_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_3958_, v_b_3959_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___boxed(lean_object* v_as_3967_, lean_object* v_as_x27_3968_, lean_object* v_b_3969_, lean_object* v_a_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(v_as_3967_, v_as_x27_3968_, v_b_3969_, v_a_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v_as_3967_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(lean_object* v_upperBounds_3977_, lean_object* v_as_3978_, lean_object* v_as_x27_3979_, lean_object* v_b_3980_, lean_object* v_a_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_3977_, v_as_x27_3979_, v_b_3980_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___boxed(lean_object* v_upperBounds_3988_, lean_object* v_as_3989_, lean_object* v_as_x27_3990_, lean_object* v_b_3991_, lean_object* v_a_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(v_upperBounds_3988_, v_as_3989_, v_as_x27_3990_, v_b_3991_, v_a_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v_as_3989_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object* v_cls_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v_options_4002_; uint8_t v_hasTrace_4003_; 
v_options_4002_ = lean_ctor_get(v___y_4000_, 2);
v_hasTrace_4003_ = lean_ctor_get_uint8(v_options_4002_, sizeof(void*)*1);
if (v_hasTrace_4003_ == 0)
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
lean_dec(v_cls_3999_);
v___x_4004_ = lean_box(v_hasTrace_4003_);
v___x_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
return v___x_4005_;
}
else
{
lean_object* v_inheritedTraceOptions_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; uint8_t v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v_inheritedTraceOptions_4006_ = lean_ctor_get(v___y_4000_, 13);
v___x_4007_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___closed__1));
v___x_4008_ = l_Lean_Name_append(v___x_4007_, v_cls_3999_);
v___x_4009_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4006_, v_options_4002_, v___x_4008_);
lean_dec(v___x_4008_);
v___x_4010_ = lean_box(v___x_4009_);
v___x_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
return v___x_4011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg___boxed(lean_object* v_cls_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4012_, v___y_4013_);
lean_dec_ref(v___y_4013_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(lean_object* v_cls_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, uint8_t v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4016_, v___y_4024_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___boxed(lean_object* v_cls_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
uint8_t v___y_14583__boxed_4039_; lean_object* v_res_4040_; 
v___y_14583__boxed_4039_ = lean_unbox(v___y_4032_);
v_res_4040_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(v_cls_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_14583__boxed_4039_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec(v___y_4029_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object* v_x_4041_, lean_object* v_x_4042_){
_start:
{
if (lean_obj_tag(v_x_4042_) == 0)
{
lean_inc(v_x_4041_);
return v_x_4041_;
}
else
{
lean_object* v_key_4043_; lean_object* v_value_4044_; lean_object* v_tail_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v_key_4043_ = lean_ctor_get(v_x_4042_, 0);
v_value_4044_ = lean_ctor_get(v_x_4042_, 1);
v_tail_4045_ = lean_ctor_get(v_x_4042_, 2);
v___x_4046_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_x_4041_, v_tail_4045_);
lean_inc(v_value_4044_);
lean_inc(v_key_4043_);
v___x_4047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4047_, 0, v_key_4043_);
lean_ctor_set(v___x_4047_, 1, v_value_4044_);
v___x_4048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
lean_ctor_set(v___x_4048_, 1, v___x_4046_);
return v___x_4048_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object* v_x_4049_, lean_object* v_x_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_x_4049_, v_x_4050_);
lean_dec(v_x_4050_);
lean_dec(v_x_4049_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4(lean_object* v_as_4052_, size_t v_i_4053_, size_t v_stop_4054_, lean_object* v_b_4055_){
_start:
{
uint8_t v___x_4056_; 
v___x_4056_ = lean_usize_dec_eq(v_i_4053_, v_stop_4054_);
if (v___x_4056_ == 0)
{
size_t v___x_4057_; size_t v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4057_ = ((size_t)1ULL);
v___x_4058_ = lean_usize_sub(v_i_4053_, v___x_4057_);
v___x_4059_ = lean_array_uget_borrowed(v_as_4052_, v___x_4058_);
v___x_4060_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_b_4055_, v___x_4059_);
lean_dec(v_b_4055_);
v_i_4053_ = v___x_4058_;
v_b_4055_ = v___x_4060_;
goto _start;
}
else
{
return v_b_4055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4___boxed(lean_object* v_as_4062_, lean_object* v_i_4063_, lean_object* v_stop_4064_, lean_object* v_b_4065_){
_start:
{
size_t v_i_boxed_4066_; size_t v_stop_boxed_4067_; lean_object* v_res_4068_; 
v_i_boxed_4066_ = lean_unbox_usize(v_i_4063_);
lean_dec(v_i_4063_);
v_stop_boxed_4067_ = lean_unbox_usize(v_stop_4064_);
lean_dec(v_stop_4064_);
v_res_4068_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4(v_as_4062_, v_i_boxed_4066_, v_stop_boxed_4067_, v_b_4065_);
lean_dec_ref(v_as_4062_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(lean_object* v_cls_4069_, lean_object* v_msg_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v_ref_4076_; lean_object* v___x_4077_; lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4122_; 
v_ref_4076_ = lean_ctor_get(v___y_4073_, 5);
v___x_4077_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4080_ = v___x_4077_;
v_isShared_4081_ = v_isSharedCheck_4122_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4077_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4122_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; lean_object* v_traceState_4083_; lean_object* v_env_4084_; lean_object* v_nextMacroScope_4085_; lean_object* v_ngen_4086_; lean_object* v_auxDeclNGen_4087_; lean_object* v_cache_4088_; lean_object* v_messages_4089_; lean_object* v_infoState_4090_; lean_object* v_snapshotTasks_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4121_; 
v___x_4082_ = lean_st_ref_take(v___y_4074_);
v_traceState_4083_ = lean_ctor_get(v___x_4082_, 4);
v_env_4084_ = lean_ctor_get(v___x_4082_, 0);
v_nextMacroScope_4085_ = lean_ctor_get(v___x_4082_, 1);
v_ngen_4086_ = lean_ctor_get(v___x_4082_, 2);
v_auxDeclNGen_4087_ = lean_ctor_get(v___x_4082_, 3);
v_cache_4088_ = lean_ctor_get(v___x_4082_, 5);
v_messages_4089_ = lean_ctor_get(v___x_4082_, 6);
v_infoState_4090_ = lean_ctor_get(v___x_4082_, 7);
v_snapshotTasks_4091_ = lean_ctor_get(v___x_4082_, 8);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4093_ = v___x_4082_;
v_isShared_4094_ = v_isSharedCheck_4121_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_snapshotTasks_4091_);
lean_inc(v_infoState_4090_);
lean_inc(v_messages_4089_);
lean_inc(v_cache_4088_);
lean_inc(v_traceState_4083_);
lean_inc(v_auxDeclNGen_4087_);
lean_inc(v_ngen_4086_);
lean_inc(v_nextMacroScope_4085_);
lean_inc(v_env_4084_);
lean_dec(v___x_4082_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4121_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
uint64_t v_tid_4095_; lean_object* v_traces_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4120_; 
v_tid_4095_ = lean_ctor_get_uint64(v_traceState_4083_, sizeof(void*)*1);
v_traces_4096_ = lean_ctor_get(v_traceState_4083_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v_traceState_4083_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4098_ = v_traceState_4083_;
v_isShared_4099_ = v_isSharedCheck_4120_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_traces_4096_);
lean_dec(v_traceState_4083_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4120_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4100_; double v___x_4101_; uint8_t v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4110_; 
v___x_4100_ = lean_box(0);
v___x_4101_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0);
v___x_4102_ = 0;
v___x_4103_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4104_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4104_, 0, v_cls_4069_);
lean_ctor_set(v___x_4104_, 1, v___x_4100_);
lean_ctor_set(v___x_4104_, 2, v___x_4103_);
lean_ctor_set_float(v___x_4104_, sizeof(void*)*3, v___x_4101_);
lean_ctor_set_float(v___x_4104_, sizeof(void*)*3 + 8, v___x_4101_);
lean_ctor_set_uint8(v___x_4104_, sizeof(void*)*3 + 16, v___x_4102_);
v___x_4105_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__1));
v___x_4106_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4104_);
lean_ctor_set(v___x_4106_, 1, v_a_4078_);
lean_ctor_set(v___x_4106_, 2, v___x_4105_);
lean_inc(v_ref_4076_);
v___x_4107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4107_, 0, v_ref_4076_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = l_Lean_PersistentArray_push___redArg(v_traces_4096_, v___x_4107_);
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 0, v___x_4108_);
v___x_4110_ = v___x_4098_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4108_);
lean_ctor_set_uint64(v_reuseFailAlloc_4119_, sizeof(void*)*1, v_tid_4095_);
v___x_4110_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
lean_object* v___x_4112_; 
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 4, v___x_4110_);
v___x_4112_ = v___x_4093_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_env_4084_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v_nextMacroScope_4085_);
lean_ctor_set(v_reuseFailAlloc_4118_, 2, v_ngen_4086_);
lean_ctor_set(v_reuseFailAlloc_4118_, 3, v_auxDeclNGen_4087_);
lean_ctor_set(v_reuseFailAlloc_4118_, 4, v___x_4110_);
lean_ctor_set(v_reuseFailAlloc_4118_, 5, v_cache_4088_);
lean_ctor_set(v_reuseFailAlloc_4118_, 6, v_messages_4089_);
lean_ctor_set(v_reuseFailAlloc_4118_, 7, v_infoState_4090_);
lean_ctor_set(v_reuseFailAlloc_4118_, 8, v_snapshotTasks_4091_);
v___x_4112_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4116_; 
v___x_4113_ = lean_st_ref_set(v___y_4074_, v___x_4112_);
v___x_4114_ = lean_box(0);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v___x_4114_);
v___x_4116_ = v___x_4080_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v___x_4114_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg___boxed(lean_object* v_cls_4123_, lean_object* v_msg_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(v_cls_4123_, v_msg_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object* v_a_4131_, lean_object* v_a_4132_){
_start:
{
if (lean_obj_tag(v_a_4131_) == 0)
{
lean_object* v___x_4133_; 
v___x_4133_ = l_List_reverse___redArg(v_a_4132_);
return v___x_4133_;
}
else
{
lean_object* v_head_4134_; lean_object* v_snd_4135_; lean_object* v_tail_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4151_; 
v_head_4134_ = lean_ctor_get(v_a_4131_, 0);
lean_inc(v_head_4134_);
v_snd_4135_ = lean_ctor_get(v_head_4134_, 1);
lean_inc(v_snd_4135_);
v_tail_4136_ = lean_ctor_get(v_a_4131_, 1);
v_isSharedCheck_4151_ = !lean_is_exclusive(v_a_4131_);
if (v_isSharedCheck_4151_ == 0)
{
lean_object* v_unused_4152_; 
v_unused_4152_ = lean_ctor_get(v_a_4131_, 0);
lean_dec(v_unused_4152_);
v___x_4138_ = v_a_4131_;
v_isShared_4139_ = v_isSharedCheck_4151_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_tail_4136_);
lean_dec(v_a_4131_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4151_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v_fst_4140_; lean_object* v_constraint_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4148_; 
v_fst_4140_ = lean_ctor_get(v_head_4134_, 0);
lean_inc(v_fst_4140_);
lean_dec(v_head_4134_);
v_constraint_4141_ = lean_ctor_get(v_snd_4135_, 1);
lean_inc_ref(v_constraint_4141_);
lean_dec(v_snd_4135_);
v___x_4142_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_fst_4140_);
lean_dec(v_fst_4140_);
v___x_4143_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_4144_ = lean_string_append(v___x_4142_, v___x_4143_);
v___x_4145_ = l_Lean_Omega_Constraint_instToString___private__1(v_constraint_4141_);
lean_dec_ref(v_constraint_4141_);
v___x_4146_ = lean_string_append(v___x_4144_, v___x_4145_);
lean_dec_ref(v___x_4145_);
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 1, v_a_4132_);
lean_ctor_set(v___x_4138_, 0, v___x_4146_);
v___x_4148_ = v___x_4138_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v___x_4146_);
lean_ctor_set(v_reuseFailAlloc_4150_, 1, v_a_4132_);
v___x_4148_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
v_a_4131_ = v_tail_4136_;
v_a_4132_ = v___x_4148_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1(void){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__0));
v___x_4155_ = l_Lean_stringToMessageData(v___x_4154_);
return v___x_4155_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1(void){
_start:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4157_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__0));
v___x_4158_ = l_Lean_stringToMessageData(v___x_4157_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega(lean_object* v_p_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, uint8_t v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_){
_start:
{
lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; uint8_t v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v_cls_4185_; lean_object* v___x_4186_; 
v_cls_4185_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4186_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4185_, v_a_4167_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; uint8_t v___x_4188_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4187_);
lean_dec_ref(v___x_4186_);
v___x_4188_ = lean_unbox(v_a_4187_);
lean_dec(v_a_4187_);
if (v___x_4188_ == 0)
{
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
v___y_4177_ = v_a_4166_;
v___y_4178_ = v_a_4167_;
v___y_4179_ = v_a_4168_;
goto v___jp_4170_;
}
else
{
lean_object* v_constraints_4189_; uint8_t v_possible_4190_; lean_object* v___x_4191_; lean_object* v___y_4193_; 
v_constraints_4189_ = lean_ctor_get(v_p_4159_, 2);
v_possible_4190_ = lean_ctor_get_uint8(v_p_4159_, sizeof(void*)*7);
v___x_4191_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1);
if (v_possible_4190_ == 0)
{
lean_object* v___x_4206_; 
v___x_4206_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
v___y_4193_ = v___x_4206_;
goto v___jp_4192_;
}
else
{
uint8_t v___x_4207_; 
v___x_4207_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_4159_);
if (v___x_4207_ == 0)
{
lean_object* v_buckets_4208_; lean_object* v___x_4209_; lean_object* v___y_4211_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; 
v_buckets_4208_ = lean_ctor_get(v_constraints_4189_, 1);
v___x_4209_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_4215_ = lean_box(0);
v___x_4216_ = lean_array_get_size(v_buckets_4208_);
v___x_4217_ = lean_unsigned_to_nat(0u);
v___x_4218_ = lean_nat_dec_lt(v___x_4217_, v___x_4216_);
if (v___x_4218_ == 0)
{
v___y_4211_ = v___x_4215_;
goto v___jp_4210_;
}
else
{
size_t v___x_4219_; size_t v___x_4220_; lean_object* v___x_4221_; 
v___x_4219_ = lean_usize_of_nat(v___x_4216_);
v___x_4220_ = ((size_t)0ULL);
v___x_4221_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4(v_buckets_4208_, v___x_4219_, v___x_4220_, v___x_4215_);
v___y_4211_ = v___x_4221_;
goto v___jp_4210_;
}
v___jp_4210_:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4212_ = lean_box(0);
v___x_4213_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v___y_4211_, v___x_4212_);
v___x_4214_ = l_String_intercalate(v___x_4209_, v___x_4213_);
v___y_4193_ = v___x_4214_;
goto v___jp_4192_;
}
}
else
{
lean_object* v___x_4222_; 
v___x_4222_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_4193_ = v___x_4222_;
goto v___jp_4192_;
}
}
v___jp_4192_:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4194_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4194_, 0, v___y_4193_);
v___x_4195_ = l_Lean_MessageData_ofFormat(v___x_4194_);
v___x_4196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4191_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___x_4197_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(v_cls_4185_, v___x_4196_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_dec_ref(v___x_4197_);
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
v___y_4177_ = v_a_4166_;
v___y_4178_ = v_a_4167_;
v___y_4179_ = v_a_4168_;
goto v___jp_4170_;
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
lean_dec(v_a_4166_);
lean_dec_ref(v_a_4165_);
lean_dec_ref(v_p_4159_);
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4197_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4197_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
lean_dec(v_a_4166_);
lean_dec_ref(v_a_4165_);
lean_dec_ref(v_p_4159_);
v_a_4223_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4186_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4186_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
v___jp_4170_:
{
uint8_t v_possible_4180_; 
v_possible_4180_ = lean_ctor_get_uint8(v_p_4159_, sizeof(void*)*7);
if (v_possible_4180_ == 0)
{
lean_object* v___x_4181_; 
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
v___x_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4181_, 0, v_p_4159_);
return v___x_4181_;
}
else
{
lean_object* v___x_4182_; 
lean_inc(v___y_4179_);
lean_inc_ref(v___y_4178_);
lean_inc(v___y_4177_);
lean_inc_ref(v___y_4176_);
v___x_4182_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_4159_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v___x_4184_; 
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
lean_inc(v_a_4183_);
lean_dec_ref(v___x_4182_);
v___x_4184_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_a_4183_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
return v___x_4184_;
}
else
{
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
return v___x_4182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination(lean_object* v_p_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, uint8_t v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_){
_start:
{
lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; uint8_t v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; uint8_t v_possible_4255_; 
v_possible_4255_ = lean_ctor_get_uint8(v_p_4231_, sizeof(void*)*7);
if (v_possible_4255_ == 0)
{
lean_object* v___x_4256_; 
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
v___x_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4256_, 0, v_p_4231_);
return v___x_4256_;
}
else
{
lean_object* v_constraints_4257_; uint8_t v___x_4258_; 
v_constraints_4257_ = lean_ctor_get(v_p_4231_, 2);
v___x_4258_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_4231_);
if (v___x_4258_ == 0)
{
lean_object* v_cls_4259_; lean_object* v___x_4260_; 
v_cls_4259_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4260_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4259_, v_a_4239_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v_a_4261_; uint8_t v___x_4262_; 
v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
lean_inc(v_a_4261_);
lean_dec_ref(v___x_4260_);
v___x_4262_ = lean_unbox(v_a_4261_);
lean_dec(v_a_4261_);
if (v___x_4262_ == 0)
{
v___y_4243_ = v_a_4232_;
v___y_4244_ = v_a_4233_;
v___y_4245_ = v_a_4234_;
v___y_4246_ = v_a_4235_;
v___y_4247_ = v_a_4236_;
v___y_4248_ = v_a_4237_;
v___y_4249_ = v_a_4238_;
v___y_4250_ = v_a_4239_;
v___y_4251_ = v_a_4240_;
goto v___jp_4242_;
}
else
{
lean_object* v___x_4263_; lean_object* v___y_4265_; 
v___x_4263_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1);
if (v___x_4258_ == 0)
{
lean_object* v_buckets_4278_; lean_object* v___x_4279_; lean_object* v___y_4281_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; uint8_t v___x_4288_; 
v_buckets_4278_ = lean_ctor_get(v_constraints_4257_, 1);
v___x_4279_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_4285_ = lean_box(0);
v___x_4286_ = lean_array_get_size(v_buckets_4278_);
v___x_4287_ = lean_unsigned_to_nat(0u);
v___x_4288_ = lean_nat_dec_lt(v___x_4287_, v___x_4286_);
if (v___x_4288_ == 0)
{
v___y_4281_ = v___x_4285_;
goto v___jp_4280_;
}
else
{
size_t v___x_4289_; size_t v___x_4290_; lean_object* v___x_4291_; 
v___x_4289_ = lean_usize_of_nat(v___x_4286_);
v___x_4290_ = ((size_t)0ULL);
v___x_4291_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4(v_buckets_4278_, v___x_4289_, v___x_4290_, v___x_4285_);
v___y_4281_ = v___x_4291_;
goto v___jp_4280_;
}
v___jp_4280_:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4282_ = lean_box(0);
v___x_4283_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v___y_4281_, v___x_4282_);
v___x_4284_ = l_String_intercalate(v___x_4279_, v___x_4283_);
v___y_4265_ = v___x_4284_;
goto v___jp_4264_;
}
}
else
{
lean_object* v___x_4292_; 
v___x_4292_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_4265_ = v___x_4292_;
goto v___jp_4264_;
}
v___jp_4264_:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4266_, 0, v___y_4265_);
v___x_4267_ = l_Lean_MessageData_ofFormat(v___x_4266_);
v___x_4268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4263_);
lean_ctor_set(v___x_4268_, 1, v___x_4267_);
v___x_4269_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(v_cls_4259_, v___x_4268_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_dec_ref(v___x_4269_);
v___y_4243_ = v_a_4232_;
v___y_4244_ = v_a_4233_;
v___y_4245_ = v_a_4234_;
v___y_4246_ = v_a_4235_;
v___y_4247_ = v_a_4236_;
v___y_4248_ = v_a_4237_;
v___y_4249_ = v_a_4238_;
v___y_4250_ = v_a_4239_;
v___y_4251_ = v_a_4240_;
goto v___jp_4242_;
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
lean_dec_ref(v_p_4231_);
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4269_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4269_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
lean_dec_ref(v_p_4231_);
v_a_4293_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4260_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4260_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
else
{
lean_object* v___x_4301_; 
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
v___x_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4301_, 0, v_p_4231_);
return v___x_4301_;
}
}
v___jp_4242_:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_4231_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4254_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_a_4253_);
lean_dec_ref(v___x_4252_);
v___x_4254_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_a_4253_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
return v___x_4254_;
}
else
{
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
return v___x_4252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___boxed(lean_object* v_p_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_){
_start:
{
uint8_t v_a_14804__boxed_4313_; lean_object* v_res_4314_; 
v_a_14804__boxed_4313_ = lean_unbox(v_a_4306_);
v_res_4314_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_p_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_14804__boxed_4313_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_);
lean_dec(v_a_4307_);
lean_dec_ref(v_a_4305_);
lean_dec(v_a_4304_);
lean_dec(v_a_4303_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___boxed(lean_object* v_p_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_){
_start:
{
uint8_t v_a_14863__boxed_4326_; lean_object* v_res_4327_; 
v_a_14863__boxed_4326_ = lean_unbox(v_a_4319_);
v_res_4327_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_p_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_14863__boxed_4326_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4318_);
lean_dec(v_a_4317_);
lean_dec(v_a_4316_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object* v_cls_4328_, lean_object* v_msg_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, uint8_t v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v___x_4340_; 
v___x_4340_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(v_cls_4328_, v_msg_4329_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___boxed(lean_object* v_cls_4341_, lean_object* v_msg_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
uint8_t v___y_15105__boxed_4353_; lean_object* v_res_4354_; 
v___y_15105__boxed_4353_ = lean_unbox(v___y_4346_);
v_res_4354_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v_cls_4341_, v_msg_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_15105__boxed_4353_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec(v___y_4343_);
return v_res_4354_;
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
