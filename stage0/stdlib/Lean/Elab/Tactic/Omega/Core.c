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
lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Omega_instBEqConstraint_beq(lean_object*, lean_object*);
lean_object* l_Lean_Omega_Constraint_exact(lean_object*);
lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Omega_Constraint_combine(lean_object*, lean_object*);
uint8_t l_Lean_Omega_instDecidableEqConstraint_decEq(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_instToExprInt;
lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__0_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__0_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__0_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__0_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 155, 144, 136, 132, 122, 189, 157)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__3_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__2_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__3_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__3_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__5_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__3_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__5_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__5_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__7_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__5_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__7_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__7_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__9_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__7_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__9_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__9_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Omega"};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__11_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__9_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 2, 97, 20, 0, 190, 151, 121)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__11_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__11_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__12_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Core"};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__12_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__12_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__13_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__11_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__12_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 127, 112, 137, 173, 73, 6, 123)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__13_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__13_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__14_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__13_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(163, 175, 232, 83, 151, 83, 109, 118)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__14_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__14_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__15_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__14_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(238, 106, 137, 58, 220, 39, 120, 132)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__15_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__15_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__16_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__15_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 56, 156, 139, 49, 21, 86, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__16_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__16_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__17_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__16_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(121, 168, 28, 9, 214, 33, 222, 145)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__17_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__17_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__18_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__17_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 182, 253, 204, 178, 225, 195, 63)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__18_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__18_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__19_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__19_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__19_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__20_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__18_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__19_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 195, 243, 156, 202, 148, 124, 21)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__20_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__20_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__21_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__21_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__21_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__22_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__20_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__21_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(42, 37, 81, 161, 75, 125, 164, 210)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__22_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__22_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__23_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__22_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(171, 132, 243, 134, 151, 208, 115, 86)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__23_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__23_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__24_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__23_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__6_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(189, 16, 5, 112, 31, 217, 215, 56)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__24_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__24_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__25_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__24_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(228, 198, 87, 252, 181, 197, 254, 4)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__25_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__25_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__26_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__25_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 202, 173, 43, 15, 49, 145, 122)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__26_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__26_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__27_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__26_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__12_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 223, 148, 224, 253, 48, 85, 158)}};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__27_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__27_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__28_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__28_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__29_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__29_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__29_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__30_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__30_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__31_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__31_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__31_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__32_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__32_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__33_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__33_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "LinearCombo"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 132, 214, 18, 187, 72, 22, 121)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo;
static const lean_string_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Constraint"};
static const lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
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
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 7, .m_data = "(-∞, ∞)"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "(-∞, "};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = ", ∞)"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∅"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ": tidying up:\n"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ": combination of:\n"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " * x + "};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " * y combo of:\n"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ": bmod with m="};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " and i="};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_toString___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " of:\n"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_toString___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_instToString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tidy_sat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 191, 70, 188, 16, 136, 82, 137)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "combine_sat'"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 192, 152, 239, 193, 179, 196, 197)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 94, 145, 248, 63, 179, 150, 35)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "combo_sat'"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__10_value),LEAN_SCALAR_PTR_LITERAL(200, 12, 56, 206, 160, 32, 217, 148)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11_value),LEAN_SCALAR_PTR_LITERAL(170, 70, 58, 212, 39, 249, 136, 90)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "get"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__10_value),LEAN_SCALAR_PTR_LITERAL(200, 12, 56, 206, 160, 32, 217, 148)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__14_value),LEAN_SCALAR_PTR_LITERAL(90, 92, 99, 234, 53, 138, 153, 24)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "bmod_div_term"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__17_value),LEAN_SCALAR_PTR_LITERAL(146, 160, 30, 167, 226, 78, 110, 197)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bmod_sat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2_value;
static const lean_array_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__8_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_repr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__1_value)} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__0_value)} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "isImpossible"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 192, 152, 239, 193, 179, 196, 197)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 20, 9, 160, 52, 15, 198, 221)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "addEquality_sat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
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
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__1_value)} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_instToString___closed__1_value)} };
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Selected variable "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__1_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__4 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1;
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "Selecting variable to eliminate from (idx, size, exact) triples:\n"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__28_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_unsigned_to_nat(3193685152u);
v___x_67_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__27_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_68_ = l_Lean_Name_num___override(v___x_67_, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__30_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__29_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_71_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__28_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__28_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__28_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_);
v___x_72_ = l_Lean_Name_str___override(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__32_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__31_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_75_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__30_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__30_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__30_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_);
v___x_76_ = l_Lean_Name_str___override(v___x_75_, v___x_74_);
return v___x_76_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__33_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_unsigned_to_nat(2u);
v___x_78_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__32_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__32_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__32_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_);
v___x_79_ = l_Lean_Name_num___override(v___x_78_, v___x_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_81_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_82_ = 0;
v___x_83_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__33_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__33_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__33_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_);
v___x_84_ = l_Lean_registerTraceClass(v___x_81_, v___x_82_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2____boxed(lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_();
return v_res_86_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_box(0);
v___x_95_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2));
v___x_96_ = l_Lean_Expr_const___override(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v_type_102_; 
v___x_100_ = lean_box(0);
v___x_101_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__5));
v_type_102_ = l_Lean_Expr_const___override(v___x_101_, v___x_100_);
return v_type_102_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_112_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__9));
v___x_113_ = l_Lean_mkConst(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12(void){
_start:
{
lean_object* v_type_114_; lean_object* v___x_115_; lean_object* v_nil_116_; 
v_type_114_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_115_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11);
v_nil_116_ = l_Lean_Expr_app___override(v___x_115_, v_type_114_);
return v_nil_116_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_122_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__14));
v___x_123_ = l_Lean_mkConst(v___x_122_, v___x_121_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16(void){
_start:
{
lean_object* v_type_124_; lean_object* v___x_125_; lean_object* v_cons_126_; 
v_type_124_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_125_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15);
v_cons_126_ = l_Lean_Expr_app___override(v___x_125_, v_type_124_);
return v_cons_126_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_nat_to_int(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = l_Lean_Level_ofNat(v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_box(0);
v___x_137_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21);
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22);
v___x_140_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__20));
v___x_141_ = l_Lean_Expr_const___override(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = lean_box(0);
v___x_147_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__25));
v___x_148_ = l_Lean_Expr_const___override(v___x_147_, v___x_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0(lean_object* v___x_149_, lean_object* v_lc_150_){
_start:
{
lean_object* v_const_151_; lean_object* v_coeffs_152_; lean_object* v___x_153_; lean_object* v___y_155_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_const_151_ = lean_ctor_get(v_lc_150_, 0);
lean_inc(v_const_151_);
v_coeffs_152_ = lean_ctor_get(v_lc_150_, 1);
lean_inc(v_coeffs_152_);
lean_dec_ref(v_lc_150_);
v___x_153_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3);
v___x_161_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_162_ = lean_int_dec_le(v___x_161_, v_const_151_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_163_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_164_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_165_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_166_ = lean_int_neg(v_const_151_);
lean_dec(v_const_151_);
v___x_167_ = l_Int_toNat(v___x_166_);
lean_dec(v___x_166_);
v___x_168_ = l_Lean_instToExprInt_mkNat(v___x_167_);
v___x_169_ = l_Lean_mkApp3(v___x_163_, v___x_164_, v___x_165_, v___x_168_);
v___y_155_ = v___x_169_;
goto v___jp_154_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = l_Int_toNat(v_const_151_);
lean_dec(v_const_151_);
v___x_171_ = l_Lean_instToExprInt_mkNat(v___x_170_);
v___y_155_ = v___x_171_;
goto v___jp_154_;
}
v___jp_154_:
{
lean_object* v_nil_156_; lean_object* v___x_157_; lean_object* v_cons_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_nil_156_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v___x_157_ = l_Lean_Expr_app___override(v___x_153_, v___y_155_);
v_cons_158_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_159_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_149_, v_nil_156_, v_cons_158_, v_coeffs_152_);
v___x_160_ = l_Lean_Expr_app___override(v___x_157_, v___x_159_);
return v___x_160_;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0(void){
_start:
{
lean_object* v___x_172_; lean_object* v___f_173_; 
v___x_172_ = l_Lean_instToExprInt;
v___f_173_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0), 2, 1);
lean_closure_set(v___f_173_, 0, v___x_172_);
return v___f_173_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_box(0);
v___x_179_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1));
v___x_180_ = l_Lean_Expr_const___override(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3(void){
_start:
{
lean_object* v___x_181_; lean_object* v___f_182_; lean_object* v___x_183_; 
v___x_181_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2);
v___f_182_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___f_182_);
lean_ctor_set(v___x_183_, 1, v___x_181_);
return v___x_183_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo(void){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_box(0);
v___x_192_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1));
v___x_193_ = l_Lean_Expr_const___override(v___x_192_, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_200_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__5));
v___x_201_ = l_Lean_mkConst(v___x_200_, v___x_199_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7(void){
_start:
{
lean_object* v_type_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_type_202_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_203_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_204_ = l_Lean_Expr_app___override(v___x_203_, v_type_202_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_210_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__9));
v___x_211_ = l_Lean_mkConst(v___x_210_, v___x_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0(lean_object* v_s_212_){
_start:
{
lean_object* v_lowerBound_213_; lean_object* v_upperBound_214_; lean_object* v___x_215_; lean_object* v_type_216_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_224_; 
v_lowerBound_213_ = lean_ctor_get(v_s_212_, 0);
v_upperBound_214_ = lean_ctor_get(v_s_212_, 1);
v___x_215_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_216_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_213_) == 0)
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_224_ = v___x_240_;
goto v___jp_223_;
}
else
{
lean_object* v_val_241_; lean_object* v___x_242_; lean_object* v___y_244_; lean_object* v___x_246_; uint8_t v___x_247_; 
v_val_241_ = lean_ctor_get(v_lowerBound_213_, 0);
v___x_242_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_246_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_247_ = lean_int_dec_le(v___x_246_, v_val_241_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_248_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_249_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_250_ = lean_int_neg(v_val_241_);
v___x_251_ = l_Int_toNat(v___x_250_);
lean_dec(v___x_250_);
v___x_252_ = l_Lean_instToExprInt_mkNat(v___x_251_);
v___x_253_ = l_Lean_mkApp3(v___x_248_, v_type_216_, v___x_249_, v___x_252_);
v___y_244_ = v___x_253_;
goto v___jp_243_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = l_Int_toNat(v_val_241_);
v___x_255_ = l_Lean_instToExprInt_mkNat(v___x_254_);
v___y_244_ = v___x_255_;
goto v___jp_243_;
}
v___jp_243_:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_mkAppB(v___x_242_, v_type_216_, v___y_244_);
v___y_224_ = v___x_245_;
goto v___jp_223_;
}
}
v___jp_217_:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_inc_ref(v___y_218_);
v___x_221_ = l_Lean_mkAppB(v___y_218_, v_type_216_, v___y_220_);
v___x_222_ = l_Lean_Expr_app___override(v___y_219_, v___x_221_);
return v___x_222_;
}
v___jp_223_:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Expr_app___override(v___x_215_, v___y_224_);
if (lean_obj_tag(v_upperBound_214_) == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_227_ = l_Lean_Expr_app___override(v___x_225_, v___x_226_);
return v___x_227_;
}
else
{
lean_object* v_val_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_val_228_ = lean_ctor_get(v_upperBound_214_, 0);
v___x_229_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_230_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_231_ = lean_int_dec_le(v___x_230_, v_val_228_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_232_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_233_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_234_ = lean_int_neg(v_val_228_);
v___x_235_ = l_Int_toNat(v___x_234_);
lean_dec(v___x_234_);
v___x_236_ = l_Lean_instToExprInt_mkNat(v___x_235_);
v___x_237_ = l_Lean_mkApp3(v___x_232_, v_type_216_, v___x_233_, v___x_236_);
v___y_218_ = v___x_229_;
v___y_219_ = v___x_225_;
v___y_220_ = v___x_237_;
goto v___jp_217_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = l_Int_toNat(v_val_228_);
v___x_239_ = l_Lean_instToExprInt_mkNat(v___x_238_);
v___y_218_ = v___x_229_;
v___y_219_ = v___x_225_;
v___y_220_ = v___x_239_;
goto v___jp_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___boxed(lean_object* v_s_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0(v_s_256_);
lean_dec_ref(v_s_256_);
return v_res_257_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_box(0);
v___x_264_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__1));
v___x_265_ = l_Lean_Expr_const___override(v___x_264_, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3(void){
_start:
{
lean_object* v___x_266_; lean_object* v___f_267_; lean_object* v___x_268_; 
v___x_266_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2);
v___f_267_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__0));
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___f_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint(void){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___redArg(lean_object* v_x_270_){
_start:
{
switch(lean_obj_tag(v_x_270_))
{
case 0:
{
lean_object* v___x_271_; 
v___x_271_ = lean_unsigned_to_nat(0u);
return v___x_271_;
}
case 1:
{
lean_object* v___x_272_; 
v___x_272_ = lean_unsigned_to_nat(1u);
return v___x_272_;
}
case 2:
{
lean_object* v___x_273_; 
v___x_273_ = lean_unsigned_to_nat(2u);
return v___x_273_;
}
case 3:
{
lean_object* v___x_274_; 
v___x_274_ = lean_unsigned_to_nat(3u);
return v___x_274_;
}
default: 
{
lean_object* v___x_275_; 
v___x_275_ = lean_unsigned_to_nat(4u);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___redArg___boxed(lean_object* v_x_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___redArg(v_x_276_);
lean_dec_ref(v_x_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx(lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_x_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___redArg(v_x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___boxed(lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_x_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Elab_Tactic_Omega_Justification_ctorIdx(v_a_282_, v_a_283_, v_x_284_);
lean_dec_ref(v_x_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(lean_object* v_t_286_, lean_object* v_k_287_){
_start:
{
switch(lean_obj_tag(v_t_286_))
{
case 0:
{
lean_object* v_s_288_; lean_object* v_x_289_; lean_object* v_i_290_; lean_object* v___x_291_; 
v_s_288_ = lean_ctor_get(v_t_286_, 0);
lean_inc_ref(v_s_288_);
v_x_289_ = lean_ctor_get(v_t_286_, 1);
lean_inc(v_x_289_);
v_i_290_ = lean_ctor_get(v_t_286_, 2);
lean_inc(v_i_290_);
lean_dec_ref_known(v_t_286_, 3);
v___x_291_ = lean_apply_3(v_k_287_, v_s_288_, v_x_289_, v_i_290_);
return v___x_291_;
}
case 1:
{
lean_object* v_s_292_; lean_object* v_c_293_; lean_object* v_j_294_; lean_object* v___x_295_; 
v_s_292_ = lean_ctor_get(v_t_286_, 0);
lean_inc_ref(v_s_292_);
v_c_293_ = lean_ctor_get(v_t_286_, 1);
lean_inc(v_c_293_);
v_j_294_ = lean_ctor_get(v_t_286_, 2);
lean_inc_ref(v_j_294_);
lean_dec_ref_known(v_t_286_, 3);
v___x_295_ = lean_apply_3(v_k_287_, v_s_292_, v_c_293_, v_j_294_);
return v___x_295_;
}
case 2:
{
lean_object* v_s_296_; lean_object* v_t_297_; lean_object* v_c_298_; lean_object* v_j_299_; lean_object* v_k_300_; lean_object* v___x_301_; 
v_s_296_ = lean_ctor_get(v_t_286_, 0);
lean_inc_ref(v_s_296_);
v_t_297_ = lean_ctor_get(v_t_286_, 1);
lean_inc_ref(v_t_297_);
v_c_298_ = lean_ctor_get(v_t_286_, 2);
lean_inc(v_c_298_);
v_j_299_ = lean_ctor_get(v_t_286_, 3);
lean_inc_ref(v_j_299_);
v_k_300_ = lean_ctor_get(v_t_286_, 4);
lean_inc_ref(v_k_300_);
lean_dec_ref_known(v_t_286_, 5);
v___x_301_ = lean_apply_5(v_k_287_, v_s_296_, v_t_297_, v_c_298_, v_j_299_, v_k_300_);
return v___x_301_;
}
case 3:
{
lean_object* v_s_302_; lean_object* v_t_303_; lean_object* v_x_304_; lean_object* v_y_305_; lean_object* v_a_306_; lean_object* v_j_307_; lean_object* v_b_308_; lean_object* v_k_309_; lean_object* v___x_310_; 
v_s_302_ = lean_ctor_get(v_t_286_, 0);
lean_inc_ref(v_s_302_);
v_t_303_ = lean_ctor_get(v_t_286_, 1);
lean_inc_ref(v_t_303_);
v_x_304_ = lean_ctor_get(v_t_286_, 2);
lean_inc(v_x_304_);
v_y_305_ = lean_ctor_get(v_t_286_, 3);
lean_inc(v_y_305_);
v_a_306_ = lean_ctor_get(v_t_286_, 4);
lean_inc(v_a_306_);
v_j_307_ = lean_ctor_get(v_t_286_, 5);
lean_inc_ref(v_j_307_);
v_b_308_ = lean_ctor_get(v_t_286_, 6);
lean_inc(v_b_308_);
v_k_309_ = lean_ctor_get(v_t_286_, 7);
lean_inc_ref(v_k_309_);
lean_dec_ref_known(v_t_286_, 8);
v___x_310_ = lean_apply_8(v_k_287_, v_s_302_, v_t_303_, v_x_304_, v_y_305_, v_a_306_, v_j_307_, v_b_308_, v_k_309_);
return v___x_310_;
}
default: 
{
lean_object* v_m_311_; lean_object* v_r_312_; lean_object* v_i_313_; lean_object* v_x_314_; lean_object* v_j_315_; lean_object* v___x_316_; 
v_m_311_ = lean_ctor_get(v_t_286_, 0);
lean_inc(v_m_311_);
v_r_312_ = lean_ctor_get(v_t_286_, 1);
lean_inc(v_r_312_);
v_i_313_ = lean_ctor_get(v_t_286_, 2);
lean_inc(v_i_313_);
v_x_314_ = lean_ctor_get(v_t_286_, 3);
lean_inc(v_x_314_);
v_j_315_ = lean_ctor_get(v_t_286_, 4);
lean_inc_ref(v_j_315_);
lean_dec_ref_known(v_t_286_, 5);
v___x_316_ = lean_apply_5(v_k_287_, v_m_311_, v_r_312_, v_i_313_, v_x_314_, v_j_315_);
return v___x_316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim(lean_object* v_motive_317_, lean_object* v_ctorIdx_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_t_321_, lean_object* v_h_322_, lean_object* v_k_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_321_, v_k_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim___boxed(lean_object* v_motive_325_, lean_object* v_ctorIdx_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_t_329_, lean_object* v_h_330_, lean_object* v_k_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim(v_motive_325_, v_ctorIdx_326_, v_a_327_, v_a_328_, v_t_329_, v_h_330_, v_k_331_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_ctorIdx_326_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim___redArg(lean_object* v_t_333_, lean_object* v_assumption_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_333_, v_assumption_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim(lean_object* v_motive_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_t_339_, lean_object* v_h_340_, lean_object* v_assumption_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_339_, v_assumption_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim___boxed(lean_object* v_motive_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_t_346_, lean_object* v_h_347_, lean_object* v_assumption_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Elab_Tactic_Omega_Justification_assumption_elim(v_motive_343_, v_a_344_, v_a_345_, v_t_346_, v_h_347_, v_assumption_348_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim___redArg(lean_object* v_t_350_, lean_object* v_tidy_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_350_, v_tidy_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim(lean_object* v_motive_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_t_356_, lean_object* v_h_357_, lean_object* v_tidy_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_356_, v_tidy_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim___boxed(lean_object* v_motive_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_t_363_, lean_object* v_h_364_, lean_object* v_tidy_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_elim(v_motive_360_, v_a_361_, v_a_362_, v_t_363_, v_h_364_, v_tidy_365_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim___redArg(lean_object* v_t_367_, lean_object* v_combine_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_367_, v_combine_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim(lean_object* v_motive_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_t_373_, lean_object* v_h_374_, lean_object* v_combine_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_373_, v_combine_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim___boxed(lean_object* v_motive_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_t_380_, lean_object* v_h_381_, lean_object* v_combine_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Elab_Tactic_Omega_Justification_combine_elim(v_motive_377_, v_a_378_, v_a_379_, v_t_380_, v_h_381_, v_combine_382_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim___redArg(lean_object* v_t_384_, lean_object* v_combo_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_384_, v_combo_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim(lean_object* v_motive_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_t_390_, lean_object* v_h_391_, lean_object* v_combo_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_390_, v_combo_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim___boxed(lean_object* v_motive_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_t_397_, lean_object* v_h_398_, lean_object* v_combo_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Elab_Tactic_Omega_Justification_combo_elim(v_motive_394_, v_a_395_, v_a_396_, v_t_397_, v_h_398_, v_combo_399_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim___redArg(lean_object* v_t_401_, lean_object* v_bmod_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_401_, v_bmod_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim(lean_object* v_motive_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_t_407_, lean_object* v_h_408_, lean_object* v_bmod_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_407_, v_bmod_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim___boxed(lean_object* v_motive_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_t_414_, lean_object* v_h_415_, lean_object* v_bmod_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Elab_Tactic_Omega_Justification_bmod_elim(v_motive_411_, v_a_412_, v_a_413_, v_t_414_, v_h_415_, v_bmod_416_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(lean_object* v_s_418_, lean_object* v_c_419_, lean_object* v_j_420_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_inc(v_c_419_);
lean_inc_ref(v_s_418_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_s_418_);
lean_ctor_set(v___x_421_, 1, v_c_419_);
lean_inc_ref(v___x_421_);
v___x_422_ = l_Lean_Omega_tidy_x3f(v___x_421_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v___x_423_; 
lean_dec_ref_known(v___x_421_, 2);
lean_dec_ref(v_j_420_);
lean_dec(v_c_419_);
lean_dec_ref(v_s_418_);
v___x_423_ = lean_box(0);
return v___x_423_;
}
else
{
lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_442_; 
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; 
v_unused_443_ = lean_ctor_get(v___x_422_, 0);
lean_dec(v_unused_443_);
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_442_;
goto v_resetjp_424_;
}
else
{
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_442_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v_fst_428_; lean_object* v_snd_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_441_; 
v___x_427_ = l_Lean_Omega_tidy(v___x_421_);
v_fst_428_ = lean_ctor_get(v___x_427_, 0);
v_snd_429_ = lean_ctor_get(v___x_427_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_441_ == 0)
{
v___x_431_ = v___x_427_;
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_snd_429_);
lean_inc(v_fst_428_);
lean_dec(v___x_427_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_433_, 0, v_s_418_);
lean_ctor_set(v___x_433_, 1, v_c_419_);
lean_ctor_set(v___x_433_, 2, v_j_420_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v___x_433_);
lean_ctor_set(v___x_431_, 0, v_snd_429_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_snd_429_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v___x_433_);
v___x_435_ = v_reuseFailAlloc_440_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v_fst_428_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_436_);
v___x_438_ = v___x_425_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(lean_object* v_s_444_, lean_object* v_replacement_445_, lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
lean_object* v_it_449_; lean_object* v_startPos_450_; lean_object* v_endPos_451_; lean_object* v_it_460_; 
switch(lean_obj_tag(v_a_446_))
{
case 0:
{
lean_object* v_pos_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_478_; 
v_pos_466_ = lean_ctor_get(v_a_446_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v_a_446_);
if (v_isSharedCheck_478_ == 0)
{
v___x_468_ = v_a_446_;
v_isShared_469_ = v_isSharedCheck_478_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_pos_466_);
lean_dec(v_a_446_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_478_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v_startInclusive_470_; lean_object* v_endExclusive_471_; lean_object* v___x_472_; uint8_t v_decide_473_; 
v_startInclusive_470_ = lean_ctor_get(v_s_444_, 1);
v_endExclusive_471_ = lean_ctor_get(v_s_444_, 2);
v___x_472_ = lean_nat_sub(v_endExclusive_471_, v_startInclusive_470_);
v_decide_473_ = lean_nat_dec_eq(v_pos_466_, v___x_472_);
lean_dec(v___x_472_);
if (v_decide_473_ == 0)
{
lean_object* v___x_475_; 
if (v_isShared_469_ == 0)
{
lean_ctor_set_tag(v___x_468_, 1);
v___x_475_ = v___x_468_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_pos_466_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
v_it_460_ = v___x_475_;
goto v___jp_459_;
}
}
else
{
lean_object* v___x_477_; 
lean_del_object(v___x_468_);
lean_dec(v_pos_466_);
v___x_477_ = lean_box(3);
v_it_460_ = v___x_477_;
goto v___jp_459_;
}
}
}
case 1:
{
lean_object* v_pos_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_491_; 
v_pos_479_ = lean_ctor_get(v_a_446_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v_a_446_);
if (v_isSharedCheck_491_ == 0)
{
v___x_481_ = v_a_446_;
v_isShared_482_ = v_isSharedCheck_491_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_pos_479_);
lean_dec(v_a_446_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_491_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v_str_483_; lean_object* v_startInclusive_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v_str_483_ = lean_ctor_get(v_s_444_, 0);
v_startInclusive_484_ = lean_ctor_get(v_s_444_, 1);
v___x_485_ = lean_nat_add(v_startInclusive_484_, v_pos_479_);
v___x_486_ = lean_string_utf8_next_fast(v_str_483_, v___x_485_);
lean_dec(v___x_485_);
v___x_487_ = lean_nat_sub(v___x_486_, v_startInclusive_484_);
lean_inc(v___x_487_);
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 0);
lean_ctor_set(v___x_481_, 0, v___x_487_);
v___x_489_ = v___x_481_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
v_it_449_ = v___x_489_;
v_startPos_450_ = v_pos_479_;
v_endPos_451_ = v___x_487_;
goto v___jp_448_;
}
}
}
case 2:
{
lean_object* v_needle_492_; lean_object* v_table_493_; lean_object* v_stackPos_494_; lean_object* v_needlePos_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_556_; 
v_needle_492_ = lean_ctor_get(v_a_446_, 0);
v_table_493_ = lean_ctor_get(v_a_446_, 1);
v_stackPos_494_ = lean_ctor_get(v_a_446_, 2);
v_needlePos_495_ = lean_ctor_get(v_a_446_, 3);
v_isSharedCheck_556_ = !lean_is_exclusive(v_a_446_);
if (v_isSharedCheck_556_ == 0)
{
v___x_497_ = v_a_446_;
v_isShared_498_ = v_isSharedCheck_556_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_needlePos_495_);
lean_inc(v_stackPos_494_);
lean_inc(v_table_493_);
lean_inc(v_needle_492_);
lean_dec(v_a_446_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_556_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_str_499_; lean_object* v_startInclusive_500_; lean_object* v_endExclusive_501_; lean_object* v_str_502_; lean_object* v_startInclusive_503_; lean_object* v_endExclusive_504_; lean_object* v_basePos_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v_str_499_ = lean_ctor_get(v_needle_492_, 0);
v_startInclusive_500_ = lean_ctor_get(v_needle_492_, 1);
v_endExclusive_501_ = lean_ctor_get(v_needle_492_, 2);
v_str_502_ = lean_ctor_get(v_s_444_, 0);
v_startInclusive_503_ = lean_ctor_get(v_s_444_, 1);
v_endExclusive_504_ = lean_ctor_get(v_s_444_, 2);
v_basePos_505_ = lean_nat_sub(v_stackPos_494_, v_needlePos_495_);
v___x_506_ = lean_nat_sub(v_endExclusive_501_, v_startInclusive_500_);
v___x_507_ = lean_nat_add(v_basePos_505_, v___x_506_);
v___x_508_ = lean_nat_sub(v_endExclusive_504_, v_startInclusive_503_);
v___x_509_ = lean_nat_dec_le(v___x_507_, v___x_508_);
lean_dec(v___x_507_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
lean_dec(v___x_506_);
lean_del_object(v___x_497_);
lean_dec(v_needlePos_495_);
lean_dec(v_stackPos_494_);
lean_dec_ref(v_table_493_);
lean_dec_ref(v_needle_492_);
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_nat_add(v_basePos_505_, v___x_510_);
v___x_512_ = lean_nat_dec_le(v___x_511_, v___x_508_);
lean_dec(v___x_511_);
if (v___x_512_ == 0)
{
lean_dec(v___x_508_);
lean_dec(v_basePos_505_);
lean_dec_ref(v_s_444_);
return v_b_447_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = l_String_Slice_pos_x21(v_s_444_, v_basePos_505_);
lean_dec(v_basePos_505_);
v___x_514_ = lean_box(3);
v_it_449_ = v___x_514_;
v_startPos_450_ = v___x_513_;
v_endPos_451_ = v___x_508_;
goto v___jp_448_;
}
}
else
{
lean_object* v___x_515_; uint8_t v_stackByte_516_; lean_object* v___x_517_; uint8_t v_patByte_518_; uint8_t v___x_519_; 
lean_dec(v___x_508_);
v___x_515_ = lean_nat_add(v_startInclusive_503_, v_stackPos_494_);
v_stackByte_516_ = lean_string_get_byte_fast(v_str_502_, v___x_515_);
v___x_517_ = lean_nat_add(v_startInclusive_500_, v_needlePos_495_);
v_patByte_518_ = lean_string_get_byte_fast(v_str_499_, v___x_517_);
v___x_519_ = lean_uint8_dec_eq(v_stackByte_516_, v_patByte_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; uint8_t v_decide_521_; 
lean_dec(v___x_506_);
v___x_520_ = lean_unsigned_to_nat(0u);
v_decide_521_ = lean_nat_dec_eq(v_needlePos_495_, v___x_520_);
if (v_decide_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v_newNeedlePos_524_; uint8_t v___x_525_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_sub(v_needlePos_495_, v___x_522_);
lean_dec(v_needlePos_495_);
v_newNeedlePos_524_ = lean_array_fget_borrowed(v_table_493_, v___x_523_);
lean_dec(v___x_523_);
v___x_525_ = lean_nat_dec_eq(v_newNeedlePos_524_, v___x_520_);
if (v___x_525_ == 0)
{
lean_object* v_oldBasePos_526_; lean_object* v___x_527_; lean_object* v_newBasePos_528_; lean_object* v___x_530_; 
lean_inc(v_newNeedlePos_524_);
v_oldBasePos_526_ = l_String_Slice_pos_x21(v_s_444_, v_basePos_505_);
lean_dec(v_basePos_505_);
v___x_527_ = lean_nat_sub(v_stackPos_494_, v_newNeedlePos_524_);
v_newBasePos_528_ = l_String_Slice_pos_x21(v_s_444_, v___x_527_);
lean_dec(v___x_527_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 3, v_newNeedlePos_524_);
v___x_530_ = v___x_497_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_needle_492_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_table_493_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_stackPos_494_);
lean_ctor_set(v_reuseFailAlloc_531_, 3, v_newNeedlePos_524_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
v_it_449_ = v___x_530_;
v_startPos_450_ = v_oldBasePos_526_;
v_endPos_451_ = v_newBasePos_528_;
goto v___jp_448_;
}
}
else
{
lean_object* v_basePos_532_; lean_object* v_nextStackPos_533_; lean_object* v___x_535_; 
v_basePos_532_ = l_String_Slice_pos_x21(v_s_444_, v_basePos_505_);
lean_dec(v_basePos_505_);
v_nextStackPos_533_ = l_String_Slice_posGE___redArg(v_s_444_, v_stackPos_494_);
lean_inc(v_nextStackPos_533_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 3, v___x_520_);
lean_ctor_set(v___x_497_, 2, v_nextStackPos_533_);
v___x_535_ = v___x_497_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_needle_492_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_table_493_);
lean_ctor_set(v_reuseFailAlloc_536_, 2, v_nextStackPos_533_);
lean_ctor_set(v_reuseFailAlloc_536_, 3, v___x_520_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
v_it_449_ = v___x_535_;
v_startPos_450_ = v_basePos_532_;
v_endPos_451_ = v_nextStackPos_533_;
goto v___jp_448_;
}
}
}
else
{
lean_object* v_basePos_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_nextStackPos_540_; lean_object* v___x_542_; 
lean_dec(v_basePos_505_);
lean_dec(v_needlePos_495_);
v_basePos_537_ = l_String_Slice_pos_x21(v_s_444_, v_stackPos_494_);
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_add(v_stackPos_494_, v___x_538_);
lean_dec(v_stackPos_494_);
v_nextStackPos_540_ = l_String_Slice_posGE___redArg(v_s_444_, v___x_539_);
lean_inc(v_nextStackPos_540_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 3, v___x_520_);
lean_ctor_set(v___x_497_, 2, v_nextStackPos_540_);
v___x_542_ = v___x_497_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_needle_492_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_table_493_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_nextStackPos_540_);
lean_ctor_set(v_reuseFailAlloc_543_, 3, v___x_520_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
v_it_449_ = v___x_542_;
v_startPos_450_ = v_basePos_537_;
v_endPos_451_ = v_nextStackPos_540_;
goto v___jp_448_;
}
}
}
else
{
lean_object* v___x_544_; lean_object* v_nextStackPos_545_; lean_object* v_nextNeedlePos_546_; uint8_t v_decide_547_; 
lean_dec(v_basePos_505_);
v___x_544_ = lean_unsigned_to_nat(1u);
v_nextStackPos_545_ = lean_nat_add(v_stackPos_494_, v___x_544_);
lean_dec(v_stackPos_494_);
v_nextNeedlePos_546_ = lean_nat_add(v_needlePos_495_, v___x_544_);
lean_dec(v_needlePos_495_);
v_decide_547_ = lean_nat_dec_eq(v_nextNeedlePos_546_, v___x_506_);
lean_dec(v___x_506_);
if (v_decide_547_ == 0)
{
lean_object* v___x_549_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 3, v_nextNeedlePos_546_);
lean_ctor_set(v___x_497_, 2, v_nextStackPos_545_);
v___x_549_ = v___x_497_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_needle_492_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_table_493_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_nextStackPos_545_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_nextNeedlePos_546_);
v___x_549_ = v_reuseFailAlloc_551_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
v_a_446_ = v___x_549_;
goto _start;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_554_; 
lean_dec(v_nextNeedlePos_546_);
v___x_552_ = lean_unsigned_to_nat(0u);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 3, v___x_552_);
lean_ctor_set(v___x_497_, 2, v_nextStackPos_545_);
v___x_554_ = v___x_497_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_needle_492_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_table_493_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_nextStackPos_545_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
v_it_460_ = v___x_554_;
goto v___jp_459_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_444_);
return v_b_447_;
}
}
v___jp_448_:
{
lean_object* v___x_452_; lean_object* v_str_453_; lean_object* v_startInclusive_454_; lean_object* v_endExclusive_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_inc_ref(v_s_444_);
v___x_452_ = l_String_Slice_slice_x21(v_s_444_, v_startPos_450_, v_endPos_451_);
lean_dec(v_endPos_451_);
lean_dec(v_startPos_450_);
v_str_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc_ref(v_str_453_);
v_startInclusive_454_ = lean_ctor_get(v___x_452_, 1);
lean_inc(v_startInclusive_454_);
v_endExclusive_455_ = lean_ctor_get(v___x_452_, 2);
lean_inc(v_endExclusive_455_);
lean_dec_ref(v___x_452_);
v___x_456_ = lean_string_utf8_extract_fast(v_str_453_, v_startInclusive_454_, v_endExclusive_455_);
lean_dec(v_endExclusive_455_);
lean_dec(v_startInclusive_454_);
lean_dec_ref(v_str_453_);
v___x_457_ = lean_string_append(v_b_447_, v___x_456_);
lean_dec_ref(v___x_456_);
v_a_446_ = v_it_449_;
v_b_447_ = v___x_457_;
goto _start;
}
v___jp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_string_utf8_byte_size(v_replacement_445_);
v___x_463_ = lean_string_utf8_extract_fast(v_replacement_445_, v___x_461_, v___x_462_);
v___x_464_ = lean_string_append(v_b_447_, v___x_463_);
lean_dec_ref(v___x_463_);
v_a_446_ = v_it_460_;
v_b_447_ = v___x_464_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg___boxed(lean_object* v_s_557_, lean_object* v_replacement_558_, lean_object* v_a_559_, lean_object* v_b_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_557_, v_replacement_558_, v_a_559_, v_b_560_);
lean_dec_ref(v_replacement_558_);
return v_res_561_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_565_ = lean_string_utf8_byte_size(v___x_564_);
return v___x_565_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2);
v___x_568_ = lean_nat_dec_eq(v___x_567_, v___x_566_);
return v___x_568_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_569_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2);
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v___x_570_);
lean_ctor_set(v___x_572_, 2, v___x_569_);
return v___x_572_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4);
v___x_574_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5);
v___x_577_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4);
v___x_578_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_576_);
lean_ctor_set(v___x_578_, 2, v___x_575_);
lean_ctor_set(v___x_578_, 3, v___x_575_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(lean_object* v_s_581_, lean_object* v_replacement_582_){
_start:
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_584_ = lean_uint8_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6);
v___x_586_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_581_, v_replacement_582_, v___x_585_, v___x_583_);
return v___x_586_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__7));
v___x_588_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_581_, v_replacement_582_, v___x_587_, v___x_583_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___boxed(lean_object* v_s_589_, lean_object* v_replacement_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v_s_589_, v_replacement_590_);
lean_dec_ref(v_replacement_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(lean_object* v_s_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_595_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__0));
v___x_596_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__1));
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_string_utf8_byte_size(v_s_594_);
v___x_599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_599_, 0, v_s_594_);
lean_ctor_set(v___x_599_, 1, v___x_597_);
lean_ctor_set(v___x_599_, 2, v___x_598_);
v___x_600_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v___x_599_, v___x_596_);
v___x_601_ = lean_string_append(v___x_595_, v___x_600_);
lean_dec_ref(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0(lean_object* v_s_602_, lean_object* v_pattern_603_, lean_object* v_replacement_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v_s_602_, v_replacement_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___boxed(lean_object* v_s_606_, lean_object* v_pattern_607_, lean_object* v_replacement_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0(v_s_606_, v_pattern_607_, v_replacement_608_);
lean_dec_ref(v_replacement_608_);
lean_dec_ref(v_pattern_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0(lean_object* v_s_610_, lean_object* v_replacement_611_, lean_object* v_inst_612_, lean_object* v_R_613_, lean_object* v_a_614_, lean_object* v_b_615_, lean_object* v_c_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_610_, v_replacement_611_, v_a_614_, v_b_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___boxed(lean_object* v_s_618_, lean_object* v_replacement_619_, lean_object* v_inst_620_, lean_object* v_R_621_, lean_object* v_a_622_, lean_object* v_b_623_, lean_object* v_c_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0(v_s_618_, v_replacement_619_, v_inst_620_, v_R_621_, v_a_622_, v_b_623_, v_c_624_);
lean_dec_ref(v_replacement_619_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
if (lean_obj_tag(v_x_628_) == 0)
{
return v_x_627_;
}
else
{
lean_object* v_head_629_; lean_object* v_tail_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_head_629_ = lean_ctor_get(v_x_628_, 0);
v_tail_630_ = lean_ctor_get(v_x_628_, 1);
v___x_631_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_632_ = lean_string_append(v_x_627_, v___x_631_);
v___x_633_ = l_Int_repr(v_head_629_);
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
lean_dec_ref(v___x_633_);
v_x_627_ = v___x_634_;
v_x_628_ = v_tail_630_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___boxed(lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v_x_636_, v_x_637_);
lean_dec(v_x_637_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(lean_object* v_x_642_){
_start:
{
if (lean_obj_tag(v_x_642_) == 0)
{
lean_object* v___x_643_; 
v___x_643_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__0));
return v___x_643_;
}
else
{
lean_object* v_tail_644_; 
v_tail_644_ = lean_ctor_get(v_x_642_, 1);
if (lean_obj_tag(v_tail_644_) == 0)
{
lean_object* v_head_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_head_645_ = lean_ctor_get(v_x_642_, 0);
v___x_646_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v___x_647_ = l_Int_repr(v_head_645_);
v___x_648_ = lean_string_append(v___x_646_, v___x_647_);
lean_dec_ref(v___x_647_);
v___x_649_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_650_ = lean_string_append(v___x_648_, v___x_649_);
return v___x_650_;
}
else
{
lean_object* v_head_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint32_t v___x_656_; lean_object* v___x_657_; 
v_head_651_ = lean_ctor_get(v_x_642_, 0);
v___x_652_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v___x_653_ = l_Int_repr(v_head_651_);
v___x_654_ = lean_string_append(v___x_652_, v___x_653_);
lean_dec_ref(v___x_653_);
v___x_655_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v___x_654_, v_tail_644_);
v___x_656_ = 93;
v___x_657_ = lean_string_push(v___x_655_, v___x_656_);
return v___x_657_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___boxed(lean_object* v_x_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_658_);
lean_dec(v_x_658_);
return v_res_659_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
if (lean_obj_tag(v_x_660_) == 0)
{
if (lean_obj_tag(v_x_661_) == 0)
{
uint8_t v___x_662_; 
v___x_662_ = 1;
return v___x_662_;
}
else
{
uint8_t v___x_663_; 
v___x_663_ = 0;
return v___x_663_;
}
}
else
{
if (lean_obj_tag(v_x_661_) == 0)
{
uint8_t v___x_664_; 
v___x_664_ = 0;
return v___x_664_;
}
else
{
lean_object* v_head_665_; lean_object* v_tail_666_; lean_object* v_head_667_; lean_object* v_tail_668_; uint8_t v___x_669_; 
v_head_665_ = lean_ctor_get(v_x_660_, 0);
v_tail_666_ = lean_ctor_get(v_x_660_, 1);
v_head_667_ = lean_ctor_get(v_x_661_, 0);
v_tail_668_ = lean_ctor_get(v_x_661_, 1);
v___x_669_ = lean_int_dec_eq(v_head_665_, v_head_667_);
if (v___x_669_ == 0)
{
return v___x_669_;
}
else
{
v_x_660_ = v_tail_666_;
v_x_661_ = v_tail_668_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1___boxed(lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_671_, v_x_672_);
lean_dec(v_x_672_);
lean_dec(v_x_671_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString(lean_object* v_s_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
switch(lean_obj_tag(v_x_694_))
{
case 0:
{
lean_object* v_i_695_; lean_object* v_lowerBound_696_; lean_object* v_upperBound_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___y_702_; lean_object* v___y_709_; lean_object* v___y_710_; 
v_i_695_ = lean_ctor_get(v_x_694_, 2);
lean_inc(v_i_695_);
lean_dec_ref_known(v_x_694_, 3);
v_lowerBound_696_ = lean_ctor_get(v_s_692_, 0);
lean_inc(v_lowerBound_696_);
v_upperBound_697_ = lean_ctor_get(v_s_692_, 1);
lean_inc(v_upperBound_697_);
lean_dec_ref(v_s_692_);
v___x_698_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_693_);
lean_dec(v_x_693_);
v___x_699_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
if (lean_obj_tag(v_lowerBound_696_) == 0)
{
if (lean_obj_tag(v_upperBound_697_) == 0)
{
lean_object* v___x_714_; 
v___x_714_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_702_ = v___x_714_;
goto v___jp_701_;
}
else
{
lean_object* v_val_715_; lean_object* v___x_716_; lean_object* v___y_718_; lean_object* v_intZero_722_; uint8_t v_isNeg_723_; 
v_val_715_ = lean_ctor_get(v_upperBound_697_, 0);
lean_inc(v_val_715_);
lean_dec_ref_known(v_upperBound_697_, 1);
v___x_716_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_722_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_723_ = lean_int_dec_lt(v_val_715_, v_intZero_722_);
if (v_isNeg_723_ == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_nat_abs(v_val_715_);
lean_dec(v_val_715_);
v___x_725_ = l_Nat_reprFast(v_a_724_);
v___y_718_ = v___x_725_;
goto v___jp_717_;
}
else
{
lean_object* v_abs_726_; lean_object* v_one_727_; lean_object* v_a_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_abs_726_ = lean_nat_abs(v_val_715_);
lean_dec(v_val_715_);
v_one_727_ = lean_unsigned_to_nat(1u);
v_a_728_ = lean_nat_sub(v_abs_726_, v_one_727_);
lean_dec(v_abs_726_);
v___x_729_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_730_ = lean_nat_add(v_a_728_, v_one_727_);
lean_dec(v_a_728_);
v___x_731_ = l_Nat_reprFast(v___x_730_);
v___x_732_ = lean_string_append(v___x_729_, v___x_731_);
lean_dec_ref(v___x_731_);
v___y_718_ = v___x_732_;
goto v___jp_717_;
}
v___jp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_string_append(v___x_716_, v___y_718_);
lean_dec_ref(v___y_718_);
v___x_720_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_721_ = lean_string_append(v___x_719_, v___x_720_);
v___y_702_ = v___x_721_;
goto v___jp_701_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_697_) == 0)
{
lean_object* v_val_733_; lean_object* v___x_734_; lean_object* v___y_736_; lean_object* v_intZero_740_; uint8_t v_isNeg_741_; 
v_val_733_ = lean_ctor_get(v_lowerBound_696_, 0);
lean_inc(v_val_733_);
lean_dec_ref_known(v_lowerBound_696_, 1);
v___x_734_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_740_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_741_ = lean_int_dec_lt(v_val_733_, v_intZero_740_);
if (v_isNeg_741_ == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; 
v_a_742_ = lean_nat_abs(v_val_733_);
lean_dec(v_val_733_);
v___x_743_ = l_Nat_reprFast(v_a_742_);
v___y_736_ = v___x_743_;
goto v___jp_735_;
}
else
{
lean_object* v_abs_744_; lean_object* v_one_745_; lean_object* v_a_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_abs_744_ = lean_nat_abs(v_val_733_);
lean_dec(v_val_733_);
v_one_745_ = lean_unsigned_to_nat(1u);
v_a_746_ = lean_nat_sub(v_abs_744_, v_one_745_);
lean_dec(v_abs_744_);
v___x_747_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_748_ = lean_nat_add(v_a_746_, v_one_745_);
lean_dec(v_a_746_);
v___x_749_ = l_Nat_reprFast(v___x_748_);
v___x_750_ = lean_string_append(v___x_747_, v___x_749_);
lean_dec_ref(v___x_749_);
v___y_736_ = v___x_750_;
goto v___jp_735_;
}
v___jp_735_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = lean_string_append(v___x_734_, v___y_736_);
lean_dec_ref(v___y_736_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_739_ = lean_string_append(v___x_737_, v___x_738_);
v___y_702_ = v___x_739_;
goto v___jp_701_;
}
}
else
{
lean_object* v_val_751_; lean_object* v_val_752_; uint8_t v___x_753_; 
v_val_751_ = lean_ctor_get(v_lowerBound_696_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v_lowerBound_696_, 1);
v_val_752_ = lean_ctor_get(v_upperBound_697_, 0);
lean_inc(v_val_752_);
lean_dec_ref_known(v_upperBound_697_, 1);
v___x_753_ = lean_int_dec_lt(v_val_752_, v_val_751_);
if (v___x_753_ == 0)
{
uint8_t v___x_754_; 
v___x_754_ = lean_int_dec_eq(v_val_751_, v_val_752_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___y_757_; lean_object* v_intZero_772_; uint8_t v_isNeg_773_; 
v___x_755_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_772_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_773_ = lean_int_dec_lt(v_val_751_, v_intZero_772_);
if (v_isNeg_773_ == 0)
{
lean_object* v_a_774_; lean_object* v___x_775_; 
v_a_774_ = lean_nat_abs(v_val_751_);
lean_dec(v_val_751_);
v___x_775_ = l_Nat_reprFast(v_a_774_);
v___y_757_ = v___x_775_;
goto v___jp_756_;
}
else
{
lean_object* v_abs_776_; lean_object* v_one_777_; lean_object* v_a_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_abs_776_ = lean_nat_abs(v_val_751_);
lean_dec(v_val_751_);
v_one_777_ = lean_unsigned_to_nat(1u);
v_a_778_ = lean_nat_sub(v_abs_776_, v_one_777_);
lean_dec(v_abs_776_);
v___x_779_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_780_ = lean_nat_add(v_a_778_, v_one_777_);
lean_dec(v_a_778_);
v___x_781_ = l_Nat_reprFast(v___x_780_);
v___x_782_ = lean_string_append(v___x_779_, v___x_781_);
lean_dec_ref(v___x_781_);
v___y_757_ = v___x_782_;
goto v___jp_756_;
}
v___jp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v_intZero_761_; uint8_t v_isNeg_762_; 
v___x_758_ = lean_string_append(v___x_755_, v___y_757_);
lean_dec_ref(v___y_757_);
v___x_759_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_760_ = lean_string_append(v___x_758_, v___x_759_);
v_intZero_761_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_762_ = lean_int_dec_lt(v_val_752_, v_intZero_761_);
if (v_isNeg_762_ == 0)
{
lean_object* v_a_763_; lean_object* v___x_764_; 
v_a_763_ = lean_nat_abs(v_val_752_);
lean_dec(v_val_752_);
v___x_764_ = l_Nat_reprFast(v_a_763_);
v___y_709_ = v___x_760_;
v___y_710_ = v___x_764_;
goto v___jp_708_;
}
else
{
lean_object* v_abs_765_; lean_object* v_one_766_; lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_abs_765_ = lean_nat_abs(v_val_752_);
lean_dec(v_val_752_);
v_one_766_ = lean_unsigned_to_nat(1u);
v_a_767_ = lean_nat_sub(v_abs_765_, v_one_766_);
lean_dec(v_abs_765_);
v___x_768_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_769_ = lean_nat_add(v_a_767_, v_one_766_);
lean_dec(v_a_767_);
v___x_770_ = l_Nat_reprFast(v___x_769_);
v___x_771_ = lean_string_append(v___x_768_, v___x_770_);
lean_dec_ref(v___x_770_);
v___y_709_ = v___x_760_;
v___y_710_ = v___x_771_;
goto v___jp_708_;
}
}
}
else
{
lean_object* v___x_783_; lean_object* v___y_785_; lean_object* v_intZero_789_; uint8_t v_isNeg_790_; 
lean_dec(v_val_752_);
v___x_783_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_789_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_790_ = lean_int_dec_lt(v_val_751_, v_intZero_789_);
if (v_isNeg_790_ == 0)
{
lean_object* v_a_791_; lean_object* v___x_792_; 
v_a_791_ = lean_nat_abs(v_val_751_);
lean_dec(v_val_751_);
v___x_792_ = l_Nat_reprFast(v_a_791_);
v___y_785_ = v___x_792_;
goto v___jp_784_;
}
else
{
lean_object* v_abs_793_; lean_object* v_one_794_; lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_abs_793_ = lean_nat_abs(v_val_751_);
lean_dec(v_val_751_);
v_one_794_ = lean_unsigned_to_nat(1u);
v_a_795_ = lean_nat_sub(v_abs_793_, v_one_794_);
lean_dec(v_abs_793_);
v___x_796_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_797_ = lean_nat_add(v_a_795_, v_one_794_);
lean_dec(v_a_795_);
v___x_798_ = l_Nat_reprFast(v___x_797_);
v___x_799_ = lean_string_append(v___x_796_, v___x_798_);
lean_dec_ref(v___x_798_);
v___y_785_ = v___x_799_;
goto v___jp_784_;
}
v___jp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = lean_string_append(v___x_783_, v___y_785_);
lean_dec_ref(v___y_785_);
v___x_787_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_788_ = lean_string_append(v___x_786_, v___x_787_);
v___y_702_ = v___x_788_;
goto v___jp_701_;
}
}
}
else
{
lean_object* v___x_800_; 
lean_dec(v_val_752_);
lean_dec(v_val_751_);
v___x_800_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_702_ = v___x_800_;
goto v___jp_701_;
}
}
}
v___jp_701_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_703_ = lean_string_append(v___x_700_, v___y_702_);
lean_dec_ref(v___y_702_);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__1));
v___x_705_ = lean_string_append(v___x_703_, v___x_704_);
v___x_706_ = l_Nat_reprFast(v_i_695_);
v___x_707_ = lean_string_append(v___x_705_, v___x_706_);
lean_dec_ref(v___x_706_);
return v___x_707_;
}
v___jp_708_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = lean_string_append(v___y_709_, v___y_710_);
lean_dec_ref(v___y_710_);
v___x_712_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_713_ = lean_string_append(v___x_711_, v___x_712_);
v___y_702_ = v___x_713_;
goto v___jp_701_;
}
}
case 1:
{
lean_object* v_s_801_; lean_object* v_c_802_; lean_object* v_j_803_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; uint8_t v___y_861_; uint8_t v___x_924_; 
v_s_801_ = lean_ctor_get(v_x_694_, 0);
lean_inc_ref(v_s_801_);
v_c_802_ = lean_ctor_get(v_x_694_, 1);
lean_inc(v_c_802_);
v_j_803_ = lean_ctor_get(v_x_694_, 2);
lean_inc_ref(v_j_803_);
lean_dec_ref_known(v_x_694_, 3);
v___x_924_ = l_Lean_Omega_instBEqConstraint_beq(v_s_692_, v_s_801_);
if (v___x_924_ == 0)
{
v___y_861_ = v___x_924_;
goto v___jp_860_;
}
else
{
uint8_t v___x_925_; 
v___x_925_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_693_, v_c_802_);
v___y_861_ = v___x_925_;
goto v___jp_860_;
}
v___jp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_807_ = lean_string_append(v___y_805_, v___y_806_);
lean_dec_ref(v___y_806_);
v___x_808_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9));
v___x_809_ = lean_string_append(v___x_807_, v___x_808_);
v___x_810_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_801_, v_c_802_, v_j_803_);
v___x_811_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_810_);
v___x_812_ = lean_string_append(v___x_809_, v___x_811_);
lean_dec_ref(v___x_811_);
return v___x_812_;
}
v___jp_813_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_inc_ref(v___y_815_);
v___x_817_ = lean_string_append(v___y_815_, v___y_816_);
lean_dec_ref(v___y_816_);
v___x_818_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_819_ = lean_string_append(v___x_817_, v___x_818_);
v___y_805_ = v___y_814_;
v___y_806_ = v___x_819_;
goto v___jp_804_;
}
v___jp_820_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
lean_inc_ref(v___y_822_);
v___x_824_ = lean_string_append(v___y_822_, v___y_823_);
lean_dec_ref(v___y_823_);
v___x_825_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_826_ = lean_string_append(v___x_824_, v___x_825_);
v___y_805_ = v___y_821_;
v___y_806_ = v___x_826_;
goto v___jp_804_;
}
v___jp_827_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_string_append(v___y_828_, v___y_830_);
lean_dec_ref(v___y_830_);
v___x_832_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_833_ = lean_string_append(v___x_831_, v___x_832_);
v___y_805_ = v___y_829_;
v___y_806_ = v___x_833_;
goto v___jp_804_;
}
v___jp_834_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v_intZero_842_; uint8_t v_isNeg_843_; 
lean_inc_ref(v___y_837_);
v___x_839_ = lean_string_append(v___y_837_, v___y_838_);
lean_dec_ref(v___y_838_);
v___x_840_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_841_ = lean_string_append(v___x_839_, v___x_840_);
v_intZero_842_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_843_ = lean_int_dec_lt(v___y_835_, v_intZero_842_);
if (v_isNeg_843_ == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; 
v_a_844_ = lean_nat_abs(v___y_835_);
lean_dec(v___y_835_);
v___x_845_ = l_Nat_reprFast(v_a_844_);
v___y_828_ = v___x_841_;
v___y_829_ = v___y_836_;
v___y_830_ = v___x_845_;
goto v___jp_827_;
}
else
{
lean_object* v_abs_846_; lean_object* v_one_847_; lean_object* v_a_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_abs_846_ = lean_nat_abs(v___y_835_);
lean_dec(v___y_835_);
v_one_847_ = lean_unsigned_to_nat(1u);
v_a_848_ = lean_nat_sub(v_abs_846_, v_one_847_);
lean_dec(v_abs_846_);
v___x_849_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_850_ = lean_nat_add(v_a_848_, v_one_847_);
lean_dec(v_a_848_);
v___x_851_ = l_Nat_reprFast(v___x_850_);
v___x_852_ = lean_string_append(v___x_849_, v___x_851_);
lean_dec_ref(v___x_851_);
v___y_828_ = v___x_841_;
v___y_829_ = v___y_836_;
v___y_830_ = v___x_852_;
goto v___jp_827_;
}
}
v___jp_853_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_inc_ref(v___y_854_);
v___x_857_ = lean_string_append(v___y_854_, v___y_856_);
lean_dec_ref(v___y_856_);
v___x_858_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_859_ = lean_string_append(v___x_857_, v___x_858_);
v___y_805_ = v___y_855_;
v___y_806_ = v___x_859_;
goto v___jp_804_;
}
v___jp_860_:
{
if (v___y_861_ == 0)
{
lean_object* v_lowerBound_862_; lean_object* v_upperBound_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_lowerBound_862_ = lean_ctor_get(v_s_692_, 0);
lean_inc(v_lowerBound_862_);
v_upperBound_863_ = lean_ctor_get(v_s_692_, 1);
lean_inc(v_upperBound_863_);
lean_dec_ref(v_s_692_);
v___x_864_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_693_);
lean_dec(v_x_693_);
v___x_865_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_866_ = lean_string_append(v___x_864_, v___x_865_);
if (lean_obj_tag(v_lowerBound_862_) == 0)
{
if (lean_obj_tag(v_upperBound_863_) == 0)
{
lean_object* v___x_867_; 
v___x_867_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_805_ = v___x_866_;
v___y_806_ = v___x_867_;
goto v___jp_804_;
}
else
{
lean_object* v_val_868_; lean_object* v___x_869_; lean_object* v_intZero_870_; uint8_t v_isNeg_871_; 
v_val_868_ = lean_ctor_get(v_upperBound_863_, 0);
lean_inc(v_val_868_);
lean_dec_ref_known(v_upperBound_863_, 1);
v___x_869_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_870_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_871_ = lean_int_dec_lt(v_val_868_, v_intZero_870_);
if (v_isNeg_871_ == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; 
v_a_872_ = lean_nat_abs(v_val_868_);
lean_dec(v_val_868_);
v___x_873_ = l_Nat_reprFast(v_a_872_);
v___y_814_ = v___x_866_;
v___y_815_ = v___x_869_;
v___y_816_ = v___x_873_;
goto v___jp_813_;
}
else
{
lean_object* v_abs_874_; lean_object* v_one_875_; lean_object* v_a_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_abs_874_ = lean_nat_abs(v_val_868_);
lean_dec(v_val_868_);
v_one_875_ = lean_unsigned_to_nat(1u);
v_a_876_ = lean_nat_sub(v_abs_874_, v_one_875_);
lean_dec(v_abs_874_);
v___x_877_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_878_ = lean_nat_add(v_a_876_, v_one_875_);
lean_dec(v_a_876_);
v___x_879_ = l_Nat_reprFast(v___x_878_);
v___x_880_ = lean_string_append(v___x_877_, v___x_879_);
lean_dec_ref(v___x_879_);
v___y_814_ = v___x_866_;
v___y_815_ = v___x_869_;
v___y_816_ = v___x_880_;
goto v___jp_813_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_863_) == 0)
{
lean_object* v_val_881_; lean_object* v___x_882_; lean_object* v_intZero_883_; uint8_t v_isNeg_884_; 
v_val_881_ = lean_ctor_get(v_lowerBound_862_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v_lowerBound_862_, 1);
v___x_882_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_883_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_884_ = lean_int_dec_lt(v_val_881_, v_intZero_883_);
if (v_isNeg_884_ == 0)
{
lean_object* v_a_885_; lean_object* v___x_886_; 
v_a_885_ = lean_nat_abs(v_val_881_);
lean_dec(v_val_881_);
v___x_886_ = l_Nat_reprFast(v_a_885_);
v___y_821_ = v___x_866_;
v___y_822_ = v___x_882_;
v___y_823_ = v___x_886_;
goto v___jp_820_;
}
else
{
lean_object* v_abs_887_; lean_object* v_one_888_; lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_abs_887_ = lean_nat_abs(v_val_881_);
lean_dec(v_val_881_);
v_one_888_ = lean_unsigned_to_nat(1u);
v_a_889_ = lean_nat_sub(v_abs_887_, v_one_888_);
lean_dec(v_abs_887_);
v___x_890_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_891_ = lean_nat_add(v_a_889_, v_one_888_);
lean_dec(v_a_889_);
v___x_892_ = l_Nat_reprFast(v___x_891_);
v___x_893_ = lean_string_append(v___x_890_, v___x_892_);
lean_dec_ref(v___x_892_);
v___y_821_ = v___x_866_;
v___y_822_ = v___x_882_;
v___y_823_ = v___x_893_;
goto v___jp_820_;
}
}
else
{
lean_object* v_val_894_; lean_object* v_val_895_; uint8_t v___x_896_; 
v_val_894_ = lean_ctor_get(v_lowerBound_862_, 0);
lean_inc(v_val_894_);
lean_dec_ref_known(v_lowerBound_862_, 1);
v_val_895_ = lean_ctor_get(v_upperBound_863_, 0);
lean_inc(v_val_895_);
lean_dec_ref_known(v_upperBound_863_, 1);
v___x_896_ = lean_int_dec_lt(v_val_895_, v_val_894_);
if (v___x_896_ == 0)
{
uint8_t v___x_897_; 
v___x_897_ = lean_int_dec_eq(v_val_894_, v_val_895_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v_intZero_899_; uint8_t v_isNeg_900_; 
v___x_898_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_899_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_900_ = lean_int_dec_lt(v_val_894_, v_intZero_899_);
if (v_isNeg_900_ == 0)
{
lean_object* v_a_901_; lean_object* v___x_902_; 
v_a_901_ = lean_nat_abs(v_val_894_);
lean_dec(v_val_894_);
v___x_902_ = l_Nat_reprFast(v_a_901_);
v___y_835_ = v_val_895_;
v___y_836_ = v___x_866_;
v___y_837_ = v___x_898_;
v___y_838_ = v___x_902_;
goto v___jp_834_;
}
else
{
lean_object* v_abs_903_; lean_object* v_one_904_; lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_abs_903_ = lean_nat_abs(v_val_894_);
lean_dec(v_val_894_);
v_one_904_ = lean_unsigned_to_nat(1u);
v_a_905_ = lean_nat_sub(v_abs_903_, v_one_904_);
lean_dec(v_abs_903_);
v___x_906_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_907_ = lean_nat_add(v_a_905_, v_one_904_);
lean_dec(v_a_905_);
v___x_908_ = l_Nat_reprFast(v___x_907_);
v___x_909_ = lean_string_append(v___x_906_, v___x_908_);
lean_dec_ref(v___x_908_);
v___y_835_ = v_val_895_;
v___y_836_ = v___x_866_;
v___y_837_ = v___x_898_;
v___y_838_ = v___x_909_;
goto v___jp_834_;
}
}
else
{
lean_object* v___x_910_; lean_object* v_intZero_911_; uint8_t v_isNeg_912_; 
lean_dec(v_val_895_);
v___x_910_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_911_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_912_ = lean_int_dec_lt(v_val_894_, v_intZero_911_);
if (v_isNeg_912_ == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_913_ = lean_nat_abs(v_val_894_);
lean_dec(v_val_894_);
v___x_914_ = l_Nat_reprFast(v_a_913_);
v___y_854_ = v___x_910_;
v___y_855_ = v___x_866_;
v___y_856_ = v___x_914_;
goto v___jp_853_;
}
else
{
lean_object* v_abs_915_; lean_object* v_one_916_; lean_object* v_a_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_abs_915_ = lean_nat_abs(v_val_894_);
lean_dec(v_val_894_);
v_one_916_ = lean_unsigned_to_nat(1u);
v_a_917_ = lean_nat_sub(v_abs_915_, v_one_916_);
lean_dec(v_abs_915_);
v___x_918_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_919_ = lean_nat_add(v_a_917_, v_one_916_);
lean_dec(v_a_917_);
v___x_920_ = l_Nat_reprFast(v___x_919_);
v___x_921_ = lean_string_append(v___x_918_, v___x_920_);
lean_dec_ref(v___x_920_);
v___y_854_ = v___x_910_;
v___y_855_ = v___x_866_;
v___y_856_ = v___x_921_;
goto v___jp_853_;
}
}
}
else
{
lean_object* v___x_922_; 
lean_dec(v_val_895_);
lean_dec(v_val_894_);
v___x_922_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_805_ = v___x_866_;
v___y_806_ = v___x_922_;
goto v___jp_804_;
}
}
}
}
else
{
lean_dec(v_x_693_);
lean_dec_ref(v_s_692_);
v_s_692_ = v_s_801_;
v_x_693_ = v_c_802_;
v_x_694_ = v_j_803_;
goto _start;
}
}
}
case 2:
{
lean_object* v_s_926_; lean_object* v_t_927_; lean_object* v_j_928_; lean_object* v_k_929_; lean_object* v_lowerBound_930_; lean_object* v_upperBound_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___y_936_; lean_object* v___y_949_; lean_object* v___y_950_; 
v_s_926_ = lean_ctor_get(v_x_694_, 0);
lean_inc_ref(v_s_926_);
v_t_927_ = lean_ctor_get(v_x_694_, 1);
lean_inc_ref(v_t_927_);
v_j_928_ = lean_ctor_get(v_x_694_, 3);
lean_inc_ref(v_j_928_);
v_k_929_ = lean_ctor_get(v_x_694_, 4);
lean_inc_ref(v_k_929_);
lean_dec_ref_known(v_x_694_, 5);
v_lowerBound_930_ = lean_ctor_get(v_s_692_, 0);
lean_inc(v_lowerBound_930_);
v_upperBound_931_ = lean_ctor_get(v_s_692_, 1);
lean_inc(v_upperBound_931_);
lean_dec_ref(v_s_692_);
v___x_932_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_693_);
v___x_933_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_934_ = lean_string_append(v___x_932_, v___x_933_);
if (lean_obj_tag(v_lowerBound_930_) == 0)
{
if (lean_obj_tag(v_upperBound_931_) == 0)
{
lean_object* v___x_954_; 
v___x_954_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_936_ = v___x_954_;
goto v___jp_935_;
}
else
{
lean_object* v_val_955_; lean_object* v___x_956_; lean_object* v___y_958_; lean_object* v_intZero_962_; uint8_t v_isNeg_963_; 
v_val_955_ = lean_ctor_get(v_upperBound_931_, 0);
lean_inc(v_val_955_);
lean_dec_ref_known(v_upperBound_931_, 1);
v___x_956_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_962_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_963_ = lean_int_dec_lt(v_val_955_, v_intZero_962_);
if (v_isNeg_963_ == 0)
{
lean_object* v_a_964_; lean_object* v___x_965_; 
v_a_964_ = lean_nat_abs(v_val_955_);
lean_dec(v_val_955_);
v___x_965_ = l_Nat_reprFast(v_a_964_);
v___y_958_ = v___x_965_;
goto v___jp_957_;
}
else
{
lean_object* v_abs_966_; lean_object* v_one_967_; lean_object* v_a_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_abs_966_ = lean_nat_abs(v_val_955_);
lean_dec(v_val_955_);
v_one_967_ = lean_unsigned_to_nat(1u);
v_a_968_ = lean_nat_sub(v_abs_966_, v_one_967_);
lean_dec(v_abs_966_);
v___x_969_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_970_ = lean_nat_add(v_a_968_, v_one_967_);
lean_dec(v_a_968_);
v___x_971_ = l_Nat_reprFast(v___x_970_);
v___x_972_ = lean_string_append(v___x_969_, v___x_971_);
lean_dec_ref(v___x_971_);
v___y_958_ = v___x_972_;
goto v___jp_957_;
}
v___jp_957_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = lean_string_append(v___x_956_, v___y_958_);
lean_dec_ref(v___y_958_);
v___x_960_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_961_ = lean_string_append(v___x_959_, v___x_960_);
v___y_936_ = v___x_961_;
goto v___jp_935_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_931_) == 0)
{
lean_object* v_val_973_; lean_object* v___x_974_; lean_object* v___y_976_; lean_object* v_intZero_980_; uint8_t v_isNeg_981_; 
v_val_973_ = lean_ctor_get(v_lowerBound_930_, 0);
lean_inc(v_val_973_);
lean_dec_ref_known(v_lowerBound_930_, 1);
v___x_974_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_980_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_981_ = lean_int_dec_lt(v_val_973_, v_intZero_980_);
if (v_isNeg_981_ == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_982_ = lean_nat_abs(v_val_973_);
lean_dec(v_val_973_);
v___x_983_ = l_Nat_reprFast(v_a_982_);
v___y_976_ = v___x_983_;
goto v___jp_975_;
}
else
{
lean_object* v_abs_984_; lean_object* v_one_985_; lean_object* v_a_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_abs_984_ = lean_nat_abs(v_val_973_);
lean_dec(v_val_973_);
v_one_985_ = lean_unsigned_to_nat(1u);
v_a_986_ = lean_nat_sub(v_abs_984_, v_one_985_);
lean_dec(v_abs_984_);
v___x_987_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_988_ = lean_nat_add(v_a_986_, v_one_985_);
lean_dec(v_a_986_);
v___x_989_ = l_Nat_reprFast(v___x_988_);
v___x_990_ = lean_string_append(v___x_987_, v___x_989_);
lean_dec_ref(v___x_989_);
v___y_976_ = v___x_990_;
goto v___jp_975_;
}
v___jp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_string_append(v___x_974_, v___y_976_);
lean_dec_ref(v___y_976_);
v___x_978_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
v___y_936_ = v___x_979_;
goto v___jp_935_;
}
}
else
{
lean_object* v_val_991_; lean_object* v_val_992_; uint8_t v___x_993_; 
v_val_991_ = lean_ctor_get(v_lowerBound_930_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v_lowerBound_930_, 1);
v_val_992_ = lean_ctor_get(v_upperBound_931_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v_upperBound_931_, 1);
v___x_993_ = lean_int_dec_lt(v_val_992_, v_val_991_);
if (v___x_993_ == 0)
{
uint8_t v___x_994_; 
v___x_994_ = lean_int_dec_eq(v_val_991_, v_val_992_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; lean_object* v___y_997_; lean_object* v_intZero_1012_; uint8_t v_isNeg_1013_; 
v___x_995_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1012_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1013_ = lean_int_dec_lt(v_val_991_, v_intZero_1012_);
if (v_isNeg_1013_ == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1015_; 
v_a_1014_ = lean_nat_abs(v_val_991_);
lean_dec(v_val_991_);
v___x_1015_ = l_Nat_reprFast(v_a_1014_);
v___y_997_ = v___x_1015_;
goto v___jp_996_;
}
else
{
lean_object* v_abs_1016_; lean_object* v_one_1017_; lean_object* v_a_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_abs_1016_ = lean_nat_abs(v_val_991_);
lean_dec(v_val_991_);
v_one_1017_ = lean_unsigned_to_nat(1u);
v_a_1018_ = lean_nat_sub(v_abs_1016_, v_one_1017_);
lean_dec(v_abs_1016_);
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1020_ = lean_nat_add(v_a_1018_, v_one_1017_);
lean_dec(v_a_1018_);
v___x_1021_ = l_Nat_reprFast(v___x_1020_);
v___x_1022_ = lean_string_append(v___x_1019_, v___x_1021_);
lean_dec_ref(v___x_1021_);
v___y_997_ = v___x_1022_;
goto v___jp_996_;
}
v___jp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_intZero_1001_; uint8_t v_isNeg_1002_; 
v___x_998_ = lean_string_append(v___x_995_, v___y_997_);
lean_dec_ref(v___y_997_);
v___x_999_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1000_ = lean_string_append(v___x_998_, v___x_999_);
v_intZero_1001_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1002_ = lean_int_dec_lt(v_val_992_, v_intZero_1001_);
if (v_isNeg_1002_ == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; 
v_a_1003_ = lean_nat_abs(v_val_992_);
lean_dec(v_val_992_);
v___x_1004_ = l_Nat_reprFast(v_a_1003_);
v___y_949_ = v___x_1000_;
v___y_950_ = v___x_1004_;
goto v___jp_948_;
}
else
{
lean_object* v_abs_1005_; lean_object* v_one_1006_; lean_object* v_a_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_abs_1005_ = lean_nat_abs(v_val_992_);
lean_dec(v_val_992_);
v_one_1006_ = lean_unsigned_to_nat(1u);
v_a_1007_ = lean_nat_sub(v_abs_1005_, v_one_1006_);
lean_dec(v_abs_1005_);
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1009_ = lean_nat_add(v_a_1007_, v_one_1006_);
lean_dec(v_a_1007_);
v___x_1010_ = l_Nat_reprFast(v___x_1009_);
v___x_1011_ = lean_string_append(v___x_1008_, v___x_1010_);
lean_dec_ref(v___x_1010_);
v___y_949_ = v___x_1000_;
v___y_950_ = v___x_1011_;
goto v___jp_948_;
}
}
}
else
{
lean_object* v___x_1023_; lean_object* v___y_1025_; lean_object* v_intZero_1029_; uint8_t v_isNeg_1030_; 
lean_dec(v_val_992_);
v___x_1023_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1029_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1030_ = lean_int_dec_lt(v_val_991_, v_intZero_1029_);
if (v_isNeg_1030_ == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1032_; 
v_a_1031_ = lean_nat_abs(v_val_991_);
lean_dec(v_val_991_);
v___x_1032_ = l_Nat_reprFast(v_a_1031_);
v___y_1025_ = v___x_1032_;
goto v___jp_1024_;
}
else
{
lean_object* v_abs_1033_; lean_object* v_one_1034_; lean_object* v_a_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_abs_1033_ = lean_nat_abs(v_val_991_);
lean_dec(v_val_991_);
v_one_1034_ = lean_unsigned_to_nat(1u);
v_a_1035_ = lean_nat_sub(v_abs_1033_, v_one_1034_);
lean_dec(v_abs_1033_);
v___x_1036_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1037_ = lean_nat_add(v_a_1035_, v_one_1034_);
lean_dec(v_a_1035_);
v___x_1038_ = l_Nat_reprFast(v___x_1037_);
v___x_1039_ = lean_string_append(v___x_1036_, v___x_1038_);
lean_dec_ref(v___x_1038_);
v___y_1025_ = v___x_1039_;
goto v___jp_1024_;
}
v___jp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = lean_string_append(v___x_1023_, v___y_1025_);
lean_dec_ref(v___y_1025_);
v___x_1027_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1028_ = lean_string_append(v___x_1026_, v___x_1027_);
v___y_936_ = v___x_1028_;
goto v___jp_935_;
}
}
}
else
{
lean_object* v___x_1040_; 
lean_dec(v_val_992_);
lean_dec(v_val_991_);
v___x_1040_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_936_ = v___x_1040_;
goto v___jp_935_;
}
}
}
v___jp_935_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_937_ = lean_string_append(v___x_934_, v___y_936_);
lean_dec_ref(v___y_936_);
v___x_938_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__10));
v___x_939_ = lean_string_append(v___x_937_, v___x_938_);
lean_inc(v_x_693_);
v___x_940_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_926_, v_x_693_, v_j_928_);
v___x_941_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_940_);
v___x_942_ = lean_string_append(v___x_939_, v___x_941_);
lean_dec_ref(v___x_941_);
v___x_943_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_944_ = lean_string_append(v___x_942_, v___x_943_);
v___x_945_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_927_, v_x_693_, v_k_929_);
v___x_946_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_945_);
v___x_947_ = lean_string_append(v___x_944_, v___x_946_);
lean_dec_ref(v___x_946_);
return v___x_947_;
}
v___jp_948_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_string_append(v___y_949_, v___y_950_);
lean_dec_ref(v___y_950_);
v___x_952_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_953_ = lean_string_append(v___x_951_, v___x_952_);
v___y_936_ = v___x_953_;
goto v___jp_935_;
}
}
case 3:
{
lean_object* v_s_1041_; lean_object* v_t_1042_; lean_object* v_x_1043_; lean_object* v_y_1044_; lean_object* v_a_1045_; lean_object* v_j_1046_; lean_object* v_b_1047_; lean_object* v_k_1048_; lean_object* v_lowerBound_1049_; lean_object* v_upperBound_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___y_1055_; lean_object* v___y_1076_; lean_object* v___y_1077_; 
v_s_1041_ = lean_ctor_get(v_x_694_, 0);
lean_inc_ref(v_s_1041_);
v_t_1042_ = lean_ctor_get(v_x_694_, 1);
lean_inc_ref(v_t_1042_);
v_x_1043_ = lean_ctor_get(v_x_694_, 2);
lean_inc(v_x_1043_);
v_y_1044_ = lean_ctor_get(v_x_694_, 3);
lean_inc(v_y_1044_);
v_a_1045_ = lean_ctor_get(v_x_694_, 4);
lean_inc(v_a_1045_);
v_j_1046_ = lean_ctor_get(v_x_694_, 5);
lean_inc_ref(v_j_1046_);
v_b_1047_ = lean_ctor_get(v_x_694_, 6);
lean_inc(v_b_1047_);
v_k_1048_ = lean_ctor_get(v_x_694_, 7);
lean_inc_ref(v_k_1048_);
lean_dec_ref_known(v_x_694_, 8);
v_lowerBound_1049_ = lean_ctor_get(v_s_692_, 0);
lean_inc(v_lowerBound_1049_);
v_upperBound_1050_ = lean_ctor_get(v_s_692_, 1);
lean_inc(v_upperBound_1050_);
lean_dec_ref(v_s_692_);
v___x_1051_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_693_);
lean_dec(v_x_693_);
v___x_1052_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1053_ = lean_string_append(v___x_1051_, v___x_1052_);
if (lean_obj_tag(v_lowerBound_1049_) == 0)
{
if (lean_obj_tag(v_upperBound_1050_) == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1055_ = v___x_1081_;
goto v___jp_1054_;
}
else
{
lean_object* v_val_1082_; lean_object* v___x_1083_; lean_object* v___y_1085_; lean_object* v_intZero_1089_; uint8_t v_isNeg_1090_; 
v_val_1082_ = lean_ctor_get(v_upperBound_1050_, 0);
lean_inc(v_val_1082_);
lean_dec_ref_known(v_upperBound_1050_, 1);
v___x_1083_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1089_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1090_ = lean_int_dec_lt(v_val_1082_, v_intZero_1089_);
if (v_isNeg_1090_ == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; 
v_a_1091_ = lean_nat_abs(v_val_1082_);
lean_dec(v_val_1082_);
v___x_1092_ = l_Nat_reprFast(v_a_1091_);
v___y_1085_ = v___x_1092_;
goto v___jp_1084_;
}
else
{
lean_object* v_abs_1093_; lean_object* v_one_1094_; lean_object* v_a_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_abs_1093_ = lean_nat_abs(v_val_1082_);
lean_dec(v_val_1082_);
v_one_1094_ = lean_unsigned_to_nat(1u);
v_a_1095_ = lean_nat_sub(v_abs_1093_, v_one_1094_);
lean_dec(v_abs_1093_);
v___x_1096_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1097_ = lean_nat_add(v_a_1095_, v_one_1094_);
lean_dec(v_a_1095_);
v___x_1098_ = l_Nat_reprFast(v___x_1097_);
v___x_1099_ = lean_string_append(v___x_1096_, v___x_1098_);
lean_dec_ref(v___x_1098_);
v___y_1085_ = v___x_1099_;
goto v___jp_1084_;
}
v___jp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = lean_string_append(v___x_1083_, v___y_1085_);
lean_dec_ref(v___y_1085_);
v___x_1087_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1088_ = lean_string_append(v___x_1086_, v___x_1087_);
v___y_1055_ = v___x_1088_;
goto v___jp_1054_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1050_) == 0)
{
lean_object* v_val_1100_; lean_object* v___x_1101_; lean_object* v___y_1103_; lean_object* v_intZero_1107_; uint8_t v_isNeg_1108_; 
v_val_1100_ = lean_ctor_get(v_lowerBound_1049_, 0);
lean_inc(v_val_1100_);
lean_dec_ref_known(v_lowerBound_1049_, 1);
v___x_1101_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1107_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1108_ = lean_int_dec_lt(v_val_1100_, v_intZero_1107_);
if (v_isNeg_1108_ == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1110_; 
v_a_1109_ = lean_nat_abs(v_val_1100_);
lean_dec(v_val_1100_);
v___x_1110_ = l_Nat_reprFast(v_a_1109_);
v___y_1103_ = v___x_1110_;
goto v___jp_1102_;
}
else
{
lean_object* v_abs_1111_; lean_object* v_one_1112_; lean_object* v_a_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_abs_1111_ = lean_nat_abs(v_val_1100_);
lean_dec(v_val_1100_);
v_one_1112_ = lean_unsigned_to_nat(1u);
v_a_1113_ = lean_nat_sub(v_abs_1111_, v_one_1112_);
lean_dec(v_abs_1111_);
v___x_1114_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1115_ = lean_nat_add(v_a_1113_, v_one_1112_);
lean_dec(v_a_1113_);
v___x_1116_ = l_Nat_reprFast(v___x_1115_);
v___x_1117_ = lean_string_append(v___x_1114_, v___x_1116_);
lean_dec_ref(v___x_1116_);
v___y_1103_ = v___x_1117_;
goto v___jp_1102_;
}
v___jp_1102_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = lean_string_append(v___x_1101_, v___y_1103_);
lean_dec_ref(v___y_1103_);
v___x_1105_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1106_ = lean_string_append(v___x_1104_, v___x_1105_);
v___y_1055_ = v___x_1106_;
goto v___jp_1054_;
}
}
else
{
lean_object* v_val_1118_; lean_object* v_val_1119_; uint8_t v___x_1120_; 
v_val_1118_ = lean_ctor_get(v_lowerBound_1049_, 0);
lean_inc(v_val_1118_);
lean_dec_ref_known(v_lowerBound_1049_, 1);
v_val_1119_ = lean_ctor_get(v_upperBound_1050_, 0);
lean_inc(v_val_1119_);
lean_dec_ref_known(v_upperBound_1050_, 1);
v___x_1120_ = lean_int_dec_lt(v_val_1119_, v_val_1118_);
if (v___x_1120_ == 0)
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_int_dec_eq(v_val_1118_, v_val_1119_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___y_1124_; lean_object* v_intZero_1139_; uint8_t v_isNeg_1140_; 
v___x_1122_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1139_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1140_ = lean_int_dec_lt(v_val_1118_, v_intZero_1139_);
if (v_isNeg_1140_ == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1142_; 
v_a_1141_ = lean_nat_abs(v_val_1118_);
lean_dec(v_val_1118_);
v___x_1142_ = l_Nat_reprFast(v_a_1141_);
v___y_1124_ = v___x_1142_;
goto v___jp_1123_;
}
else
{
lean_object* v_abs_1143_; lean_object* v_one_1144_; lean_object* v_a_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v_abs_1143_ = lean_nat_abs(v_val_1118_);
lean_dec(v_val_1118_);
v_one_1144_ = lean_unsigned_to_nat(1u);
v_a_1145_ = lean_nat_sub(v_abs_1143_, v_one_1144_);
lean_dec(v_abs_1143_);
v___x_1146_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1147_ = lean_nat_add(v_a_1145_, v_one_1144_);
lean_dec(v_a_1145_);
v___x_1148_ = l_Nat_reprFast(v___x_1147_);
v___x_1149_ = lean_string_append(v___x_1146_, v___x_1148_);
lean_dec_ref(v___x_1148_);
v___y_1124_ = v___x_1149_;
goto v___jp_1123_;
}
v___jp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v_intZero_1128_; uint8_t v_isNeg_1129_; 
v___x_1125_ = lean_string_append(v___x_1122_, v___y_1124_);
lean_dec_ref(v___y_1124_);
v___x_1126_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1127_ = lean_string_append(v___x_1125_, v___x_1126_);
v_intZero_1128_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1129_ = lean_int_dec_lt(v_val_1119_, v_intZero_1128_);
if (v_isNeg_1129_ == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; 
v_a_1130_ = lean_nat_abs(v_val_1119_);
lean_dec(v_val_1119_);
v___x_1131_ = l_Nat_reprFast(v_a_1130_);
v___y_1076_ = v___x_1127_;
v___y_1077_ = v___x_1131_;
goto v___jp_1075_;
}
else
{
lean_object* v_abs_1132_; lean_object* v_one_1133_; lean_object* v_a_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v_abs_1132_ = lean_nat_abs(v_val_1119_);
lean_dec(v_val_1119_);
v_one_1133_ = lean_unsigned_to_nat(1u);
v_a_1134_ = lean_nat_sub(v_abs_1132_, v_one_1133_);
lean_dec(v_abs_1132_);
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1136_ = lean_nat_add(v_a_1134_, v_one_1133_);
lean_dec(v_a_1134_);
v___x_1137_ = l_Nat_reprFast(v___x_1136_);
v___x_1138_ = lean_string_append(v___x_1135_, v___x_1137_);
lean_dec_ref(v___x_1137_);
v___y_1076_ = v___x_1127_;
v___y_1077_ = v___x_1138_;
goto v___jp_1075_;
}
}
}
else
{
lean_object* v___x_1150_; lean_object* v___y_1152_; lean_object* v_intZero_1156_; uint8_t v_isNeg_1157_; 
lean_dec(v_val_1119_);
v___x_1150_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1156_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1157_ = lean_int_dec_lt(v_val_1118_, v_intZero_1156_);
if (v_isNeg_1157_ == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1159_; 
v_a_1158_ = lean_nat_abs(v_val_1118_);
lean_dec(v_val_1118_);
v___x_1159_ = l_Nat_reprFast(v_a_1158_);
v___y_1152_ = v___x_1159_;
goto v___jp_1151_;
}
else
{
lean_object* v_abs_1160_; lean_object* v_one_1161_; lean_object* v_a_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_abs_1160_ = lean_nat_abs(v_val_1118_);
lean_dec(v_val_1118_);
v_one_1161_ = lean_unsigned_to_nat(1u);
v_a_1162_ = lean_nat_sub(v_abs_1160_, v_one_1161_);
lean_dec(v_abs_1160_);
v___x_1163_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1164_ = lean_nat_add(v_a_1162_, v_one_1161_);
lean_dec(v_a_1162_);
v___x_1165_ = l_Nat_reprFast(v___x_1164_);
v___x_1166_ = lean_string_append(v___x_1163_, v___x_1165_);
lean_dec_ref(v___x_1165_);
v___y_1152_ = v___x_1166_;
goto v___jp_1151_;
}
v___jp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = lean_string_append(v___x_1150_, v___y_1152_);
lean_dec_ref(v___y_1152_);
v___x_1154_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1155_ = lean_string_append(v___x_1153_, v___x_1154_);
v___y_1055_ = v___x_1155_;
goto v___jp_1054_;
}
}
}
else
{
lean_object* v___x_1167_; 
lean_dec(v_val_1119_);
lean_dec(v_val_1118_);
v___x_1167_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1055_ = v___x_1167_;
goto v___jp_1054_;
}
}
}
v___jp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1056_ = lean_string_append(v___x_1053_, v___y_1055_);
lean_dec_ref(v___y_1055_);
v___x_1057_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__11));
v___x_1058_ = lean_string_append(v___x_1056_, v___x_1057_);
v___x_1059_ = l_Int_repr(v_a_1045_);
lean_dec(v_a_1045_);
v___x_1060_ = lean_string_append(v___x_1058_, v___x_1059_);
lean_dec_ref(v___x_1059_);
v___x_1061_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__12));
v___x_1062_ = lean_string_append(v___x_1060_, v___x_1061_);
v___x_1063_ = l_Int_repr(v_b_1047_);
lean_dec(v_b_1047_);
v___x_1064_ = lean_string_append(v___x_1062_, v___x_1063_);
lean_dec_ref(v___x_1063_);
v___x_1065_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__13));
v___x_1066_ = lean_string_append(v___x_1064_, v___x_1065_);
v___x_1067_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_1041_, v_x_1043_, v_j_1046_);
v___x_1068_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1067_);
v___x_1069_ = lean_string_append(v___x_1066_, v___x_1068_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_1071_ = lean_string_append(v___x_1069_, v___x_1070_);
v___x_1072_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_1042_, v_y_1044_, v_k_1048_);
v___x_1073_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1072_);
v___x_1074_ = lean_string_append(v___x_1071_, v___x_1073_);
lean_dec_ref(v___x_1073_);
return v___x_1074_;
}
v___jp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = lean_string_append(v___y_1076_, v___y_1077_);
lean_dec_ref(v___y_1077_);
v___x_1079_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1080_ = lean_string_append(v___x_1078_, v___x_1079_);
v___y_1055_ = v___x_1080_;
goto v___jp_1054_;
}
}
default: 
{
lean_object* v_m_1168_; lean_object* v_r_1169_; lean_object* v_i_1170_; lean_object* v_x_1171_; lean_object* v_j_1172_; lean_object* v_lowerBound_1173_; lean_object* v_upperBound_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___y_1179_; lean_object* v___y_1196_; lean_object* v___y_1197_; 
v_m_1168_ = lean_ctor_get(v_x_694_, 0);
lean_inc(v_m_1168_);
v_r_1169_ = lean_ctor_get(v_x_694_, 1);
lean_inc(v_r_1169_);
v_i_1170_ = lean_ctor_get(v_x_694_, 2);
lean_inc(v_i_1170_);
v_x_1171_ = lean_ctor_get(v_x_694_, 3);
lean_inc(v_x_1171_);
v_j_1172_ = lean_ctor_get(v_x_694_, 4);
lean_inc_ref(v_j_1172_);
lean_dec_ref_known(v_x_694_, 5);
v_lowerBound_1173_ = lean_ctor_get(v_s_692_, 0);
lean_inc(v_lowerBound_1173_);
v_upperBound_1174_ = lean_ctor_get(v_s_692_, 1);
lean_inc(v_upperBound_1174_);
lean_dec_ref(v_s_692_);
v___x_1175_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_693_);
lean_dec(v_x_693_);
v___x_1176_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1177_ = lean_string_append(v___x_1175_, v___x_1176_);
if (lean_obj_tag(v_lowerBound_1173_) == 0)
{
if (lean_obj_tag(v_upperBound_1174_) == 0)
{
lean_object* v___x_1201_; 
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1179_ = v___x_1201_;
goto v___jp_1178_;
}
else
{
lean_object* v_val_1202_; lean_object* v___x_1203_; lean_object* v___y_1205_; lean_object* v_intZero_1209_; uint8_t v_isNeg_1210_; 
v_val_1202_ = lean_ctor_get(v_upperBound_1174_, 0);
lean_inc(v_val_1202_);
lean_dec_ref_known(v_upperBound_1174_, 1);
v___x_1203_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1209_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1210_ = lean_int_dec_lt(v_val_1202_, v_intZero_1209_);
if (v_isNeg_1210_ == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; 
v_a_1211_ = lean_nat_abs(v_val_1202_);
lean_dec(v_val_1202_);
v___x_1212_ = l_Nat_reprFast(v_a_1211_);
v___y_1205_ = v___x_1212_;
goto v___jp_1204_;
}
else
{
lean_object* v_abs_1213_; lean_object* v_one_1214_; lean_object* v_a_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_abs_1213_ = lean_nat_abs(v_val_1202_);
lean_dec(v_val_1202_);
v_one_1214_ = lean_unsigned_to_nat(1u);
v_a_1215_ = lean_nat_sub(v_abs_1213_, v_one_1214_);
lean_dec(v_abs_1213_);
v___x_1216_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1217_ = lean_nat_add(v_a_1215_, v_one_1214_);
lean_dec(v_a_1215_);
v___x_1218_ = l_Nat_reprFast(v___x_1217_);
v___x_1219_ = lean_string_append(v___x_1216_, v___x_1218_);
lean_dec_ref(v___x_1218_);
v___y_1205_ = v___x_1219_;
goto v___jp_1204_;
}
v___jp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_string_append(v___x_1203_, v___y_1205_);
lean_dec_ref(v___y_1205_);
v___x_1207_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1208_ = lean_string_append(v___x_1206_, v___x_1207_);
v___y_1179_ = v___x_1208_;
goto v___jp_1178_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1174_) == 0)
{
lean_object* v_val_1220_; lean_object* v___x_1221_; lean_object* v___y_1223_; lean_object* v_intZero_1227_; uint8_t v_isNeg_1228_; 
v_val_1220_ = lean_ctor_get(v_lowerBound_1173_, 0);
lean_inc(v_val_1220_);
lean_dec_ref_known(v_lowerBound_1173_, 1);
v___x_1221_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1227_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1228_ = lean_int_dec_lt(v_val_1220_, v_intZero_1227_);
if (v_isNeg_1228_ == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1230_; 
v_a_1229_ = lean_nat_abs(v_val_1220_);
lean_dec(v_val_1220_);
v___x_1230_ = l_Nat_reprFast(v_a_1229_);
v___y_1223_ = v___x_1230_;
goto v___jp_1222_;
}
else
{
lean_object* v_abs_1231_; lean_object* v_one_1232_; lean_object* v_a_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_abs_1231_ = lean_nat_abs(v_val_1220_);
lean_dec(v_val_1220_);
v_one_1232_ = lean_unsigned_to_nat(1u);
v_a_1233_ = lean_nat_sub(v_abs_1231_, v_one_1232_);
lean_dec(v_abs_1231_);
v___x_1234_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1235_ = lean_nat_add(v_a_1233_, v_one_1232_);
lean_dec(v_a_1233_);
v___x_1236_ = l_Nat_reprFast(v___x_1235_);
v___x_1237_ = lean_string_append(v___x_1234_, v___x_1236_);
lean_dec_ref(v___x_1236_);
v___y_1223_ = v___x_1237_;
goto v___jp_1222_;
}
v___jp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = lean_string_append(v___x_1221_, v___y_1223_);
lean_dec_ref(v___y_1223_);
v___x_1225_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1226_ = lean_string_append(v___x_1224_, v___x_1225_);
v___y_1179_ = v___x_1226_;
goto v___jp_1178_;
}
}
else
{
lean_object* v_val_1238_; lean_object* v_val_1239_; uint8_t v___x_1240_; 
v_val_1238_ = lean_ctor_get(v_lowerBound_1173_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v_lowerBound_1173_, 1);
v_val_1239_ = lean_ctor_get(v_upperBound_1174_, 0);
lean_inc(v_val_1239_);
lean_dec_ref_known(v_upperBound_1174_, 1);
v___x_1240_ = lean_int_dec_lt(v_val_1239_, v_val_1238_);
if (v___x_1240_ == 0)
{
uint8_t v___x_1241_; 
v___x_1241_ = lean_int_dec_eq(v_val_1238_, v_val_1239_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___y_1244_; lean_object* v_intZero_1259_; uint8_t v_isNeg_1260_; 
v___x_1242_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1259_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1260_ = lean_int_dec_lt(v_val_1238_, v_intZero_1259_);
if (v_isNeg_1260_ == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1262_; 
v_a_1261_ = lean_nat_abs(v_val_1238_);
lean_dec(v_val_1238_);
v___x_1262_ = l_Nat_reprFast(v_a_1261_);
v___y_1244_ = v___x_1262_;
goto v___jp_1243_;
}
else
{
lean_object* v_abs_1263_; lean_object* v_one_1264_; lean_object* v_a_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_abs_1263_ = lean_nat_abs(v_val_1238_);
lean_dec(v_val_1238_);
v_one_1264_ = lean_unsigned_to_nat(1u);
v_a_1265_ = lean_nat_sub(v_abs_1263_, v_one_1264_);
lean_dec(v_abs_1263_);
v___x_1266_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1267_ = lean_nat_add(v_a_1265_, v_one_1264_);
lean_dec(v_a_1265_);
v___x_1268_ = l_Nat_reprFast(v___x_1267_);
v___x_1269_ = lean_string_append(v___x_1266_, v___x_1268_);
lean_dec_ref(v___x_1268_);
v___y_1244_ = v___x_1269_;
goto v___jp_1243_;
}
v___jp_1243_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v_intZero_1248_; uint8_t v_isNeg_1249_; 
v___x_1245_ = lean_string_append(v___x_1242_, v___y_1244_);
lean_dec_ref(v___y_1244_);
v___x_1246_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1247_ = lean_string_append(v___x_1245_, v___x_1246_);
v_intZero_1248_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1249_ = lean_int_dec_lt(v_val_1239_, v_intZero_1248_);
if (v_isNeg_1249_ == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1251_; 
v_a_1250_ = lean_nat_abs(v_val_1239_);
lean_dec(v_val_1239_);
v___x_1251_ = l_Nat_reprFast(v_a_1250_);
v___y_1196_ = v___x_1247_;
v___y_1197_ = v___x_1251_;
goto v___jp_1195_;
}
else
{
lean_object* v_abs_1252_; lean_object* v_one_1253_; lean_object* v_a_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_abs_1252_ = lean_nat_abs(v_val_1239_);
lean_dec(v_val_1239_);
v_one_1253_ = lean_unsigned_to_nat(1u);
v_a_1254_ = lean_nat_sub(v_abs_1252_, v_one_1253_);
lean_dec(v_abs_1252_);
v___x_1255_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1256_ = lean_nat_add(v_a_1254_, v_one_1253_);
lean_dec(v_a_1254_);
v___x_1257_ = l_Nat_reprFast(v___x_1256_);
v___x_1258_ = lean_string_append(v___x_1255_, v___x_1257_);
lean_dec_ref(v___x_1257_);
v___y_1196_ = v___x_1247_;
v___y_1197_ = v___x_1258_;
goto v___jp_1195_;
}
}
}
else
{
lean_object* v___x_1270_; lean_object* v___y_1272_; lean_object* v_intZero_1276_; uint8_t v_isNeg_1277_; 
lean_dec(v_val_1239_);
v___x_1270_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1276_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1277_ = lean_int_dec_lt(v_val_1238_, v_intZero_1276_);
if (v_isNeg_1277_ == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; 
v_a_1278_ = lean_nat_abs(v_val_1238_);
lean_dec(v_val_1238_);
v___x_1279_ = l_Nat_reprFast(v_a_1278_);
v___y_1272_ = v___x_1279_;
goto v___jp_1271_;
}
else
{
lean_object* v_abs_1280_; lean_object* v_one_1281_; lean_object* v_a_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_abs_1280_ = lean_nat_abs(v_val_1238_);
lean_dec(v_val_1238_);
v_one_1281_ = lean_unsigned_to_nat(1u);
v_a_1282_ = lean_nat_sub(v_abs_1280_, v_one_1281_);
lean_dec(v_abs_1280_);
v___x_1283_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1284_ = lean_nat_add(v_a_1282_, v_one_1281_);
lean_dec(v_a_1282_);
v___x_1285_ = l_Nat_reprFast(v___x_1284_);
v___x_1286_ = lean_string_append(v___x_1283_, v___x_1285_);
lean_dec_ref(v___x_1285_);
v___y_1272_ = v___x_1286_;
goto v___jp_1271_;
}
v___jp_1271_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_string_append(v___x_1270_, v___y_1272_);
lean_dec_ref(v___y_1272_);
v___x_1274_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1275_ = lean_string_append(v___x_1273_, v___x_1274_);
v___y_1179_ = v___x_1275_;
goto v___jp_1178_;
}
}
}
else
{
lean_object* v___x_1287_; 
lean_dec(v_val_1239_);
lean_dec(v_val_1238_);
v___x_1287_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1179_ = v___x_1287_;
goto v___jp_1178_;
}
}
}
v___jp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1180_ = lean_string_append(v___x_1177_, v___y_1179_);
lean_dec_ref(v___y_1179_);
v___x_1181_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__14));
v___x_1182_ = lean_string_append(v___x_1180_, v___x_1181_);
v___x_1183_ = l_Nat_reprFast(v_m_1168_);
v___x_1184_ = lean_string_append(v___x_1182_, v___x_1183_);
lean_dec_ref(v___x_1183_);
v___x_1185_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__15));
v___x_1186_ = lean_string_append(v___x_1184_, v___x_1185_);
v___x_1187_ = l_Nat_reprFast(v_i_1170_);
v___x_1188_ = lean_string_append(v___x_1186_, v___x_1187_);
lean_dec_ref(v___x_1187_);
v___x_1189_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__16));
v___x_1190_ = lean_string_append(v___x_1188_, v___x_1189_);
v___x_1191_ = l_Lean_Omega_Constraint_exact(v_r_1169_);
v___x_1192_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v___x_1191_, v_x_1171_, v_j_1172_);
v___x_1193_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1192_);
v___x_1194_ = lean_string_append(v___x_1190_, v___x_1193_);
lean_dec_ref(v___x_1193_);
return v___x_1194_;
}
v___jp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = lean_string_append(v___y_1196_, v___y_1197_);
lean_dec_ref(v___y_1197_);
v___x_1199_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1200_ = lean_string_append(v___x_1198_, v___x_1199_);
v___y_1179_ = v___x_1200_;
goto v___jp_1178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_instToString(lean_object* v_s_1288_, lean_object* v_x_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Justification_toString), 3, 2);
lean_closure_set(v___x_1290_, 0, v_s_1288_);
lean_closure_set(v___x_1290_, 1, v_x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(lean_object* v_nilFn_1291_, lean_object* v_consFn_1292_, lean_object* v_x_1293_){
_start:
{
if (lean_obj_tag(v_x_1293_) == 0)
{
lean_dec_ref(v_consFn_1292_);
lean_inc_ref(v_nilFn_1291_);
return v_nilFn_1291_;
}
else
{
lean_object* v_head_1294_; lean_object* v_tail_1295_; lean_object* v___y_1297_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_head_1294_ = lean_ctor_get(v_x_1293_, 0);
v_tail_1295_ = lean_ctor_get(v_x_1293_, 1);
v___x_1300_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1301_ = lean_int_dec_le(v___x_1300_, v_head_1294_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1302_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1303_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1304_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1305_ = lean_int_neg(v_head_1294_);
v___x_1306_ = l_Int_toNat(v___x_1305_);
lean_dec(v___x_1305_);
v___x_1307_ = l_Lean_instToExprInt_mkNat(v___x_1306_);
v___x_1308_ = l_Lean_mkApp3(v___x_1302_, v___x_1303_, v___x_1304_, v___x_1307_);
v___y_1297_ = v___x_1308_;
goto v___jp_1296_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = l_Int_toNat(v_head_1294_);
v___x_1310_ = l_Lean_instToExprInt_mkNat(v___x_1309_);
v___y_1297_ = v___x_1310_;
goto v___jp_1296_;
}
v___jp_1296_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_inc_ref(v_consFn_1292_);
v___x_1298_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1291_, v_consFn_1292_, v_tail_1295_);
v___x_1299_ = l_Lean_mkAppB(v_consFn_1292_, v___y_1297_, v___x_1298_);
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0___boxed(lean_object* v_nilFn_1311_, lean_object* v_consFn_1312_, lean_object* v_x_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1311_, v_consFn_1312_, v_x_1313_);
lean_dec(v_x_1313_);
lean_dec_ref(v_nilFn_1311_);
return v_res_1314_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = lean_box(0);
v___x_1321_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1));
v___x_1322_ = l_Lean_Expr_const___override(v___x_1321_, v___x_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof(lean_object* v_s_1323_, lean_object* v_x_1324_, lean_object* v_v_1325_, lean_object* v_prf_1326_){
_start:
{
lean_object* v___x_1327_; lean_object* v___y_1329_; lean_object* v_lowerBound_1334_; lean_object* v_upperBound_1335_; lean_object* v___x_1336_; lean_object* v_type_1337_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1345_; 
v___x_1327_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2);
v_lowerBound_1334_ = lean_ctor_get(v_s_1323_, 0);
v_upperBound_1335_ = lean_ctor_get(v_s_1323_, 1);
v___x_1336_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1337_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1334_) == 0)
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1345_ = v___x_1361_;
goto v___jp_1344_;
}
else
{
lean_object* v_val_1362_; lean_object* v___x_1363_; lean_object* v___y_1365_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_val_1362_ = lean_ctor_get(v_lowerBound_1334_, 0);
v___x_1363_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1367_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1368_ = lean_int_dec_le(v___x_1367_, v_val_1362_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1369_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1370_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1371_ = lean_int_neg(v_val_1362_);
v___x_1372_ = l_Int_toNat(v___x_1371_);
lean_dec(v___x_1371_);
v___x_1373_ = l_Lean_instToExprInt_mkNat(v___x_1372_);
v___x_1374_ = l_Lean_mkApp3(v___x_1369_, v_type_1337_, v___x_1370_, v___x_1373_);
v___y_1365_ = v___x_1374_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = l_Int_toNat(v_val_1362_);
v___x_1376_ = l_Lean_instToExprInt_mkNat(v___x_1375_);
v___y_1365_ = v___x_1376_;
goto v___jp_1364_;
}
v___jp_1364_:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_mkAppB(v___x_1363_, v_type_1337_, v___y_1365_);
v___y_1345_ = v___x_1366_;
goto v___jp_1344_;
}
}
v___jp_1328_:
{
lean_object* v_nil_1330_; lean_object* v_cons_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v_nil_1330_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1331_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1332_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1330_, v_cons_1331_, v_x_1324_);
v___x_1333_ = l_Lean_mkApp4(v___x_1327_, v___y_1329_, v___x_1332_, v_v_1325_, v_prf_1326_);
return v___x_1333_;
}
v___jp_1338_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_inc_ref(v___y_1340_);
v___x_1342_ = l_Lean_mkAppB(v___y_1340_, v_type_1337_, v___y_1341_);
v___x_1343_ = l_Lean_Expr_app___override(v___y_1339_, v___x_1342_);
v___y_1329_ = v___x_1343_;
goto v___jp_1328_;
}
v___jp_1344_:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_Expr_app___override(v___x_1336_, v___y_1345_);
if (lean_obj_tag(v_upperBound_1335_) == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1348_ = l_Lean_Expr_app___override(v___x_1346_, v___x_1347_);
v___y_1329_ = v___x_1348_;
goto v___jp_1328_;
}
else
{
lean_object* v_val_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_val_1349_ = lean_ctor_get(v_upperBound_1335_, 0);
v___x_1350_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1351_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1352_ = lean_int_dec_le(v___x_1351_, v_val_1349_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1353_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1354_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1355_ = lean_int_neg(v_val_1349_);
v___x_1356_ = l_Int_toNat(v___x_1355_);
lean_dec(v___x_1355_);
v___x_1357_ = l_Lean_instToExprInt_mkNat(v___x_1356_);
v___x_1358_ = l_Lean_mkApp3(v___x_1353_, v_type_1337_, v___x_1354_, v___x_1357_);
v___y_1339_ = v___x_1346_;
v___y_1340_ = v___x_1350_;
v___y_1341_ = v___x_1358_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = l_Int_toNat(v_val_1349_);
v___x_1360_ = l_Lean_instToExprInt_mkNat(v___x_1359_);
v___y_1339_ = v___x_1346_;
v___y_1340_ = v___x_1350_;
v___y_1341_ = v___x_1360_;
goto v___jp_1338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___boxed(lean_object* v_s_1377_, lean_object* v_x_1378_, lean_object* v_v_1379_, lean_object* v_prf_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1377_, v_x_1378_, v_v_1379_, v_prf_1380_);
lean_dec(v_x_1378_);
lean_dec_ref(v_s_1377_);
return v_res_1381_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_box(0);
v___x_1389_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1));
v___x_1390_ = l_Lean_Expr_const___override(v___x_1389_, v___x_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof(lean_object* v_s_1391_, lean_object* v_t_1392_, lean_object* v_x_1393_, lean_object* v_v_1394_, lean_object* v_ps_1395_, lean_object* v_pt_1396_){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1448_; lean_object* v_lowerBound_1466_; lean_object* v_upperBound_1467_; lean_object* v___x_1468_; lean_object* v_type_1469_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1477_; 
v___x_1397_ = lean_box(0);
v___x_1398_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2);
v_lowerBound_1466_ = lean_ctor_get(v_s_1391_, 0);
v_upperBound_1467_ = lean_ctor_get(v_s_1391_, 1);
v___x_1468_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1469_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1466_) == 0)
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1477_ = v___x_1493_;
goto v___jp_1476_;
}
else
{
lean_object* v_val_1494_; lean_object* v___x_1495_; lean_object* v___y_1497_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v_val_1494_ = lean_ctor_get(v_lowerBound_1466_, 0);
v___x_1495_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1499_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1500_ = lean_int_dec_le(v___x_1499_, v_val_1494_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1501_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1502_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1503_ = lean_int_neg(v_val_1494_);
v___x_1504_ = l_Int_toNat(v___x_1503_);
lean_dec(v___x_1503_);
v___x_1505_ = l_Lean_instToExprInt_mkNat(v___x_1504_);
v___x_1506_ = l_Lean_mkApp3(v___x_1501_, v_type_1469_, v___x_1502_, v___x_1505_);
v___y_1497_ = v___x_1506_;
goto v___jp_1496_;
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = l_Int_toNat(v_val_1494_);
v___x_1508_ = l_Lean_instToExprInt_mkNat(v___x_1507_);
v___y_1497_ = v___x_1508_;
goto v___jp_1496_;
}
v___jp_1496_:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_mkAppB(v___x_1495_, v_type_1469_, v___y_1497_);
v___y_1477_ = v___x_1498_;
goto v___jp_1476_;
}
}
v___jp_1399_:
{
lean_object* v_nil_1402_; lean_object* v_cons_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_nil_1402_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1403_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1404_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1402_, v_cons_1403_, v_x_1393_);
v___x_1405_ = l_Lean_mkApp6(v___x_1398_, v___y_1400_, v___y_1401_, v___x_1404_, v_v_1394_, v_ps_1395_, v_pt_1396_);
return v___x_1405_;
}
v___jp_1406_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_inc_ref(v___y_1410_);
v___x_1412_ = l_Lean_mkAppB(v___y_1410_, v___y_1407_, v___y_1411_);
v___x_1413_ = l_Lean_Expr_app___override(v___y_1408_, v___x_1412_);
v___y_1400_ = v___y_1409_;
v___y_1401_ = v___x_1413_;
goto v___jp_1399_;
}
v___jp_1414_:
{
lean_object* v_upperBound_1420_; lean_object* v___x_1421_; 
v_upperBound_1420_ = lean_ctor_get(v_t_1392_, 1);
lean_inc_ref(v___y_1417_);
v___x_1421_ = l_Lean_Expr_app___override(v___y_1417_, v___y_1419_);
if (lean_obj_tag(v_upperBound_1420_) == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1423_ = l_Lean_Expr_app___override(v___x_1422_, v___y_1415_);
v___x_1424_ = l_Lean_Expr_app___override(v___x_1421_, v___x_1423_);
v___y_1400_ = v___y_1416_;
v___y_1401_ = v___x_1424_;
goto v___jp_1399_;
}
else
{
lean_object* v_val_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v_val_1425_ = lean_ctor_get(v_upperBound_1420_, 0);
v___x_1426_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1427_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1428_ = lean_int_dec_le(v___x_1427_, v_val_1425_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1429_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1430_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1418_);
v___x_1431_ = l_Lean_Name_mkStr2(v___y_1418_, v___x_1430_);
v___x_1432_ = l_Lean_Expr_const___override(v___x_1431_, v___x_1397_);
v___x_1433_ = lean_int_neg(v_val_1425_);
v___x_1434_ = l_Int_toNat(v___x_1433_);
lean_dec(v___x_1433_);
v___x_1435_ = l_Lean_instToExprInt_mkNat(v___x_1434_);
lean_inc_ref(v___y_1415_);
v___x_1436_ = l_Lean_mkApp3(v___x_1429_, v___y_1415_, v___x_1432_, v___x_1435_);
v___y_1407_ = v___y_1415_;
v___y_1408_ = v___x_1421_;
v___y_1409_ = v___y_1416_;
v___y_1410_ = v___x_1426_;
v___y_1411_ = v___x_1436_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = l_Int_toNat(v_val_1425_);
v___x_1438_ = l_Lean_instToExprInt_mkNat(v___x_1437_);
v___y_1407_ = v___y_1415_;
v___y_1408_ = v___x_1421_;
v___y_1409_ = v___y_1416_;
v___y_1410_ = v___x_1426_;
v___y_1411_ = v___x_1438_;
goto v___jp_1406_;
}
}
}
v___jp_1439_:
{
lean_object* v___x_1446_; 
lean_inc_ref(v___y_1440_);
lean_inc_ref(v___y_1443_);
v___x_1446_ = l_Lean_mkAppB(v___y_1443_, v___y_1440_, v___y_1445_);
v___y_1415_ = v___y_1440_;
v___y_1416_ = v___y_1442_;
v___y_1417_ = v___y_1441_;
v___y_1418_ = v___y_1444_;
v___y_1419_ = v___x_1446_;
goto v___jp_1414_;
}
v___jp_1447_:
{
lean_object* v_lowerBound_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v_type_1452_; 
v_lowerBound_1449_ = lean_ctor_get(v_t_1392_, 0);
v___x_1450_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1451_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1452_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1449_) == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1415_ = v_type_1452_;
v___y_1416_ = v___y_1448_;
v___y_1417_ = v___x_1450_;
v___y_1418_ = v___x_1451_;
v___y_1419_ = v___x_1453_;
goto v___jp_1414_;
}
else
{
lean_object* v_val_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v_val_1454_ = lean_ctor_get(v_lowerBound_1449_, 0);
v___x_1455_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1456_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1457_ = lean_int_dec_le(v___x_1456_, v_val_1454_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1458_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1459_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1460_ = lean_int_neg(v_val_1454_);
v___x_1461_ = l_Int_toNat(v___x_1460_);
lean_dec(v___x_1460_);
v___x_1462_ = l_Lean_instToExprInt_mkNat(v___x_1461_);
v___x_1463_ = l_Lean_mkApp3(v___x_1458_, v_type_1452_, v___x_1459_, v___x_1462_);
v___y_1440_ = v_type_1452_;
v___y_1441_ = v___x_1450_;
v___y_1442_ = v___y_1448_;
v___y_1443_ = v___x_1455_;
v___y_1444_ = v___x_1451_;
v___y_1445_ = v___x_1463_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = l_Int_toNat(v_val_1454_);
v___x_1465_ = l_Lean_instToExprInt_mkNat(v___x_1464_);
v___y_1440_ = v_type_1452_;
v___y_1441_ = v___x_1450_;
v___y_1442_ = v___y_1448_;
v___y_1443_ = v___x_1455_;
v___y_1444_ = v___x_1451_;
v___y_1445_ = v___x_1465_;
goto v___jp_1439_;
}
}
}
v___jp_1470_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_inc_ref(v___y_1471_);
v___x_1474_ = l_Lean_mkAppB(v___y_1471_, v_type_1469_, v___y_1473_);
v___x_1475_ = l_Lean_Expr_app___override(v___y_1472_, v___x_1474_);
v___y_1448_ = v___x_1475_;
goto v___jp_1447_;
}
v___jp_1476_:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Expr_app___override(v___x_1468_, v___y_1477_);
if (lean_obj_tag(v_upperBound_1467_) == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1480_ = l_Lean_Expr_app___override(v___x_1478_, v___x_1479_);
v___y_1448_ = v___x_1480_;
goto v___jp_1447_;
}
else
{
lean_object* v_val_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v_val_1481_ = lean_ctor_get(v_upperBound_1467_, 0);
v___x_1482_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1483_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1484_ = lean_int_dec_le(v___x_1483_, v_val_1481_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1485_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1486_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1487_ = lean_int_neg(v_val_1481_);
v___x_1488_ = l_Int_toNat(v___x_1487_);
lean_dec(v___x_1487_);
v___x_1489_ = l_Lean_instToExprInt_mkNat(v___x_1488_);
v___x_1490_ = l_Lean_mkApp3(v___x_1485_, v_type_1469_, v___x_1486_, v___x_1489_);
v___y_1471_ = v___x_1482_;
v___y_1472_ = v___x_1478_;
v___y_1473_ = v___x_1490_;
goto v___jp_1470_;
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = l_Int_toNat(v_val_1481_);
v___x_1492_ = l_Lean_instToExprInt_mkNat(v___x_1491_);
v___y_1471_ = v___x_1482_;
v___y_1472_ = v___x_1478_;
v___y_1473_ = v___x_1492_;
goto v___jp_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___boxed(lean_object* v_s_1509_, lean_object* v_t_1510_, lean_object* v_x_1511_, lean_object* v_v_1512_, lean_object* v_ps_1513_, lean_object* v_pt_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1509_, v_t_1510_, v_x_1511_, v_v_1512_, v_ps_1513_, v_pt_1514_);
lean_dec(v_x_1511_);
lean_dec_ref(v_t_1510_);
lean_dec_ref(v_s_1509_);
return v_res_1515_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = lean_box(0);
v___x_1522_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1));
v___x_1523_ = l_Lean_Expr_const___override(v___x_1522_, v___x_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof(lean_object* v_s_1524_, lean_object* v_t_1525_, lean_object* v_a_1526_, lean_object* v_x_1527_, lean_object* v_b_1528_, lean_object* v_y_1529_, lean_object* v_v_1530_, lean_object* v_px_1531_, lean_object* v_py_1532_){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1619_; lean_object* v_lowerBound_1637_; lean_object* v_upperBound_1638_; lean_object* v___x_1639_; lean_object* v_type_1640_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1648_; 
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2);
v_lowerBound_1637_ = lean_ctor_get(v_s_1524_, 0);
v_upperBound_1638_ = lean_ctor_get(v_s_1524_, 1);
v___x_1639_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1640_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1637_) == 0)
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1648_ = v___x_1664_;
goto v___jp_1647_;
}
else
{
lean_object* v_val_1665_; lean_object* v___x_1666_; lean_object* v___y_1668_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v_val_1665_ = lean_ctor_get(v_lowerBound_1637_, 0);
v___x_1666_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1670_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1671_ = lean_int_dec_le(v___x_1670_, v_val_1665_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1672_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1673_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1674_ = lean_int_neg(v_val_1665_);
v___x_1675_ = l_Int_toNat(v___x_1674_);
lean_dec(v___x_1674_);
v___x_1676_ = l_Lean_instToExprInt_mkNat(v___x_1675_);
v___x_1677_ = l_Lean_mkApp3(v___x_1672_, v_type_1640_, v___x_1673_, v___x_1676_);
v___y_1668_ = v___x_1677_;
goto v___jp_1667_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = l_Int_toNat(v_val_1665_);
v___x_1679_ = l_Lean_instToExprInt_mkNat(v___x_1678_);
v___y_1668_ = v___x_1679_;
goto v___jp_1667_;
}
v___jp_1667_:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_mkAppB(v___x_1666_, v_type_1640_, v___y_1668_);
v___y_1648_ = v___x_1669_;
goto v___jp_1647_;
}
}
v___jp_1535_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v___y_1540_, v___y_1541_, v_y_1529_);
v___x_1544_ = l_Lean_mkApp9(v___x_1534_, v___y_1537_, v___y_1539_, v___y_1538_, v___y_1536_, v___y_1542_, v___x_1543_, v_v_1530_, v_px_1531_, v_py_1532_);
return v___x_1544_;
}
v___jp_1545_:
{
lean_object* v_type_1549_; lean_object* v_nil_1550_; lean_object* v_cons_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v_type_1549_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_nil_1550_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1551_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1552_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1550_, v_cons_1551_, v_x_1527_);
v___x_1553_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1554_ = lean_int_dec_le(v___x_1553_, v_b_1528_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1555_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1556_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1557_ = lean_int_neg(v_b_1528_);
v___x_1558_ = l_Int_toNat(v___x_1557_);
lean_dec(v___x_1557_);
v___x_1559_ = l_Lean_instToExprInt_mkNat(v___x_1558_);
v___x_1560_ = l_Lean_mkApp3(v___x_1555_, v_type_1549_, v___x_1556_, v___x_1559_);
v___y_1536_ = v___x_1552_;
v___y_1537_ = v___y_1546_;
v___y_1538_ = v___y_1548_;
v___y_1539_ = v___y_1547_;
v___y_1540_ = v_nil_1550_;
v___y_1541_ = v_cons_1551_;
v___y_1542_ = v___x_1560_;
goto v___jp_1535_;
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = l_Int_toNat(v_b_1528_);
v___x_1562_ = l_Lean_instToExprInt_mkNat(v___x_1561_);
v___y_1536_ = v___x_1552_;
v___y_1537_ = v___y_1546_;
v___y_1538_ = v___y_1548_;
v___y_1539_ = v___y_1547_;
v___y_1540_ = v_nil_1550_;
v___y_1541_ = v_cons_1551_;
v___y_1542_ = v___x_1562_;
goto v___jp_1535_;
}
}
v___jp_1563_:
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1567_ = lean_int_dec_le(v___x_1566_, v_a_1526_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1568_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1569_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1570_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1571_ = lean_int_neg(v_a_1526_);
v___x_1572_ = l_Int_toNat(v___x_1571_);
lean_dec(v___x_1571_);
v___x_1573_ = l_Lean_instToExprInt_mkNat(v___x_1572_);
v___x_1574_ = l_Lean_mkApp3(v___x_1568_, v___x_1569_, v___x_1570_, v___x_1573_);
v___y_1546_ = v___y_1564_;
v___y_1547_ = v___y_1565_;
v___y_1548_ = v___x_1574_;
goto v___jp_1545_;
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = l_Int_toNat(v_a_1526_);
v___x_1576_ = l_Lean_instToExprInt_mkNat(v___x_1575_);
v___y_1546_ = v___y_1564_;
v___y_1547_ = v___y_1565_;
v___y_1548_ = v___x_1576_;
goto v___jp_1545_;
}
}
v___jp_1577_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_inc_ref(v___y_1578_);
v___x_1583_ = l_Lean_mkAppB(v___y_1578_, v___y_1581_, v___y_1582_);
v___x_1584_ = l_Lean_Expr_app___override(v___y_1579_, v___x_1583_);
v___y_1564_ = v___y_1580_;
v___y_1565_ = v___x_1584_;
goto v___jp_1563_;
}
v___jp_1585_:
{
lean_object* v_upperBound_1591_; lean_object* v___x_1592_; 
v_upperBound_1591_ = lean_ctor_get(v_t_1525_, 1);
lean_inc_ref(v___y_1586_);
v___x_1592_ = l_Lean_Expr_app___override(v___y_1586_, v___y_1590_);
if (lean_obj_tag(v_upperBound_1591_) == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1594_ = l_Lean_Expr_app___override(v___x_1593_, v___y_1588_);
v___x_1595_ = l_Lean_Expr_app___override(v___x_1592_, v___x_1594_);
v___y_1564_ = v___y_1587_;
v___y_1565_ = v___x_1595_;
goto v___jp_1563_;
}
else
{
lean_object* v_val_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v_val_1596_ = lean_ctor_get(v_upperBound_1591_, 0);
v___x_1597_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1598_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1599_ = lean_int_dec_le(v___x_1598_, v_val_1596_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1600_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1601_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1589_);
v___x_1602_ = l_Lean_Name_mkStr2(v___y_1589_, v___x_1601_);
v___x_1603_ = l_Lean_Expr_const___override(v___x_1602_, v___x_1533_);
v___x_1604_ = lean_int_neg(v_val_1596_);
v___x_1605_ = l_Int_toNat(v___x_1604_);
lean_dec(v___x_1604_);
v___x_1606_ = l_Lean_instToExprInt_mkNat(v___x_1605_);
lean_inc_ref(v___y_1588_);
v___x_1607_ = l_Lean_mkApp3(v___x_1600_, v___y_1588_, v___x_1603_, v___x_1606_);
v___y_1578_ = v___x_1597_;
v___y_1579_ = v___x_1592_;
v___y_1580_ = v___y_1587_;
v___y_1581_ = v___y_1588_;
v___y_1582_ = v___x_1607_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = l_Int_toNat(v_val_1596_);
v___x_1609_ = l_Lean_instToExprInt_mkNat(v___x_1608_);
v___y_1578_ = v___x_1597_;
v___y_1579_ = v___x_1592_;
v___y_1580_ = v___y_1587_;
v___y_1581_ = v___y_1588_;
v___y_1582_ = v___x_1609_;
goto v___jp_1577_;
}
}
}
v___jp_1610_:
{
lean_object* v___x_1617_; 
lean_inc_ref(v___y_1614_);
lean_inc_ref(v___y_1612_);
v___x_1617_ = l_Lean_mkAppB(v___y_1612_, v___y_1614_, v___y_1616_);
v___y_1586_ = v___y_1611_;
v___y_1587_ = v___y_1613_;
v___y_1588_ = v___y_1614_;
v___y_1589_ = v___y_1615_;
v___y_1590_ = v___x_1617_;
goto v___jp_1585_;
}
v___jp_1618_:
{
lean_object* v_lowerBound_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v_type_1623_; 
v_lowerBound_1620_ = lean_ctor_get(v_t_1525_, 0);
v___x_1621_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1622_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1623_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1620_) == 0)
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1586_ = v___x_1621_;
v___y_1587_ = v___y_1619_;
v___y_1588_ = v_type_1623_;
v___y_1589_ = v___x_1622_;
v___y_1590_ = v___x_1624_;
goto v___jp_1585_;
}
else
{
lean_object* v_val_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v_val_1625_ = lean_ctor_get(v_lowerBound_1620_, 0);
v___x_1626_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1627_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1628_ = lean_int_dec_le(v___x_1627_, v_val_1625_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1629_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1630_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1631_ = lean_int_neg(v_val_1625_);
v___x_1632_ = l_Int_toNat(v___x_1631_);
lean_dec(v___x_1631_);
v___x_1633_ = l_Lean_instToExprInt_mkNat(v___x_1632_);
v___x_1634_ = l_Lean_mkApp3(v___x_1629_, v_type_1623_, v___x_1630_, v___x_1633_);
v___y_1611_ = v___x_1621_;
v___y_1612_ = v___x_1626_;
v___y_1613_ = v___y_1619_;
v___y_1614_ = v_type_1623_;
v___y_1615_ = v___x_1622_;
v___y_1616_ = v___x_1634_;
goto v___jp_1610_;
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = l_Int_toNat(v_val_1625_);
v___x_1636_ = l_Lean_instToExprInt_mkNat(v___x_1635_);
v___y_1611_ = v___x_1621_;
v___y_1612_ = v___x_1626_;
v___y_1613_ = v___y_1619_;
v___y_1614_ = v_type_1623_;
v___y_1615_ = v___x_1622_;
v___y_1616_ = v___x_1636_;
goto v___jp_1610_;
}
}
}
v___jp_1641_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_inc_ref(v___y_1642_);
v___x_1645_ = l_Lean_mkAppB(v___y_1642_, v_type_1640_, v___y_1644_);
v___x_1646_ = l_Lean_Expr_app___override(v___y_1643_, v___x_1645_);
v___y_1619_ = v___x_1646_;
goto v___jp_1618_;
}
v___jp_1647_:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_Expr_app___override(v___x_1639_, v___y_1648_);
if (lean_obj_tag(v_upperBound_1638_) == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1651_ = l_Lean_Expr_app___override(v___x_1649_, v___x_1650_);
v___y_1619_ = v___x_1651_;
goto v___jp_1618_;
}
else
{
lean_object* v_val_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v_val_1652_ = lean_ctor_get(v_upperBound_1638_, 0);
v___x_1653_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1654_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1655_ = lean_int_dec_le(v___x_1654_, v_val_1652_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1656_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1657_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1658_ = lean_int_neg(v_val_1652_);
v___x_1659_ = l_Int_toNat(v___x_1658_);
lean_dec(v___x_1658_);
v___x_1660_ = l_Lean_instToExprInt_mkNat(v___x_1659_);
v___x_1661_ = l_Lean_mkApp3(v___x_1656_, v_type_1640_, v___x_1657_, v___x_1660_);
v___y_1642_ = v___x_1653_;
v___y_1643_ = v___x_1649_;
v___y_1644_ = v___x_1661_;
goto v___jp_1641_;
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = l_Int_toNat(v_val_1652_);
v___x_1663_ = l_Lean_instToExprInt_mkNat(v___x_1662_);
v___y_1642_ = v___x_1653_;
v___y_1643_ = v___x_1649_;
v___y_1644_ = v___x_1663_;
goto v___jp_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___boxed(lean_object* v_s_1680_, lean_object* v_t_1681_, lean_object* v_a_1682_, lean_object* v_x_1683_, lean_object* v_b_1684_, lean_object* v_y_1685_, lean_object* v_v_1686_, lean_object* v_px_1687_, lean_object* v_py_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1680_, v_t_1681_, v_a_1682_, v_x_1683_, v_b_1684_, v_y_1685_, v_v_1686_, v_px_1687_, v_py_1688_);
lean_dec(v_y_1685_);
lean_dec(v_b_1684_);
lean_dec(v_x_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_t_1681_);
lean_dec_ref(v_s_1680_);
return v_res_1689_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_1696_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2));
v___x_1697_ = l_Lean_Expr_const___override(v___x_1696_, v___x_1695_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_box(0);
v___x_1702_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5));
v___x_1703_ = l_Lean_Expr_const___override(v___x_1702_, v___x_1701_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = lean_box(0);
v___x_1708_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8));
v___x_1709_ = l_Lean_Expr_const___override(v___x_1708_, v___x_1707_);
return v___x_1709_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = lean_box(0);
v___x_1718_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12));
v___x_1719_ = l_Lean_Expr_const___override(v___x_1718_, v___x_1717_);
return v___x_1719_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = lean_box(0);
v___x_1727_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15));
v___x_1728_ = l_Lean_Expr_const___override(v___x_1727_, v___x_1726_);
return v___x_1728_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = lean_box(0);
v___x_1735_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18));
v___x_1736_ = l_Lean_Expr_const___override(v___x_1735_, v___x_1734_);
return v___x_1736_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22(void){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1742_ = lean_box(0);
v___x_1743_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21));
v___x_1744_ = l_Lean_Expr_const___override(v___x_1743_, v___x_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof(lean_object* v_m_1745_, lean_object* v_r_1746_, lean_object* v_i_1747_, lean_object* v_x_1748_, lean_object* v_v_1749_, lean_object* v_w_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_m_1756_; lean_object* v___y_1758_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v_m_1756_ = l_Lean_mkNatLit(v_m_1745_);
v___x_1786_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1787_ = lean_int_dec_le(v___x_1786_, v_r_1746_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1788_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1789_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1790_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1791_ = lean_int_neg(v_r_1746_);
v___x_1792_ = l_Int_toNat(v___x_1791_);
lean_dec(v___x_1791_);
v___x_1793_ = l_Lean_instToExprInt_mkNat(v___x_1792_);
v___x_1794_ = l_Lean_mkApp3(v___x_1788_, v___x_1789_, v___x_1790_, v___x_1793_);
v___y_1758_ = v___x_1794_;
goto v___jp_1757_;
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = l_Int_toNat(v_r_1746_);
v___x_1796_ = l_Lean_instToExprInt_mkNat(v___x_1795_);
v___y_1758_ = v___x_1796_;
goto v___jp_1757_;
}
v___jp_1757_:
{
lean_object* v_i_1759_; lean_object* v_nil_1760_; lean_object* v_cons_1761_; lean_object* v_x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_i_1759_ = l_Lean_mkNatLit(v_i_1747_);
v_nil_1760_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1761_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v_x_1762_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1760_, v_cons_1761_, v_x_1748_);
v___x_1763_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3);
v___x_1764_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6);
v___x_1765_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9);
v___x_1766_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13);
lean_inc_ref(v_x_1762_);
v___x_1767_ = l_Lean_Expr_app___override(v___x_1766_, v_x_1762_);
lean_inc_ref(v_i_1759_);
v___x_1768_ = l_Lean_mkApp4(v___x_1763_, v___x_1764_, v___x_1765_, v___x_1767_, v_i_1759_);
v___x_1769_ = l_Lean_Meta_mkDecideProof(v___x_1768_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v___x_1771_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16);
lean_inc_ref(v_i_1759_);
lean_inc_ref_n(v_v_1749_, 2);
v___x_1772_ = l_Lean_mkAppB(v___x_1771_, v_v_1749_, v_i_1759_);
v___x_1773_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc_ref(v_x_1762_);
lean_inc_ref(v_m_1756_);
v___x_1774_ = l_Lean_mkApp3(v___x_1773_, v_m_1756_, v_x_1762_, v_v_1749_);
v___x_1775_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v___x_1772_, v___x_1774_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1785_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1783_; 
v___x_1780_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22);
v___x_1781_ = l_Lean_mkApp8(v___x_1780_, v_m_1756_, v___y_1758_, v_i_1759_, v_x_1762_, v_v_1749_, v_a_1770_, v_a_1776_, v_w_1750_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1781_);
v___x_1783_ = v___x_1778_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
else
{
lean_dec(v_a_1770_);
lean_dec_ref(v_x_1762_);
lean_dec_ref(v_i_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v_m_1756_);
lean_dec_ref(v_w_1750_);
lean_dec_ref(v_v_1749_);
return v___x_1775_;
}
}
else
{
lean_dec_ref(v_x_1762_);
lean_dec_ref(v_i_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v_m_1756_);
lean_dec_ref(v_w_1750_);
lean_dec_ref(v_v_1749_);
return v___x_1769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___boxed(lean_object* v_m_1797_, lean_object* v_r_1798_, lean_object* v_i_1799_, lean_object* v_x_1800_, lean_object* v_v_1801_, lean_object* v_w_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1797_, v_r_1798_, v_i_1799_, v_x_1800_, v_v_1801_, v_w_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_x_1800_);
lean_dec(v_r_1798_);
return v_res_1808_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0(void){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_instMonadEIO(lean_box(0));
return v___x_1809_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0);
v___x_1811_ = l_StateRefT_x27_instMonad___redArg(v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(lean_object* v_c_1816_, lean_object* v_v_1817_, lean_object* v_assumptions_1818_, lean_object* v_x_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, uint8_t v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1830_; lean_object* v_toApplicative_1831_; lean_object* v_toFunctor_1832_; lean_object* v_toSeq_1833_; lean_object* v_toSeqLeft_1834_; lean_object* v_toSeqRight_1835_; lean_object* v___f_1836_; lean_object* v___f_1837_; lean_object* v___f_1838_; lean_object* v___f_1839_; lean_object* v___x_1840_; lean_object* v___f_1841_; lean_object* v___f_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v_toApplicative_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1942_; 
v___x_1830_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1);
v_toApplicative_1831_ = lean_ctor_get(v___x_1830_, 0);
v_toFunctor_1832_ = lean_ctor_get(v_toApplicative_1831_, 0);
v_toSeq_1833_ = lean_ctor_get(v_toApplicative_1831_, 2);
v_toSeqLeft_1834_ = lean_ctor_get(v_toApplicative_1831_, 3);
v_toSeqRight_1835_ = lean_ctor_get(v_toApplicative_1831_, 4);
v___f_1836_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2));
v___f_1837_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1832_, 2);
v___f_1838_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1838_, 0, v_toFunctor_1832_);
v___f_1839_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1839_, 0, v_toFunctor_1832_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___f_1838_);
lean_ctor_set(v___x_1840_, 1, v___f_1839_);
lean_inc(v_toSeqRight_1835_);
v___f_1841_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1841_, 0, v_toSeqRight_1835_);
lean_inc(v_toSeqLeft_1834_);
v___f_1842_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1842_, 0, v_toSeqLeft_1834_);
lean_inc(v_toSeq_1833_);
v___f_1843_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1843_, 0, v_toSeq_1833_);
v___x_1844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1840_);
lean_ctor_set(v___x_1844_, 1, v___f_1836_);
lean_ctor_set(v___x_1844_, 2, v___f_1843_);
lean_ctor_set(v___x_1844_, 3, v___f_1842_);
lean_ctor_set(v___x_1844_, 4, v___f_1841_);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v___f_1837_);
v___x_1846_ = l_StateRefT_x27_instMonad___redArg(v___x_1845_);
v_toApplicative_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v___x_1846_, 1);
lean_dec(v_unused_1943_);
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1942_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_toApplicative_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1942_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_toFunctor_1851_; lean_object* v_toSeq_1852_; lean_object* v_toSeqLeft_1853_; lean_object* v_toSeqRight_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1940_; 
v_toFunctor_1851_ = lean_ctor_get(v_toApplicative_1847_, 0);
v_toSeq_1852_ = lean_ctor_get(v_toApplicative_1847_, 2);
v_toSeqLeft_1853_ = lean_ctor_get(v_toApplicative_1847_, 3);
v_toSeqRight_1854_ = lean_ctor_get(v_toApplicative_1847_, 4);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_toApplicative_1847_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v_toApplicative_1847_, 1);
lean_dec(v_unused_1941_);
v___x_1856_ = v_toApplicative_1847_;
v_isShared_1857_ = v_isSharedCheck_1940_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_toSeqRight_1854_);
lean_inc(v_toSeqLeft_1853_);
lean_inc(v_toSeq_1852_);
lean_inc(v_toFunctor_1851_);
lean_dec(v_toApplicative_1847_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1940_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___f_1858_; lean_object* v___f_1859_; lean_object* v___f_1860_; lean_object* v___f_1861_; lean_object* v___x_1862_; lean_object* v___f_1863_; lean_object* v___f_1864_; lean_object* v___f_1865_; lean_object* v___x_1867_; 
v___f_1858_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4));
v___f_1859_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5));
lean_inc_ref(v_toFunctor_1851_);
v___f_1860_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1860_, 0, v_toFunctor_1851_);
v___f_1861_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1861_, 0, v_toFunctor_1851_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___f_1860_);
lean_ctor_set(v___x_1862_, 1, v___f_1861_);
v___f_1863_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1863_, 0, v_toSeqRight_1854_);
v___f_1864_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1864_, 0, v_toSeqLeft_1853_);
v___f_1865_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1865_, 0, v_toSeq_1852_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 4, v___f_1863_);
lean_ctor_set(v___x_1856_, 3, v___f_1864_);
lean_ctor_set(v___x_1856_, 2, v___f_1865_);
lean_ctor_set(v___x_1856_, 1, v___f_1858_);
lean_ctor_set(v___x_1856_, 0, v___x_1862_);
v___x_1867_ = v___x_1856_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1862_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___f_1858_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v___f_1865_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v___f_1864_);
lean_ctor_set(v_reuseFailAlloc_1939_, 4, v___f_1863_);
v___x_1867_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v___f_1859_);
lean_ctor_set(v___x_1849_, 0, v___x_1867_);
v___x_1869_ = v___x_1849_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v___f_1859_);
v___x_1869_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1870_ = l_StateRefT_x27_instMonad___redArg(v___x_1869_);
v___x_1871_ = l_ReaderT_instMonad___redArg(v___x_1870_);
v___x_1872_ = l_ReaderT_instMonad___redArg(v___x_1871_);
v___x_1873_ = l_StateRefT_x27_instMonad___redArg(v___x_1872_);
v___x_1874_ = l_StateRefT_x27_instMonad___redArg(v___x_1873_);
switch(lean_obj_tag(v_x_1819_))
{
case 0:
{
lean_object* v_i_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_3776__overap_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_dec_ref(v_v_1817_);
v_i_1875_ = lean_ctor_get(v_x_1819_, 2);
lean_inc(v_i_1875_);
lean_dec_ref_known(v_x_1819_, 3);
v___x_1876_ = l_Lean_instInhabitedExpr;
v___x_1877_ = l_instInhabitedOfMonad___redArg(v___x_1874_, v___x_1876_);
v___x_3776__overap_1878_ = lean_array_get(v___x_1877_, v_assumptions_1818_, v_i_1875_);
lean_dec(v_i_1875_);
lean_dec(v___x_1877_);
v___x_1879_ = lean_box(v_a_1823_);
lean_inc(v_a_1828_);
lean_inc_ref(v_a_1827_);
lean_inc(v_a_1826_);
lean_inc_ref(v_a_1825_);
lean_inc(v_a_1824_);
lean_inc_ref(v_a_1822_);
lean_inc(v_a_1821_);
lean_inc(v_a_1820_);
v___x_1880_ = lean_apply_10(v___x_3776__overap_1878_, v_a_1820_, v_a_1821_, v_a_1822_, v___x_1879_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, lean_box(0));
return v___x_1880_;
}
case 1:
{
lean_object* v_s_1881_; lean_object* v_c_1882_; lean_object* v_j_1883_; lean_object* v___x_1884_; 
lean_dec_ref(v___x_1874_);
v_s_1881_ = lean_ctor_get(v_x_1819_, 0);
lean_inc_ref(v_s_1881_);
v_c_1882_ = lean_ctor_get(v_x_1819_, 1);
lean_inc(v_c_1882_);
v_j_1883_ = lean_ctor_get(v_x_1819_, 2);
lean_inc_ref(v_j_1883_);
lean_dec_ref_known(v_x_1819_, 3);
lean_inc_ref(v_v_1817_);
v___x_1884_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1882_, v_v_1817_, v_assumptions_1818_, v_j_1883_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1893_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1887_ = v___x_1884_;
v_isShared_1888_ = v_isSharedCheck_1893_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1893_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1889_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1881_, v_c_1882_, v_v_1817_, v_a_1885_);
lean_dec(v_c_1882_);
lean_dec_ref(v_s_1881_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1889_);
v___x_1891_ = v___x_1887_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
else
{
lean_dec(v_c_1882_);
lean_dec_ref(v_s_1881_);
lean_dec_ref(v_v_1817_);
return v___x_1884_;
}
}
case 2:
{
lean_object* v_s_1894_; lean_object* v_t_1895_; lean_object* v_j_1896_; lean_object* v_k_1897_; lean_object* v___x_1898_; 
lean_dec_ref(v___x_1874_);
v_s_1894_ = lean_ctor_get(v_x_1819_, 0);
lean_inc_ref(v_s_1894_);
v_t_1895_ = lean_ctor_get(v_x_1819_, 1);
lean_inc_ref(v_t_1895_);
v_j_1896_ = lean_ctor_get(v_x_1819_, 3);
lean_inc_ref(v_j_1896_);
v_k_1897_ = lean_ctor_get(v_x_1819_, 4);
lean_inc_ref(v_k_1897_);
lean_dec_ref_known(v_x_1819_, 5);
lean_inc_ref(v_v_1817_);
v___x_1898_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1816_, v_v_1817_, v_assumptions_1818_, v_j_1896_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
lean_inc_ref(v_v_1817_);
v___x_1900_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1816_, v_v_1817_, v_assumptions_1818_, v_k_1897_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1909_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1894_, v_t_1895_, v_c_1816_, v_v_1817_, v_a_1899_, v_a_1901_);
lean_dec_ref(v_t_1895_);
lean_dec_ref(v_s_1894_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1905_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
else
{
lean_dec(v_a_1899_);
lean_dec_ref(v_t_1895_);
lean_dec_ref(v_s_1894_);
lean_dec_ref(v_v_1817_);
return v___x_1900_;
}
}
else
{
lean_dec_ref(v_k_1897_);
lean_dec_ref(v_t_1895_);
lean_dec_ref(v_s_1894_);
lean_dec_ref(v_v_1817_);
return v___x_1898_;
}
}
case 3:
{
lean_object* v_s_1910_; lean_object* v_t_1911_; lean_object* v_x_1912_; lean_object* v_y_1913_; lean_object* v_a_1914_; lean_object* v_j_1915_; lean_object* v_b_1916_; lean_object* v_k_1917_; lean_object* v___x_1918_; 
lean_dec_ref(v___x_1874_);
v_s_1910_ = lean_ctor_get(v_x_1819_, 0);
lean_inc_ref(v_s_1910_);
v_t_1911_ = lean_ctor_get(v_x_1819_, 1);
lean_inc_ref(v_t_1911_);
v_x_1912_ = lean_ctor_get(v_x_1819_, 2);
lean_inc(v_x_1912_);
v_y_1913_ = lean_ctor_get(v_x_1819_, 3);
lean_inc(v_y_1913_);
v_a_1914_ = lean_ctor_get(v_x_1819_, 4);
lean_inc(v_a_1914_);
v_j_1915_ = lean_ctor_get(v_x_1819_, 5);
lean_inc_ref(v_j_1915_);
v_b_1916_ = lean_ctor_get(v_x_1819_, 6);
lean_inc(v_b_1916_);
v_k_1917_ = lean_ctor_get(v_x_1819_, 7);
lean_inc_ref(v_k_1917_);
lean_dec_ref_known(v_x_1819_, 8);
lean_inc_ref(v_v_1817_);
v___x_1918_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1912_, v_v_1817_, v_assumptions_1818_, v_j_1915_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
lean_inc_ref(v_v_1817_);
v___x_1920_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_y_1913_, v_v_1817_, v_assumptions_1818_, v_k_1917_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1929_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1910_, v_t_1911_, v_a_1914_, v_x_1912_, v_b_1916_, v_y_1913_, v_v_1817_, v_a_1919_, v_a_1921_);
lean_dec(v_y_1913_);
lean_dec(v_b_1916_);
lean_dec(v_x_1912_);
lean_dec(v_a_1914_);
lean_dec_ref(v_t_1911_);
lean_dec_ref(v_s_1910_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
else
{
lean_dec(v_a_1919_);
lean_dec(v_b_1916_);
lean_dec(v_a_1914_);
lean_dec(v_y_1913_);
lean_dec(v_x_1912_);
lean_dec_ref(v_t_1911_);
lean_dec_ref(v_s_1910_);
lean_dec_ref(v_v_1817_);
return v___x_1920_;
}
}
else
{
lean_dec_ref(v_k_1917_);
lean_dec(v_b_1916_);
lean_dec(v_a_1914_);
lean_dec(v_y_1913_);
lean_dec(v_x_1912_);
lean_dec_ref(v_t_1911_);
lean_dec_ref(v_s_1910_);
lean_dec_ref(v_v_1817_);
return v___x_1918_;
}
}
default: 
{
lean_object* v_m_1930_; lean_object* v_r_1931_; lean_object* v_i_1932_; lean_object* v_x_1933_; lean_object* v_j_1934_; lean_object* v___x_1935_; 
lean_dec_ref(v___x_1874_);
v_m_1930_ = lean_ctor_get(v_x_1819_, 0);
lean_inc(v_m_1930_);
v_r_1931_ = lean_ctor_get(v_x_1819_, 1);
lean_inc(v_r_1931_);
v_i_1932_ = lean_ctor_get(v_x_1819_, 2);
lean_inc(v_i_1932_);
v_x_1933_ = lean_ctor_get(v_x_1819_, 3);
lean_inc(v_x_1933_);
v_j_1934_ = lean_ctor_get(v_x_1819_, 4);
lean_inc_ref(v_j_1934_);
lean_dec_ref_known(v_x_1819_, 5);
lean_inc_ref(v_v_1817_);
v___x_1935_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1933_, v_v_1817_, v_assumptions_1818_, v_j_1934_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1937_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1937_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1930_, v_r_1931_, v_i_1932_, v_x_1933_, v_v_1817_, v_a_1936_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
lean_dec(v_x_1933_);
lean_dec(v_r_1931_);
return v___x_1937_;
}
else
{
lean_dec(v_x_1933_);
lean_dec(v_i_1932_);
lean_dec(v_r_1931_);
lean_dec(v_m_1930_);
lean_dec_ref(v_v_1817_);
return v___x_1935_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___boxed(lean_object* v_c_1944_, lean_object* v_v_1945_, lean_object* v_assumptions_1946_, lean_object* v_x_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
uint8_t v_a_boxed_1958_; lean_object* v_res_1959_; 
v_a_boxed_1958_ = lean_unbox(v_a_1951_);
v_res_1959_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1944_, v_v_1945_, v_assumptions_1946_, v_x_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_boxed_1958_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec_ref(v_assumptions_1946_);
lean_dec(v_c_1944_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof(lean_object* v_s_1960_, lean_object* v_c_1961_, lean_object* v_v_1962_, lean_object* v_assumptions_1963_, lean_object* v_x_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, uint8_t v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1961_, v_v_1962_, v_assumptions_1963_, v_x_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___boxed(lean_object* v_s_1976_, lean_object* v_c_1977_, lean_object* v_v_1978_, lean_object* v_assumptions_1979_, lean_object* v_x_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
uint8_t v_a_boxed_1991_; lean_object* v_res_1992_; 
v_a_boxed_1991_ = lean_unbox(v_a_1984_);
v_res_1992_ = l_Lean_Elab_Tactic_Omega_Justification_proof(v_s_1976_, v_c_1977_, v_v_1978_, v_assumptions_1979_, v_x_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_boxed_1991_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1983_);
lean_dec(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_assumptions_1979_);
lean_dec(v_c_1977_);
lean_dec_ref(v_s_1976_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_instToString___lam__0(lean_object* v_f_1993_){
_start:
{
lean_object* v_coeffs_1994_; lean_object* v_constraint_1995_; lean_object* v_justification_1996_; lean_object* v___x_1997_; 
v_coeffs_1994_ = lean_ctor_get(v_f_1993_, 0);
lean_inc(v_coeffs_1994_);
v_constraint_1995_ = lean_ctor_get(v_f_1993_, 1);
lean_inc_ref(v_constraint_1995_);
v_justification_1996_ = lean_ctor_get(v_f_1993_, 2);
lean_inc_ref(v_justification_1996_);
lean_dec_ref(v_f_1993_);
v___x_1997_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_1995_, v_coeffs_1994_, v_justification_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_tidy(lean_object* v_f_2000_){
_start:
{
lean_object* v_coeffs_2001_; lean_object* v_constraint_2002_; lean_object* v_justification_2003_; lean_object* v___x_2004_; 
v_coeffs_2001_ = lean_ctor_get(v_f_2000_, 0);
v_constraint_2002_ = lean_ctor_get(v_f_2000_, 1);
v_justification_2003_ = lean_ctor_get(v_f_2000_, 2);
lean_inc_ref(v_justification_2003_);
lean_inc(v_coeffs_2001_);
lean_inc_ref(v_constraint_2002_);
v___x_2004_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(v_constraint_2002_, v_coeffs_2001_, v_justification_2003_);
if (lean_obj_tag(v___x_2004_) == 0)
{
return v_f_2000_;
}
else
{
lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2016_; 
v_isSharedCheck_2016_ = !lean_is_exclusive(v_f_2000_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; lean_object* v_unused_2018_; lean_object* v_unused_2019_; 
v_unused_2017_ = lean_ctor_get(v_f_2000_, 2);
lean_dec(v_unused_2017_);
v_unused_2018_ = lean_ctor_get(v_f_2000_, 1);
lean_dec(v_unused_2018_);
v_unused_2019_ = lean_ctor_get(v_f_2000_, 0);
lean_dec(v_unused_2019_);
v___x_2006_ = v_f_2000_;
v_isShared_2007_ = v_isSharedCheck_2016_;
goto v_resetjp_2005_;
}
else
{
lean_dec(v_f_2000_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2016_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v_val_2008_; lean_object* v_snd_2009_; lean_object* v_fst_2010_; lean_object* v_fst_2011_; lean_object* v_snd_2012_; lean_object* v___x_2014_; 
v_val_2008_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_val_2008_);
lean_dec_ref_known(v___x_2004_, 1);
v_snd_2009_ = lean_ctor_get(v_val_2008_, 1);
lean_inc(v_snd_2009_);
v_fst_2010_ = lean_ctor_get(v_val_2008_, 0);
lean_inc(v_fst_2010_);
lean_dec(v_val_2008_);
v_fst_2011_ = lean_ctor_get(v_snd_2009_, 0);
lean_inc(v_fst_2011_);
v_snd_2012_ = lean_ctor_get(v_snd_2009_, 1);
lean_inc(v_snd_2012_);
lean_dec(v_snd_2009_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 2, v_snd_2012_);
lean_ctor_set(v___x_2006_, 1, v_fst_2010_);
lean_ctor_set(v___x_2006_, 0, v_fst_2011_);
v___x_2014_ = v___x_2006_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_fst_2011_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_fst_2010_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_snd_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_combo(lean_object* v_a_2020_, lean_object* v_f_2021_, lean_object* v_b_2022_, lean_object* v_g_2023_){
_start:
{
lean_object* v_coeffs_2024_; lean_object* v_constraint_2025_; lean_object* v_justification_2026_; lean_object* v_coeffs_2027_; lean_object* v_constraint_2028_; lean_object* v_justification_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2039_; 
v_coeffs_2024_ = lean_ctor_get(v_f_2021_, 0);
lean_inc(v_coeffs_2024_);
v_constraint_2025_ = lean_ctor_get(v_f_2021_, 1);
lean_inc_ref(v_constraint_2025_);
v_justification_2026_ = lean_ctor_get(v_f_2021_, 2);
lean_inc_ref(v_justification_2026_);
lean_dec_ref(v_f_2021_);
v_coeffs_2027_ = lean_ctor_get(v_g_2023_, 0);
v_constraint_2028_ = lean_ctor_get(v_g_2023_, 1);
v_justification_2029_ = lean_ctor_get(v_g_2023_, 2);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_g_2023_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2031_ = v_g_2023_;
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_justification_2029_);
lean_inc(v_constraint_2028_);
lean_inc(v_coeffs_2027_);
lean_dec(v_g_2023_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
lean_inc(v_coeffs_2027_);
lean_inc(v_coeffs_2024_);
v___x_2033_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_2020_, v_b_2022_, v_coeffs_2024_, v_coeffs_2027_);
lean_inc_ref(v_constraint_2028_);
lean_inc(v_b_2022_);
lean_inc_ref(v_constraint_2025_);
lean_inc(v_a_2020_);
v___x_2034_ = l_Lean_Omega_Constraint_combo(v_a_2020_, v_constraint_2025_, v_b_2022_, v_constraint_2028_);
v___x_2035_ = lean_alloc_ctor(3, 8, 0);
lean_ctor_set(v___x_2035_, 0, v_constraint_2025_);
lean_ctor_set(v___x_2035_, 1, v_constraint_2028_);
lean_ctor_set(v___x_2035_, 2, v_coeffs_2024_);
lean_ctor_set(v___x_2035_, 3, v_coeffs_2027_);
lean_ctor_set(v___x_2035_, 4, v_a_2020_);
lean_ctor_set(v___x_2035_, 5, v_justification_2026_);
lean_ctor_set(v___x_2035_, 6, v_b_2022_);
lean_ctor_set(v___x_2035_, 7, v_justification_2029_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 2, v___x_2035_);
lean_ctor_set(v___x_2031_, 1, v___x_2034_);
lean_ctor_set(v___x_2031_, 0, v___x_2033_);
v___x_2037_ = v___x_2031_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2038_, 2, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__10));
v___x_2066_ = l_Lean_mkAtom(v___x_2065_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2067_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11);
v___x_2068_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2069_ = lean_array_push(v___x_2068_, v___x_2067_);
return v___x_2069_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2070_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12);
v___x_2071_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9));
v___x_2072_ = lean_box(2);
v___x_2073_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
lean_ctor_set(v___x_2073_, 1, v___x_2071_);
lean_ctor_set(v___x_2073_, 2, v___x_2070_);
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13);
v___x_2075_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2076_ = lean_array_push(v___x_2075_, v___x_2074_);
return v___x_2076_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2077_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14);
v___x_2078_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7));
v___x_2079_ = lean_box(2);
v___x_2080_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v___x_2078_);
lean_ctor_set(v___x_2080_, 2, v___x_2077_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15);
v___x_2082_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2083_ = lean_array_push(v___x_2082_, v___x_2081_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2084_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16);
v___x_2085_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5));
v___x_2086_ = lean_box(2);
v___x_2087_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v___x_2085_);
lean_ctor_set(v___x_2087_, 2, v___x_2084_);
return v___x_2087_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17);
v___x_2089_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2090_ = lean_array_push(v___x_2089_, v___x_2088_);
return v___x_2090_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2091_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18);
v___x_2092_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2));
v___x_2093_ = lean_box(2);
v___x_2094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v___x_2092_);
lean_ctor_set(v___x_2094_, 2, v___x_2091_);
return v___x_2094_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam(void){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19);
return v___x_2095_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_isEmpty(lean_object* v_p_2096_){
_start:
{
lean_object* v_constraints_2097_; lean_object* v_size_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v_constraints_2097_ = lean_ctor_get(v_p_2096_, 2);
v_size_2098_ = lean_ctor_get(v_constraints_2097_, 0);
v___x_2099_ = lean_unsigned_to_nat(0u);
v___x_2100_ = lean_nat_dec_eq(v_size_2098_, v___x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_isEmpty___boxed(lean_object* v_p_2101_){
_start:
{
uint8_t v_res_2102_; lean_object* v_r_2103_; 
v_res_2102_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2101_);
lean_dec_ref(v_p_2101_);
v_r_2103_ = lean_box(v_res_2102_);
return v_r_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object* v_a_2104_, lean_object* v_b_2105_, lean_object* v_d_2106_){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v_a_2104_);
lean_ctor_set(v___x_2107_, 1, v_b_2105_);
v___x_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set(v___x_2108_, 1, v_d_2106_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object* v___x_2109_, lean_object* v_x_2110_){
_start:
{
lean_object* v_snd_2111_; lean_object* v_constraint_2112_; lean_object* v_fst_2113_; lean_object* v_lowerBound_2114_; lean_object* v_upperBound_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___y_2120_; lean_object* v___y_2121_; 
v_snd_2111_ = lean_ctor_get(v_x_2110_, 1);
v_constraint_2112_ = lean_ctor_get(v_snd_2111_, 1);
lean_inc_ref(v_constraint_2112_);
v_fst_2113_ = lean_ctor_get(v_x_2110_, 0);
lean_inc(v_fst_2113_);
lean_dec_ref(v_x_2110_);
v_lowerBound_2114_ = lean_ctor_get(v_constraint_2112_, 0);
lean_inc(v_lowerBound_2114_);
v_upperBound_2115_ = lean_ctor_get(v_constraint_2112_, 1);
lean_inc(v_upperBound_2115_);
lean_dec_ref(v_constraint_2112_);
v___x_2116_ = l_List_toString___redArg(v___x_2109_, v_fst_2113_);
v___x_2117_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_2118_ = lean_string_append(v___x_2116_, v___x_2117_);
if (lean_obj_tag(v_lowerBound_2114_) == 0)
{
if (lean_obj_tag(v_upperBound_2115_) == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_2127_ = lean_string_append(v___x_2118_, v___x_2126_);
return v___x_2127_;
}
else
{
lean_object* v_val_2128_; lean_object* v___x_2129_; lean_object* v___y_2131_; lean_object* v_intZero_2136_; uint8_t v_isNeg_2137_; 
v_val_2128_ = lean_ctor_get(v_upperBound_2115_, 0);
lean_inc(v_val_2128_);
lean_dec_ref_known(v_upperBound_2115_, 1);
v___x_2129_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_2136_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2137_ = lean_int_dec_lt(v_val_2128_, v_intZero_2136_);
if (v_isNeg_2137_ == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_nat_abs(v_val_2128_);
lean_dec(v_val_2128_);
v___x_2139_ = l_Nat_reprFast(v_a_2138_);
v___y_2131_ = v___x_2139_;
goto v___jp_2130_;
}
else
{
lean_object* v_abs_2140_; lean_object* v_one_2141_; lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_abs_2140_ = lean_nat_abs(v_val_2128_);
lean_dec(v_val_2128_);
v_one_2141_ = lean_unsigned_to_nat(1u);
v_a_2142_ = lean_nat_sub(v_abs_2140_, v_one_2141_);
lean_dec(v_abs_2140_);
v___x_2143_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2144_ = lean_nat_add(v_a_2142_, v_one_2141_);
lean_dec(v_a_2142_);
v___x_2145_ = l_Nat_reprFast(v___x_2144_);
v___x_2146_ = lean_string_append(v___x_2143_, v___x_2145_);
lean_dec_ref(v___x_2145_);
v___y_2131_ = v___x_2146_;
goto v___jp_2130_;
}
v___jp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2132_ = lean_string_append(v___x_2129_, v___y_2131_);
lean_dec_ref(v___y_2131_);
v___x_2133_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2134_ = lean_string_append(v___x_2132_, v___x_2133_);
v___x_2135_ = lean_string_append(v___x_2118_, v___x_2134_);
lean_dec_ref(v___x_2134_);
return v___x_2135_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_2115_) == 0)
{
lean_object* v_val_2147_; lean_object* v___x_2148_; lean_object* v___y_2150_; lean_object* v_intZero_2155_; uint8_t v_isNeg_2156_; 
v_val_2147_ = lean_ctor_get(v_lowerBound_2114_, 0);
lean_inc(v_val_2147_);
lean_dec_ref_known(v_lowerBound_2114_, 1);
v___x_2148_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2155_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2156_ = lean_int_dec_lt(v_val_2147_, v_intZero_2155_);
if (v_isNeg_2156_ == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2158_; 
v_a_2157_ = lean_nat_abs(v_val_2147_);
lean_dec(v_val_2147_);
v___x_2158_ = l_Nat_reprFast(v_a_2157_);
v___y_2150_ = v___x_2158_;
goto v___jp_2149_;
}
else
{
lean_object* v_abs_2159_; lean_object* v_one_2160_; lean_object* v_a_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v_abs_2159_ = lean_nat_abs(v_val_2147_);
lean_dec(v_val_2147_);
v_one_2160_ = lean_unsigned_to_nat(1u);
v_a_2161_ = lean_nat_sub(v_abs_2159_, v_one_2160_);
lean_dec(v_abs_2159_);
v___x_2162_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2163_ = lean_nat_add(v_a_2161_, v_one_2160_);
lean_dec(v_a_2161_);
v___x_2164_ = l_Nat_reprFast(v___x_2163_);
v___x_2165_ = lean_string_append(v___x_2162_, v___x_2164_);
lean_dec_ref(v___x_2164_);
v___y_2150_ = v___x_2165_;
goto v___jp_2149_;
}
v___jp_2149_:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2151_ = lean_string_append(v___x_2148_, v___y_2150_);
lean_dec_ref(v___y_2150_);
v___x_2152_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_2153_ = lean_string_append(v___x_2151_, v___x_2152_);
v___x_2154_ = lean_string_append(v___x_2118_, v___x_2153_);
lean_dec_ref(v___x_2153_);
return v___x_2154_;
}
}
else
{
lean_object* v_val_2166_; lean_object* v_val_2167_; uint8_t v___x_2168_; 
v_val_2166_ = lean_ctor_get(v_lowerBound_2114_, 0);
lean_inc(v_val_2166_);
lean_dec_ref_known(v_lowerBound_2114_, 1);
v_val_2167_ = lean_ctor_get(v_upperBound_2115_, 0);
lean_inc(v_val_2167_);
lean_dec_ref_known(v_upperBound_2115_, 1);
v___x_2168_ = lean_int_dec_lt(v_val_2167_, v_val_2166_);
if (v___x_2168_ == 0)
{
uint8_t v___x_2169_; 
v___x_2169_ = lean_int_dec_eq(v_val_2166_, v_val_2167_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___y_2172_; lean_object* v_intZero_2187_; uint8_t v_isNeg_2188_; 
v___x_2170_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2187_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2188_ = lean_int_dec_lt(v_val_2166_, v_intZero_2187_);
if (v_isNeg_2188_ == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; 
v_a_2189_ = lean_nat_abs(v_val_2166_);
lean_dec(v_val_2166_);
v___x_2190_ = l_Nat_reprFast(v_a_2189_);
v___y_2172_ = v___x_2190_;
goto v___jp_2171_;
}
else
{
lean_object* v_abs_2191_; lean_object* v_one_2192_; lean_object* v_a_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v_abs_2191_ = lean_nat_abs(v_val_2166_);
lean_dec(v_val_2166_);
v_one_2192_ = lean_unsigned_to_nat(1u);
v_a_2193_ = lean_nat_sub(v_abs_2191_, v_one_2192_);
lean_dec(v_abs_2191_);
v___x_2194_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2195_ = lean_nat_add(v_a_2193_, v_one_2192_);
lean_dec(v_a_2193_);
v___x_2196_ = l_Nat_reprFast(v___x_2195_);
v___x_2197_ = lean_string_append(v___x_2194_, v___x_2196_);
lean_dec_ref(v___x_2196_);
v___y_2172_ = v___x_2197_;
goto v___jp_2171_;
}
v___jp_2171_:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v_intZero_2176_; uint8_t v_isNeg_2177_; 
v___x_2173_ = lean_string_append(v___x_2170_, v___y_2172_);
lean_dec_ref(v___y_2172_);
v___x_2174_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_2175_ = lean_string_append(v___x_2173_, v___x_2174_);
v_intZero_2176_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2177_ = lean_int_dec_lt(v_val_2167_, v_intZero_2176_);
if (v_isNeg_2177_ == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; 
v_a_2178_ = lean_nat_abs(v_val_2167_);
lean_dec(v_val_2167_);
v___x_2179_ = l_Nat_reprFast(v_a_2178_);
v___y_2120_ = v___x_2175_;
v___y_2121_ = v___x_2179_;
goto v___jp_2119_;
}
else
{
lean_object* v_abs_2180_; lean_object* v_one_2181_; lean_object* v_a_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v_abs_2180_ = lean_nat_abs(v_val_2167_);
lean_dec(v_val_2167_);
v_one_2181_ = lean_unsigned_to_nat(1u);
v_a_2182_ = lean_nat_sub(v_abs_2180_, v_one_2181_);
lean_dec(v_abs_2180_);
v___x_2183_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2184_ = lean_nat_add(v_a_2182_, v_one_2181_);
lean_dec(v_a_2182_);
v___x_2185_ = l_Nat_reprFast(v___x_2184_);
v___x_2186_ = lean_string_append(v___x_2183_, v___x_2185_);
lean_dec_ref(v___x_2185_);
v___y_2120_ = v___x_2175_;
v___y_2121_ = v___x_2186_;
goto v___jp_2119_;
}
}
}
else
{
lean_object* v___x_2198_; lean_object* v___y_2200_; lean_object* v_intZero_2205_; uint8_t v_isNeg_2206_; 
lean_dec(v_val_2167_);
v___x_2198_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_2205_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2206_ = lean_int_dec_lt(v_val_2166_, v_intZero_2205_);
if (v_isNeg_2206_ == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2208_; 
v_a_2207_ = lean_nat_abs(v_val_2166_);
lean_dec(v_val_2166_);
v___x_2208_ = l_Nat_reprFast(v_a_2207_);
v___y_2200_ = v___x_2208_;
goto v___jp_2199_;
}
else
{
lean_object* v_abs_2209_; lean_object* v_one_2210_; lean_object* v_a_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v_abs_2209_ = lean_nat_abs(v_val_2166_);
lean_dec(v_val_2166_);
v_one_2210_ = lean_unsigned_to_nat(1u);
v_a_2211_ = lean_nat_sub(v_abs_2209_, v_one_2210_);
lean_dec(v_abs_2209_);
v___x_2212_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2213_ = lean_nat_add(v_a_2211_, v_one_2210_);
lean_dec(v_a_2211_);
v___x_2214_ = l_Nat_reprFast(v___x_2213_);
v___x_2215_ = lean_string_append(v___x_2212_, v___x_2214_);
lean_dec_ref(v___x_2214_);
v___y_2200_ = v___x_2215_;
goto v___jp_2199_;
}
v___jp_2199_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2201_ = lean_string_append(v___x_2198_, v___y_2200_);
lean_dec_ref(v___y_2200_);
v___x_2202_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_2203_ = lean_string_append(v___x_2201_, v___x_2202_);
v___x_2204_ = lean_string_append(v___x_2118_, v___x_2203_);
lean_dec_ref(v___x_2203_);
return v___x_2204_;
}
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_dec(v_val_2167_);
lean_dec(v_val_2166_);
v___x_2216_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_2217_ = lean_string_append(v___x_2118_, v___x_2216_);
return v___x_2217_;
}
}
}
v___jp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2122_ = lean_string_append(v___y_2120_, v___y_2121_);
lean_dec_ref(v___y_2121_);
v___x_2123_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2124_ = lean_string_append(v___x_2122_, v___x_2123_);
v___x_2125_ = lean_string_append(v___x_2118_, v___x_2124_);
lean_dec_ref(v___x_2124_);
return v___x_2125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2(lean_object* v___x_2218_, lean_object* v___f_2219_, lean_object* v_l_2220_, lean_object* v_acc_2221_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2218_, v___f_2219_, v_acc_2221_, v_l_2220_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3(lean_object* v___f_2244_, lean_object* v___f_2245_, lean_object* v_p_2246_){
_start:
{
uint8_t v_possible_2247_; 
v_possible_2247_ = lean_ctor_get_uint8(v_p_2246_, sizeof(void*)*7);
if (v_possible_2247_ == 0)
{
lean_object* v___x_2248_; 
lean_dec_ref(v_p_2246_);
lean_dec_ref(v___f_2245_);
lean_dec_ref(v___f_2244_);
v___x_2248_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
return v___x_2248_;
}
else
{
lean_object* v_constraints_2249_; uint8_t v___x_2250_; 
v_constraints_2249_ = lean_ctor_get(v_p_2246_, 2);
lean_inc_ref(v_constraints_2249_);
v___x_2250_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2246_);
lean_dec_ref(v_p_2246_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v_buckets_2252_; lean_object* v___x_2253_; lean_object* v___y_2255_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2251_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10));
v_buckets_2252_ = lean_ctor_get(v_constraints_2249_, 1);
lean_inc_ref(v_buckets_2252_);
lean_dec_ref(v_constraints_2249_);
v___x_2253_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_2259_ = lean_box(0);
v___x_2260_ = lean_array_get_size(v_buckets_2252_);
v___x_2261_ = lean_unsigned_to_nat(0u);
v___x_2262_ = lean_nat_dec_lt(v___x_2261_, v___x_2260_);
if (v___x_2262_ == 0)
{
lean_dec_ref(v_buckets_2252_);
lean_dec_ref(v___f_2245_);
v___y_2255_ = v___x_2259_;
goto v___jp_2254_;
}
else
{
lean_object* v___f_2263_; size_t v___x_2264_; size_t v___x_2265_; lean_object* v___x_2266_; 
v___f_2263_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2), 4, 2);
lean_closure_set(v___f_2263_, 0, v___x_2251_);
lean_closure_set(v___f_2263_, 1, v___f_2245_);
v___x_2264_ = lean_usize_of_nat(v___x_2260_);
v___x_2265_ = ((size_t)0ULL);
v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2251_, v___f_2263_, v_buckets_2252_, v___x_2264_, v___x_2265_, v___x_2259_);
v___y_2255_ = v___x_2266_;
goto v___jp_2254_;
}
v___jp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = lean_box(0);
v___x_2257_ = l_List_mapTR_loop___redArg(v___f_2244_, v___y_2255_, v___x_2256_);
v___x_2258_ = l_String_intercalate(v___x_2253_, v___x_2257_);
return v___x_2258_;
}
}
else
{
lean_object* v___x_2267_; 
lean_dec_ref(v_constraints_2249_);
lean_dec_ref(v___f_2245_);
lean_dec_ref(v___f_2244_);
v___x_2267_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
return v___x_2267_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = lean_box(0);
v___x_2283_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1));
v___x_2284_ = l_Lean_Expr_const___override(v___x_2283_, v___x_2282_);
return v___x_2284_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = lean_box(0);
v___x_2291_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5));
v___x_2292_ = l_Lean_Expr_const___override(v___x_2291_, v___x_2290_);
return v___x_2292_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = lean_box(0);
v___x_2300_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8));
v___x_2301_ = l_Lean_Expr_const___override(v___x_2300_, v___x_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse(lean_object* v_s_2302_, lean_object* v_x_2303_, lean_object* v_j_2304_, lean_object* v_assumptions_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, uint8_t v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2307_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc_n(v_a_2317_, 2);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_2303_, v_a_2317_, v_assumptions_2305_, v_j_2304_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; lean_object* v_lowerBound_2321_; lean_object* v_upperBound_2322_; lean_object* v_nil_2323_; lean_object* v_cons_2324_; lean_object* v___x_2325_; lean_object* v___y_2327_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___x_2350_; lean_object* v___y_2352_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2320_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_lowerBound_2321_ = lean_ctor_get(v_s_2302_, 0);
v_upperBound_2322_ = lean_ctor_get(v_s_2302_, 1);
v_nil_2323_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2324_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2325_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2323_, v_cons_2324_, v_x_2303_);
v___x_2350_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
if (lean_obj_tag(v_lowerBound_2321_) == 0)
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_2352_ = v___x_2368_;
goto v___jp_2351_;
}
else
{
lean_object* v_val_2369_; lean_object* v___x_2370_; lean_object* v___y_2372_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v_val_2369_ = lean_ctor_get(v_lowerBound_2321_, 0);
v___x_2370_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2374_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2375_ = lean_int_dec_le(v___x_2374_, v_val_2369_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2376_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2377_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2378_ = lean_int_neg(v_val_2369_);
v___x_2379_ = l_Int_toNat(v___x_2378_);
lean_dec(v___x_2378_);
v___x_2380_ = l_Lean_instToExprInt_mkNat(v___x_2379_);
v___x_2381_ = l_Lean_mkApp3(v___x_2376_, v___x_2320_, v___x_2377_, v___x_2380_);
v___y_2372_ = v___x_2381_;
goto v___jp_2371_;
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = l_Int_toNat(v_val_2369_);
v___x_2383_ = l_Lean_instToExprInt_mkNat(v___x_2382_);
v___y_2372_ = v___x_2383_;
goto v___jp_2371_;
}
v___jp_2371_:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Lean_mkAppB(v___x_2370_, v___x_2320_, v___y_2372_);
v___y_2352_ = v___x_2373_;
goto v___jp_2351_;
}
}
v___jp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2328_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2);
lean_inc_ref(v___y_2327_);
v___x_2329_ = l_Lean_Expr_app___override(v___x_2328_, v___y_2327_);
v___x_2330_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6);
v___x_2331_ = l_Lean_Meta_mkEq(v___x_2329_, v___x_2330_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2333_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2333_ = l_Lean_Meta_mkDecideProof(v_a_2332_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2343_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2343_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2343_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2338_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9);
v___x_2339_ = l_Lean_mkApp5(v___x_2338_, v___y_2327_, v_a_2334_, v___x_2325_, v_a_2317_, v_a_2319_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2339_);
v___x_2341_ = v___x_2336_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
else
{
lean_dec_ref(v___y_2327_);
lean_dec_ref(v___x_2325_);
lean_dec(v_a_2319_);
lean_dec(v_a_2317_);
return v___x_2333_;
}
}
else
{
lean_dec_ref(v___y_2327_);
lean_dec_ref(v___x_2325_);
lean_dec(v_a_2319_);
lean_dec(v_a_2317_);
return v___x_2331_;
}
}
v___jp_2344_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
lean_inc_ref(v___y_2345_);
v___x_2348_ = l_Lean_mkAppB(v___y_2345_, v___x_2320_, v___y_2347_);
v___x_2349_ = l_Lean_Expr_app___override(v___y_2346_, v___x_2348_);
v___y_2327_ = v___x_2349_;
goto v___jp_2326_;
}
v___jp_2351_:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Expr_app___override(v___x_2350_, v___y_2352_);
if (lean_obj_tag(v_upperBound_2322_) == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_2355_ = l_Lean_Expr_app___override(v___x_2353_, v___x_2354_);
v___y_2327_ = v___x_2355_;
goto v___jp_2326_;
}
else
{
lean_object* v_val_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v_val_2356_ = lean_ctor_get(v_upperBound_2322_, 0);
v___x_2357_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2358_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2359_ = lean_int_dec_le(v___x_2358_, v_val_2356_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2360_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2361_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2362_ = lean_int_neg(v_val_2356_);
v___x_2363_ = l_Int_toNat(v___x_2362_);
lean_dec(v___x_2362_);
v___x_2364_ = l_Lean_instToExprInt_mkNat(v___x_2363_);
v___x_2365_ = l_Lean_mkApp3(v___x_2360_, v___x_2320_, v___x_2361_, v___x_2364_);
v___y_2345_ = v___x_2357_;
v___y_2346_ = v___x_2353_;
v___y_2347_ = v___x_2365_;
goto v___jp_2344_;
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = l_Int_toNat(v_val_2356_);
v___x_2367_ = l_Lean_instToExprInt_mkNat(v___x_2366_);
v___y_2345_ = v___x_2357_;
v___y_2346_ = v___x_2353_;
v___y_2347_ = v___x_2367_;
goto v___jp_2344_;
}
}
}
}
else
{
lean_dec(v_a_2317_);
return v___x_2318_;
}
}
else
{
lean_dec_ref(v_j_2304_);
return v___x_2316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed(lean_object* v_s_2384_, lean_object* v_x_2385_, lean_object* v_j_2386_, lean_object* v_assumptions_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
uint8_t v_a_boxed_2398_; lean_object* v_res_2399_; 
v_a_boxed_2398_ = lean_unbox(v_a_2391_);
v_res_2399_ = l_Lean_Elab_Tactic_Omega_Problem_proveFalse(v_s_2384_, v_x_2385_, v_j_2386_, v_assumptions_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_boxed_2398_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_assumptions_2387_);
lean_dec(v_x_2385_);
lean_dec_ref(v_s_2384_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0(lean_object* v_constraint_2400_, lean_object* v_coeffs_2401_, lean_object* v_justification_2402_, lean_object* v_x_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_2400_, v_coeffs_2401_, v_justification_2402_);
return v___x_2404_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(lean_object* v_a_2405_, lean_object* v_x_2406_){
_start:
{
if (lean_obj_tag(v_x_2406_) == 0)
{
uint8_t v___x_2407_; 
v___x_2407_ = 0;
return v___x_2407_;
}
else
{
lean_object* v_key_2408_; lean_object* v_tail_2409_; uint8_t v___x_2410_; 
v_key_2408_ = lean_ctor_get(v_x_2406_, 0);
v_tail_2409_ = lean_ctor_get(v_x_2406_, 2);
v___x_2410_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2408_, v_a_2405_);
if (v___x_2410_ == 0)
{
v_x_2406_ = v_tail_2409_;
goto _start;
}
else
{
return v___x_2410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg___boxed(lean_object* v_a_2412_, lean_object* v_x_2413_){
_start:
{
uint8_t v_res_2414_; lean_object* v_r_2415_; 
v_res_2414_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2412_, v_x_2413_);
lean_dec(v_x_2413_);
lean_dec(v_a_2412_);
v_r_2415_ = lean_box(v_res_2414_);
return v_r_2415_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(uint64_t v_x_2416_, lean_object* v_x_2417_){
_start:
{
if (lean_obj_tag(v_x_2417_) == 0)
{
return v_x_2416_;
}
else
{
lean_object* v_head_2418_; lean_object* v_tail_2419_; lean_object* v_intZero_2420_; uint8_t v_isNeg_2421_; 
v_head_2418_ = lean_ctor_get(v_x_2417_, 0);
v_tail_2419_ = lean_ctor_get(v_x_2417_, 1);
v_intZero_2420_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2421_ = lean_int_dec_lt(v_head_2418_, v_intZero_2420_);
if (v_isNeg_2421_ == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; uint64_t v___x_2425_; uint64_t v___x_2426_; 
v_a_2422_ = lean_nat_abs(v_head_2418_);
v___x_2423_ = lean_unsigned_to_nat(2u);
v___x_2424_ = lean_nat_mul(v___x_2423_, v_a_2422_);
lean_dec(v_a_2422_);
v___x_2425_ = lean_uint64_of_nat(v___x_2424_);
lean_dec(v___x_2424_);
v___x_2426_ = lean_uint64_mix_hash(v_x_2416_, v___x_2425_);
v_x_2416_ = v___x_2426_;
v_x_2417_ = v_tail_2419_;
goto _start;
}
else
{
lean_object* v_abs_2428_; lean_object* v_one_2429_; lean_object* v_a_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; uint64_t v___x_2434_; uint64_t v___x_2435_; 
v_abs_2428_ = lean_nat_abs(v_head_2418_);
v_one_2429_ = lean_unsigned_to_nat(1u);
v_a_2430_ = lean_nat_sub(v_abs_2428_, v_one_2429_);
lean_dec(v_abs_2428_);
v___x_2431_ = lean_unsigned_to_nat(2u);
v___x_2432_ = lean_nat_mul(v___x_2431_, v_a_2430_);
lean_dec(v_a_2430_);
v___x_2433_ = lean_nat_add(v___x_2432_, v_one_2429_);
lean_dec(v___x_2432_);
v___x_2434_ = lean_uint64_of_nat(v___x_2433_);
lean_dec(v___x_2433_);
v___x_2435_ = lean_uint64_mix_hash(v_x_2416_, v___x_2434_);
v_x_2416_ = v___x_2435_;
v_x_2417_ = v_tail_2419_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0___boxed(lean_object* v_x_2437_, lean_object* v_x_2438_){
_start:
{
uint64_t v_x_802__boxed_2439_; uint64_t v_res_2440_; lean_object* v_r_2441_; 
v_x_802__boxed_2439_ = lean_unbox_uint64(v_x_2437_);
lean_dec_ref(v_x_2437_);
v_res_2440_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v_x_802__boxed_2439_, v_x_2438_);
lean_dec(v_x_2438_);
v_r_2441_ = lean_box_uint64(v_res_2440_);
return v_r_2441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_2442_, lean_object* v_x_2443_){
_start:
{
if (lean_obj_tag(v_x_2443_) == 0)
{
return v_x_2442_;
}
else
{
lean_object* v_key_2444_; lean_object* v_value_2445_; lean_object* v_tail_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2470_; 
v_key_2444_ = lean_ctor_get(v_x_2443_, 0);
v_value_2445_ = lean_ctor_get(v_x_2443_, 1);
v_tail_2446_ = lean_ctor_get(v_x_2443_, 2);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_x_2443_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2448_ = v_x_2443_;
v_isShared_2449_ = v_isSharedCheck_2470_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_tail_2446_);
lean_inc(v_value_2445_);
lean_inc(v_key_2444_);
lean_dec(v_x_2443_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2470_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; uint64_t v___x_2451_; uint64_t v___x_2452_; uint64_t v___x_2453_; uint64_t v___x_2454_; uint64_t v_fold_2455_; uint64_t v___x_2456_; uint64_t v___x_2457_; uint64_t v___x_2458_; size_t v___x_2459_; size_t v___x_2460_; size_t v___x_2461_; size_t v___x_2462_; size_t v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2450_ = lean_array_get_size(v_x_2442_);
v___x_2451_ = 7ULL;
v___x_2452_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2451_, v_key_2444_);
v___x_2453_ = 32ULL;
v___x_2454_ = lean_uint64_shift_right(v___x_2452_, v___x_2453_);
v_fold_2455_ = lean_uint64_xor(v___x_2452_, v___x_2454_);
v___x_2456_ = 16ULL;
v___x_2457_ = lean_uint64_shift_right(v_fold_2455_, v___x_2456_);
v___x_2458_ = lean_uint64_xor(v_fold_2455_, v___x_2457_);
v___x_2459_ = lean_uint64_to_usize(v___x_2458_);
v___x_2460_ = lean_usize_of_nat(v___x_2450_);
v___x_2461_ = ((size_t)1ULL);
v___x_2462_ = lean_usize_sub(v___x_2460_, v___x_2461_);
v___x_2463_ = lean_usize_land(v___x_2459_, v___x_2462_);
v___x_2464_ = lean_array_uget_borrowed(v_x_2442_, v___x_2463_);
lean_inc(v___x_2464_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 2, v___x_2464_);
v___x_2466_ = v___x_2448_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_key_2444_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_value_2445_);
lean_ctor_set(v_reuseFailAlloc_2469_, 2, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; 
v___x_2467_ = lean_array_uset(v_x_2442_, v___x_2463_, v___x_2466_);
v_x_2442_ = v___x_2467_;
v_x_2443_ = v_tail_2446_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(lean_object* v_i_2471_, lean_object* v_source_2472_, lean_object* v_target_2473_){
_start:
{
lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2474_ = lean_array_get_size(v_source_2472_);
v___x_2475_ = lean_nat_dec_lt(v_i_2471_, v___x_2474_);
if (v___x_2475_ == 0)
{
lean_dec_ref(v_source_2472_);
lean_dec(v_i_2471_);
return v_target_2473_;
}
else
{
lean_object* v_es_2476_; lean_object* v___x_2477_; lean_object* v_source_2478_; lean_object* v_target_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_es_2476_ = lean_array_fget(v_source_2472_, v_i_2471_);
v___x_2477_ = lean_box(0);
v_source_2478_ = lean_array_fset(v_source_2472_, v_i_2471_, v___x_2477_);
v_target_2479_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_target_2473_, v_es_2476_);
v___x_2480_ = lean_unsigned_to_nat(1u);
v___x_2481_ = lean_nat_add(v_i_2471_, v___x_2480_);
lean_dec(v_i_2471_);
v_i_2471_ = v___x_2481_;
v_source_2472_ = v_source_2478_;
v_target_2473_ = v_target_2479_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(lean_object* v_data_2483_){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v_nbuckets_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2484_ = lean_array_get_size(v_data_2483_);
v___x_2485_ = lean_unsigned_to_nat(2u);
v_nbuckets_2486_ = lean_nat_mul(v___x_2484_, v___x_2485_);
v___x_2487_ = lean_unsigned_to_nat(0u);
v___x_2488_ = lean_box(0);
v___x_2489_ = lean_mk_array(v_nbuckets_2486_, v___x_2488_);
v___x_2490_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v___x_2487_, v_data_2483_, v___x_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(lean_object* v_m_2491_, lean_object* v_a_2492_, lean_object* v_b_2493_){
_start:
{
lean_object* v_size_2494_; lean_object* v_buckets_2495_; lean_object* v___x_2496_; uint64_t v___x_2497_; uint64_t v___x_2498_; uint64_t v___x_2499_; uint64_t v___x_2500_; uint64_t v_fold_2501_; uint64_t v___x_2502_; uint64_t v___x_2503_; uint64_t v___x_2504_; size_t v___x_2505_; size_t v___x_2506_; size_t v___x_2507_; size_t v___x_2508_; size_t v___x_2509_; lean_object* v_bkt_2510_; uint8_t v___x_2511_; 
v_size_2494_ = lean_ctor_get(v_m_2491_, 0);
v_buckets_2495_ = lean_ctor_get(v_m_2491_, 1);
v___x_2496_ = lean_array_get_size(v_buckets_2495_);
v___x_2497_ = 7ULL;
v___x_2498_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2497_, v_a_2492_);
v___x_2499_ = 32ULL;
v___x_2500_ = lean_uint64_shift_right(v___x_2498_, v___x_2499_);
v_fold_2501_ = lean_uint64_xor(v___x_2498_, v___x_2500_);
v___x_2502_ = 16ULL;
v___x_2503_ = lean_uint64_shift_right(v_fold_2501_, v___x_2502_);
v___x_2504_ = lean_uint64_xor(v_fold_2501_, v___x_2503_);
v___x_2505_ = lean_uint64_to_usize(v___x_2504_);
v___x_2506_ = lean_usize_of_nat(v___x_2496_);
v___x_2507_ = ((size_t)1ULL);
v___x_2508_ = lean_usize_sub(v___x_2506_, v___x_2507_);
v___x_2509_ = lean_usize_land(v___x_2505_, v___x_2508_);
v_bkt_2510_ = lean_array_uget_borrowed(v_buckets_2495_, v___x_2509_);
v___x_2511_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2492_, v_bkt_2510_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2532_; 
lean_inc_ref(v_buckets_2495_);
lean_inc(v_size_2494_);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_m_2491_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; lean_object* v_unused_2534_; 
v_unused_2533_ = lean_ctor_get(v_m_2491_, 1);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v_m_2491_, 0);
lean_dec(v_unused_2534_);
v___x_2513_ = v_m_2491_;
v_isShared_2514_ = v_isSharedCheck_2532_;
goto v_resetjp_2512_;
}
else
{
lean_dec(v_m_2491_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2532_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v_size_x27_2516_; lean_object* v___x_2517_; lean_object* v_buckets_x27_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2515_ = lean_unsigned_to_nat(1u);
v_size_x27_2516_ = lean_nat_add(v_size_2494_, v___x_2515_);
lean_dec(v_size_2494_);
lean_inc(v_bkt_2510_);
v___x_2517_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2517_, 0, v_a_2492_);
lean_ctor_set(v___x_2517_, 1, v_b_2493_);
lean_ctor_set(v___x_2517_, 2, v_bkt_2510_);
v_buckets_x27_2518_ = lean_array_uset(v_buckets_2495_, v___x_2509_, v___x_2517_);
v___x_2519_ = lean_unsigned_to_nat(4u);
v___x_2520_ = lean_nat_mul(v_size_x27_2516_, v___x_2519_);
v___x_2521_ = lean_unsigned_to_nat(3u);
v___x_2522_ = lean_nat_div(v___x_2520_, v___x_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_array_get_size(v_buckets_x27_2518_);
v___x_2524_ = lean_nat_dec_le(v___x_2522_, v___x_2523_);
lean_dec(v___x_2522_);
if (v___x_2524_ == 0)
{
lean_object* v_val_2525_; lean_object* v___x_2527_; 
v_val_2525_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2518_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 1, v_val_2525_);
lean_ctor_set(v___x_2513_, 0, v_size_x27_2516_);
v___x_2527_ = v___x_2513_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_size_x27_2516_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_val_2525_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
else
{
lean_object* v___x_2530_; 
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 1, v_buckets_x27_2518_);
lean_ctor_set(v___x_2513_, 0, v_size_x27_2516_);
v___x_2530_ = v___x_2513_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_size_x27_2516_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_buckets_x27_2518_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
else
{
lean_dec(v_b_2493_);
lean_dec(v_a_2492_);
return v_m_2491_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(lean_object* v_a_2535_, lean_object* v_b_2536_, lean_object* v_x_2537_){
_start:
{
if (lean_obj_tag(v_x_2537_) == 0)
{
lean_dec(v_b_2536_);
lean_dec(v_a_2535_);
return v_x_2537_;
}
else
{
lean_object* v_key_2538_; lean_object* v_value_2539_; lean_object* v_tail_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2552_; 
v_key_2538_ = lean_ctor_get(v_x_2537_, 0);
v_value_2539_ = lean_ctor_get(v_x_2537_, 1);
v_tail_2540_ = lean_ctor_get(v_x_2537_, 2);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_x_2537_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2542_ = v_x_2537_;
v_isShared_2543_ = v_isSharedCheck_2552_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_tail_2540_);
lean_inc(v_value_2539_);
lean_inc(v_key_2538_);
lean_dec(v_x_2537_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2552_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
uint8_t v___x_2544_; 
v___x_2544_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2538_, v_a_2535_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2545_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2535_, v_b_2536_, v_tail_2540_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 2, v___x_2545_);
v___x_2547_ = v___x_2542_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_key_2538_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_value_2539_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
else
{
lean_object* v___x_2550_; 
lean_dec(v_value_2539_);
lean_dec(v_key_2538_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 1, v_b_2536_);
lean_ctor_set(v___x_2542_, 0, v_a_2535_);
v___x_2550_ = v___x_2542_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2535_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_b_2536_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v_tail_2540_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(lean_object* v_m_2553_, lean_object* v_a_2554_, lean_object* v_b_2555_){
_start:
{
lean_object* v_size_2556_; lean_object* v_buckets_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2601_; 
v_size_2556_ = lean_ctor_get(v_m_2553_, 0);
v_buckets_2557_ = lean_ctor_get(v_m_2553_, 1);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_m_2553_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2559_ = v_m_2553_;
v_isShared_2560_ = v_isSharedCheck_2601_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_buckets_2557_);
lean_inc(v_size_2556_);
lean_dec(v_m_2553_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2601_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; uint64_t v___x_2562_; uint64_t v___x_2563_; uint64_t v___x_2564_; uint64_t v___x_2565_; uint64_t v_fold_2566_; uint64_t v___x_2567_; uint64_t v___x_2568_; uint64_t v___x_2569_; size_t v___x_2570_; size_t v___x_2571_; size_t v___x_2572_; size_t v___x_2573_; size_t v___x_2574_; lean_object* v_bkt_2575_; uint8_t v___x_2576_; 
v___x_2561_ = lean_array_get_size(v_buckets_2557_);
v___x_2562_ = 7ULL;
v___x_2563_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2562_, v_a_2554_);
v___x_2564_ = 32ULL;
v___x_2565_ = lean_uint64_shift_right(v___x_2563_, v___x_2564_);
v_fold_2566_ = lean_uint64_xor(v___x_2563_, v___x_2565_);
v___x_2567_ = 16ULL;
v___x_2568_ = lean_uint64_shift_right(v_fold_2566_, v___x_2567_);
v___x_2569_ = lean_uint64_xor(v_fold_2566_, v___x_2568_);
v___x_2570_ = lean_uint64_to_usize(v___x_2569_);
v___x_2571_ = lean_usize_of_nat(v___x_2561_);
v___x_2572_ = ((size_t)1ULL);
v___x_2573_ = lean_usize_sub(v___x_2571_, v___x_2572_);
v___x_2574_ = lean_usize_land(v___x_2570_, v___x_2573_);
v_bkt_2575_ = lean_array_uget_borrowed(v_buckets_2557_, v___x_2574_);
v___x_2576_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2554_, v_bkt_2575_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; lean_object* v_size_x27_2578_; lean_object* v___x_2579_; lean_object* v_buckets_x27_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2577_ = lean_unsigned_to_nat(1u);
v_size_x27_2578_ = lean_nat_add(v_size_2556_, v___x_2577_);
lean_dec(v_size_2556_);
lean_inc(v_bkt_2575_);
v___x_2579_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2579_, 0, v_a_2554_);
lean_ctor_set(v___x_2579_, 1, v_b_2555_);
lean_ctor_set(v___x_2579_, 2, v_bkt_2575_);
v_buckets_x27_2580_ = lean_array_uset(v_buckets_2557_, v___x_2574_, v___x_2579_);
v___x_2581_ = lean_unsigned_to_nat(4u);
v___x_2582_ = lean_nat_mul(v_size_x27_2578_, v___x_2581_);
v___x_2583_ = lean_unsigned_to_nat(3u);
v___x_2584_ = lean_nat_div(v___x_2582_, v___x_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_array_get_size(v_buckets_x27_2580_);
v___x_2586_ = lean_nat_dec_le(v___x_2584_, v___x_2585_);
lean_dec(v___x_2584_);
if (v___x_2586_ == 0)
{
lean_object* v_val_2587_; lean_object* v___x_2589_; 
v_val_2587_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2580_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 1, v_val_2587_);
lean_ctor_set(v___x_2559_, 0, v_size_x27_2578_);
v___x_2589_ = v___x_2559_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_size_x27_2578_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_val_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
else
{
lean_object* v___x_2592_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 1, v_buckets_x27_2580_);
lean_ctor_set(v___x_2559_, 0, v_size_x27_2578_);
v___x_2592_ = v___x_2559_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_size_x27_2578_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v_buckets_x27_2580_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
else
{
lean_object* v___x_2594_; lean_object* v_buckets_x27_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
lean_inc(v_bkt_2575_);
v___x_2594_ = lean_box(0);
v_buckets_x27_2595_ = lean_array_uset(v_buckets_2557_, v___x_2574_, v___x_2594_);
v___x_2596_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2554_, v_b_2555_, v_bkt_2575_);
v___x_2597_ = lean_array_uset(v_buckets_x27_2595_, v___x_2574_, v___x_2596_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 1, v___x_2597_);
v___x_2599_ = v___x_2559_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_size_2556_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(lean_object* v_p_2602_, lean_object* v_x_2603_){
_start:
{
lean_object* v_coeffs_2604_; lean_object* v_constraint_2605_; lean_object* v_justification_2606_; uint8_t v___x_2607_; 
v_coeffs_2604_ = lean_ctor_get(v_x_2603_, 0);
lean_inc(v_coeffs_2604_);
v_constraint_2605_ = lean_ctor_get(v_x_2603_, 1);
lean_inc_ref(v_constraint_2605_);
v_justification_2606_ = lean_ctor_get(v_x_2603_, 2);
v___x_2607_ = l_Lean_Omega_Constraint_isImpossible(v_constraint_2605_);
if (v___x_2607_ == 0)
{
lean_object* v_assumptions_2608_; lean_object* v_numVars_2609_; lean_object* v_constraints_2610_; lean_object* v_equalities_2611_; lean_object* v_eliminations_2612_; uint8_t v_possible_2613_; lean_object* v_proveFalse_x3f_2614_; lean_object* v_explanation_x3f_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2633_; 
v_assumptions_2608_ = lean_ctor_get(v_p_2602_, 0);
v_numVars_2609_ = lean_ctor_get(v_p_2602_, 1);
v_constraints_2610_ = lean_ctor_get(v_p_2602_, 2);
v_equalities_2611_ = lean_ctor_get(v_p_2602_, 3);
v_eliminations_2612_ = lean_ctor_get(v_p_2602_, 4);
v_possible_2613_ = lean_ctor_get_uint8(v_p_2602_, sizeof(void*)*7);
v_proveFalse_x3f_2614_ = lean_ctor_get(v_p_2602_, 5);
v_explanation_x3f_2615_ = lean_ctor_get(v_p_2602_, 6);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_p_2602_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2617_ = v_p_2602_;
v_isShared_2618_ = v_isSharedCheck_2633_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_explanation_x3f_2615_);
lean_inc(v_proveFalse_x3f_2614_);
lean_inc(v_eliminations_2612_);
lean_inc(v_equalities_2611_);
lean_inc(v_constraints_2610_);
lean_inc(v_numVars_2609_);
lean_inc(v_assumptions_2608_);
lean_dec(v_p_2602_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2633_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___y_2620_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2631_ = l_List_lengthTR___redArg(v_coeffs_2604_);
v___x_2632_ = lean_nat_dec_le(v_numVars_2609_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_dec(v___x_2631_);
v___y_2620_ = v_numVars_2609_;
goto v___jp_2619_;
}
else
{
lean_dec(v_numVars_2609_);
v___y_2620_ = v___x_2631_;
goto v___jp_2619_;
}
v___jp_2619_:
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
lean_inc(v_coeffs_2604_);
v___x_2621_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_constraints_2610_, v_coeffs_2604_, v_x_2603_);
v___x_2622_ = l_Lean_Omega_Constraint_isExact(v_constraint_2605_);
lean_dec_ref(v_constraint_2605_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2624_; 
lean_dec(v_coeffs_2604_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 2, v___x_2621_);
lean_ctor_set(v___x_2617_, 1, v___y_2620_);
v___x_2624_ = v___x_2617_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_assumptions_2608_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v___y_2620_);
lean_ctor_set(v_reuseFailAlloc_2625_, 2, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2625_, 3, v_equalities_2611_);
lean_ctor_set(v_reuseFailAlloc_2625_, 4, v_eliminations_2612_);
lean_ctor_set(v_reuseFailAlloc_2625_, 5, v_proveFalse_x3f_2614_);
lean_ctor_set(v_reuseFailAlloc_2625_, 6, v_explanation_x3f_2615_);
lean_ctor_set_uint8(v_reuseFailAlloc_2625_, sizeof(void*)*7, v_possible_2613_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2626_ = lean_box(0);
v___x_2627_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_equalities_2611_, v_coeffs_2604_, v___x_2626_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 3, v___x_2627_);
lean_ctor_set(v___x_2617_, 2, v___x_2621_);
lean_ctor_set(v___x_2617_, 1, v___y_2620_);
v___x_2629_ = v___x_2617_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_assumptions_2608_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v___y_2620_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2630_, 3, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2630_, 4, v_eliminations_2612_);
lean_ctor_set(v_reuseFailAlloc_2630_, 5, v_proveFalse_x3f_2614_);
lean_ctor_set(v_reuseFailAlloc_2630_, 6, v_explanation_x3f_2615_);
lean_ctor_set_uint8(v_reuseFailAlloc_2630_, sizeof(void*)*7, v_possible_2613_);
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
}
else
{
lean_object* v_assumptions_2634_; lean_object* v_numVars_2635_; lean_object* v_constraints_2636_; lean_object* v_equalities_2637_; lean_object* v_eliminations_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2650_; 
lean_inc_ref(v_justification_2606_);
lean_dec_ref(v_x_2603_);
v_assumptions_2634_ = lean_ctor_get(v_p_2602_, 0);
v_numVars_2635_ = lean_ctor_get(v_p_2602_, 1);
v_constraints_2636_ = lean_ctor_get(v_p_2602_, 2);
v_equalities_2637_ = lean_ctor_get(v_p_2602_, 3);
v_eliminations_2638_ = lean_ctor_get(v_p_2602_, 4);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_p_2602_);
if (v_isSharedCheck_2650_ == 0)
{
lean_object* v_unused_2651_; lean_object* v_unused_2652_; 
v_unused_2651_ = lean_ctor_get(v_p_2602_, 6);
lean_dec(v_unused_2651_);
v_unused_2652_ = lean_ctor_get(v_p_2602_, 5);
lean_dec(v_unused_2652_);
v___x_2640_ = v_p_2602_;
v_isShared_2641_ = v_isSharedCheck_2650_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_eliminations_2638_);
lean_inc(v_equalities_2637_);
lean_inc(v_constraints_2636_);
lean_inc(v_numVars_2635_);
lean_inc(v_assumptions_2634_);
lean_dec(v_p_2602_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2650_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___f_2642_; uint8_t v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
lean_inc_ref(v_justification_2606_);
lean_inc(v_coeffs_2604_);
lean_inc_ref(v_constraint_2605_);
v___f_2642_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0), 4, 3);
lean_closure_set(v___f_2642_, 0, v_constraint_2605_);
lean_closure_set(v___f_2642_, 1, v_coeffs_2604_);
lean_closure_set(v___f_2642_, 2, v_justification_2606_);
v___x_2643_ = 0;
lean_inc_ref(v_assumptions_2634_);
v___x_2644_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed), 14, 4);
lean_closure_set(v___x_2644_, 0, v_constraint_2605_);
lean_closure_set(v___x_2644_, 1, v_coeffs_2604_);
lean_closure_set(v___x_2644_, 2, v_justification_2606_);
lean_closure_set(v___x_2644_, 3, v_assumptions_2634_);
v___x_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
v___x_2646_ = lean_mk_thunk(v___f_2642_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 6, v___x_2646_);
lean_ctor_set(v___x_2640_, 5, v___x_2645_);
v___x_2648_ = v___x_2640_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_assumptions_2634_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_numVars_2635_);
lean_ctor_set(v_reuseFailAlloc_2649_, 2, v_constraints_2636_);
lean_ctor_set(v_reuseFailAlloc_2649_, 3, v_equalities_2637_);
lean_ctor_set(v_reuseFailAlloc_2649_, 4, v_eliminations_2638_);
lean_ctor_set(v_reuseFailAlloc_2649_, 5, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2649_, 6, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_ctor_set_uint8(v___x_2648_, sizeof(void*)*7, v___x_2643_);
return v___x_2648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0(lean_object* v_00_u03b2_2653_, lean_object* v_m_2654_, lean_object* v_a_2655_, lean_object* v_b_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_m_2654_, v_a_2655_, v_b_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1(lean_object* v_00_u03b2_2658_, lean_object* v_m_2659_, lean_object* v_a_2660_, lean_object* v_b_2661_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_m_2659_, v_a_2660_, v_b_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_object* v_00_u03b2_2663_, lean_object* v_a_2664_, lean_object* v_x_2665_){
_start:
{
uint8_t v___x_2666_; 
v___x_2666_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2664_, v_x_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2667_, lean_object* v_a_2668_, lean_object* v_x_2669_){
_start:
{
uint8_t v_res_2670_; lean_object* v_r_2671_; 
v_res_2670_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(v_00_u03b2_2667_, v_a_2668_, v_x_2669_);
lean_dec(v_x_2669_);
lean_dec(v_a_2668_);
v_r_2671_ = lean_box(v_res_2670_);
return v_r_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2(lean_object* v_00_u03b2_2672_, lean_object* v_data_2673_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_data_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3(lean_object* v_00_u03b2_2675_, lean_object* v_a_2676_, lean_object* v_b_2677_, lean_object* v_x_2678_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2676_, v_b_2677_, v_x_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2680_, lean_object* v_i_2681_, lean_object* v_source_2682_, lean_object* v_target_2683_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v_i_2681_, v_source_2682_, v_target_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2685_, lean_object* v_x_2686_, lean_object* v_x_2687_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_x_2686_, v_x_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(lean_object* v_a_2689_, lean_object* v_x_2690_){
_start:
{
if (lean_obj_tag(v_x_2690_) == 0)
{
lean_object* v___x_2691_; 
v___x_2691_ = lean_box(0);
return v___x_2691_;
}
else
{
lean_object* v_key_2692_; lean_object* v_value_2693_; lean_object* v_tail_2694_; uint8_t v___x_2695_; 
v_key_2692_ = lean_ctor_get(v_x_2690_, 0);
v_value_2693_ = lean_ctor_get(v_x_2690_, 1);
v_tail_2694_ = lean_ctor_get(v_x_2690_, 2);
v___x_2695_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2692_, v_a_2689_);
if (v___x_2695_ == 0)
{
v_x_2690_ = v_tail_2694_;
goto _start;
}
else
{
lean_object* v___x_2697_; 
lean_inc(v_value_2693_);
v___x_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2697_, 0, v_value_2693_);
return v___x_2697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg___boxed(lean_object* v_a_2698_, lean_object* v_x_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2698_, v_x_2699_);
lean_dec(v_x_2699_);
lean_dec(v_a_2698_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(lean_object* v_m_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_buckets_2703_; lean_object* v___x_2704_; uint64_t v___x_2705_; uint64_t v___x_2706_; uint64_t v___x_2707_; uint64_t v___x_2708_; uint64_t v_fold_2709_; uint64_t v___x_2710_; uint64_t v___x_2711_; uint64_t v___x_2712_; size_t v___x_2713_; size_t v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v_buckets_2703_ = lean_ctor_get(v_m_2701_, 1);
v___x_2704_ = lean_array_get_size(v_buckets_2703_);
v___x_2705_ = 7ULL;
v___x_2706_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2705_, v_a_2702_);
v___x_2707_ = 32ULL;
v___x_2708_ = lean_uint64_shift_right(v___x_2706_, v___x_2707_);
v_fold_2709_ = lean_uint64_xor(v___x_2706_, v___x_2708_);
v___x_2710_ = 16ULL;
v___x_2711_ = lean_uint64_shift_right(v_fold_2709_, v___x_2710_);
v___x_2712_ = lean_uint64_xor(v_fold_2709_, v___x_2711_);
v___x_2713_ = lean_uint64_to_usize(v___x_2712_);
v___x_2714_ = lean_usize_of_nat(v___x_2704_);
v___x_2715_ = ((size_t)1ULL);
v___x_2716_ = lean_usize_sub(v___x_2714_, v___x_2715_);
v___x_2717_ = lean_usize_land(v___x_2713_, v___x_2716_);
v___x_2718_ = lean_array_uget_borrowed(v_buckets_2703_, v___x_2717_);
v___x_2719_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2702_, v___x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg___boxed(lean_object* v_m_2720_, lean_object* v_a_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2720_, v_a_2721_);
lean_dec(v_a_2721_);
lean_dec_ref(v_m_2720_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addConstraint(lean_object* v_p_2723_, lean_object* v_x_2724_){
_start:
{
uint8_t v_possible_2725_; 
v_possible_2725_ = lean_ctor_get_uint8(v_p_2723_, sizeof(void*)*7);
if (v_possible_2725_ == 0)
{
lean_dec_ref(v_x_2724_);
return v_p_2723_;
}
else
{
lean_object* v_coeffs_2726_; lean_object* v_constraint_2727_; lean_object* v_justification_2728_; lean_object* v_constraints_2729_; lean_object* v___x_2730_; 
v_coeffs_2726_ = lean_ctor_get(v_x_2724_, 0);
v_constraint_2727_ = lean_ctor_get(v_x_2724_, 1);
v_justification_2728_ = lean_ctor_get(v_x_2724_, 2);
v_constraints_2729_ = lean_ctor_get(v_p_2723_, 2);
v___x_2730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2729_, v_coeffs_2726_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_lowerBound_2731_; 
v_lowerBound_2731_ = lean_ctor_get(v_constraint_2727_, 0);
if (lean_obj_tag(v_lowerBound_2731_) == 0)
{
lean_object* v_upperBound_2732_; 
v_upperBound_2732_ = lean_ctor_get(v_constraint_2727_, 1);
if (lean_obj_tag(v_upperBound_2732_) == 0)
{
lean_dec_ref(v_x_2724_);
return v_p_2723_;
}
else
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2723_, v_x_2724_);
return v___x_2733_;
}
}
else
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2723_, v_x_2724_);
return v___x_2734_;
}
}
else
{
lean_object* v_val_2735_; lean_object* v_coeffs_2736_; lean_object* v_constraint_2737_; lean_object* v_justification_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2753_; 
v_val_2735_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_val_2735_);
lean_dec_ref_known(v___x_2730_, 1);
v_coeffs_2736_ = lean_ctor_get(v_val_2735_, 0);
v_constraint_2737_ = lean_ctor_get(v_val_2735_, 1);
v_justification_2738_ = lean_ctor_get(v_val_2735_, 2);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_val_2735_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2740_ = v_val_2735_;
v_isShared_2741_ = v_isSharedCheck_2753_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_justification_2738_);
lean_inc(v_constraint_2737_);
lean_inc(v_coeffs_2736_);
lean_dec(v_val_2735_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2753_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc(v_coeffs_2726_);
v___x_2743_ = l_instDecidableEqList___redArg(v___x_2742_, v_coeffs_2726_, v_coeffs_2736_);
if (v___x_2743_ == 0)
{
lean_del_object(v___x_2740_);
lean_dec_ref(v_justification_2738_);
lean_dec_ref(v_constraint_2737_);
lean_dec_ref(v_x_2724_);
return v_p_2723_;
}
else
{
lean_object* v_r_2744_; uint8_t v___x_2745_; 
lean_inc_ref_n(v_constraint_2737_, 2);
lean_inc_ref(v_constraint_2727_);
v_r_2744_ = l_Lean_Omega_Constraint_combine(v_constraint_2727_, v_constraint_2737_);
lean_inc_ref(v_r_2744_);
v___x_2745_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2744_, v_constraint_2737_);
if (v___x_2745_ == 0)
{
uint8_t v___x_2746_; 
lean_inc_ref(v_constraint_2727_);
lean_inc_ref(v_r_2744_);
v___x_2746_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2744_, v_constraint_2727_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
lean_inc_ref(v_justification_2728_);
lean_inc_ref(v_constraint_2727_);
lean_inc_n(v_coeffs_2726_, 2);
lean_dec_ref(v_x_2724_);
v___x_2747_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_2747_, 0, v_constraint_2727_);
lean_ctor_set(v___x_2747_, 1, v_constraint_2737_);
lean_ctor_set(v___x_2747_, 2, v_coeffs_2726_);
lean_ctor_set(v___x_2747_, 3, v_justification_2728_);
lean_ctor_set(v___x_2747_, 4, v_justification_2738_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 2, v___x_2747_);
lean_ctor_set(v___x_2740_, 1, v_r_2744_);
lean_ctor_set(v___x_2740_, 0, v_coeffs_2726_);
v___x_2749_ = v___x_2740_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_coeffs_2726_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_r_2744_);
lean_ctor_set(v_reuseFailAlloc_2751_, 2, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2723_, v___x_2749_);
return v___x_2750_;
}
}
else
{
lean_object* v___x_2752_; 
lean_dec_ref(v_r_2744_);
lean_del_object(v___x_2740_);
lean_dec_ref(v_justification_2738_);
lean_dec_ref(v_constraint_2737_);
v___x_2752_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2723_, v_x_2724_);
return v___x_2752_;
}
}
else
{
lean_dec_ref(v_r_2744_);
lean_del_object(v___x_2740_);
lean_dec_ref(v_justification_2738_);
lean_dec_ref(v_constraint_2737_);
lean_dec_ref(v_x_2724_);
return v_p_2723_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(lean_object* v_00_u03b2_2754_, lean_object* v_m_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2755_, v_a_2756_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___boxed(lean_object* v_00_u03b2_2758_, lean_object* v_m_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(v_00_u03b2_2758_, v_m_2759_, v_a_2760_);
lean_dec(v_a_2760_);
lean_dec_ref(v_m_2759_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(lean_object* v_00_u03b2_2762_, lean_object* v_a_2763_, lean_object* v_x_2764_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2763_, v_x_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2766_, lean_object* v_a_2767_, lean_object* v_x_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(v_00_u03b2_2766_, v_a_2767_, v_x_2768_);
lean_dec(v_x_2768_);
lean_dec(v_a_2767_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(lean_object* v_x_2770_, lean_object* v_x_2771_){
_start:
{
if (lean_obj_tag(v_x_2771_) == 0)
{
return v_x_2770_;
}
else
{
if (lean_obj_tag(v_x_2770_) == 0)
{
lean_object* v_key_2772_; lean_object* v_tail_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_key_2772_ = lean_ctor_get(v_x_2771_, 0);
lean_inc_n(v_key_2772_, 2);
v_tail_2773_ = lean_ctor_get(v_x_2771_, 2);
lean_inc(v_tail_2773_);
lean_dec_ref_known(v_x_2771_, 3);
v___x_2774_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2772_);
v___x_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2775_, 0, v_key_2772_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
v___x_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
v_x_2770_ = v___x_2776_;
v_x_2771_ = v_tail_2773_;
goto _start;
}
else
{
lean_object* v_val_2778_; lean_object* v_key_2779_; lean_object* v_tail_2780_; lean_object* v_fst_2781_; lean_object* v_snd_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2803_; 
v_val_2778_ = lean_ctor_get(v_x_2770_, 0);
lean_inc(v_val_2778_);
v_key_2779_ = lean_ctor_get(v_x_2771_, 0);
lean_inc(v_key_2779_);
v_tail_2780_ = lean_ctor_get(v_x_2771_, 2);
lean_inc(v_tail_2780_);
lean_dec_ref_known(v_x_2771_, 3);
v_fst_2781_ = lean_ctor_get(v_val_2778_, 0);
v_snd_2782_ = lean_ctor_get(v_val_2778_, 1);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_val_2778_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2784_ = v_val_2778_;
v_isShared_2785_ = v_isSharedCheck_2803_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_snd_2782_);
lean_inc(v_fst_2781_);
lean_dec(v_val_2778_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2803_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; uint8_t v___x_2787_; 
v___x_2786_ = lean_unsigned_to_nat(2u);
v___x_2787_ = lean_nat_dec_le(v___x_2786_, v_snd_2782_);
if (v___x_2787_ == 0)
{
lean_del_object(v___x_2784_);
lean_dec(v_snd_2782_);
lean_dec(v_fst_2781_);
lean_dec(v_key_2779_);
v_x_2771_ = v_tail_2780_;
goto _start;
}
else
{
lean_object* v_m_x27_2789_; uint8_t v___x_2796_; 
lean_inc(v_key_2779_);
v_m_x27_2789_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2779_);
v___x_2796_ = lean_nat_dec_lt(v_m_x27_2789_, v_snd_2782_);
if (v___x_2796_ == 0)
{
uint8_t v___x_2797_; 
v___x_2797_ = lean_nat_dec_eq(v_m_x27_2789_, v_snd_2782_);
lean_dec(v_snd_2782_);
if (v___x_2797_ == 0)
{
lean_dec(v_m_x27_2789_);
lean_del_object(v___x_2784_);
lean_dec(v_fst_2781_);
lean_dec(v_key_2779_);
v_x_2771_ = v_tail_2780_;
goto _start;
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
lean_inc(v_key_2779_);
v___x_2799_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_key_2779_);
v___x_2800_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_fst_2781_);
v___x_2801_ = lean_nat_dec_lt(v___x_2799_, v___x_2800_);
lean_dec(v___x_2800_);
lean_dec(v___x_2799_);
if (v___x_2801_ == 0)
{
lean_dec(v_m_x27_2789_);
lean_del_object(v___x_2784_);
lean_dec(v_key_2779_);
v_x_2771_ = v_tail_2780_;
goto _start;
}
else
{
lean_dec_ref_known(v_x_2770_, 1);
goto v___jp_2790_;
}
}
}
else
{
lean_dec(v_snd_2782_);
lean_dec(v_fst_2781_);
lean_dec_ref_known(v_x_2770_, 1);
goto v___jp_2790_;
}
v___jp_2790_:
{
lean_object* v___x_2792_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 1, v_m_x27_2789_);
lean_ctor_set(v___x_2784_, 0, v_key_2779_);
v___x_2792_ = v___x_2784_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_key_2779_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_m_x27_2789_);
v___x_2792_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2793_; 
v___x_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
v_x_2770_ = v___x_2793_;
v_x_2771_ = v_tail_2780_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(lean_object* v_as_2804_, size_t v_i_2805_, size_t v_stop_2806_, lean_object* v_b_2807_){
_start:
{
uint8_t v___x_2808_; 
v___x_2808_ = lean_usize_dec_eq(v_i_2805_, v_stop_2806_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2810_; size_t v___x_2811_; size_t v___x_2812_; 
v___x_2809_ = lean_array_uget_borrowed(v_as_2804_, v_i_2805_);
lean_inc(v___x_2809_);
v___x_2810_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(v_b_2807_, v___x_2809_);
v___x_2811_ = ((size_t)1ULL);
v___x_2812_ = lean_usize_add(v_i_2805_, v___x_2811_);
v_i_2805_ = v___x_2812_;
v_b_2807_ = v___x_2810_;
goto _start;
}
else
{
return v_b_2807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1___boxed(lean_object* v_as_2814_, lean_object* v_i_2815_, lean_object* v_stop_2816_, lean_object* v_b_2817_){
_start:
{
size_t v_i_boxed_2818_; size_t v_stop_boxed_2819_; lean_object* v_res_2820_; 
v_i_boxed_2818_ = lean_unbox_usize(v_i_2815_);
lean_dec(v_i_2815_);
v_stop_boxed_2819_ = lean_unbox_usize(v_stop_2816_);
lean_dec(v_stop_2816_);
v_res_2820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_as_2814_, v_i_boxed_2818_, v_stop_boxed_2819_, v_b_2817_);
lean_dec_ref(v_as_2814_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality(lean_object* v_p_2821_){
_start:
{
lean_object* v_equalities_2822_; lean_object* v_buckets_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v_equalities_2822_ = lean_ctor_get(v_p_2821_, 3);
v_buckets_2823_ = lean_ctor_get(v_equalities_2822_, 1);
v___x_2824_ = lean_box(0);
v___x_2825_ = lean_unsigned_to_nat(0u);
v___x_2826_ = lean_array_get_size(v_buckets_2823_);
v___x_2827_ = lean_nat_dec_lt(v___x_2825_, v___x_2826_);
if (v___x_2827_ == 0)
{
return v___x_2824_;
}
else
{
size_t v___x_2828_; size_t v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = ((size_t)0ULL);
v___x_2829_ = lean_usize_of_nat(v___x_2826_);
v___x_2830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2823_, v___x_2828_, v___x_2829_, v___x_2824_);
return v___x_2830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality___boxed(lean_object* v_p_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_2831_);
lean_dec_ref(v_p_2831_);
return v_res_2832_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_unsigned_to_nat(1u);
v___x_2834_ = lean_nat_to_int(v___x_2833_);
return v___x_2834_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2836_ = lean_int_neg(v___x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(lean_object* v_as_2837_, size_t v_i_2838_, size_t v_stop_2839_, lean_object* v_b_2840_){
_start:
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_usize_dec_eq(v_i_2838_, v_stop_2839_);
if (v___x_2841_ == 0)
{
size_t v___x_2842_; size_t v___x_2843_; lean_object* v___x_2844_; lean_object* v_snd_2845_; lean_object* v_fst_2846_; lean_object* v_fst_2847_; lean_object* v_snd_2848_; lean_object* v_coeffs_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2842_ = ((size_t)1ULL);
v___x_2843_ = lean_usize_sub(v_i_2838_, v___x_2842_);
v___x_2844_ = lean_array_uget_borrowed(v_as_2837_, v___x_2843_);
v_snd_2845_ = lean_ctor_get(v___x_2844_, 1);
v_fst_2846_ = lean_ctor_get(v___x_2844_, 0);
v_fst_2847_ = lean_ctor_get(v_snd_2845_, 0);
v_snd_2848_ = lean_ctor_get(v_snd_2845_, 1);
v_coeffs_2849_ = lean_ctor_get(v_b_2840_, 0);
lean_inc(v_fst_2847_);
v___x_2850_ = l_Lean_Omega_IntList_get(v_coeffs_2849_, v_fst_2847_);
v___x_2851_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2852_ = lean_int_dec_eq(v___x_2850_, v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2853_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2854_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2855_ = lean_int_mul(v___x_2854_, v_snd_2848_);
v___x_2856_ = lean_int_mul(v___x_2855_, v___x_2850_);
lean_dec(v___x_2850_);
lean_dec(v___x_2855_);
lean_inc(v_fst_2846_);
v___x_2857_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v___x_2856_, v_fst_2846_, v___x_2853_, v_b_2840_);
v_i_2838_ = v___x_2843_;
v_b_2840_ = v___x_2857_;
goto _start;
}
else
{
lean_dec(v___x_2850_);
v_i_2838_ = v___x_2843_;
goto _start;
}
}
else
{
return v_b_2840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___boxed(lean_object* v_as_2860_, lean_object* v_i_2861_, lean_object* v_stop_2862_, lean_object* v_b_2863_){
_start:
{
size_t v_i_boxed_2864_; size_t v_stop_boxed_2865_; lean_object* v_res_2866_; 
v_i_boxed_2864_ = lean_unbox_usize(v_i_2861_);
lean_dec(v_i_2861_);
v_stop_boxed_2865_ = lean_unbox_usize(v_stop_2862_);
lean_dec(v_stop_2862_);
v_res_2866_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v_as_2860_, v_i_boxed_2864_, v_stop_boxed_2865_, v_b_2863_);
lean_dec_ref(v_as_2860_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(lean_object* v_init_2867_, lean_object* v_l_2868_){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2869_ = lean_array_mk(v_l_2868_);
v___x_2870_ = lean_array_get_size(v___x_2869_);
v___x_2871_ = lean_unsigned_to_nat(0u);
v___x_2872_ = lean_nat_dec_lt(v___x_2871_, v___x_2870_);
if (v___x_2872_ == 0)
{
lean_dec_ref(v___x_2869_);
return v_init_2867_;
}
else
{
size_t v___x_2873_; size_t v___x_2874_; lean_object* v___x_2875_; 
v___x_2873_ = lean_usize_of_nat(v___x_2870_);
v___x_2874_ = ((size_t)0ULL);
v___x_2875_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v___x_2869_, v___x_2873_, v___x_2874_, v_init_2867_);
lean_dec_ref(v___x_2869_);
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(lean_object* v_p_2876_, lean_object* v_f_2877_){
_start:
{
lean_object* v_eliminations_2878_; lean_object* v___x_2879_; 
v_eliminations_2878_ = lean_ctor_get(v_p_2876_, 4);
lean_inc(v_eliminations_2878_);
lean_dec_ref(v_p_2876_);
v___x_2879_ = l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(v_f_2877_, v_eliminations_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__0(lean_object* v_x_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(lean_object* v___y_2882_, lean_object* v_sign_2883_, lean_object* v_val_2884_, lean_object* v_x_2885_, lean_object* v_x_2886_){
_start:
{
if (lean_obj_tag(v_x_2886_) == 0)
{
lean_dec_ref(v_val_2884_);
lean_dec(v___y_2882_);
return v_x_2885_;
}
else
{
lean_object* v_key_2887_; lean_object* v_value_2888_; lean_object* v_tail_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; 
v_key_2887_ = lean_ctor_get(v_x_2886_, 0);
lean_inc(v_key_2887_);
v_value_2888_ = lean_ctor_get(v_x_2886_, 1);
lean_inc(v_value_2888_);
v_tail_2889_ = lean_ctor_get(v_x_2886_, 2);
lean_inc(v_tail_2889_);
lean_dec_ref_known(v_x_2886_, 3);
lean_inc(v___y_2882_);
v___x_2890_ = l_Lean_Omega_IntList_get(v_key_2887_, v___y_2882_);
lean_dec(v_key_2887_);
v___x_2891_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2892_ = lean_int_dec_eq(v___x_2890_, v___x_2891_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v_k_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2893_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2894_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2895_ = lean_int_mul(v___x_2894_, v_sign_2883_);
v_k_2896_ = lean_int_mul(v___x_2895_, v___x_2890_);
lean_dec(v___x_2890_);
lean_dec(v___x_2895_);
lean_inc_ref(v_val_2884_);
v___x_2897_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_k_2896_, v_val_2884_, v___x_2893_, v_value_2888_);
v___x_2898_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_2897_);
v___x_2899_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2885_, v___x_2898_);
v_x_2885_ = v___x_2899_;
v_x_2886_ = v_tail_2889_;
goto _start;
}
else
{
lean_object* v___x_2901_; 
lean_dec(v___x_2890_);
v___x_2901_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2885_, v_value_2888_);
v_x_2885_ = v___x_2901_;
v_x_2886_ = v_tail_2889_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0___boxed(lean_object* v___y_2903_, lean_object* v_sign_2904_, lean_object* v_val_2905_, lean_object* v_x_2906_, lean_object* v_x_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2903_, v_sign_2904_, v_val_2905_, v_x_2906_, v_x_2907_);
lean_dec(v_sign_2904_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object* v___y_2909_, lean_object* v_sign_2910_, lean_object* v_val_2911_, lean_object* v_as_2912_, size_t v_i_2913_, size_t v_stop_2914_, lean_object* v_b_2915_){
_start:
{
uint8_t v___x_2916_; 
v___x_2916_ = lean_usize_dec_eq(v_i_2913_, v_stop_2914_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; size_t v___x_2919_; size_t v___x_2920_; 
v___x_2917_ = lean_array_uget_borrowed(v_as_2912_, v_i_2913_);
lean_inc(v___x_2917_);
lean_inc_ref(v_val_2911_);
lean_inc(v___y_2909_);
v___x_2918_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2909_, v_sign_2910_, v_val_2911_, v_b_2915_, v___x_2917_);
v___x_2919_ = ((size_t)1ULL);
v___x_2920_ = lean_usize_add(v_i_2913_, v___x_2919_);
v_i_2913_ = v___x_2920_;
v_b_2915_ = v___x_2918_;
goto _start;
}
else
{
lean_dec_ref(v_val_2911_);
lean_dec(v___y_2909_);
return v_b_2915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1___boxed(lean_object* v___y_2922_, lean_object* v_sign_2923_, lean_object* v_val_2924_, lean_object* v_as_2925_, lean_object* v_i_2926_, lean_object* v_stop_2927_, lean_object* v_b_2928_){
_start:
{
size_t v_i_boxed_2929_; size_t v_stop_boxed_2930_; lean_object* v_res_2931_; 
v_i_boxed_2929_ = lean_unbox_usize(v_i_2926_);
lean_dec(v_i_2926_);
v_stop_boxed_2930_ = lean_unbox_usize(v_stop_2927_);
lean_dec(v_stop_2927_);
v_res_2931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2922_, v_sign_2923_, v_val_2924_, v_as_2925_, v_i_boxed_2929_, v_stop_boxed_2930_, v_b_2928_);
lean_dec_ref(v_as_2925_);
lean_dec(v_sign_2923_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
if (lean_obj_tag(v_a_2932_) == 0)
{
lean_object* v___x_2934_; 
lean_dec(v_a_2933_);
v___x_2934_ = lean_box(0);
return v___x_2934_;
}
else
{
lean_object* v_head_2935_; lean_object* v_tail_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; 
v_head_2935_ = lean_ctor_get(v_a_2932_, 0);
v_tail_2936_ = lean_ctor_get(v_a_2932_, 1);
v___x_2937_ = lean_nat_abs(v_head_2935_);
v___x_2938_ = lean_unsigned_to_nat(1u);
v___x_2939_ = lean_nat_dec_eq(v___x_2937_, v___x_2938_);
lean_dec(v___x_2937_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; 
v___x_2940_ = lean_nat_add(v_a_2933_, v___x_2938_);
lean_dec(v_a_2933_);
v_a_2932_ = v_tail_2936_;
v_a_2933_ = v___x_2940_;
goto _start;
}
else
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_a_2933_);
return v___x_2942_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2___boxed(lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(v_a_2943_, v_a_2944_);
lean_dec(v_a_2943_);
return v_res_2945_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = lean_box(0);
v___x_2948_ = lean_unsigned_to_nat(16u);
v___x_2949_ = lean_mk_array(v___x_2948_, v___x_2947_);
return v___x_2949_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2(void){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1);
v___x_2951_ = lean_unsigned_to_nat(0u);
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
lean_ctor_set(v___x_2952_, 1, v___x_2950_);
return v___x_2952_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3(void){
_start:
{
lean_object* v___f_2953_; lean_object* v___x_2954_; 
v___f_2953_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0));
v___x_2954_ = lean_mk_thunk(v___f_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(lean_object* v_p_2955_, lean_object* v_c_2956_){
_start:
{
lean_object* v___y_2958_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_unsigned_to_nat(0u);
v___x_3002_ = l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(v_c_2956_, v___x_3001_);
if (lean_obj_tag(v___x_3002_) == 0)
{
v___y_2958_ = v___x_3001_;
goto v___jp_2957_;
}
else
{
lean_object* v_val_3003_; 
v_val_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_val_3003_);
lean_dec_ref_known(v___x_3002_, 1);
v___y_2958_ = v_val_3003_;
goto v___jp_2957_;
}
v___jp_2957_:
{
lean_object* v_assumptions_2959_; lean_object* v_constraints_2960_; lean_object* v_eliminations_2961_; lean_object* v___x_2962_; 
v_assumptions_2959_ = lean_ctor_get(v_p_2955_, 0);
v_constraints_2960_ = lean_ctor_get(v_p_2955_, 2);
lean_inc_ref(v_constraints_2960_);
v_eliminations_2961_ = lean_ctor_get(v_p_2955_, 4);
v___x_2962_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2960_, v_c_2956_);
if (lean_obj_tag(v___x_2962_) == 1)
{
lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2993_; 
lean_inc(v_eliminations_2961_);
lean_inc_ref(v_assumptions_2959_);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_p_2955_);
if (v_isSharedCheck_2993_ == 0)
{
lean_object* v_unused_2994_; lean_object* v_unused_2995_; lean_object* v_unused_2996_; lean_object* v_unused_2997_; lean_object* v_unused_2998_; lean_object* v_unused_2999_; lean_object* v_unused_3000_; 
v_unused_2994_ = lean_ctor_get(v_p_2955_, 6);
lean_dec(v_unused_2994_);
v_unused_2995_ = lean_ctor_get(v_p_2955_, 5);
lean_dec(v_unused_2995_);
v_unused_2996_ = lean_ctor_get(v_p_2955_, 4);
lean_dec(v_unused_2996_);
v_unused_2997_ = lean_ctor_get(v_p_2955_, 3);
lean_dec(v_unused_2997_);
v_unused_2998_ = lean_ctor_get(v_p_2955_, 2);
lean_dec(v_unused_2998_);
v_unused_2999_ = lean_ctor_get(v_p_2955_, 1);
lean_dec(v_unused_2999_);
v_unused_3000_ = lean_ctor_get(v_p_2955_, 0);
lean_dec(v_unused_3000_);
v___x_2964_ = v_p_2955_;
v_isShared_2965_ = v_isSharedCheck_2993_;
goto v_resetjp_2963_;
}
else
{
lean_dec(v_p_2955_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2993_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v_val_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v_buckets_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2991_; 
v_val_2966_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_val_2966_);
lean_dec_ref_known(v___x_2962_, 1);
v___x_2967_ = lean_unsigned_to_nat(0u);
v___x_2968_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v_buckets_2969_ = lean_ctor_get(v_constraints_2960_, 1);
v_isSharedCheck_2991_ = !lean_is_exclusive(v_constraints_2960_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; 
v_unused_2992_ = lean_ctor_get(v_constraints_2960_, 0);
lean_dec(v_unused_2992_);
v___x_2971_ = v_constraints_2960_;
v_isShared_2972_ = v_isSharedCheck_2991_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_buckets_2969_);
lean_dec(v_constraints_2960_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2991_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2973_; lean_object* v_sign_2974_; lean_object* v___x_2976_; 
lean_inc_n(v___y_2958_, 2);
v___x_2973_ = l_Lean_Omega_IntList_get(v_c_2956_, v___y_2958_);
v_sign_2974_ = l_Int_sign(v___x_2973_);
lean_dec(v___x_2973_);
lean_inc(v_sign_2974_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 1, v_sign_2974_);
lean_ctor_set(v___x_2971_, 0, v___y_2958_);
v___x_2976_ = v___x_2971_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___y_2958_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_sign_2974_);
v___x_2976_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v_init_2983_; 
lean_inc(v_val_2966_);
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v_val_2966_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
v___x_2978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
lean_ctor_set(v___x_2978_, 1, v_eliminations_2961_);
v___x_2979_ = 1;
v___x_2980_ = lean_box(0);
v___x_2981_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 6, v___x_2981_);
lean_ctor_set(v___x_2964_, 5, v___x_2980_);
lean_ctor_set(v___x_2964_, 4, v___x_2978_);
lean_ctor_set(v___x_2964_, 3, v___x_2968_);
lean_ctor_set(v___x_2964_, 2, v___x_2968_);
lean_ctor_set(v___x_2964_, 1, v___x_2967_);
v_init_2983_ = v___x_2964_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_assumptions_2959_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_2989_, 2, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2989_, 3, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2989_, 4, v___x_2978_);
lean_ctor_set(v_reuseFailAlloc_2989_, 5, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_2989_, 6, v___x_2981_);
v_init_2983_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; uint8_t v___x_2985_; 
lean_ctor_set_uint8(v_init_2983_, sizeof(void*)*7, v___x_2979_);
v___x_2984_ = lean_array_get_size(v_buckets_2969_);
v___x_2985_ = lean_nat_dec_lt(v___x_2967_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_dec(v_sign_2974_);
lean_dec_ref(v_buckets_2969_);
lean_dec(v_val_2966_);
lean_dec(v___y_2958_);
return v_init_2983_;
}
else
{
size_t v___x_2986_; size_t v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = ((size_t)0ULL);
v___x_2987_ = lean_usize_of_nat(v___x_2984_);
v___x_2988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2958_, v_sign_2974_, v_val_2966_, v_buckets_2969_, v___x_2986_, v___x_2987_, v_init_2983_);
lean_dec_ref(v_buckets_2969_);
lean_dec(v_sign_2974_);
return v___x_2988_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2962_);
lean_dec_ref(v_constraints_2960_);
lean_dec(v___y_2958_);
return v_p_2955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___boxed(lean_object* v_p_3004_, lean_object* v_c_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_3004_, v_c_3005_);
lean_dec(v_c_3005_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(lean_object* v_msgData_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v___x_3013_; lean_object* v_env_3014_; lean_object* v___x_3015_; lean_object* v_toCold_3016_; lean_object* v_mctx_3017_; lean_object* v_lctx_3018_; lean_object* v_options_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3013_ = lean_st_ref_get(v___y_3011_);
v_env_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc_ref(v_env_3014_);
lean_dec(v___x_3013_);
v___x_3015_ = lean_st_ref_get(v___y_3009_);
v_toCold_3016_ = lean_ctor_get(v___y_3010_, 0);
v_mctx_3017_ = lean_ctor_get(v___x_3015_, 0);
lean_inc_ref(v_mctx_3017_);
lean_dec(v___x_3015_);
v_lctx_3018_ = lean_ctor_get(v___y_3008_, 2);
v_options_3019_ = lean_ctor_get(v_toCold_3016_, 2);
lean_inc_ref(v_options_3019_);
lean_inc_ref(v_lctx_3018_);
v___x_3020_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3020_, 0, v_env_3014_);
lean_ctor_set(v___x_3020_, 1, v_mctx_3017_);
lean_ctor_set(v___x_3020_, 2, v_lctx_3018_);
lean_ctor_set(v___x_3020_, 3, v_options_3019_);
v___x_3021_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
lean_ctor_set(v___x_3021_, 1, v_msgData_3007_);
v___x_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0___boxed(lean_object* v_msgData_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msgData_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(lean_object* v_msg_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v_ref_3036_; lean_object* v___x_3037_; lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3046_; 
v_ref_3036_ = lean_ctor_get(v___y_3033_, 2);
v___x_3037_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3046_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3046_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3042_; lean_object* v___x_3044_; 
lean_inc(v_ref_3036_);
v___x_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3042_, 0, v_ref_3036_);
lean_ctor_set(v___x_3042_, 1, v_a_3038_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set_tag(v___x_3040_, 1);
lean_ctor_set(v___x_3040_, 0, v___x_3042_);
v___x_3044_ = v___x_3040_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg___boxed(lean_object* v_msg_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
return v_res_3053_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0));
v___x_3056_ = l_Lean_stringToMessageData(v___x_3055_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2));
v___x_3059_ = l_Lean_stringToMessageData(v___x_3058_);
return v___x_3059_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4));
v___x_3062_ = l_Lean_stringToMessageData(v___x_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(lean_object* v_p_3063_, lean_object* v_c_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, uint8_t v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_constraints_3075_; lean_object* v___x_3076_; 
v_constraints_3075_ = lean_ctor_get(v_p_3063_, 2);
v___x_3076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_3075_, v_c_3064_);
if (lean_obj_tag(v___x_3076_) == 1)
{
lean_object* v_val_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3176_; 
v_val_3077_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3079_ = v___x_3076_;
v_isShared_3080_ = v_isSharedCheck_3176_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_val_3077_);
lean_dec(v___x_3076_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3176_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v_constraint_3081_; lean_object* v_lowerBound_3082_; 
v_constraint_3081_ = lean_ctor_get(v_val_3077_, 1);
v_lowerBound_3082_ = lean_ctor_get(v_constraint_3081_, 0);
lean_inc(v_lowerBound_3082_);
if (lean_obj_tag(v_lowerBound_3082_) == 1)
{
lean_object* v_upperBound_3083_; 
lean_del_object(v___x_3079_);
v_upperBound_3083_ = lean_ctor_get(v_constraint_3081_, 1);
lean_inc(v_upperBound_3083_);
if (lean_obj_tag(v_upperBound_3083_) == 1)
{
lean_object* v_coeffs_3084_; lean_object* v_justification_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3163_; 
v_coeffs_3084_ = lean_ctor_get(v_val_3077_, 0);
v_justification_3085_ = lean_ctor_get(v_val_3077_, 2);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_val_3077_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; 
v_unused_3164_ = lean_ctor_get(v_val_3077_, 1);
lean_dec(v_unused_3164_);
v___x_3087_ = v_val_3077_;
v_isShared_3088_ = v_isSharedCheck_3163_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_justification_3085_);
lean_inc(v_coeffs_3084_);
lean_dec(v_val_3077_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3163_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v_val_3089_; lean_object* v_val_3090_; lean_object* v___x_3091_; 
v_val_3089_ = lean_ctor_get(v_lowerBound_3082_, 0);
lean_inc(v_val_3089_);
lean_dec_ref_known(v_lowerBound_3082_, 1);
v_val_3090_ = lean_ctor_get(v_upperBound_3083_, 0);
lean_inc(v_val_3090_);
lean_dec_ref_known(v_upperBound_3083_, 1);
v___x_3091_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3066_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v_m_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v_nil_3098_; lean_object* v_cons_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_a_3092_);
lean_dec_ref_known(v___x_3091_, 1);
lean_inc(v_c_3064_);
v___x_3093_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_c_3064_);
v___x_3094_ = lean_unsigned_to_nat(1u);
v_m_3095_ = lean_nat_add(v___x_3093_, v___x_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc(v_m_3095_);
v___x_3097_ = l_Lean_mkNatLit(v_m_3095_);
v_nil_3098_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3099_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3100_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3098_, v_cons_3099_, v_c_3064_);
lean_dec(v_c_3064_);
v___x_3101_ = l_Lean_mkApp3(v___x_3096_, v___x_3097_, v___x_3100_, v_a_3092_);
v___x_3102_ = l_Lean_Elab_Tactic_Omega_lookup(v___x_3101_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3146_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3146_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3146_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v_fst_3107_; lean_object* v_snd_3108_; uint8_t v___x_3121_; 
v_fst_3107_ = lean_ctor_get(v_a_3103_, 0);
lean_inc(v_fst_3107_);
v_snd_3108_ = lean_ctor_get(v_a_3103_, 1);
lean_inc(v_snd_3108_);
lean_dec(v_a_3103_);
v___x_3121_ = lean_int_dec_eq(v_val_3090_, v_val_3089_);
lean_dec(v_val_3090_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
lean_dec(v_snd_3108_);
lean_dec(v_fst_3107_);
lean_del_object(v___x_3105_);
lean_dec(v_m_3095_);
lean_dec(v_val_3089_);
lean_del_object(v___x_3087_);
lean_dec_ref(v_justification_3085_);
lean_dec(v_coeffs_3084_);
lean_dec_ref(v_p_3063_);
v___x_3122_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1);
v___x_3123_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3122_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
return v___x_3123_;
}
else
{
if (lean_obj_tag(v_snd_3108_) == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_fst_3107_);
lean_del_object(v___x_3105_);
lean_dec(v_m_3095_);
lean_dec(v_val_3089_);
lean_del_object(v___x_3087_);
lean_dec_ref(v_justification_3085_);
lean_dec(v_coeffs_3084_);
lean_dec_ref(v_p_3063_);
v___x_3124_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3);
v___x_3125_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3124_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3125_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3125_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
else
{
lean_object* v_val_3134_; uint8_t v___x_3135_; 
v_val_3134_ = lean_ctor_get(v_snd_3108_, 0);
lean_inc(v_val_3134_);
lean_dec_ref_known(v_snd_3108_, 1);
v___x_3135_ = l_List_isEmpty___redArg(v_val_3134_);
lean_dec(v_val_3134_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec(v_fst_3107_);
lean_del_object(v___x_3105_);
lean_dec(v_m_3095_);
lean_dec(v_val_3089_);
lean_del_object(v___x_3087_);
lean_dec_ref(v_justification_3085_);
lean_dec(v_coeffs_3084_);
lean_dec_ref(v_p_3063_);
v___x_3136_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5);
v___x_3137_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3136_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
else
{
goto v___jp_3109_;
}
}
}
v___jp_3109_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
lean_inc(v_coeffs_3084_);
lean_inc_n(v_m_3095_, 2);
v___x_3110_ = l_Lean_Omega_bmod__coeffs(v_m_3095_, v_fst_3107_, v_coeffs_3084_);
v___x_3111_ = l_Int_bmod(v_val_3089_, v_m_3095_);
v___x_3112_ = l_Lean_Omega_Constraint_exact(v___x_3111_);
v___x_3113_ = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(v___x_3113_, 0, v_m_3095_);
lean_ctor_set(v___x_3113_, 1, v_val_3089_);
lean_ctor_set(v___x_3113_, 2, v_fst_3107_);
lean_ctor_set(v___x_3113_, 3, v_coeffs_3084_);
lean_ctor_set(v___x_3113_, 4, v_justification_3085_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 2, v___x_3113_);
lean_ctor_set(v___x_3087_, 1, v___x_3112_);
lean_ctor_set(v___x_3087_, 0, v___x_3110_);
v___x_3115_ = v___x_3087_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3110_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v___x_3112_);
lean_ctor_set(v_reuseFailAlloc_3120_, 2, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_3063_, v___x_3115_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3116_);
v___x_3118_ = v___x_3105_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v_m_3095_);
lean_dec(v_val_3090_);
lean_dec(v_val_3089_);
lean_del_object(v___x_3087_);
lean_dec_ref(v_justification_3085_);
lean_dec(v_coeffs_3084_);
lean_dec_ref(v_p_3063_);
v_a_3147_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3102_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3102_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec(v_val_3090_);
lean_dec(v_val_3089_);
lean_del_object(v___x_3087_);
lean_dec_ref(v_justification_3085_);
lean_dec(v_coeffs_3084_);
lean_dec(v_c_3064_);
lean_dec_ref(v_p_3063_);
v_a_3155_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3091_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3091_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
}
else
{
lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v_upperBound_3083_);
lean_dec(v_val_3077_);
lean_dec(v_c_3064_);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_lowerBound_3082_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; 
v_unused_3172_ = lean_ctor_get(v_lowerBound_3082_, 0);
lean_dec(v_unused_3172_);
v___x_3166_ = v_lowerBound_3082_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_dec(v_lowerBound_3082_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set_tag(v___x_3166_, 0);
lean_ctor_set(v___x_3166_, 0, v_p_3063_);
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_p_3063_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_object* v___x_3174_; 
lean_dec(v_lowerBound_3082_);
lean_dec(v_val_3077_);
lean_dec(v_c_3064_);
if (v_isShared_3080_ == 0)
{
lean_ctor_set_tag(v___x_3079_, 0);
lean_ctor_set(v___x_3079_, 0, v_p_3063_);
v___x_3174_ = v___x_3079_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_p_3063_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
else
{
lean_object* v___x_3177_; 
lean_dec(v___x_3076_);
lean_dec(v_c_3064_);
v___x_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3177_, 0, v_p_3063_);
return v___x_3177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___boxed(lean_object* v_p_3178_, lean_object* v_c_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
uint8_t v_a_boxed_3190_; lean_object* v_res_3191_; 
v_a_boxed_3190_ = lean_unbox(v_a_3183_);
v_res_3191_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3178_, v_c_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_boxed_3190_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3182_);
lean_dec(v_a_3181_);
lean_dec(v_a_3180_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_object* v_00_u03b1_3192_, lean_object* v_msg_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, uint8_t v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3193_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___boxed(lean_object* v_00_u03b1_3205_, lean_object* v_msg_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
uint8_t v___y_9256__boxed_3217_; lean_object* v_res_3218_; 
v___y_9256__boxed_3217_ = lean_unbox(v___y_3210_);
v_res_3218_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(v_00_u03b1_3205_, v_msg_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_9256__boxed_3217_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec(v___y_3207_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality(lean_object* v_p_3219_, lean_object* v_c_3220_, lean_object* v_m_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, uint8_t v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_){
_start:
{
lean_object* v___x_3232_; uint8_t v___x_3233_; 
v___x_3232_ = lean_unsigned_to_nat(1u);
v___x_3233_ = lean_nat_dec_eq(v_m_3221_, v___x_3232_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3219_, v_c_3220_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
return v___x_3234_;
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_3219_, v_c_3220_);
lean_dec(v_c_3220_);
v___x_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
return v___x_3236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality___boxed(lean_object* v_p_3237_, lean_object* v_c_3238_, lean_object* v_m_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_){
_start:
{
uint8_t v_a_boxed_3250_; lean_object* v_res_3251_; 
v_a_boxed_3250_ = lean_unbox(v_a_3243_);
v_res_3251_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3237_, v_c_3238_, v_m_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_boxed_3250_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_);
lean_dec(v_a_3248_);
lean_dec_ref(v_a_3247_);
lean_dec(v_a_3246_);
lean_dec_ref(v_a_3245_);
lean_dec(v_a_3244_);
lean_dec_ref(v_a_3242_);
lean_dec(v_a_3241_);
lean_dec(v_a_3240_);
lean_dec(v_m_3239_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(lean_object* v_p_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, uint8_t v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_){
_start:
{
uint8_t v_possible_3263_; 
v_possible_3263_ = lean_ctor_get_uint8(v_p_3252_, sizeof(void*)*7);
if (v_possible_3263_ == 0)
{
lean_object* v___x_3264_; 
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v_p_3252_);
return v___x_3264_;
}
else
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_3252_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v___x_3266_; 
v___x_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3266_, 0, v_p_3252_);
return v___x_3266_;
}
else
{
lean_object* v_val_3267_; lean_object* v_fst_3268_; lean_object* v_snd_3269_; lean_object* v___x_3270_; 
v_val_3267_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_val_3267_);
lean_dec_ref_known(v___x_3265_, 1);
v_fst_3268_ = lean_ctor_get(v_val_3267_, 0);
lean_inc(v_fst_3268_);
v_snd_3269_ = lean_ctor_get(v_val_3267_, 1);
lean_inc(v_snd_3269_);
lean_dec(v_val_3267_);
v___x_3270_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3252_, v_fst_3268_, v_snd_3269_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
lean_dec(v_snd_3269_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v_p_3252_ = v_a_3271_;
goto _start;
}
else
{
return v___x_3270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities___boxed(lean_object* v_p_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
uint8_t v_a_boxed_3284_; lean_object* v_res_3285_; 
v_a_boxed_3284_ = lean_unbox(v_a_3277_);
v_res_3285_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_boxed_3284_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec(v_a_3274_);
return v_res_3285_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3292_ = lean_box(0);
v___x_3293_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1));
v___x_3294_ = l_Lean_Expr_const___override(v___x_3293_, v___x_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object* v_c_3295_, lean_object* v_x_3296_, lean_object* v_p_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, uint8_t v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3299_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3309_);
lean_dec_ref_known(v___x_3308_, 1);
v___x_3310_ = lean_box(v_a_3301_);
lean_inc(v_a_3306_);
lean_inc_ref(v_a_3305_);
lean_inc(v_a_3304_);
lean_inc_ref(v_a_3303_);
lean_inc(v_a_3302_);
lean_inc_ref(v_a_3300_);
lean_inc(v_a_3299_);
lean_inc(v_a_3298_);
v___x_3311_ = lean_apply_10(v_p_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v___x_3310_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, lean_box(0));
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3337_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3337_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3337_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___y_3318_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v___x_3316_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2);
v___x_3326_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3327_ = lean_int_dec_le(v___x_3326_, v_c_3295_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3328_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3329_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3330_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3331_ = lean_int_neg(v_c_3295_);
v___x_3332_ = l_Int_toNat(v___x_3331_);
lean_dec(v___x_3331_);
v___x_3333_ = l_Lean_instToExprInt_mkNat(v___x_3332_);
v___x_3334_ = l_Lean_mkApp3(v___x_3328_, v___x_3329_, v___x_3330_, v___x_3333_);
v___y_3318_ = v___x_3334_;
goto v___jp_3317_;
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = l_Int_toNat(v_c_3295_);
v___x_3336_ = l_Lean_instToExprInt_mkNat(v___x_3335_);
v___y_3318_ = v___x_3336_;
goto v___jp_3317_;
}
v___jp_3317_:
{
lean_object* v_nil_3319_; lean_object* v_cons_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
v_nil_3319_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3320_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3321_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3319_, v_cons_3320_, v_x_3296_);
v___x_3322_ = l_Lean_mkApp4(v___x_3316_, v___y_3318_, v___x_3321_, v_a_3309_, v_a_3312_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3322_);
v___x_3324_ = v___x_3314_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
else
{
lean_dec(v_a_3309_);
return v___x_3311_;
}
}
else
{
lean_dec_ref(v_p_3297_);
return v___x_3308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object* v_c_3338_, lean_object* v_x_3339_, lean_object* v_p_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_){
_start:
{
uint8_t v_a_boxed_3351_; lean_object* v_res_3352_; 
v_a_boxed_3351_ = lean_unbox(v_a_3344_);
v_res_3352_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(v_c_3338_, v_x_3339_, v_p_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_boxed_3351_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
lean_dec(v_a_3349_);
lean_dec_ref(v_a_3348_);
lean_dec(v_a_3347_);
lean_dec_ref(v_a_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3343_);
lean_dec(v_a_3342_);
lean_dec(v_a_3341_);
lean_dec(v_x_3339_);
lean_dec(v_c_3338_);
return v_res_3352_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2(void){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = lean_box(0);
v___x_3360_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1));
v___x_3361_ = l_Lean_Expr_const___override(v___x_3360_, v___x_3359_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(lean_object* v_c_3362_, lean_object* v_x_3363_, lean_object* v_p_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, uint8_t v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3366_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
lean_dec_ref_known(v___x_3375_, 1);
v___x_3377_ = lean_box(v_a_3368_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc(v_a_3371_);
lean_inc_ref(v_a_3370_);
lean_inc(v_a_3369_);
lean_inc_ref(v_a_3367_);
lean_inc(v_a_3366_);
lean_inc(v_a_3365_);
v___x_3378_ = lean_apply_10(v_p_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v___x_3377_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, lean_box(0));
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3404_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3381_ = v___x_3378_;
v_isShared_3382_ = v_isSharedCheck_3404_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3378_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3404_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; lean_object* v___y_3385_; lean_object* v___x_3393_; uint8_t v___x_3394_; 
v___x_3383_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2);
v___x_3393_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3394_ = lean_int_dec_le(v___x_3393_, v_c_3362_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3395_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3396_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3397_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3398_ = lean_int_neg(v_c_3362_);
v___x_3399_ = l_Int_toNat(v___x_3398_);
lean_dec(v___x_3398_);
v___x_3400_ = l_Lean_instToExprInt_mkNat(v___x_3399_);
v___x_3401_ = l_Lean_mkApp3(v___x_3395_, v___x_3396_, v___x_3397_, v___x_3400_);
v___y_3385_ = v___x_3401_;
goto v___jp_3384_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = l_Int_toNat(v_c_3362_);
v___x_3403_ = l_Lean_instToExprInt_mkNat(v___x_3402_);
v___y_3385_ = v___x_3403_;
goto v___jp_3384_;
}
v___jp_3384_:
{
lean_object* v_nil_3386_; lean_object* v_cons_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3391_; 
v_nil_3386_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3387_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3388_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3386_, v_cons_3387_, v_x_3363_);
v___x_3389_ = l_Lean_mkApp4(v___x_3383_, v___y_3385_, v___x_3388_, v_a_3376_, v_a_3379_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 0, v___x_3389_);
v___x_3391_ = v___x_3381_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3389_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
else
{
lean_dec(v_a_3376_);
return v___x_3378_;
}
}
else
{
lean_dec_ref(v_p_3364_);
return v___x_3375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed(lean_object* v_c_3405_, lean_object* v_x_3406_, lean_object* v_p_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_){
_start:
{
uint8_t v_a_boxed_3418_; lean_object* v_res_3419_; 
v_a_boxed_3418_ = lean_unbox(v_a_3411_);
v_res_3419_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(v_c_3405_, v_x_3406_, v_p_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_boxed_3418_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_);
lean_dec(v_a_3416_);
lean_dec_ref(v_a_3415_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3410_);
lean_dec(v_a_3409_);
lean_dec(v_a_3408_);
lean_dec(v_x_3406_);
lean_dec(v_c_3405_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(lean_object* v_prf_x3f_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, uint8_t v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
if (lean_obj_tag(v_prf_x3f_3420_) == 0)
{
lean_object* v___x_3431_; uint8_t v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3431_ = lean_box(0);
v___x_3432_ = 0;
v___x_3433_ = lean_box(0);
v___x_3434_ = l_Lean_Meta_mkFreshExprMVar(v___x_3431_, v___x_3432_, v___x_3433_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; uint8_t v___x_3436_; lean_object* v___x_3437_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3434_, 1);
v___x_3436_ = 0;
v___x_3437_ = l_Lean_Meta_mkSorry(v_a_3435_, v___x_3436_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
return v___x_3437_;
}
else
{
return v___x_3434_;
}
}
else
{
lean_object* v_val_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v_val_3438_ = lean_ctor_get(v_prf_x3f_3420_, 0);
lean_inc(v_val_3438_);
lean_dec_ref_known(v_prf_x3f_3420_, 1);
v___x_3439_ = lean_box(v___y_3424_);
lean_inc(v___y_3429_);
lean_inc_ref(v___y_3428_);
lean_inc(v___y_3427_);
lean_inc_ref(v___y_3426_);
lean_inc(v___y_3425_);
lean_inc_ref(v___y_3423_);
lean_inc(v___y_3422_);
lean_inc(v___y_3421_);
v___x_3440_ = lean_apply_10(v_val_3438_, v___y_3421_, v___y_3422_, v___y_3423_, v___x_3439_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, lean_box(0));
return v___x_3440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed(lean_object* v_prf_x3f_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
uint8_t v___y_833__boxed_3452_; lean_object* v_res_3453_; 
v___y_833__boxed_3452_ = lean_unbox(v___y_3445_);
v_res_3453_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(v_prf_x3f_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_833__boxed_3452_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3442_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality(lean_object* v_p_3454_, lean_object* v_const_3455_, lean_object* v_coeffs_3456_, lean_object* v_prf_x3f_3457_){
_start:
{
lean_object* v_assumptions_3458_; lean_object* v_numVars_3459_; lean_object* v_constraints_3460_; lean_object* v_equalities_3461_; lean_object* v_eliminations_3462_; uint8_t v_possible_3463_; lean_object* v_proveFalse_x3f_3464_; lean_object* v_explanation_x3f_3465_; lean_object* v_prf_3466_; lean_object* v_i_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v_p_x27_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v_f_3476_; lean_object* v_f_3477_; lean_object* v_f_3478_; lean_object* v___x_3479_; 
v_assumptions_3458_ = lean_ctor_get(v_p_3454_, 0);
v_numVars_3459_ = lean_ctor_get(v_p_3454_, 1);
v_constraints_3460_ = lean_ctor_get(v_p_3454_, 2);
v_equalities_3461_ = lean_ctor_get(v_p_3454_, 3);
v_eliminations_3462_ = lean_ctor_get(v_p_3454_, 4);
v_possible_3463_ = lean_ctor_get_uint8(v_p_3454_, sizeof(void*)*7);
v_proveFalse_x3f_3464_ = lean_ctor_get(v_p_3454_, 5);
v_explanation_x3f_3465_ = lean_ctor_get(v_p_3454_, 6);
v_prf_3466_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3466_, 0, v_prf_x3f_3457_);
v_i_3467_ = lean_array_get_size(v_assumptions_3458_);
lean_inc_n(v_coeffs_3456_, 2);
lean_inc(v_const_3455_);
v___x_3468_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed), 13, 3);
lean_closure_set(v___x_3468_, 0, v_const_3455_);
lean_closure_set(v___x_3468_, 1, v_coeffs_3456_);
lean_closure_set(v___x_3468_, 2, v_prf_3466_);
lean_inc_ref(v_assumptions_3458_);
v___x_3469_ = lean_array_push(v_assumptions_3458_, v___x_3468_);
lean_inc_ref(v_explanation_x3f_3465_);
lean_inc(v_proveFalse_x3f_3464_);
lean_inc(v_eliminations_3462_);
lean_inc_ref(v_equalities_3461_);
lean_inc_ref(v_constraints_3460_);
lean_inc(v_numVars_3459_);
v_p_x27_3470_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3470_, 0, v___x_3469_);
lean_ctor_set(v_p_x27_3470_, 1, v_numVars_3459_);
lean_ctor_set(v_p_x27_3470_, 2, v_constraints_3460_);
lean_ctor_set(v_p_x27_3470_, 3, v_equalities_3461_);
lean_ctor_set(v_p_x27_3470_, 4, v_eliminations_3462_);
lean_ctor_set(v_p_x27_3470_, 5, v_proveFalse_x3f_3464_);
lean_ctor_set(v_p_x27_3470_, 6, v_explanation_x3f_3465_);
lean_ctor_set_uint8(v_p_x27_3470_, sizeof(void*)*7, v_possible_3463_);
v___x_3471_ = lean_int_neg(v_const_3455_);
lean_dec(v_const_3455_);
v___x_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
v___x_3473_ = lean_box(0);
v___x_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3472_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
lean_inc_ref(v___x_3474_);
v___x_3475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v_coeffs_3456_);
lean_ctor_set(v___x_3475_, 2, v_i_3467_);
v_f_3476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3476_, 0, v_coeffs_3456_);
lean_ctor_set(v_f_3476_, 1, v___x_3474_);
lean_ctor_set(v_f_3476_, 2, v___x_3475_);
v_f_3477_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3454_, v_f_3476_);
v_f_3478_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3477_);
v___x_3479_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3470_, v_f_3478_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality(lean_object* v_p_3480_, lean_object* v_const_3481_, lean_object* v_coeffs_3482_, lean_object* v_prf_x3f_3483_){
_start:
{
lean_object* v_assumptions_3484_; lean_object* v_numVars_3485_; lean_object* v_constraints_3486_; lean_object* v_equalities_3487_; lean_object* v_eliminations_3488_; uint8_t v_possible_3489_; lean_object* v_proveFalse_x3f_3490_; lean_object* v_explanation_x3f_3491_; lean_object* v_prf_3492_; lean_object* v_i_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v_p_x27_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v_f_3501_; lean_object* v_f_3502_; lean_object* v_f_3503_; lean_object* v___x_3504_; 
v_assumptions_3484_ = lean_ctor_get(v_p_3480_, 0);
v_numVars_3485_ = lean_ctor_get(v_p_3480_, 1);
v_constraints_3486_ = lean_ctor_get(v_p_3480_, 2);
v_equalities_3487_ = lean_ctor_get(v_p_3480_, 3);
v_eliminations_3488_ = lean_ctor_get(v_p_3480_, 4);
v_possible_3489_ = lean_ctor_get_uint8(v_p_3480_, sizeof(void*)*7);
v_proveFalse_x3f_3490_ = lean_ctor_get(v_p_3480_, 5);
v_explanation_x3f_3491_ = lean_ctor_get(v_p_3480_, 6);
v_prf_3492_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3492_, 0, v_prf_x3f_3483_);
v_i_3493_ = lean_array_get_size(v_assumptions_3484_);
lean_inc_n(v_coeffs_3482_, 2);
lean_inc(v_const_3481_);
v___x_3494_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed), 13, 3);
lean_closure_set(v___x_3494_, 0, v_const_3481_);
lean_closure_set(v___x_3494_, 1, v_coeffs_3482_);
lean_closure_set(v___x_3494_, 2, v_prf_3492_);
lean_inc_ref(v_assumptions_3484_);
v___x_3495_ = lean_array_push(v_assumptions_3484_, v___x_3494_);
lean_inc_ref(v_explanation_x3f_3491_);
lean_inc(v_proveFalse_x3f_3490_);
lean_inc(v_eliminations_3488_);
lean_inc_ref(v_equalities_3487_);
lean_inc_ref(v_constraints_3486_);
lean_inc(v_numVars_3485_);
v_p_x27_3496_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3496_, 0, v___x_3495_);
lean_ctor_set(v_p_x27_3496_, 1, v_numVars_3485_);
lean_ctor_set(v_p_x27_3496_, 2, v_constraints_3486_);
lean_ctor_set(v_p_x27_3496_, 3, v_equalities_3487_);
lean_ctor_set(v_p_x27_3496_, 4, v_eliminations_3488_);
lean_ctor_set(v_p_x27_3496_, 5, v_proveFalse_x3f_3490_);
lean_ctor_set(v_p_x27_3496_, 6, v_explanation_x3f_3491_);
lean_ctor_set_uint8(v_p_x27_3496_, sizeof(void*)*7, v_possible_3489_);
v___x_3497_ = lean_int_neg(v_const_3481_);
lean_dec(v_const_3481_);
v___x_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
lean_inc_ref(v___x_3498_);
v___x_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
lean_inc_ref(v___x_3499_);
v___x_3500_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v_coeffs_3482_);
lean_ctor_set(v___x_3500_, 2, v_i_3493_);
v_f_3501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3501_, 0, v_coeffs_3482_);
lean_ctor_set(v_f_3501_, 1, v___x_3499_);
lean_ctor_set(v_f_3501_, 2, v___x_3500_);
v_f_3502_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3480_, v_f_3501_);
v_f_3503_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3502_);
v___x_3504_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3496_, v_f_3503_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(lean_object* v_x_3505_, lean_object* v_x_3506_){
_start:
{
if (lean_obj_tag(v_x_3506_) == 0)
{
return v_x_3505_;
}
else
{
lean_object* v_head_3507_; lean_object* v_snd_3508_; lean_object* v_tail_3509_; lean_object* v_fst_3510_; lean_object* v_fst_3511_; lean_object* v_snd_3512_; lean_object* v___x_3513_; 
v_head_3507_ = lean_ctor_get(v_x_3506_, 0);
lean_inc(v_head_3507_);
v_snd_3508_ = lean_ctor_get(v_head_3507_, 1);
lean_inc(v_snd_3508_);
v_tail_3509_ = lean_ctor_get(v_x_3506_, 1);
lean_inc(v_tail_3509_);
lean_dec_ref_known(v_x_3506_, 2);
v_fst_3510_ = lean_ctor_get(v_head_3507_, 0);
lean_inc(v_fst_3510_);
lean_dec(v_head_3507_);
v_fst_3511_ = lean_ctor_get(v_snd_3508_, 0);
lean_inc(v_fst_3511_);
v_snd_3512_ = lean_ctor_get(v_snd_3508_, 1);
lean_inc(v_snd_3512_);
lean_dec(v_snd_3508_);
v___x_3513_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality(v_x_3505_, v_fst_3510_, v_fst_3511_, v_snd_3512_);
v_x_3505_ = v___x_3513_;
v_x_3506_ = v_tail_3509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequalities(lean_object* v_p_3515_, lean_object* v_ineqs_3516_){
_start:
{
lean_object* v___x_3517_; 
v___x_3517_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(v_p_3515_, v_ineqs_3516_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(lean_object* v_x_3518_, lean_object* v_x_3519_){
_start:
{
if (lean_obj_tag(v_x_3519_) == 0)
{
return v_x_3518_;
}
else
{
lean_object* v_head_3520_; lean_object* v_snd_3521_; lean_object* v_tail_3522_; lean_object* v_fst_3523_; lean_object* v_fst_3524_; lean_object* v_snd_3525_; lean_object* v___x_3526_; 
v_head_3520_ = lean_ctor_get(v_x_3519_, 0);
lean_inc(v_head_3520_);
v_snd_3521_ = lean_ctor_get(v_head_3520_, 1);
lean_inc(v_snd_3521_);
v_tail_3522_ = lean_ctor_get(v_x_3519_, 1);
lean_inc(v_tail_3522_);
lean_dec_ref_known(v_x_3519_, 2);
v_fst_3523_ = lean_ctor_get(v_head_3520_, 0);
lean_inc(v_fst_3523_);
lean_dec(v_head_3520_);
v_fst_3524_ = lean_ctor_get(v_snd_3521_, 0);
lean_inc(v_fst_3524_);
v_snd_3525_ = lean_ctor_get(v_snd_3521_, 1);
lean_inc(v_snd_3525_);
lean_dec(v_snd_3521_);
v___x_3526_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality(v_x_3518_, v_fst_3523_, v_fst_3524_, v_snd_3525_);
v_x_3518_ = v___x_3526_;
v_x_3519_ = v_tail_3522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEqualities(lean_object* v_p_3528_, lean_object* v_eqs_3529_){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(v_p_3528_, v_eqs_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0(lean_object* v___x_3537_, lean_object* v_x_3538_){
_start:
{
lean_object* v_constraint_3539_; lean_object* v_coeffs_3540_; lean_object* v_lowerBound_3541_; lean_object* v_upperBound_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___y_3547_; lean_object* v___y_3548_; 
v_constraint_3539_ = lean_ctor_get(v_x_3538_, 1);
lean_inc_ref(v_constraint_3539_);
v_coeffs_3540_ = lean_ctor_get(v_x_3538_, 0);
lean_inc(v_coeffs_3540_);
lean_dec_ref(v_x_3538_);
v_lowerBound_3541_ = lean_ctor_get(v_constraint_3539_, 0);
lean_inc(v_lowerBound_3541_);
v_upperBound_3542_ = lean_ctor_get(v_constraint_3539_, 1);
lean_inc(v_upperBound_3542_);
lean_dec_ref(v_constraint_3539_);
v___x_3543_ = l_List_toString___redArg(v___x_3537_, v_coeffs_3540_);
v___x_3544_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3545_ = lean_string_append(v___x_3543_, v___x_3544_);
if (lean_obj_tag(v_lowerBound_3541_) == 0)
{
if (lean_obj_tag(v_upperBound_3542_) == 0)
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3554_ = lean_string_append(v___x_3545_, v___x_3553_);
return v___x_3554_;
}
else
{
lean_object* v_val_3555_; lean_object* v___x_3556_; lean_object* v___y_3558_; lean_object* v_intZero_3563_; uint8_t v_isNeg_3564_; 
v_val_3555_ = lean_ctor_get(v_upperBound_3542_, 0);
lean_inc(v_val_3555_);
lean_dec_ref_known(v_upperBound_3542_, 1);
v___x_3556_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3563_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3564_ = lean_int_dec_lt(v_val_3555_, v_intZero_3563_);
if (v_isNeg_3564_ == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3566_; 
v_a_3565_ = lean_nat_abs(v_val_3555_);
lean_dec(v_val_3555_);
v___x_3566_ = l_Nat_reprFast(v_a_3565_);
v___y_3558_ = v___x_3566_;
goto v___jp_3557_;
}
else
{
lean_object* v_abs_3567_; lean_object* v_one_3568_; lean_object* v_a_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v_abs_3567_ = lean_nat_abs(v_val_3555_);
lean_dec(v_val_3555_);
v_one_3568_ = lean_unsigned_to_nat(1u);
v_a_3569_ = lean_nat_sub(v_abs_3567_, v_one_3568_);
lean_dec(v_abs_3567_);
v___x_3570_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3571_ = lean_nat_add(v_a_3569_, v_one_3568_);
lean_dec(v_a_3569_);
v___x_3572_ = l_Nat_reprFast(v___x_3571_);
v___x_3573_ = lean_string_append(v___x_3570_, v___x_3572_);
lean_dec_ref(v___x_3572_);
v___y_3558_ = v___x_3573_;
goto v___jp_3557_;
}
v___jp_3557_:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3559_ = lean_string_append(v___x_3556_, v___y_3558_);
lean_dec_ref(v___y_3558_);
v___x_3560_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3561_ = lean_string_append(v___x_3559_, v___x_3560_);
v___x_3562_ = lean_string_append(v___x_3545_, v___x_3561_);
lean_dec_ref(v___x_3561_);
return v___x_3562_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3542_) == 0)
{
lean_object* v_val_3574_; lean_object* v___x_3575_; lean_object* v___y_3577_; lean_object* v_intZero_3582_; uint8_t v_isNeg_3583_; 
v_val_3574_ = lean_ctor_get(v_lowerBound_3541_, 0);
lean_inc(v_val_3574_);
lean_dec_ref_known(v_lowerBound_3541_, 1);
v___x_3575_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3582_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3583_ = lean_int_dec_lt(v_val_3574_, v_intZero_3582_);
if (v_isNeg_3583_ == 0)
{
lean_object* v_a_3584_; lean_object* v___x_3585_; 
v_a_3584_ = lean_nat_abs(v_val_3574_);
lean_dec(v_val_3574_);
v___x_3585_ = l_Nat_reprFast(v_a_3584_);
v___y_3577_ = v___x_3585_;
goto v___jp_3576_;
}
else
{
lean_object* v_abs_3586_; lean_object* v_one_3587_; lean_object* v_a_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v_abs_3586_ = lean_nat_abs(v_val_3574_);
lean_dec(v_val_3574_);
v_one_3587_ = lean_unsigned_to_nat(1u);
v_a_3588_ = lean_nat_sub(v_abs_3586_, v_one_3587_);
lean_dec(v_abs_3586_);
v___x_3589_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3590_ = lean_nat_add(v_a_3588_, v_one_3587_);
lean_dec(v_a_3588_);
v___x_3591_ = l_Nat_reprFast(v___x_3590_);
v___x_3592_ = lean_string_append(v___x_3589_, v___x_3591_);
lean_dec_ref(v___x_3591_);
v___y_3577_ = v___x_3592_;
goto v___jp_3576_;
}
v___jp_3576_:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3578_ = lean_string_append(v___x_3575_, v___y_3577_);
lean_dec_ref(v___y_3577_);
v___x_3579_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3580_ = lean_string_append(v___x_3578_, v___x_3579_);
v___x_3581_ = lean_string_append(v___x_3545_, v___x_3580_);
lean_dec_ref(v___x_3580_);
return v___x_3581_;
}
}
else
{
lean_object* v_val_3593_; lean_object* v_val_3594_; uint8_t v___x_3595_; 
v_val_3593_ = lean_ctor_get(v_lowerBound_3541_, 0);
lean_inc(v_val_3593_);
lean_dec_ref_known(v_lowerBound_3541_, 1);
v_val_3594_ = lean_ctor_get(v_upperBound_3542_, 0);
lean_inc(v_val_3594_);
lean_dec_ref_known(v_upperBound_3542_, 1);
v___x_3595_ = lean_int_dec_lt(v_val_3594_, v_val_3593_);
if (v___x_3595_ == 0)
{
uint8_t v___x_3596_; 
v___x_3596_ = lean_int_dec_eq(v_val_3593_, v_val_3594_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; lean_object* v___y_3599_; lean_object* v_intZero_3614_; uint8_t v_isNeg_3615_; 
v___x_3597_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3614_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3615_ = lean_int_dec_lt(v_val_3593_, v_intZero_3614_);
if (v_isNeg_3615_ == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3617_; 
v_a_3616_ = lean_nat_abs(v_val_3593_);
lean_dec(v_val_3593_);
v___x_3617_ = l_Nat_reprFast(v_a_3616_);
v___y_3599_ = v___x_3617_;
goto v___jp_3598_;
}
else
{
lean_object* v_abs_3618_; lean_object* v_one_3619_; lean_object* v_a_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v_abs_3618_ = lean_nat_abs(v_val_3593_);
lean_dec(v_val_3593_);
v_one_3619_ = lean_unsigned_to_nat(1u);
v_a_3620_ = lean_nat_sub(v_abs_3618_, v_one_3619_);
lean_dec(v_abs_3618_);
v___x_3621_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3622_ = lean_nat_add(v_a_3620_, v_one_3619_);
lean_dec(v_a_3620_);
v___x_3623_ = l_Nat_reprFast(v___x_3622_);
v___x_3624_ = lean_string_append(v___x_3621_, v___x_3623_);
lean_dec_ref(v___x_3623_);
v___y_3599_ = v___x_3624_;
goto v___jp_3598_;
}
v___jp_3598_:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v_intZero_3603_; uint8_t v_isNeg_3604_; 
v___x_3600_ = lean_string_append(v___x_3597_, v___y_3599_);
lean_dec_ref(v___y_3599_);
v___x_3601_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3602_ = lean_string_append(v___x_3600_, v___x_3601_);
v_intZero_3603_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3604_ = lean_int_dec_lt(v_val_3594_, v_intZero_3603_);
if (v_isNeg_3604_ == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3606_; 
v_a_3605_ = lean_nat_abs(v_val_3594_);
lean_dec(v_val_3594_);
v___x_3606_ = l_Nat_reprFast(v_a_3605_);
v___y_3547_ = v___x_3602_;
v___y_3548_ = v___x_3606_;
goto v___jp_3546_;
}
else
{
lean_object* v_abs_3607_; lean_object* v_one_3608_; lean_object* v_a_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v_abs_3607_ = lean_nat_abs(v_val_3594_);
lean_dec(v_val_3594_);
v_one_3608_ = lean_unsigned_to_nat(1u);
v_a_3609_ = lean_nat_sub(v_abs_3607_, v_one_3608_);
lean_dec(v_abs_3607_);
v___x_3610_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3611_ = lean_nat_add(v_a_3609_, v_one_3608_);
lean_dec(v_a_3609_);
v___x_3612_ = l_Nat_reprFast(v___x_3611_);
v___x_3613_ = lean_string_append(v___x_3610_, v___x_3612_);
lean_dec_ref(v___x_3612_);
v___y_3547_ = v___x_3602_;
v___y_3548_ = v___x_3613_;
goto v___jp_3546_;
}
}
}
else
{
lean_object* v___x_3625_; lean_object* v___y_3627_; lean_object* v_intZero_3632_; uint8_t v_isNeg_3633_; 
lean_dec(v_val_3594_);
v___x_3625_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3632_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3633_ = lean_int_dec_lt(v_val_3593_, v_intZero_3632_);
if (v_isNeg_3633_ == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3635_; 
v_a_3634_ = lean_nat_abs(v_val_3593_);
lean_dec(v_val_3593_);
v___x_3635_ = l_Nat_reprFast(v_a_3634_);
v___y_3627_ = v___x_3635_;
goto v___jp_3626_;
}
else
{
lean_object* v_abs_3636_; lean_object* v_one_3637_; lean_object* v_a_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v_abs_3636_ = lean_nat_abs(v_val_3593_);
lean_dec(v_val_3593_);
v_one_3637_ = lean_unsigned_to_nat(1u);
v_a_3638_ = lean_nat_sub(v_abs_3636_, v_one_3637_);
lean_dec(v_abs_3636_);
v___x_3639_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3640_ = lean_nat_add(v_a_3638_, v_one_3637_);
lean_dec(v_a_3638_);
v___x_3641_ = l_Nat_reprFast(v___x_3640_);
v___x_3642_ = lean_string_append(v___x_3639_, v___x_3641_);
lean_dec_ref(v___x_3641_);
v___y_3627_ = v___x_3642_;
goto v___jp_3626_;
}
v___jp_3626_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3628_ = lean_string_append(v___x_3625_, v___y_3627_);
lean_dec_ref(v___y_3627_);
v___x_3629_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3630_ = lean_string_append(v___x_3628_, v___x_3629_);
v___x_3631_ = lean_string_append(v___x_3545_, v___x_3630_);
lean_dec_ref(v___x_3630_);
return v___x_3631_;
}
}
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
lean_dec(v_val_3594_);
lean_dec(v_val_3593_);
v___x_3643_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3644_ = lean_string_append(v___x_3545_, v___x_3643_);
return v___x_3644_;
}
}
}
v___jp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3549_ = lean_string_append(v___y_3547_, v___y_3548_);
lean_dec_ref(v___y_3548_);
v___x_3550_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3551_ = lean_string_append(v___x_3549_, v___x_3550_);
v___x_3552_ = lean_string_append(v___x_3545_, v___x_3551_);
lean_dec_ref(v___x_3551_);
return v___x_3552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1(lean_object* v___x_3645_, lean_object* v_x_3646_){
_start:
{
lean_object* v_fst_3647_; lean_object* v_constraint_3648_; lean_object* v_coeffs_3649_; lean_object* v_lowerBound_3650_; lean_object* v_upperBound_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___y_3656_; lean_object* v___y_3657_; 
v_fst_3647_ = lean_ctor_get(v_x_3646_, 0);
lean_inc(v_fst_3647_);
lean_dec_ref(v_x_3646_);
v_constraint_3648_ = lean_ctor_get(v_fst_3647_, 1);
lean_inc_ref(v_constraint_3648_);
v_coeffs_3649_ = lean_ctor_get(v_fst_3647_, 0);
lean_inc(v_coeffs_3649_);
lean_dec(v_fst_3647_);
v_lowerBound_3650_ = lean_ctor_get(v_constraint_3648_, 0);
lean_inc(v_lowerBound_3650_);
v_upperBound_3651_ = lean_ctor_get(v_constraint_3648_, 1);
lean_inc(v_upperBound_3651_);
lean_dec_ref(v_constraint_3648_);
v___x_3652_ = l_List_toString___redArg(v___x_3645_, v_coeffs_3649_);
v___x_3653_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3654_ = lean_string_append(v___x_3652_, v___x_3653_);
if (lean_obj_tag(v_lowerBound_3650_) == 0)
{
if (lean_obj_tag(v_upperBound_3651_) == 0)
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3663_ = lean_string_append(v___x_3654_, v___x_3662_);
return v___x_3663_;
}
else
{
lean_object* v_val_3664_; lean_object* v___x_3665_; lean_object* v___y_3667_; lean_object* v_intZero_3672_; uint8_t v_isNeg_3673_; 
v_val_3664_ = lean_ctor_get(v_upperBound_3651_, 0);
lean_inc(v_val_3664_);
lean_dec_ref_known(v_upperBound_3651_, 1);
v___x_3665_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3672_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3673_ = lean_int_dec_lt(v_val_3664_, v_intZero_3672_);
if (v_isNeg_3673_ == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3675_; 
v_a_3674_ = lean_nat_abs(v_val_3664_);
lean_dec(v_val_3664_);
v___x_3675_ = l_Nat_reprFast(v_a_3674_);
v___y_3667_ = v___x_3675_;
goto v___jp_3666_;
}
else
{
lean_object* v_abs_3676_; lean_object* v_one_3677_; lean_object* v_a_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v_abs_3676_ = lean_nat_abs(v_val_3664_);
lean_dec(v_val_3664_);
v_one_3677_ = lean_unsigned_to_nat(1u);
v_a_3678_ = lean_nat_sub(v_abs_3676_, v_one_3677_);
lean_dec(v_abs_3676_);
v___x_3679_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3680_ = lean_nat_add(v_a_3678_, v_one_3677_);
lean_dec(v_a_3678_);
v___x_3681_ = l_Nat_reprFast(v___x_3680_);
v___x_3682_ = lean_string_append(v___x_3679_, v___x_3681_);
lean_dec_ref(v___x_3681_);
v___y_3667_ = v___x_3682_;
goto v___jp_3666_;
}
v___jp_3666_:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3668_ = lean_string_append(v___x_3665_, v___y_3667_);
lean_dec_ref(v___y_3667_);
v___x_3669_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3670_ = lean_string_append(v___x_3668_, v___x_3669_);
v___x_3671_ = lean_string_append(v___x_3654_, v___x_3670_);
lean_dec_ref(v___x_3670_);
return v___x_3671_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3651_) == 0)
{
lean_object* v_val_3683_; lean_object* v___x_3684_; lean_object* v___y_3686_; lean_object* v_intZero_3691_; uint8_t v_isNeg_3692_; 
v_val_3683_ = lean_ctor_get(v_lowerBound_3650_, 0);
lean_inc(v_val_3683_);
lean_dec_ref_known(v_lowerBound_3650_, 1);
v___x_3684_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3691_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3692_ = lean_int_dec_lt(v_val_3683_, v_intZero_3691_);
if (v_isNeg_3692_ == 0)
{
lean_object* v_a_3693_; lean_object* v___x_3694_; 
v_a_3693_ = lean_nat_abs(v_val_3683_);
lean_dec(v_val_3683_);
v___x_3694_ = l_Nat_reprFast(v_a_3693_);
v___y_3686_ = v___x_3694_;
goto v___jp_3685_;
}
else
{
lean_object* v_abs_3695_; lean_object* v_one_3696_; lean_object* v_a_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v_abs_3695_ = lean_nat_abs(v_val_3683_);
lean_dec(v_val_3683_);
v_one_3696_ = lean_unsigned_to_nat(1u);
v_a_3697_ = lean_nat_sub(v_abs_3695_, v_one_3696_);
lean_dec(v_abs_3695_);
v___x_3698_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3699_ = lean_nat_add(v_a_3697_, v_one_3696_);
lean_dec(v_a_3697_);
v___x_3700_ = l_Nat_reprFast(v___x_3699_);
v___x_3701_ = lean_string_append(v___x_3698_, v___x_3700_);
lean_dec_ref(v___x_3700_);
v___y_3686_ = v___x_3701_;
goto v___jp_3685_;
}
v___jp_3685_:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3687_ = lean_string_append(v___x_3684_, v___y_3686_);
lean_dec_ref(v___y_3686_);
v___x_3688_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3689_ = lean_string_append(v___x_3687_, v___x_3688_);
v___x_3690_ = lean_string_append(v___x_3654_, v___x_3689_);
lean_dec_ref(v___x_3689_);
return v___x_3690_;
}
}
else
{
lean_object* v_val_3702_; lean_object* v_val_3703_; uint8_t v___x_3704_; 
v_val_3702_ = lean_ctor_get(v_lowerBound_3650_, 0);
lean_inc(v_val_3702_);
lean_dec_ref_known(v_lowerBound_3650_, 1);
v_val_3703_ = lean_ctor_get(v_upperBound_3651_, 0);
lean_inc(v_val_3703_);
lean_dec_ref_known(v_upperBound_3651_, 1);
v___x_3704_ = lean_int_dec_lt(v_val_3703_, v_val_3702_);
if (v___x_3704_ == 0)
{
uint8_t v___x_3705_; 
v___x_3705_ = lean_int_dec_eq(v_val_3702_, v_val_3703_);
if (v___x_3705_ == 0)
{
lean_object* v___x_3706_; lean_object* v___y_3708_; lean_object* v_intZero_3723_; uint8_t v_isNeg_3724_; 
v___x_3706_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3723_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3724_ = lean_int_dec_lt(v_val_3702_, v_intZero_3723_);
if (v_isNeg_3724_ == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3726_; 
v_a_3725_ = lean_nat_abs(v_val_3702_);
lean_dec(v_val_3702_);
v___x_3726_ = l_Nat_reprFast(v_a_3725_);
v___y_3708_ = v___x_3726_;
goto v___jp_3707_;
}
else
{
lean_object* v_abs_3727_; lean_object* v_one_3728_; lean_object* v_a_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v_abs_3727_ = lean_nat_abs(v_val_3702_);
lean_dec(v_val_3702_);
v_one_3728_ = lean_unsigned_to_nat(1u);
v_a_3729_ = lean_nat_sub(v_abs_3727_, v_one_3728_);
lean_dec(v_abs_3727_);
v___x_3730_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3731_ = lean_nat_add(v_a_3729_, v_one_3728_);
lean_dec(v_a_3729_);
v___x_3732_ = l_Nat_reprFast(v___x_3731_);
v___x_3733_ = lean_string_append(v___x_3730_, v___x_3732_);
lean_dec_ref(v___x_3732_);
v___y_3708_ = v___x_3733_;
goto v___jp_3707_;
}
v___jp_3707_:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v_intZero_3712_; uint8_t v_isNeg_3713_; 
v___x_3709_ = lean_string_append(v___x_3706_, v___y_3708_);
lean_dec_ref(v___y_3708_);
v___x_3710_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3711_ = lean_string_append(v___x_3709_, v___x_3710_);
v_intZero_3712_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3713_ = lean_int_dec_lt(v_val_3703_, v_intZero_3712_);
if (v_isNeg_3713_ == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; 
v_a_3714_ = lean_nat_abs(v_val_3703_);
lean_dec(v_val_3703_);
v___x_3715_ = l_Nat_reprFast(v_a_3714_);
v___y_3656_ = v___x_3711_;
v___y_3657_ = v___x_3715_;
goto v___jp_3655_;
}
else
{
lean_object* v_abs_3716_; lean_object* v_one_3717_; lean_object* v_a_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v_abs_3716_ = lean_nat_abs(v_val_3703_);
lean_dec(v_val_3703_);
v_one_3717_ = lean_unsigned_to_nat(1u);
v_a_3718_ = lean_nat_sub(v_abs_3716_, v_one_3717_);
lean_dec(v_abs_3716_);
v___x_3719_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3720_ = lean_nat_add(v_a_3718_, v_one_3717_);
lean_dec(v_a_3718_);
v___x_3721_ = l_Nat_reprFast(v___x_3720_);
v___x_3722_ = lean_string_append(v___x_3719_, v___x_3721_);
lean_dec_ref(v___x_3721_);
v___y_3656_ = v___x_3711_;
v___y_3657_ = v___x_3722_;
goto v___jp_3655_;
}
}
}
else
{
lean_object* v___x_3734_; lean_object* v___y_3736_; lean_object* v_intZero_3741_; uint8_t v_isNeg_3742_; 
lean_dec(v_val_3703_);
v___x_3734_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3741_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3742_ = lean_int_dec_lt(v_val_3702_, v_intZero_3741_);
if (v_isNeg_3742_ == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3744_; 
v_a_3743_ = lean_nat_abs(v_val_3702_);
lean_dec(v_val_3702_);
v___x_3744_ = l_Nat_reprFast(v_a_3743_);
v___y_3736_ = v___x_3744_;
goto v___jp_3735_;
}
else
{
lean_object* v_abs_3745_; lean_object* v_one_3746_; lean_object* v_a_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v_abs_3745_ = lean_nat_abs(v_val_3702_);
lean_dec(v_val_3702_);
v_one_3746_ = lean_unsigned_to_nat(1u);
v_a_3747_ = lean_nat_sub(v_abs_3745_, v_one_3746_);
lean_dec(v_abs_3745_);
v___x_3748_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3749_ = lean_nat_add(v_a_3747_, v_one_3746_);
lean_dec(v_a_3747_);
v___x_3750_ = l_Nat_reprFast(v___x_3749_);
v___x_3751_ = lean_string_append(v___x_3748_, v___x_3750_);
lean_dec_ref(v___x_3750_);
v___y_3736_ = v___x_3751_;
goto v___jp_3735_;
}
v___jp_3735_:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3737_ = lean_string_append(v___x_3734_, v___y_3736_);
lean_dec_ref(v___y_3736_);
v___x_3738_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3739_ = lean_string_append(v___x_3737_, v___x_3738_);
v___x_3740_ = lean_string_append(v___x_3654_, v___x_3739_);
lean_dec_ref(v___x_3739_);
return v___x_3740_;
}
}
}
else
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_dec(v_val_3703_);
lean_dec(v_val_3702_);
v___x_3752_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3753_ = lean_string_append(v___x_3654_, v___x_3752_);
return v___x_3753_;
}
}
}
v___jp_3655_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3658_ = lean_string_append(v___y_3656_, v___y_3657_);
lean_dec_ref(v___y_3657_);
v___x_3659_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3660_ = lean_string_append(v___x_3658_, v___x_3659_);
v___x_3661_ = lean_string_append(v___x_3654_, v___x_3660_);
lean_dec_ref(v___x_3660_);
return v___x_3661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2(lean_object* v___f_3758_, lean_object* v___f_3759_, lean_object* v___f_3760_, lean_object* v_d_3761_){
_start:
{
lean_object* v_var_3762_; lean_object* v_irrelevant_3763_; lean_object* v_lowerBounds_3764_; lean_object* v_upperBounds_3765_; lean_object* v___x_3766_; lean_object* v_irrelevant_3767_; lean_object* v_lowerBounds_3768_; lean_object* v_upperBounds_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v_var_3762_ = lean_ctor_get(v_d_3761_, 0);
lean_inc(v_var_3762_);
v_irrelevant_3763_ = lean_ctor_get(v_d_3761_, 1);
lean_inc(v_irrelevant_3763_);
v_lowerBounds_3764_ = lean_ctor_get(v_d_3761_, 2);
lean_inc(v_lowerBounds_3764_);
v_upperBounds_3765_ = lean_ctor_get(v_d_3761_, 3);
lean_inc(v_upperBounds_3765_);
lean_dec_ref(v_d_3761_);
v___x_3766_ = lean_box(0);
v_irrelevant_3767_ = l_List_mapTR_loop___redArg(v___f_3758_, v_irrelevant_3763_, v___x_3766_);
lean_inc_ref(v___f_3759_);
v_lowerBounds_3768_ = l_List_mapTR_loop___redArg(v___f_3759_, v_lowerBounds_3764_, v___x_3766_);
v_upperBounds_3769_ = l_List_mapTR_loop___redArg(v___f_3759_, v_upperBounds_3765_, v___x_3766_);
v___x_3770_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0));
v___x_3771_ = l_Nat_reprFast(v_var_3762_);
v___x_3772_ = lean_string_append(v___x_3770_, v___x_3771_);
lean_dec_ref(v___x_3771_);
v___x_3773_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_3774_ = lean_string_append(v___x_3772_, v___x_3773_);
v___x_3775_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1));
lean_inc_ref_n(v___f_3760_, 2);
v___x_3776_ = l_List_toString___redArg(v___f_3760_, v_irrelevant_3767_);
v___x_3777_ = lean_string_append(v___x_3775_, v___x_3776_);
lean_dec_ref(v___x_3776_);
v___x_3778_ = lean_string_append(v___x_3777_, v___x_3773_);
v___x_3779_ = lean_string_append(v___x_3774_, v___x_3778_);
lean_dec_ref(v___x_3778_);
v___x_3780_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2));
v___x_3781_ = l_List_toString___redArg(v___f_3760_, v_lowerBounds_3768_);
v___x_3782_ = lean_string_append(v___x_3780_, v___x_3781_);
lean_dec_ref(v___x_3781_);
v___x_3783_ = lean_string_append(v___x_3782_, v___x_3773_);
v___x_3784_ = lean_string_append(v___x_3779_, v___x_3783_);
lean_dec_ref(v___x_3783_);
v___x_3785_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3));
v___x_3786_ = l_List_toString___redArg(v___f_3760_, v_upperBounds_3769_);
v___x_3787_ = lean_string_append(v___x_3785_, v___x_3786_);
lean_dec_ref(v___x_3786_);
v___x_3788_ = lean_string_append(v___x_3784_, v___x_3787_);
lean_dec_ref(v___x_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(lean_object* v_d_3799_){
_start:
{
lean_object* v_lowerBounds_3800_; lean_object* v_upperBounds_3801_; uint8_t v___x_3802_; 
v_lowerBounds_3800_ = lean_ctor_get(v_d_3799_, 2);
v_upperBounds_3801_ = lean_ctor_get(v_d_3799_, 3);
v___x_3802_ = l_List_isEmpty___redArg(v_lowerBounds_3800_);
if (v___x_3802_ == 0)
{
return v___x_3802_;
}
else
{
uint8_t v___x_3803_; 
v___x_3803_ = l_List_isEmpty___redArg(v_upperBounds_3801_);
return v___x_3803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty___boxed(lean_object* v_d_3804_){
_start:
{
uint8_t v_res_3805_; lean_object* v_r_3806_; 
v_res_3805_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v_d_3804_);
lean_dec_ref(v_d_3804_);
v_r_3806_ = lean_box(v_res_3805_);
return v_r_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(lean_object* v_d_3807_){
_start:
{
lean_object* v_lowerBounds_3808_; lean_object* v_upperBounds_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v_lowerBounds_3808_ = lean_ctor_get(v_d_3807_, 2);
v_upperBounds_3809_ = lean_ctor_get(v_d_3807_, 3);
v___x_3810_ = l_List_lengthTR___redArg(v_lowerBounds_3808_);
v___x_3811_ = l_List_lengthTR___redArg(v_upperBounds_3809_);
v___x_3812_ = lean_nat_mul(v___x_3810_, v___x_3811_);
lean_dec(v___x_3811_);
lean_dec(v___x_3810_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size___boxed(lean_object* v_d_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_d_3813_);
lean_dec_ref(v_d_3813_);
return v_res_3814_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(lean_object* v_d_3815_){
_start:
{
uint8_t v_lowerExact_3816_; 
v_lowerExact_3816_ = lean_ctor_get_uint8(v_d_3815_, sizeof(void*)*4);
if (v_lowerExact_3816_ == 0)
{
uint8_t v_upperExact_3817_; 
v_upperExact_3817_ = lean_ctor_get_uint8(v_d_3815_, sizeof(void*)*4 + 1);
return v_upperExact_3817_;
}
else
{
return v_lowerExact_3816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact___boxed(lean_object* v_d_3818_){
_start:
{
uint8_t v_res_3819_; lean_object* v_r_3820_; 
v_res_3819_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_d_3818_);
lean_dec_ref(v_d_3818_);
v_r_3820_ = lean_box(v_res_3819_);
return v_r_3820_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(lean_object* v_x_3821_, lean_object* v_x_3822_){
_start:
{
if (lean_obj_tag(v_x_3822_) == 0)
{
return v_x_3821_;
}
else
{
lean_object* v_head_3823_; lean_object* v_tail_3824_; lean_object* v___x_3825_; uint8_t v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v_head_3823_ = lean_ctor_get(v_x_3822_, 0);
v_tail_3824_ = lean_ctor_get(v_x_3822_, 1);
v___x_3825_ = lean_box(0);
v___x_3826_ = 1;
lean_inc(v_head_3823_);
v___x_3827_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3827_, 0, v_head_3823_);
lean_ctor_set(v___x_3827_, 1, v___x_3825_);
lean_ctor_set(v___x_3827_, 2, v___x_3825_);
lean_ctor_set(v___x_3827_, 3, v___x_3825_);
lean_ctor_set_uint8(v___x_3827_, sizeof(void*)*4, v___x_3826_);
lean_ctor_set_uint8(v___x_3827_, sizeof(void*)*4 + 1, v___x_3826_);
v___x_3828_ = lean_array_push(v_x_3821_, v___x_3827_);
v_x_3821_ = v___x_3828_;
v_x_3822_ = v_tail_3824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2___boxed(lean_object* v_x_3830_, lean_object* v_x_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v_x_3830_, v_x_3831_);
lean_dec(v_x_3831_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object* v___x_3833_, lean_object* v_b_3834_, lean_object* v___x_3835_, uint8_t v___x_3836_, lean_object* v_____r_3837_, lean_object* v_d_x27_3838_){
_start:
{
lean_object* v_upperBound_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3866_; 
v_upperBound_3839_ = lean_ctor_get(v___x_3833_, 1);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3866_ == 0)
{
lean_object* v_unused_3867_; 
v_unused_3867_ = lean_ctor_get(v___x_3833_, 0);
lean_dec(v_unused_3867_);
v___x_3841_ = v___x_3833_;
v_isShared_3842_ = v_isSharedCheck_3866_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_upperBound_3839_);
lean_dec(v___x_3833_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3866_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
if (lean_obj_tag(v_upperBound_3839_) == 0)
{
lean_del_object(v___x_3841_);
lean_dec(v___x_3835_);
lean_dec_ref(v_b_3834_);
return v_d_x27_3838_;
}
else
{
lean_object* v_var_3843_; lean_object* v_irrelevant_3844_; lean_object* v_lowerBounds_3845_; lean_object* v_upperBounds_3846_; uint8_t v_lowerExact_3847_; uint8_t v_upperExact_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3865_; 
lean_dec_ref_known(v_upperBound_3839_, 1);
v_var_3843_ = lean_ctor_get(v_d_x27_3838_, 0);
v_irrelevant_3844_ = lean_ctor_get(v_d_x27_3838_, 1);
v_lowerBounds_3845_ = lean_ctor_get(v_d_x27_3838_, 2);
v_upperBounds_3846_ = lean_ctor_get(v_d_x27_3838_, 3);
v_lowerExact_3847_ = lean_ctor_get_uint8(v_d_x27_3838_, sizeof(void*)*4);
v_upperExact_3848_ = lean_ctor_get_uint8(v_d_x27_3838_, sizeof(void*)*4 + 1);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_d_x27_3838_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3850_ = v_d_x27_3838_;
v_isShared_3851_ = v_isSharedCheck_3865_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_upperBounds_3846_);
lean_inc(v_lowerBounds_3845_);
lean_inc(v_irrelevant_3844_);
lean_inc(v_var_3843_);
lean_dec(v_d_x27_3838_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3865_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
lean_inc(v___x_3835_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 1, v___x_3835_);
lean_ctor_set(v___x_3841_, 0, v_b_3834_);
v___x_3853_ = v___x_3841_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_b_3834_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v___x_3835_);
v___x_3853_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v___x_3854_; 
v___x_3854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3853_);
lean_ctor_set(v___x_3854_, 1, v_upperBounds_3846_);
if (v_upperExact_3848_ == 0)
{
lean_object* v___x_3856_; 
lean_dec(v___x_3835_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 3, v___x_3854_);
v___x_3856_ = v___x_3850_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_var_3843_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v_irrelevant_3844_);
lean_ctor_set(v_reuseFailAlloc_3857_, 2, v_lowerBounds_3845_);
lean_ctor_set(v_reuseFailAlloc_3857_, 3, v___x_3854_);
lean_ctor_set_uint8(v_reuseFailAlloc_3857_, sizeof(void*)*4, v_lowerExact_3847_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_ctor_set_uint8(v___x_3856_, sizeof(void*)*4 + 1, v___x_3836_);
return v___x_3856_;
}
}
else
{
lean_object* v___x_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; lean_object* v___x_3862_; 
v___x_3858_ = lean_nat_abs(v___x_3835_);
lean_dec(v___x_3835_);
v___x_3859_ = lean_unsigned_to_nat(1u);
v___x_3860_ = lean_nat_dec_eq(v___x_3858_, v___x_3859_);
lean_dec(v___x_3858_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 3, v___x_3854_);
v___x_3862_ = v___x_3850_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_var_3843_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_irrelevant_3844_);
lean_ctor_set(v_reuseFailAlloc_3863_, 2, v_lowerBounds_3845_);
lean_ctor_set(v_reuseFailAlloc_3863_, 3, v___x_3854_);
lean_ctor_set_uint8(v_reuseFailAlloc_3863_, sizeof(void*)*4, v_lowerExact_3847_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_ctor_set_uint8(v___x_3862_, sizeof(void*)*4 + 1, v___x_3860_);
return v___x_3862_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0___boxed(lean_object* v___x_3868_, lean_object* v_b_3869_, lean_object* v___x_3870_, lean_object* v___x_3871_, lean_object* v_____r_3872_, lean_object* v_d_x27_3873_){
_start:
{
uint8_t v___x_1958__boxed_3874_; lean_object* v_res_3875_; 
v___x_1958__boxed_3874_ = lean_unbox(v___x_3871_);
v_res_3875_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3868_, v_b_3869_, v___x_3870_, v___x_1958__boxed_3874_, v_____r_3872_, v_d_x27_3873_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(lean_object* v_upperBound_3876_, lean_object* v_coeffs_3877_, lean_object* v_constraint_3878_, lean_object* v_b_3879_, lean_object* v_a_3880_, lean_object* v_b_3881_){
_start:
{
lean_object* v_a_3883_; uint8_t v___x_3887_; 
v___x_3887_ = lean_nat_dec_lt(v_a_3880_, v_upperBound_3876_);
if (v___x_3887_ == 0)
{
lean_dec(v_a_3880_);
lean_dec_ref(v_b_3879_);
lean_dec_ref(v_constraint_3878_);
return v_b_3881_;
}
else
{
lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3888_ = lean_array_get_size(v_b_3881_);
v___x_3889_ = lean_nat_dec_lt(v_a_3880_, v___x_3888_);
if (v___x_3889_ == 0)
{
v_a_3883_ = v_b_3881_;
goto v___jp_3882_;
}
else
{
lean_object* v___x_3890_; lean_object* v_v_3891_; lean_object* v___x_3892_; lean_object* v_xs_x27_3893_; lean_object* v___y_3895_; lean_object* v___x_3897_; uint8_t v___x_3898_; 
lean_inc(v_a_3880_);
v___x_3890_ = l_Lean_Omega_IntList_get(v_coeffs_3877_, v_a_3880_);
v_v_3891_ = lean_array_fget(v_b_3881_, v_a_3880_);
v___x_3892_ = lean_box(0);
v_xs_x27_3893_ = lean_array_fset(v_b_3881_, v_a_3880_, v___x_3892_);
v___x_3897_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3898_ = lean_int_dec_eq(v___x_3890_, v___x_3897_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; lean_object* v_lowerBound_3900_; 
lean_inc_ref(v_constraint_3878_);
lean_inc(v___x_3890_);
v___x_3899_ = l_Lean_Omega_Constraint_scale(v___x_3890_, v_constraint_3878_);
v_lowerBound_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_lowerBound_3900_);
if (lean_obj_tag(v_lowerBound_3900_) == 0)
{
lean_object* v___x_3901_; 
lean_inc_ref(v_b_3879_);
v___x_3901_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3899_, v_b_3879_, v___x_3890_, v___x_3898_, v___x_3892_, v_v_3891_);
v___y_3895_ = v___x_3901_;
goto v___jp_3894_;
}
else
{
lean_object* v_var_3902_; lean_object* v_irrelevant_3903_; lean_object* v_lowerBounds_3904_; lean_object* v_upperBounds_3905_; uint8_t v_lowerExact_3906_; uint8_t v_upperExact_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3922_; 
lean_dec_ref_known(v_lowerBound_3900_, 1);
v_var_3902_ = lean_ctor_get(v_v_3891_, 0);
v_irrelevant_3903_ = lean_ctor_get(v_v_3891_, 1);
v_lowerBounds_3904_ = lean_ctor_get(v_v_3891_, 2);
v_upperBounds_3905_ = lean_ctor_get(v_v_3891_, 3);
v_lowerExact_3906_ = lean_ctor_get_uint8(v_v_3891_, sizeof(void*)*4);
v_upperExact_3907_ = lean_ctor_get_uint8(v_v_3891_, sizeof(void*)*4 + 1);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_v_3891_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3909_ = v_v_3891_;
v_isShared_3910_ = v_isSharedCheck_3922_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_upperBounds_3905_);
lean_inc(v_lowerBounds_3904_);
lean_inc(v_irrelevant_3903_);
lean_inc(v_var_3902_);
lean_dec(v_v_3891_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3922_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; uint8_t v___y_3914_; 
lean_inc(v___x_3890_);
lean_inc_ref(v_b_3879_);
v___x_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3911_, 0, v_b_3879_);
lean_ctor_set(v___x_3911_, 1, v___x_3890_);
v___x_3912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
lean_ctor_set(v___x_3912_, 1, v_lowerBounds_3904_);
if (v_lowerExact_3906_ == 0)
{
v___y_3914_ = v___x_3898_;
goto v___jp_3913_;
}
else
{
lean_object* v___x_3919_; lean_object* v___x_3920_; uint8_t v___x_3921_; 
v___x_3919_ = lean_nat_abs(v___x_3890_);
v___x_3920_ = lean_unsigned_to_nat(1u);
v___x_3921_ = lean_nat_dec_eq(v___x_3919_, v___x_3920_);
lean_dec(v___x_3919_);
v___y_3914_ = v___x_3921_;
goto v___jp_3913_;
}
v___jp_3913_:
{
lean_object* v___x_3916_; 
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 2, v___x_3912_);
v___x_3916_ = v___x_3909_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_var_3902_);
lean_ctor_set(v_reuseFailAlloc_3918_, 1, v_irrelevant_3903_);
lean_ctor_set(v_reuseFailAlloc_3918_, 2, v___x_3912_);
lean_ctor_set(v_reuseFailAlloc_3918_, 3, v_upperBounds_3905_);
lean_ctor_set_uint8(v_reuseFailAlloc_3918_, sizeof(void*)*4 + 1, v_upperExact_3907_);
v___x_3916_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3917_; 
lean_ctor_set_uint8(v___x_3916_, sizeof(void*)*4, v___y_3914_);
lean_inc_ref(v_b_3879_);
v___x_3917_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3899_, v_b_3879_, v___x_3890_, v___x_3898_, v___x_3892_, v___x_3916_);
v___y_3895_ = v___x_3917_;
goto v___jp_3894_;
}
}
}
}
}
else
{
lean_object* v_var_3923_; lean_object* v_irrelevant_3924_; lean_object* v_lowerBounds_3925_; lean_object* v_upperBounds_3926_; uint8_t v_lowerExact_3927_; uint8_t v_upperExact_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3936_; 
lean_dec(v___x_3890_);
v_var_3923_ = lean_ctor_get(v_v_3891_, 0);
v_irrelevant_3924_ = lean_ctor_get(v_v_3891_, 1);
v_lowerBounds_3925_ = lean_ctor_get(v_v_3891_, 2);
v_upperBounds_3926_ = lean_ctor_get(v_v_3891_, 3);
v_lowerExact_3927_ = lean_ctor_get_uint8(v_v_3891_, sizeof(void*)*4);
v_upperExact_3928_ = lean_ctor_get_uint8(v_v_3891_, sizeof(void*)*4 + 1);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_v_3891_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3930_ = v_v_3891_;
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_upperBounds_3926_);
lean_inc(v_lowerBounds_3925_);
lean_inc(v_irrelevant_3924_);
lean_inc(v_var_3923_);
lean_dec(v_v_3891_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
lean_inc_ref(v_b_3879_);
v___x_3932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3932_, 0, v_b_3879_);
lean_ctor_set(v___x_3932_, 1, v_irrelevant_3924_);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 1, v___x_3932_);
v___x_3934_ = v___x_3930_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_var_3923_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_3935_, 2, v_lowerBounds_3925_);
lean_ctor_set(v_reuseFailAlloc_3935_, 3, v_upperBounds_3926_);
lean_ctor_set_uint8(v_reuseFailAlloc_3935_, sizeof(void*)*4, v_lowerExact_3927_);
lean_ctor_set_uint8(v_reuseFailAlloc_3935_, sizeof(void*)*4 + 1, v_upperExact_3928_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
v___y_3895_ = v___x_3934_;
goto v___jp_3894_;
}
}
}
v___jp_3894_:
{
lean_object* v___x_3896_; 
v___x_3896_ = lean_array_fset(v_xs_x27_3893_, v_a_3880_, v___y_3895_);
v_a_3883_ = v___x_3896_;
goto v___jp_3882_;
}
}
}
v___jp_3882_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = lean_unsigned_to_nat(1u);
v___x_3885_ = lean_nat_add(v_a_3880_, v___x_3884_);
lean_dec(v_a_3880_);
v_a_3880_ = v___x_3885_;
v_b_3881_ = v_a_3883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___boxed(lean_object* v_upperBound_3937_, lean_object* v_coeffs_3938_, lean_object* v_constraint_3939_, lean_object* v_b_3940_, lean_object* v_a_3941_, lean_object* v_b_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3937_, v_coeffs_3938_, v_constraint_3939_, v_b_3940_, v_a_3941_, v_b_3942_);
lean_dec(v_coeffs_3938_);
lean_dec(v_upperBound_3937_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(lean_object* v_n_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
if (lean_obj_tag(v_a_3945_) == 0)
{
lean_object* v___x_3947_; 
v___x_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3947_, 0, v_a_3946_);
return v___x_3947_;
}
else
{
lean_object* v_value_3948_; lean_object* v_tail_3949_; lean_object* v_coeffs_3950_; lean_object* v_constraint_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v_value_3948_ = lean_ctor_get(v_a_3945_, 1);
lean_inc(v_value_3948_);
v_tail_3949_ = lean_ctor_get(v_a_3945_, 2);
lean_inc(v_tail_3949_);
lean_dec_ref_known(v_a_3945_, 3);
v_coeffs_3950_ = lean_ctor_get(v_value_3948_, 0);
lean_inc(v_coeffs_3950_);
v_constraint_3951_ = lean_ctor_get(v_value_3948_, 1);
lean_inc_ref(v_constraint_3951_);
v___x_3952_ = lean_unsigned_to_nat(0u);
v___x_3953_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_n_3944_, v_coeffs_3950_, v_constraint_3951_, v_value_3948_, v___x_3952_, v_a_3946_);
lean_dec(v_coeffs_3950_);
v_a_3945_ = v_tail_3949_;
v_a_3946_ = v___x_3953_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1___boxed(lean_object* v_n_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3955_, v_a_3956_, v_a_3957_);
lean_dec(v_n_3955_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(lean_object* v_n_3959_, lean_object* v_as_3960_, size_t v_sz_3961_, size_t v_i_3962_, lean_object* v_b_3963_){
_start:
{
uint8_t v___x_3964_; 
v___x_3964_ = lean_usize_dec_lt(v_i_3962_, v_sz_3961_);
if (v___x_3964_ == 0)
{
return v_b_3963_;
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3966_; 
v_a_3965_ = lean_array_uget_borrowed(v_as_3960_, v_i_3962_);
lean_inc(v_a_3965_);
v___x_3966_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3959_, v_a_3965_, v_b_3963_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref_known(v___x_3966_, 1);
return v_a_3967_;
}
else
{
lean_object* v_a_3968_; size_t v___x_3969_; size_t v___x_3970_; 
v_a_3968_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3968_);
lean_dec_ref_known(v___x_3966_, 1);
v___x_3969_ = ((size_t)1ULL);
v___x_3970_ = lean_usize_add(v_i_3962_, v___x_3969_);
v_i_3962_ = v___x_3970_;
v_b_3963_ = v_a_3968_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3___boxed(lean_object* v_n_3972_, lean_object* v_as_3973_, lean_object* v_sz_3974_, lean_object* v_i_3975_, lean_object* v_b_3976_){
_start:
{
size_t v_sz_boxed_3977_; size_t v_i_boxed_3978_; lean_object* v_res_3979_; 
v_sz_boxed_3977_ = lean_unbox_usize(v_sz_3974_);
lean_dec(v_sz_3974_);
v_i_boxed_3978_ = lean_unbox_usize(v_i_3975_);
lean_dec(v_i_3975_);
v_res_3979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_n_3972_, v_as_3973_, v_sz_boxed_3977_, v_i_boxed_3978_, v_b_3976_);
lean_dec_ref(v_as_3973_);
lean_dec(v_n_3972_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(lean_object* v_p_3982_){
_start:
{
lean_object* v_constraints_3983_; lean_object* v_numVars_3984_; lean_object* v_buckets_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v_data_3988_; size_t v_sz_3989_; size_t v___x_3990_; lean_object* v___x_3991_; 
v_constraints_3983_ = lean_ctor_get(v_p_3982_, 2);
lean_inc_ref(v_constraints_3983_);
v_numVars_3984_ = lean_ctor_get(v_p_3982_, 1);
lean_inc_n(v_numVars_3984_, 2);
lean_dec_ref(v_p_3982_);
v_buckets_3985_ = lean_ctor_get(v_constraints_3983_, 1);
lean_inc_ref(v_buckets_3985_);
lean_dec_ref(v_constraints_3983_);
v___x_3986_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_3987_ = l_List_range(v_numVars_3984_);
v_data_3988_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v___x_3986_, v___x_3987_);
lean_dec(v___x_3987_);
v_sz_3989_ = lean_array_size(v_buckets_3985_);
v___x_3990_ = ((size_t)0ULL);
v___x_3991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_numVars_3984_, v_buckets_3985_, v_sz_3989_, v___x_3990_, v_data_3988_);
lean_dec_ref(v_buckets_3985_);
lean_dec(v_numVars_3984_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(lean_object* v_upperBound_3992_, lean_object* v_coeffs_3993_, lean_object* v_constraint_3994_, lean_object* v_b_3995_, lean_object* v_inst_3996_, lean_object* v_R_3997_, lean_object* v_a_3998_, lean_object* v_b_3999_, lean_object* v_c_4000_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3992_, v_coeffs_3993_, v_constraint_3994_, v_b_3995_, v_a_3998_, v_b_3999_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___boxed(lean_object* v_upperBound_4002_, lean_object* v_coeffs_4003_, lean_object* v_constraint_4004_, lean_object* v_b_4005_, lean_object* v_inst_4006_, lean_object* v_R_4007_, lean_object* v_a_4008_, lean_object* v_b_4009_, lean_object* v_c_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(v_upperBound_4002_, v_coeffs_4003_, v_constraint_4004_, v_b_4005_, v_inst_4006_, v_R_4007_, v_a_4008_, v_b_4009_, v_c_4010_);
lean_dec(v_coeffs_4003_);
lean_dec(v_upperBound_4002_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(lean_object* v_cls_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v_toCold_4021_; lean_object* v_options_4022_; uint8_t v_hasTrace_4023_; 
v_toCold_4021_ = lean_ctor_get(v___y_4018_, 0);
v_options_4022_ = lean_ctor_get(v_toCold_4021_, 2);
v_hasTrace_4023_ = lean_ctor_get_uint8(v_options_4022_, sizeof(void*)*1);
if (v_hasTrace_4023_ == 0)
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
lean_dec(v_cls_4015_);
v___x_4024_ = lean_box(v_hasTrace_4023_);
v___x_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
return v___x_4025_;
}
else
{
lean_object* v_inheritedTraceOptions_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v_inheritedTraceOptions_4026_ = lean_ctor_get(v_toCold_4021_, 11);
v___x_4027_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4028_ = l_Lean_Name_append(v___x_4027_, v_cls_4015_);
v___x_4029_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4026_, v_options_4022_, v___x_4028_);
lean_dec(v___x_4028_);
v___x_4030_ = lean_box(v___x_4029_);
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
return v___x_4031_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___boxed(lean_object* v_cls_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(lean_object* v___x_4039_, lean_object* v_fst_4040_, lean_object* v_snd_4041_, lean_object* v_fst_4042_, lean_object* v_____r_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4039_);
v___x_4050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4050_, 0, v_fst_4040_);
lean_ctor_set(v___x_4050_, 1, v_snd_4041_);
v___x_4051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4051_, 0, v_fst_4042_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4049_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
v___x_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
v___x_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0___boxed(lean_object* v___x_4055_, lean_object* v_fst_4056_, lean_object* v_snd_4057_, lean_object* v_fst_4058_, lean_object* v_____r_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4055_, v_fst_4056_, v_snd_4057_, v_fst_4058_, v_____r_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
return v_res_4065_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4066_; double v___x_4067_; 
v___x_4066_ = lean_unsigned_to_nat(0u);
v___x_4067_ = lean_float_of_nat(v___x_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(lean_object* v_cls_4070_, lean_object* v_msg_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v_ref_4077_; lean_object* v___x_4078_; lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4123_; 
v_ref_4077_ = lean_ctor_get(v___y_4074_, 2);
v___x_4078_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4081_ = v___x_4078_;
v_isShared_4082_ = v_isSharedCheck_4123_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4078_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4123_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4083_; lean_object* v_traceState_4084_; lean_object* v_env_4085_; lean_object* v_nextMacroScope_4086_; lean_object* v_ngen_4087_; lean_object* v_auxDeclNGen_4088_; lean_object* v_cache_4089_; lean_object* v_messages_4090_; lean_object* v_infoState_4091_; lean_object* v_snapshotTasks_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4122_; 
v___x_4083_ = lean_st_ref_take(v___y_4075_);
v_traceState_4084_ = lean_ctor_get(v___x_4083_, 4);
v_env_4085_ = lean_ctor_get(v___x_4083_, 0);
v_nextMacroScope_4086_ = lean_ctor_get(v___x_4083_, 1);
v_ngen_4087_ = lean_ctor_get(v___x_4083_, 2);
v_auxDeclNGen_4088_ = lean_ctor_get(v___x_4083_, 3);
v_cache_4089_ = lean_ctor_get(v___x_4083_, 5);
v_messages_4090_ = lean_ctor_get(v___x_4083_, 6);
v_infoState_4091_ = lean_ctor_get(v___x_4083_, 7);
v_snapshotTasks_4092_ = lean_ctor_get(v___x_4083_, 8);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4094_ = v___x_4083_;
v_isShared_4095_ = v_isSharedCheck_4122_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_snapshotTasks_4092_);
lean_inc(v_infoState_4091_);
lean_inc(v_messages_4090_);
lean_inc(v_cache_4089_);
lean_inc(v_traceState_4084_);
lean_inc(v_auxDeclNGen_4088_);
lean_inc(v_ngen_4087_);
lean_inc(v_nextMacroScope_4086_);
lean_inc(v_env_4085_);
lean_dec(v___x_4083_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4122_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
uint64_t v_tid_4096_; lean_object* v_traces_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4121_; 
v_tid_4096_ = lean_ctor_get_uint64(v_traceState_4084_, sizeof(void*)*1);
v_traces_4097_ = lean_ctor_get(v_traceState_4084_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_traceState_4084_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4099_ = v_traceState_4084_;
v_isShared_4100_ = v_isSharedCheck_4121_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_traces_4097_);
lean_dec(v_traceState_4084_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4121_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4101_; double v___x_4102_; uint8_t v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4111_; 
v___x_4101_ = lean_box(0);
v___x_4102_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4103_ = 0;
v___x_4104_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4105_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4105_, 0, v_cls_4070_);
lean_ctor_set(v___x_4105_, 1, v___x_4101_);
lean_ctor_set(v___x_4105_, 2, v___x_4104_);
lean_ctor_set_float(v___x_4105_, sizeof(void*)*3, v___x_4102_);
lean_ctor_set_float(v___x_4105_, sizeof(void*)*3 + 8, v___x_4102_);
lean_ctor_set_uint8(v___x_4105_, sizeof(void*)*3 + 16, v___x_4103_);
v___x_4106_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4107_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4105_);
lean_ctor_set(v___x_4107_, 1, v_a_4079_);
lean_ctor_set(v___x_4107_, 2, v___x_4106_);
lean_inc(v_ref_4077_);
v___x_4108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4108_, 0, v_ref_4077_);
lean_ctor_set(v___x_4108_, 1, v___x_4107_);
v___x_4109_ = l_Lean_PersistentArray_push___redArg(v_traces_4097_, v___x_4108_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 0, v___x_4109_);
v___x_4111_ = v___x_4099_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4109_);
lean_ctor_set_uint64(v_reuseFailAlloc_4120_, sizeof(void*)*1, v_tid_4096_);
v___x_4111_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
lean_object* v___x_4113_; 
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 4, v___x_4111_);
v___x_4113_ = v___x_4094_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_env_4085_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v_nextMacroScope_4086_);
lean_ctor_set(v_reuseFailAlloc_4119_, 2, v_ngen_4087_);
lean_ctor_set(v_reuseFailAlloc_4119_, 3, v_auxDeclNGen_4088_);
lean_ctor_set(v_reuseFailAlloc_4119_, 4, v___x_4111_);
lean_ctor_set(v_reuseFailAlloc_4119_, 5, v_cache_4089_);
lean_ctor_set(v_reuseFailAlloc_4119_, 6, v_messages_4090_);
lean_ctor_set(v_reuseFailAlloc_4119_, 7, v_infoState_4091_);
lean_ctor_set(v_reuseFailAlloc_4119_, 8, v_snapshotTasks_4092_);
v___x_4113_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4117_; 
v___x_4114_ = lean_st_ref_put(v___y_4075_, v___x_4113_);
v___x_4115_ = lean_box(0);
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 0, v___x_4115_);
v___x_4117_ = v___x_4081_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4115_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___boxed(lean_object* v_cls_4124_, lean_object* v_msg_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4124_, v_msg_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
return v_res_4131_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v_cls_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v_cls_4132_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4133_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4134_ = l_Lean_Name_append(v___x_4133_, v_cls_4132_);
return v___x_4134_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4136_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__1));
v___x_4137_ = l_Lean_stringToMessageData(v___x_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(lean_object* v_upperBound_4138_, lean_object* v___y_4139_, lean_object* v_a_4140_, lean_object* v_b_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_a_4148_; lean_object* v___y_4153_; uint8_t v___x_4172_; 
v___x_4172_ = lean_nat_dec_lt(v_a_4140_, v_upperBound_4138_);
if (v___x_4172_ == 0)
{
lean_object* v___x_4173_; 
lean_dec(v_a_4140_);
v___x_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4173_, 0, v_b_4141_);
return v___x_4173_;
}
else
{
lean_object* v_snd_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4245_; 
v_snd_4174_ = lean_ctor_get(v_b_4141_, 1);
v_isSharedCheck_4245_ = !lean_is_exclusive(v_b_4141_);
if (v_isSharedCheck_4245_ == 0)
{
lean_object* v_unused_4246_; 
v_unused_4246_ = lean_ctor_get(v_b_4141_, 0);
lean_dec(v_unused_4246_);
v___x_4176_ = v_b_4141_;
v_isShared_4177_ = v_isSharedCheck_4245_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_snd_4174_);
lean_dec(v_b_4141_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4245_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v_snd_4178_; lean_object* v_fst_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4244_; 
v_snd_4178_ = lean_ctor_get(v_snd_4174_, 1);
v_fst_4179_ = lean_ctor_get(v_snd_4174_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v_snd_4174_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4181_ = v_snd_4174_;
v_isShared_4182_ = v_isSharedCheck_4244_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_snd_4178_);
lean_inc(v_fst_4179_);
lean_dec(v_snd_4174_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4244_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v_fst_4183_; lean_object* v_snd_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4243_; 
v_fst_4183_ = lean_ctor_get(v_snd_4178_, 0);
v_snd_4184_ = lean_ctor_get(v_snd_4178_, 1);
v_isSharedCheck_4243_ = !lean_is_exclusive(v_snd_4178_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4186_ = v_snd_4178_;
v_isShared_4187_ = v_isSharedCheck_4243_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_snd_4184_);
lean_inc(v_fst_4183_);
lean_dec(v_snd_4178_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4243_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4188_; lean_object* v_bestIdx_4199_; lean_object* v_cls_4200_; lean_object* v___x_4201_; uint8_t v___x_4205_; lean_object* v___x_4206_; uint8_t v___x_4207_; 
v___x_4188_ = lean_box(0);
v_bestIdx_4199_ = lean_unsigned_to_nat(0u);
v_cls_4200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4201_ = lean_array_fget_borrowed(v___y_4139_, v_a_4140_);
v___x_4205_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4201_);
v___x_4206_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4201_);
v___x_4207_ = lean_nat_dec_eq(v___x_4206_, v_bestIdx_4199_);
if (v___x_4207_ == 0)
{
uint8_t v___x_4236_; uint8_t v___y_4238_; uint8_t v___x_4242_; 
v___x_4236_ = lean_nat_dec_lt(v___x_4206_, v_fst_4183_);
v___x_4242_ = lean_unbox(v_snd_4184_);
if (v___x_4242_ == 0)
{
if (v___x_4205_ == 0)
{
goto v___jp_4239_;
}
else
{
lean_del_object(v___x_4186_);
lean_del_object(v___x_4181_);
lean_del_object(v___x_4176_);
goto v___jp_4208_;
}
}
else
{
goto v___jp_4239_;
}
v___jp_4237_:
{
if (v___y_4238_ == 0)
{
lean_dec(v___x_4206_);
goto v___jp_4189_;
}
else
{
if (v___x_4236_ == 0)
{
lean_dec(v___x_4206_);
goto v___jp_4189_;
}
else
{
lean_del_object(v___x_4186_);
lean_del_object(v___x_4181_);
lean_del_object(v___x_4176_);
goto v___jp_4208_;
}
}
}
v___jp_4239_:
{
if (v___x_4205_ == 0)
{
uint8_t v___x_4240_; 
v___x_4240_ = lean_unbox(v_snd_4184_);
if (v___x_4240_ == 0)
{
v___y_4238_ = v___x_4172_;
goto v___jp_4237_;
}
else
{
v___y_4238_ = v___x_4205_;
goto v___jp_4237_;
}
}
else
{
uint8_t v___x_4241_; 
v___x_4241_ = lean_unbox(v_snd_4184_);
v___y_4238_ = v___x_4241_;
goto v___jp_4237_;
}
}
}
else
{
lean_del_object(v___x_4186_);
lean_del_object(v___x_4181_);
lean_del_object(v___x_4176_);
goto v___jp_4208_;
}
v___jp_4189_:
{
lean_object* v___x_4191_; 
if (v_isShared_4187_ == 0)
{
v___x_4191_ = v___x_4186_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_fst_4183_);
lean_ctor_set(v_reuseFailAlloc_4198_, 1, v_snd_4184_);
v___x_4191_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4193_; 
if (v_isShared_4182_ == 0)
{
lean_ctor_set(v___x_4181_, 1, v___x_4191_);
v___x_4193_ = v___x_4181_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_fst_4179_);
lean_ctor_set(v_reuseFailAlloc_4197_, 1, v___x_4191_);
v___x_4193_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
lean_object* v___x_4195_; 
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 1, v___x_4193_);
lean_ctor_set(v___x_4176_, 0, v___x_4188_);
v___x_4195_ = v___x_4176_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4196_, 1, v___x_4193_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
v_a_4148_ = v___x_4195_;
goto v___jp_4147_;
}
}
}
}
v___jp_4202_:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4203_ = lean_box(0);
lean_inc(v___x_4201_);
v___x_4204_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4201_, v_fst_4183_, v_snd_4184_, v_fst_4179_, v___x_4203_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
v___y_4153_ = v___x_4204_;
goto v___jp_4152_;
}
v___jp_4208_:
{
if (v___x_4207_ == 0)
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
lean_dec(v_snd_4184_);
lean_dec(v_fst_4183_);
lean_dec(v_fst_4179_);
v___x_4209_ = lean_box(v___x_4205_);
v___x_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4206_);
lean_ctor_set(v___x_4210_, 1, v___x_4209_);
lean_inc(v_a_4140_);
v___x_4211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4211_, 0, v_a_4140_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
v___x_4212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4188_);
lean_ctor_set(v___x_4212_, 1, v___x_4211_);
v_a_4148_ = v___x_4212_;
goto v___jp_4147_;
}
else
{
lean_object* v_toCold_4213_; lean_object* v_options_4214_; uint8_t v_hasTrace_4215_; 
lean_dec(v___x_4206_);
v_toCold_4213_ = lean_ctor_get(v___y_4144_, 0);
v_options_4214_ = lean_ctor_get(v_toCold_4213_, 2);
v_hasTrace_4215_ = lean_ctor_get_uint8(v_options_4214_, sizeof(void*)*1);
if (v_hasTrace_4215_ == 0)
{
goto v___jp_4202_;
}
else
{
lean_object* v_inheritedTraceOptions_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; 
v_inheritedTraceOptions_4216_ = lean_ctor_get(v_toCold_4213_, 11);
v___x_4217_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_4218_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4216_, v_options_4214_, v___x_4217_);
if (v___x_4218_ == 0)
{
goto v___jp_4202_;
}
else
{
lean_object* v_var_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v_var_4219_ = lean_ctor_get(v___x_4201_, 0);
v___x_4220_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4219_);
v___x_4221_ = l_Nat_reprFast(v_var_4219_);
v___x_4222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4221_);
v___x_4223_ = l_Lean_MessageData_ofFormat(v___x_4222_);
v___x_4224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4220_);
lean_ctor_set(v___x_4224_, 1, v___x_4223_);
v___x_4225_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4200_, v___x_4224_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4227_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
lean_inc(v___x_4201_);
v___x_4227_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4201_, v_fst_4183_, v_snd_4184_, v_fst_4179_, v_a_4226_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
v___y_4153_ = v___x_4227_;
goto v___jp_4152_;
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
lean_dec(v_snd_4184_);
lean_dec(v_fst_4183_);
lean_dec(v_fst_4179_);
lean_dec(v_a_4140_);
v_a_4228_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4225_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4225_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
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
v___jp_4147_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = lean_unsigned_to_nat(1u);
v___x_4150_ = lean_nat_add(v_a_4140_, v___x_4149_);
lean_dec(v_a_4140_);
v_a_4140_ = v___x_4150_;
v_b_4141_ = v_a_4148_;
goto _start;
}
v___jp_4152_:
{
if (lean_obj_tag(v___y_4153_) == 0)
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4163_; 
v_a_4154_ = lean_ctor_get(v___y_4153_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___y_4153_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4156_ = v___y_4153_;
v_isShared_4157_ = v_isSharedCheck_4163_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___y_4153_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4163_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
if (lean_obj_tag(v_a_4154_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4160_; 
lean_dec(v_a_4140_);
v_a_4158_ = lean_ctor_get(v_a_4154_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v_a_4154_, 1);
if (v_isShared_4157_ == 0)
{
lean_ctor_set(v___x_4156_, 0, v_a_4158_);
v___x_4160_ = v___x_4156_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4158_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
else
{
lean_object* v_a_4162_; 
lean_del_object(v___x_4156_);
v_a_4162_ = lean_ctor_get(v_a_4154_, 0);
lean_inc(v_a_4162_);
lean_dec_ref_known(v_a_4154_, 1);
v_a_4148_ = v_a_4162_;
goto v___jp_4147_;
}
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec(v_a_4140_);
v_a_4164_ = lean_ctor_get(v___y_4153_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___y_4153_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___y_4153_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___y_4153_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___boxed(lean_object* v_upperBound_4247_, lean_object* v___y_4248_, lean_object* v_a_4249_, lean_object* v_b_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4247_, v___y_4248_, v_a_4249_, v_b_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec_ref(v___y_4248_);
lean_dec(v_upperBound_4247_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(lean_object* v_as_4257_, size_t v_i_4258_, size_t v_stop_4259_, lean_object* v_b_4260_){
_start:
{
lean_object* v___y_4262_; uint8_t v___x_4266_; 
v___x_4266_ = lean_usize_dec_eq(v_i_4258_, v_stop_4259_);
if (v___x_4266_ == 0)
{
lean_object* v___x_4267_; uint8_t v___x_4270_; 
v___x_4267_ = lean_array_uget_borrowed(v_as_4257_, v_i_4258_);
v___x_4270_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v___x_4267_);
if (v___x_4270_ == 0)
{
goto v___jp_4268_;
}
else
{
if (v___x_4266_ == 0)
{
v___y_4262_ = v_b_4260_;
goto v___jp_4261_;
}
else
{
goto v___jp_4268_;
}
}
v___jp_4268_:
{
lean_object* v___x_4269_; 
lean_inc(v___x_4267_);
v___x_4269_ = lean_array_push(v_b_4260_, v___x_4267_);
v___y_4262_ = v___x_4269_;
goto v___jp_4261_;
}
}
else
{
return v_b_4260_;
}
v___jp_4261_:
{
size_t v___x_4263_; size_t v___x_4264_; 
v___x_4263_ = ((size_t)1ULL);
v___x_4264_ = lean_usize_add(v_i_4258_, v___x_4263_);
v_i_4258_ = v___x_4264_;
v_b_4260_ = v___y_4262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___boxed(lean_object* v_as_4271_, lean_object* v_i_4272_, lean_object* v_stop_4273_, lean_object* v_b_4274_){
_start:
{
size_t v_i_boxed_4275_; size_t v_stop_boxed_4276_; lean_object* v_res_4277_; 
v_i_boxed_4275_ = lean_unbox_usize(v_i_4272_);
lean_dec(v_i_4272_);
v_stop_boxed_4276_ = lean_unbox_usize(v_stop_4273_);
lean_dec(v_stop_4273_);
v_res_4277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_as_4271_, v_i_boxed_4275_, v_stop_boxed_4276_, v_b_4274_);
lean_dec_ref(v_as_4271_);
return v_res_4277_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2(void){
_start:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__1));
v___x_4282_ = l_Lean_MessageData_ofFormat(v___x_4281_);
return v___x_4282_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4283_ = lean_box(1);
v___x_4284_ = l_Lean_MessageData_ofFormat(v___x_4283_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(lean_object* v_a_4286_, lean_object* v_a_4287_){
_start:
{
if (lean_obj_tag(v_a_4286_) == 0)
{
lean_object* v___x_4288_; 
v___x_4288_ = l_List_reverse___redArg(v_a_4287_);
return v___x_4288_;
}
else
{
lean_object* v_head_4289_; lean_object* v_snd_4290_; lean_object* v_tail_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4338_; 
v_head_4289_ = lean_ctor_get(v_a_4286_, 0);
lean_inc(v_head_4289_);
v_snd_4290_ = lean_ctor_get(v_head_4289_, 1);
lean_inc(v_snd_4290_);
v_tail_4291_ = lean_ctor_get(v_a_4286_, 1);
v_isSharedCheck_4338_ = !lean_is_exclusive(v_a_4286_);
if (v_isSharedCheck_4338_ == 0)
{
lean_object* v_unused_4339_; 
v_unused_4339_ = lean_ctor_get(v_a_4286_, 0);
lean_dec(v_unused_4339_);
v___x_4293_ = v_a_4286_;
v_isShared_4294_ = v_isSharedCheck_4338_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_tail_4291_);
lean_dec(v_a_4286_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4338_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v_fst_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4336_; 
v_fst_4295_ = lean_ctor_get(v_head_4289_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v_head_4289_);
if (v_isSharedCheck_4336_ == 0)
{
lean_object* v_unused_4337_; 
v_unused_4337_ = lean_ctor_get(v_head_4289_, 1);
lean_dec(v_unused_4337_);
v___x_4297_ = v_head_4289_;
v_isShared_4298_ = v_isSharedCheck_4336_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_fst_4295_);
lean_dec(v_head_4289_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4336_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v_fst_4299_; lean_object* v_snd_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4335_; 
v_fst_4299_ = lean_ctor_get(v_snd_4290_, 0);
v_snd_4300_ = lean_ctor_get(v_snd_4290_, 1);
v_isSharedCheck_4335_ = !lean_is_exclusive(v_snd_4290_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4302_ = v_snd_4290_;
v_isShared_4303_ = v_isSharedCheck_4335_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_snd_4300_);
lean_inc(v_fst_4299_);
lean_dec(v_snd_4290_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4335_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4309_; 
v___x_4304_ = l_Nat_reprFast(v_fst_4295_);
v___x_4305_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4304_);
v___x_4306_ = l_Lean_MessageData_ofFormat(v___x_4305_);
v___x_4307_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2);
if (v_isShared_4303_ == 0)
{
lean_ctor_set_tag(v___x_4302_, 7);
lean_ctor_set(v___x_4302_, 1, v___x_4307_);
lean_ctor_set(v___x_4302_, 0, v___x_4306_);
v___x_4309_ = v___x_4302_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4306_);
lean_ctor_set(v_reuseFailAlloc_4334_, 1, v___x_4307_);
v___x_4309_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
lean_object* v___x_4310_; lean_object* v___x_4312_; 
v___x_4310_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3);
if (v_isShared_4298_ == 0)
{
lean_ctor_set_tag(v___x_4297_, 7);
lean_ctor_set(v___x_4297_, 1, v___x_4310_);
lean_ctor_set(v___x_4297_, 0, v___x_4309_);
v___x_4312_ = v___x_4297_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4309_);
lean_ctor_set(v_reuseFailAlloc_4333_, 1, v___x_4310_);
v___x_4312_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___y_4319_; uint8_t v___x_4330_; 
v___x_4313_ = l_Nat_reprFast(v_fst_4299_);
v___x_4314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4313_);
v___x_4315_ = l_Lean_MessageData_ofFormat(v___x_4314_);
v___x_4316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4315_);
lean_ctor_set(v___x_4316_, 1, v___x_4307_);
v___x_4317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4316_);
lean_ctor_set(v___x_4317_, 1, v___x_4310_);
v___x_4330_ = lean_unbox(v_snd_4300_);
lean_dec(v_snd_4300_);
if (v___x_4330_ == 0)
{
lean_object* v___x_4331_; 
v___x_4331_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__4));
v___y_4319_ = v___x_4331_;
goto v___jp_4318_;
}
else
{
lean_object* v___x_4332_; 
v___x_4332_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4));
v___y_4319_ = v___x_4332_;
goto v___jp_4318_;
}
v___jp_4318_:
{
lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4327_; 
lean_inc_ref(v___y_4319_);
v___x_4320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4320_, 0, v___y_4319_);
v___x_4321_ = l_Lean_MessageData_ofFormat(v___x_4320_);
v___x_4322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4317_);
lean_ctor_set(v___x_4322_, 1, v___x_4321_);
v___x_4323_ = l_Lean_MessageData_paren(v___x_4322_);
v___x_4324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4312_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
v___x_4325_ = l_Lean_MessageData_paren(v___x_4324_);
if (v_isShared_4294_ == 0)
{
lean_ctor_set(v___x_4293_, 1, v_a_4287_);
lean_ctor_set(v___x_4293_, 0, v___x_4325_);
v___x_4327_ = v___x_4293_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v___x_4325_);
lean_ctor_set(v_reuseFailAlloc_4329_, 1, v_a_4287_);
v___x_4327_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
v_a_4286_ = v_tail_4291_;
v_a_4287_ = v___x_4327_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(size_t v_sz_4340_, size_t v_i_4341_, lean_object* v_bs_4342_){
_start:
{
uint8_t v___x_4343_; 
v___x_4343_ = lean_usize_dec_lt(v_i_4341_, v_sz_4340_);
if (v___x_4343_ == 0)
{
return v_bs_4342_;
}
else
{
lean_object* v_v_4344_; lean_object* v_var_4345_; lean_object* v___x_4346_; lean_object* v_bs_x27_4347_; lean_object* v___x_4348_; uint8_t v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; size_t v___x_4353_; size_t v___x_4354_; lean_object* v___x_4355_; 
v_v_4344_ = lean_array_uget(v_bs_4342_, v_i_4341_);
v_var_4345_ = lean_ctor_get(v_v_4344_, 0);
lean_inc(v_var_4345_);
v___x_4346_ = lean_unsigned_to_nat(0u);
v_bs_x27_4347_ = lean_array_uset(v_bs_4342_, v_i_4341_, v___x_4346_);
v___x_4348_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_v_4344_);
v___x_4349_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_v_4344_);
lean_dec(v_v_4344_);
v___x_4350_ = lean_box(v___x_4349_);
v___x_4351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4348_);
lean_ctor_set(v___x_4351_, 1, v___x_4350_);
v___x_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4352_, 0, v_var_4345_);
lean_ctor_set(v___x_4352_, 1, v___x_4351_);
v___x_4353_ = ((size_t)1ULL);
v___x_4354_ = lean_usize_add(v_i_4341_, v___x_4353_);
v___x_4355_ = lean_array_uset(v_bs_x27_4347_, v_i_4341_, v___x_4352_);
v_i_4341_ = v___x_4354_;
v_bs_4342_ = v___x_4355_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___boxed(lean_object* v_sz_4357_, lean_object* v_i_4358_, lean_object* v_bs_4359_){
_start:
{
size_t v_sz_boxed_4360_; size_t v_i_boxed_4361_; lean_object* v_res_4362_; 
v_sz_boxed_4360_ = lean_unbox_usize(v_sz_4357_);
lean_dec(v_sz_4357_);
v_i_boxed_4361_ = lean_unbox_usize(v_i_4358_);
lean_dec(v_i_4358_);
v_res_4362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_boxed_4360_, v_i_boxed_4361_, v_bs_4359_);
return v_res_4362_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1(void){
_start:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4364_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0));
v___x_4365_ = l_Lean_stringToMessageData(v___x_4364_);
return v___x_4365_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4369_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3));
v___x_4370_ = l_Lean_stringToMessageData(v___x_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(lean_object* v_data_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_){
_start:
{
lean_object* v___x_4377_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v_bestIdx_4383_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4512_; lean_object* v___x_4536_; lean_object* v___x_4537_; uint8_t v___x_4538_; 
v___x_4377_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default));
v_bestIdx_4383_ = lean_unsigned_to_nat(0u);
v___x_4536_ = lean_array_get_size(v_data_4371_);
v___x_4537_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_4538_ = lean_nat_dec_lt(v_bestIdx_4383_, v___x_4536_);
if (v___x_4538_ == 0)
{
v___y_4512_ = v___x_4537_;
goto v___jp_4511_;
}
else
{
uint8_t v___x_4539_; 
v___x_4539_ = lean_nat_dec_le(v___x_4536_, v___x_4536_);
if (v___x_4539_ == 0)
{
if (v___x_4538_ == 0)
{
v___y_4512_ = v___x_4537_;
goto v___jp_4511_;
}
else
{
size_t v___x_4540_; size_t v___x_4541_; lean_object* v___x_4542_; 
v___x_4540_ = ((size_t)0ULL);
v___x_4541_ = lean_usize_of_nat(v___x_4536_);
v___x_4542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4371_, v___x_4540_, v___x_4541_, v___x_4537_);
v___y_4512_ = v___x_4542_;
goto v___jp_4511_;
}
}
else
{
size_t v___x_4543_; size_t v___x_4544_; lean_object* v___x_4545_; 
v___x_4543_ = ((size_t)0ULL);
v___x_4544_ = lean_usize_of_nat(v___x_4536_);
v___x_4545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4371_, v___x_4543_, v___x_4544_, v___x_4537_);
v___y_4512_ = v___x_4545_;
goto v___jp_4511_;
}
}
v___jp_4378_:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4381_ = lean_array_get(v___x_4377_, v___y_4379_, v___y_4380_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
v___x_4382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4381_);
return v___x_4382_;
}
v___jp_4384_:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; uint8_t v___x_4394_; 
v___x_4392_ = lean_array_get_borrowed(v___x_4377_, v___y_4385_, v_bestIdx_4383_);
v___x_4393_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4392_);
v___x_4394_ = lean_nat_dec_eq(v___x_4393_, v_bestIdx_4383_);
if (v___x_4394_ == 0)
{
lean_object* v___x_4395_; lean_object* v___x_4396_; uint8_t v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4395_ = lean_unsigned_to_nat(1u);
v___x_4396_ = lean_array_get_size(v___y_4385_);
v___x_4397_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4392_);
v___x_4398_ = lean_box(0);
v___x_4399_ = lean_box(v___x_4397_);
v___x_4400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4393_);
lean_ctor_set(v___x_4400_, 1, v___x_4399_);
v___x_4401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4401_, 0, v_bestIdx_4383_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
v___x_4402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4398_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
v___x_4403_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v___x_4396_, v___y_4385_, v___x_4395_, v___x_4402_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4459_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4406_ = v___x_4403_;
v_isShared_4407_ = v_isSharedCheck_4459_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4403_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4459_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v_fst_4408_; 
v_fst_4408_ = lean_ctor_get(v_a_4404_, 0);
if (lean_obj_tag(v_fst_4408_) == 0)
{
lean_object* v_snd_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4453_; 
lean_del_object(v___x_4406_);
v_snd_4409_ = lean_ctor_get(v_a_4404_, 1);
v_isSharedCheck_4453_ = !lean_is_exclusive(v_a_4404_);
if (v_isSharedCheck_4453_ == 0)
{
lean_object* v_unused_4454_; 
v_unused_4454_ = lean_ctor_get(v_a_4404_, 0);
lean_dec(v_unused_4454_);
v___x_4411_ = v_a_4404_;
v_isShared_4412_ = v_isSharedCheck_4453_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_snd_4409_);
lean_dec(v_a_4404_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4453_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4413_; 
lean_inc_ref(v___y_4386_);
lean_inc(v___y_4391_);
lean_inc_ref(v___y_4390_);
lean_inc(v___y_4389_);
lean_inc_ref(v___y_4388_);
v___x_4413_ = lean_apply_5(v___y_4386_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, lean_box(0));
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; uint8_t v___x_4415_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4414_);
lean_dec_ref_known(v___x_4413_, 1);
v___x_4415_ = lean_unbox(v_a_4414_);
lean_dec(v_a_4414_);
if (v___x_4415_ == 0)
{
lean_object* v_fst_4416_; 
lean_del_object(v___x_4411_);
lean_dec(v___y_4387_);
v_fst_4416_ = lean_ctor_get(v_snd_4409_, 0);
lean_inc(v_fst_4416_);
lean_dec(v_snd_4409_);
v___y_4379_ = v___y_4385_;
v___y_4380_ = v_fst_4416_;
goto v___jp_4378_;
}
else
{
lean_object* v_fst_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4443_; 
v_fst_4417_ = lean_ctor_get(v_snd_4409_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v_snd_4409_);
if (v_isSharedCheck_4443_ == 0)
{
lean_object* v_unused_4444_; 
v_unused_4444_ = lean_ctor_get(v_snd_4409_, 1);
lean_dec(v_unused_4444_);
v___x_4419_ = v_snd_4409_;
v_isShared_4420_ = v_isSharedCheck_4443_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_fst_4417_);
lean_dec(v_snd_4409_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4443_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4421_; lean_object* v_var_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4428_; 
v___x_4421_ = lean_array_get_borrowed(v___x_4377_, v___y_4385_, v_fst_4417_);
v_var_4422_ = lean_ctor_get(v___x_4421_, 0);
v___x_4423_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4422_);
v___x_4424_ = l_Nat_reprFast(v_var_4422_);
v___x_4425_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
v___x_4426_ = l_Lean_MessageData_ofFormat(v___x_4425_);
if (v_isShared_4420_ == 0)
{
lean_ctor_set_tag(v___x_4419_, 7);
lean_ctor_set(v___x_4419_, 1, v___x_4426_);
lean_ctor_set(v___x_4419_, 0, v___x_4423_);
v___x_4428_ = v___x_4419_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4423_);
lean_ctor_set(v_reuseFailAlloc_4442_, 1, v___x_4426_);
v___x_4428_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
lean_object* v___x_4429_; lean_object* v___x_4431_; 
v___x_4429_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
if (v_isShared_4412_ == 0)
{
lean_ctor_set_tag(v___x_4411_, 7);
lean_ctor_set(v___x_4411_, 1, v___x_4429_);
lean_ctor_set(v___x_4411_, 0, v___x_4428_);
v___x_4431_ = v___x_4411_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4428_);
lean_ctor_set(v_reuseFailAlloc_4441_, 1, v___x_4429_);
v___x_4431_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
lean_object* v___x_4432_; 
v___x_4432_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4387_, v___x_4431_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_dec_ref_known(v___x_4432_, 1);
v___y_4379_ = v___y_4385_;
v___y_4380_ = v_fst_4417_;
goto v___jp_4378_;
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec(v_fst_4417_);
lean_dec_ref(v___y_4385_);
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4432_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4432_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
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
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_del_object(v___x_4411_);
lean_dec(v_snd_4409_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4385_);
v_a_4445_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4413_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4413_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
}
else
{
lean_object* v_val_4455_; lean_object* v___x_4457_; 
lean_inc_ref(v_fst_4408_);
lean_dec(v_a_4404_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4385_);
v_val_4455_ = lean_ctor_get(v_fst_4408_, 0);
lean_inc(v_val_4455_);
lean_dec_ref_known(v_fst_4408_, 1);
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 0, v_val_4455_);
v___x_4457_ = v___x_4406_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_val_4455_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
else
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4385_);
v_a_4460_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4403_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4403_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
else
{
lean_object* v___x_4468_; 
lean_inc(v___x_4392_);
lean_dec(v___x_4393_);
lean_dec_ref(v___y_4385_);
lean_inc_ref(v___y_4386_);
lean_inc(v___y_4391_);
lean_inc_ref(v___y_4390_);
lean_inc(v___y_4389_);
lean_inc_ref(v___y_4388_);
v___x_4468_ = lean_apply_5(v___y_4386_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, lean_box(0));
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4502_; 
v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4471_ = v___x_4468_;
v_isShared_4472_ = v_isSharedCheck_4502_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4468_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4502_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
uint8_t v___x_4473_; 
v___x_4473_ = lean_unbox(v_a_4469_);
lean_dec(v_a_4469_);
if (v___x_4473_ == 0)
{
lean_object* v___x_4475_; 
lean_dec(v___y_4387_);
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 0, v___x_4392_);
v___x_4475_ = v___x_4471_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4392_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
else
{
lean_object* v_var_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
lean_del_object(v___x_4471_);
v_var_4477_ = lean_ctor_get(v___x_4392_, 0);
v___x_4478_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4477_);
v___x_4479_ = l_Nat_reprFast(v_var_4477_);
v___x_4480_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
v___x_4481_ = l_Lean_MessageData_ofFormat(v___x_4480_);
v___x_4482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4478_);
lean_ctor_set(v___x_4482_, 1, v___x_4481_);
v___x_4483_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
v___x_4484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4482_);
lean_ctor_set(v___x_4484_, 1, v___x_4483_);
v___x_4485_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4387_, v___x_4484_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4492_ == 0)
{
lean_object* v_unused_4493_; 
v_unused_4493_ = lean_ctor_get(v___x_4485_, 0);
lean_dec(v_unused_4493_);
v___x_4487_ = v___x_4485_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_dec(v___x_4485_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 0, v___x_4392_);
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4392_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v___x_4392_);
v_a_4494_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4485_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4485_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
}
}
else
{
lean_object* v_a_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4510_; 
lean_dec(v___x_4392_);
lean_dec(v___y_4387_);
v_a_4503_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4505_ = v___x_4468_;
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_a_4503_);
lean_dec(v___x_4468_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4508_; 
if (v_isShared_4506_ == 0)
{
v___x_4508_ = v___x_4505_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4503_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
}
}
}
}
}
v___jp_4511_:
{
lean_object* v_cls_4513_; lean_object* v___f_4514_; lean_object* v___x_4515_; lean_object* v_a_4516_; uint8_t v___x_4517_; 
v_cls_4513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___f_4514_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2));
v___x_4515_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4513_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_);
v_a_4516_ = lean_ctor_get(v___x_4515_, 0);
lean_inc(v_a_4516_);
lean_dec_ref(v___x_4515_);
v___x_4517_ = lean_unbox(v_a_4516_);
lean_dec(v_a_4516_);
if (v___x_4517_ == 0)
{
v___y_4385_ = v___y_4512_;
v___y_4386_ = v___f_4514_;
v___y_4387_ = v_cls_4513_;
v___y_4388_ = v_a_4372_;
v___y_4389_ = v_a_4373_;
v___y_4390_ = v_a_4374_;
v___y_4391_ = v_a_4375_;
goto v___jp_4384_;
}
else
{
lean_object* v___x_4518_; size_t v_sz_4519_; size_t v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4518_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4);
v_sz_4519_ = lean_array_size(v___y_4512_);
v___x_4520_ = ((size_t)0ULL);
lean_inc_ref(v___y_4512_);
v___x_4521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_4519_, v___x_4520_, v___y_4512_);
v___x_4522_ = lean_array_to_list(v___x_4521_);
v___x_4523_ = lean_box(0);
v___x_4524_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v___x_4522_, v___x_4523_);
v___x_4525_ = l_Lean_MessageData_ofList(v___x_4524_);
v___x_4526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4518_);
lean_ctor_set(v___x_4526_, 1, v___x_4525_);
v___x_4527_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4513_, v___x_4526_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_dec_ref_known(v___x_4527_, 1);
v___y_4385_ = v___y_4512_;
v___y_4386_ = v___f_4514_;
v___y_4387_ = v_cls_4513_;
v___y_4388_ = v_a_4372_;
v___y_4389_ = v_a_4373_;
v___y_4390_ = v_a_4374_;
v___y_4391_ = v_a_4375_;
goto v___jp_4384_;
}
else
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4535_; 
lean_dec_ref(v___y_4512_);
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4530_ = v___x_4527_;
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4527_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4533_; 
if (v_isShared_4531_ == 0)
{
v___x_4533_ = v___x_4530_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_a_4528_);
v___x_4533_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
return v___x_4533_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object* v_data_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_);
lean_dec(v_a_4550_);
lean_dec_ref(v_a_4549_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec_ref(v_data_4546_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object* v_upperBound_4553_, lean_object* v___y_4554_, lean_object* v_inst_4555_, lean_object* v_R_4556_, lean_object* v_a_4557_, lean_object* v_b_4558_, lean_object* v_c_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v___x_4565_; 
v___x_4565_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4553_, v___y_4554_, v_a_4557_, v_b_4558_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object* v_upperBound_4566_, lean_object* v___y_4567_, lean_object* v_inst_4568_, lean_object* v_R_4569_, lean_object* v_a_4570_, lean_object* v_b_4571_, lean_object* v_c_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_upperBound_4566_, v___y_4567_, v_inst_4568_, v_R_4569_, v_a_4570_, v_b_4571_, v_c_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
lean_dec_ref(v___y_4567_);
lean_dec(v_upperBound_4566_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(lean_object* v_snd_4579_, lean_object* v_fst_4580_, lean_object* v_as_x27_4581_, lean_object* v_b_4582_){
_start:
{
if (lean_obj_tag(v_as_x27_4581_) == 0)
{
lean_object* v___x_4584_; 
lean_dec_ref(v_fst_4580_);
v___x_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4584_, 0, v_b_4582_);
return v___x_4584_;
}
else
{
lean_object* v_head_4585_; lean_object* v_tail_4586_; lean_object* v_fst_4587_; lean_object* v_snd_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v_head_4585_ = lean_ctor_get(v_as_x27_4581_, 0);
v_tail_4586_ = lean_ctor_get(v_as_x27_4581_, 1);
v_fst_4587_ = lean_ctor_get(v_head_4585_, 0);
v_snd_4588_ = lean_ctor_get(v_head_4585_, 1);
v___x_4589_ = lean_int_neg(v_snd_4579_);
lean_inc(v_fst_4587_);
lean_inc_ref(v_fst_4580_);
lean_inc(v_snd_4588_);
v___x_4590_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_snd_4588_, v_fst_4580_, v___x_4589_, v_fst_4587_);
v___x_4591_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_4590_);
v___x_4592_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_b_4582_, v___x_4591_);
v_as_x27_4581_ = v_tail_4586_;
v_b_4582_ = v___x_4592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg___boxed(lean_object* v_snd_4594_, lean_object* v_fst_4595_, lean_object* v_as_x27_4596_, lean_object* v_b_4597_, lean_object* v___y_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4594_, v_fst_4595_, v_as_x27_4596_, v_b_4597_);
lean_dec(v_as_x27_4596_);
lean_dec(v_snd_4594_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(lean_object* v_upperBounds_4600_, lean_object* v_as_x27_4601_, lean_object* v_b_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
if (lean_obj_tag(v_as_x27_4601_) == 0)
{
lean_object* v___x_4608_; 
v___x_4608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4608_, 0, v_b_4602_);
return v___x_4608_;
}
else
{
lean_object* v_head_4609_; lean_object* v_tail_4610_; lean_object* v_fst_4611_; lean_object* v_snd_4612_; lean_object* v___x_4613_; lean_object* v_a_4614_; 
v_head_4609_ = lean_ctor_get(v_as_x27_4601_, 0);
v_tail_4610_ = lean_ctor_get(v_as_x27_4601_, 1);
v_fst_4611_ = lean_ctor_get(v_head_4609_, 0);
v_snd_4612_ = lean_ctor_get(v_head_4609_, 1);
lean_inc(v_fst_4611_);
v___x_4613_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4612_, v_fst_4611_, v_upperBounds_4600_, v_b_4602_);
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
lean_inc(v_a_4614_);
lean_dec_ref(v___x_4613_);
v_as_x27_4601_ = v_tail_4610_;
v_b_4602_ = v_a_4614_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg___boxed(lean_object* v_upperBounds_4616_, lean_object* v_as_x27_4617_, lean_object* v_b_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
lean_object* v_res_4624_; 
v_res_4624_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4616_, v_as_x27_4617_, v_b_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec(v_as_x27_4617_);
lean_dec(v_upperBounds_4616_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(lean_object* v_as_x27_4625_, lean_object* v_b_4626_){
_start:
{
if (lean_obj_tag(v_as_x27_4625_) == 0)
{
lean_object* v___x_4628_; 
v___x_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4628_, 0, v_b_4626_);
return v___x_4628_;
}
else
{
lean_object* v_head_4629_; lean_object* v_tail_4630_; lean_object* v___x_4631_; 
v_head_4629_ = lean_ctor_get(v_as_x27_4625_, 0);
v_tail_4630_ = lean_ctor_get(v_as_x27_4625_, 1);
lean_inc(v_head_4629_);
v___x_4631_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_b_4626_, v_head_4629_);
v_as_x27_4625_ = v_tail_4630_;
v_b_4626_ = v___x_4631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg___boxed(lean_object* v_as_x27_4633_, lean_object* v_b_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4633_, v_b_4634_);
lean_dec(v_as_x27_4633_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(lean_object* v_p_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_){
_start:
{
lean_object* v_data_4643_; lean_object* v___x_4644_; 
lean_inc_ref(v_p_4637_);
v_data_4643_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(v_p_4637_);
v___x_4644_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4643_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_);
lean_dec_ref(v_data_4643_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v_irrelevant_4646_; lean_object* v_lowerBounds_4647_; lean_object* v_upperBounds_4648_; lean_object* v_assumptions_4649_; lean_object* v_eliminations_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4665_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
lean_dec_ref_known(v___x_4644_, 1);
v_irrelevant_4646_ = lean_ctor_get(v_a_4645_, 1);
lean_inc(v_irrelevant_4646_);
v_lowerBounds_4647_ = lean_ctor_get(v_a_4645_, 2);
lean_inc(v_lowerBounds_4647_);
v_upperBounds_4648_ = lean_ctor_get(v_a_4645_, 3);
lean_inc(v_upperBounds_4648_);
lean_dec(v_a_4645_);
v_assumptions_4649_ = lean_ctor_get(v_p_4637_, 0);
v_eliminations_4650_ = lean_ctor_get(v_p_4637_, 4);
v_isSharedCheck_4665_ = !lean_is_exclusive(v_p_4637_);
if (v_isSharedCheck_4665_ == 0)
{
lean_object* v_unused_4666_; lean_object* v_unused_4667_; lean_object* v_unused_4668_; lean_object* v_unused_4669_; lean_object* v_unused_4670_; 
v_unused_4666_ = lean_ctor_get(v_p_4637_, 6);
lean_dec(v_unused_4666_);
v_unused_4667_ = lean_ctor_get(v_p_4637_, 5);
lean_dec(v_unused_4667_);
v_unused_4668_ = lean_ctor_get(v_p_4637_, 3);
lean_dec(v_unused_4668_);
v_unused_4669_ = lean_ctor_get(v_p_4637_, 2);
lean_dec(v_unused_4669_);
v_unused_4670_ = lean_ctor_get(v_p_4637_, 1);
lean_dec(v_unused_4670_);
v___x_4652_ = v_p_4637_;
v_isShared_4653_ = v_isSharedCheck_4665_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_eliminations_4650_);
lean_inc(v_assumptions_4649_);
lean_dec(v_p_4637_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4665_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; uint8_t v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4660_; 
v___x_4654_ = lean_unsigned_to_nat(0u);
v___x_4655_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v___x_4656_ = 1;
v___x_4657_ = lean_box(0);
v___x_4658_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 6, v___x_4658_);
lean_ctor_set(v___x_4652_, 5, v___x_4657_);
lean_ctor_set(v___x_4652_, 3, v___x_4655_);
lean_ctor_set(v___x_4652_, 2, v___x_4655_);
lean_ctor_set(v___x_4652_, 1, v___x_4654_);
v___x_4660_ = v___x_4652_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_assumptions_4649_);
lean_ctor_set(v_reuseFailAlloc_4664_, 1, v___x_4654_);
lean_ctor_set(v_reuseFailAlloc_4664_, 2, v___x_4655_);
lean_ctor_set(v_reuseFailAlloc_4664_, 3, v___x_4655_);
lean_ctor_set(v_reuseFailAlloc_4664_, 4, v_eliminations_4650_);
lean_ctor_set(v_reuseFailAlloc_4664_, 5, v___x_4657_);
lean_ctor_set(v_reuseFailAlloc_4664_, 6, v___x_4658_);
v___x_4660_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
lean_object* v___x_4661_; lean_object* v_a_4662_; lean_object* v___x_4663_; 
lean_ctor_set_uint8(v___x_4660_, sizeof(void*)*7, v___x_4656_);
v___x_4661_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_irrelevant_4646_, v___x_4660_);
lean_dec(v_irrelevant_4646_);
v_a_4662_ = lean_ctor_get(v___x_4661_, 0);
lean_inc(v_a_4662_);
lean_dec_ref(v___x_4661_);
v___x_4663_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4648_, v_lowerBounds_4647_, v_a_4662_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_);
lean_dec(v_lowerBounds_4647_);
lean_dec(v_upperBounds_4648_);
return v___x_4663_;
}
}
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
lean_dec_ref(v_p_4637_);
v_a_4671_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4644_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4644_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin___boxed(lean_object* v_p_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_);
lean_dec(v_a_4683_);
lean_dec_ref(v_a_4682_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(lean_object* v_snd_4686_, lean_object* v_fst_4687_, lean_object* v_as_4688_, lean_object* v_as_x27_4689_, lean_object* v_b_4690_, lean_object* v_a_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
lean_object* v___x_4697_; 
v___x_4697_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4686_, v_fst_4687_, v_as_x27_4689_, v_b_4690_);
return v___x_4697_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___boxed(lean_object* v_snd_4698_, lean_object* v_fst_4699_, lean_object* v_as_4700_, lean_object* v_as_x27_4701_, lean_object* v_b_4702_, lean_object* v_a_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(v_snd_4698_, v_fst_4699_, v_as_4700_, v_as_x27_4701_, v_b_4702_, v_a_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v_as_x27_4701_);
lean_dec(v_as_4700_);
lean_dec(v_snd_4698_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(lean_object* v_as_4710_, lean_object* v_as_x27_4711_, lean_object* v_b_4712_, lean_object* v_a_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4711_, v_b_4712_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___boxed(lean_object* v_as_4720_, lean_object* v_as_x27_4721_, lean_object* v_b_4722_, lean_object* v_a_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(v_as_4720_, v_as_x27_4721_, v_b_4722_, v_a_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
lean_dec(v_as_x27_4721_);
lean_dec(v_as_4720_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(lean_object* v_upperBounds_4730_, lean_object* v_as_4731_, lean_object* v_as_x27_4732_, lean_object* v_b_4733_, lean_object* v_a_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_){
_start:
{
lean_object* v___x_4740_; 
v___x_4740_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4730_, v_as_x27_4732_, v_b_4733_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___boxed(lean_object* v_upperBounds_4741_, lean_object* v_as_4742_, lean_object* v_as_x27_4743_, lean_object* v_b_4744_, lean_object* v_a_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
lean_object* v_res_4751_; 
v_res_4751_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(v_upperBounds_4741_, v_as_4742_, v_as_x27_4743_, v_b_4744_, v_a_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_);
lean_dec(v___y_4749_);
lean_dec_ref(v___y_4748_);
lean_dec(v___y_4747_);
lean_dec_ref(v___y_4746_);
lean_dec(v_as_x27_4743_);
lean_dec(v_as_4742_);
lean_dec(v_upperBounds_4741_);
return v_res_4751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object* v_x_4752_, lean_object* v_x_4753_){
_start:
{
if (lean_obj_tag(v_x_4753_) == 0)
{
lean_inc(v_x_4752_);
return v_x_4752_;
}
else
{
lean_object* v_key_4754_; lean_object* v_value_4755_; lean_object* v_tail_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v_key_4754_ = lean_ctor_get(v_x_4753_, 0);
v_value_4755_ = lean_ctor_get(v_x_4753_, 1);
v_tail_4756_ = lean_ctor_get(v_x_4753_, 2);
v___x_4757_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4752_, v_tail_4756_);
lean_inc(v_value_4755_);
lean_inc(v_key_4754_);
v___x_4758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4758_, 0, v_key_4754_);
lean_ctor_set(v___x_4758_, 1, v_value_4755_);
v___x_4759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4759_, 0, v___x_4758_);
lean_ctor_set(v___x_4759_, 1, v___x_4757_);
return v___x_4759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2___boxed(lean_object* v_x_4760_, lean_object* v_x_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4760_, v_x_4761_);
lean_dec(v_x_4761_);
lean_dec(v_x_4760_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object* v_as_4763_, size_t v_i_4764_, size_t v_stop_4765_, lean_object* v_b_4766_){
_start:
{
uint8_t v___x_4767_; 
v___x_4767_ = lean_usize_dec_eq(v_i_4764_, v_stop_4765_);
if (v___x_4767_ == 0)
{
size_t v___x_4768_; size_t v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4768_ = ((size_t)1ULL);
v___x_4769_ = lean_usize_sub(v_i_4764_, v___x_4768_);
v___x_4770_ = lean_array_uget_borrowed(v_as_4763_, v___x_4769_);
v___x_4771_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_b_4766_, v___x_4770_);
lean_dec(v_b_4766_);
v_i_4764_ = v___x_4769_;
v_b_4766_ = v___x_4771_;
goto _start;
}
else
{
return v_b_4766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object* v_as_4773_, lean_object* v_i_4774_, lean_object* v_stop_4775_, lean_object* v_b_4776_){
_start:
{
size_t v_i_boxed_4777_; size_t v_stop_boxed_4778_; lean_object* v_res_4779_; 
v_i_boxed_4777_ = lean_unbox_usize(v_i_4774_);
lean_dec(v_i_4774_);
v_stop_boxed_4778_ = lean_unbox_usize(v_stop_4775_);
lean_dec(v_stop_4775_);
v_res_4779_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_as_4773_, v_i_boxed_4777_, v_stop_boxed_4778_, v_b_4776_);
lean_dec_ref(v_as_4773_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object* v_a_4780_, lean_object* v_a_4781_){
_start:
{
if (lean_obj_tag(v_a_4780_) == 0)
{
lean_object* v___x_4782_; 
v___x_4782_ = l_List_reverse___redArg(v_a_4781_);
return v___x_4782_;
}
else
{
lean_object* v_head_4783_; lean_object* v_tail_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4901_; 
v_head_4783_ = lean_ctor_get(v_a_4780_, 0);
v_tail_4784_ = lean_ctor_get(v_a_4780_, 1);
v_isSharedCheck_4901_ = !lean_is_exclusive(v_a_4780_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4786_ = v_a_4780_;
v_isShared_4787_ = v_isSharedCheck_4901_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_tail_4784_);
lean_inc(v_head_4783_);
lean_dec(v_a_4780_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4901_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___y_4789_; lean_object* v_snd_4794_; lean_object* v_constraint_4795_; lean_object* v_fst_4796_; lean_object* v_lowerBound_4797_; lean_object* v_upperBound_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___y_4803_; lean_object* v___y_4804_; 
v_snd_4794_ = lean_ctor_get(v_head_4783_, 1);
v_constraint_4795_ = lean_ctor_get(v_snd_4794_, 1);
lean_inc_ref(v_constraint_4795_);
v_fst_4796_ = lean_ctor_get(v_head_4783_, 0);
lean_inc(v_fst_4796_);
lean_dec(v_head_4783_);
v_lowerBound_4797_ = lean_ctor_get(v_constraint_4795_, 0);
lean_inc(v_lowerBound_4797_);
v_upperBound_4798_ = lean_ctor_get(v_constraint_4795_, 1);
lean_inc(v_upperBound_4798_);
lean_dec_ref(v_constraint_4795_);
v___x_4799_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_fst_4796_);
lean_dec(v_fst_4796_);
v___x_4800_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_4801_ = lean_string_append(v___x_4799_, v___x_4800_);
if (lean_obj_tag(v_lowerBound_4797_) == 0)
{
if (lean_obj_tag(v_upperBound_4798_) == 0)
{
lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4809_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_4810_ = lean_string_append(v___x_4801_, v___x_4809_);
v___y_4789_ = v___x_4810_;
goto v___jp_4788_;
}
else
{
lean_object* v_val_4811_; lean_object* v___x_4812_; lean_object* v___y_4814_; lean_object* v_intZero_4819_; uint8_t v_isNeg_4820_; 
v_val_4811_ = lean_ctor_get(v_upperBound_4798_, 0);
lean_inc(v_val_4811_);
lean_dec_ref_known(v_upperBound_4798_, 1);
v___x_4812_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_4819_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4820_ = lean_int_dec_lt(v_val_4811_, v_intZero_4819_);
if (v_isNeg_4820_ == 0)
{
lean_object* v_a_4821_; lean_object* v___x_4822_; 
v_a_4821_ = lean_nat_abs(v_val_4811_);
lean_dec(v_val_4811_);
v___x_4822_ = l_Nat_reprFast(v_a_4821_);
v___y_4814_ = v___x_4822_;
goto v___jp_4813_;
}
else
{
lean_object* v_abs_4823_; lean_object* v_one_4824_; lean_object* v_a_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v_abs_4823_ = lean_nat_abs(v_val_4811_);
lean_dec(v_val_4811_);
v_one_4824_ = lean_unsigned_to_nat(1u);
v_a_4825_ = lean_nat_sub(v_abs_4823_, v_one_4824_);
lean_dec(v_abs_4823_);
v___x_4826_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4827_ = lean_nat_add(v_a_4825_, v_one_4824_);
lean_dec(v_a_4825_);
v___x_4828_ = l_Nat_reprFast(v___x_4827_);
v___x_4829_ = lean_string_append(v___x_4826_, v___x_4828_);
lean_dec_ref(v___x_4828_);
v___y_4814_ = v___x_4829_;
goto v___jp_4813_;
}
v___jp_4813_:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
v___x_4815_ = lean_string_append(v___x_4812_, v___y_4814_);
lean_dec_ref(v___y_4814_);
v___x_4816_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4817_ = lean_string_append(v___x_4815_, v___x_4816_);
v___x_4818_ = lean_string_append(v___x_4801_, v___x_4817_);
lean_dec_ref(v___x_4817_);
v___y_4789_ = v___x_4818_;
goto v___jp_4788_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_4798_) == 0)
{
lean_object* v_val_4830_; lean_object* v___x_4831_; lean_object* v___y_4833_; lean_object* v_intZero_4838_; uint8_t v_isNeg_4839_; 
v_val_4830_ = lean_ctor_get(v_lowerBound_4797_, 0);
lean_inc(v_val_4830_);
lean_dec_ref_known(v_lowerBound_4797_, 1);
v___x_4831_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4838_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4839_ = lean_int_dec_lt(v_val_4830_, v_intZero_4838_);
if (v_isNeg_4839_ == 0)
{
lean_object* v_a_4840_; lean_object* v___x_4841_; 
v_a_4840_ = lean_nat_abs(v_val_4830_);
lean_dec(v_val_4830_);
v___x_4841_ = l_Nat_reprFast(v_a_4840_);
v___y_4833_ = v___x_4841_;
goto v___jp_4832_;
}
else
{
lean_object* v_abs_4842_; lean_object* v_one_4843_; lean_object* v_a_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v_abs_4842_ = lean_nat_abs(v_val_4830_);
lean_dec(v_val_4830_);
v_one_4843_ = lean_unsigned_to_nat(1u);
v_a_4844_ = lean_nat_sub(v_abs_4842_, v_one_4843_);
lean_dec(v_abs_4842_);
v___x_4845_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4846_ = lean_nat_add(v_a_4844_, v_one_4843_);
lean_dec(v_a_4844_);
v___x_4847_ = l_Nat_reprFast(v___x_4846_);
v___x_4848_ = lean_string_append(v___x_4845_, v___x_4847_);
lean_dec_ref(v___x_4847_);
v___y_4833_ = v___x_4848_;
goto v___jp_4832_;
}
v___jp_4832_:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4834_ = lean_string_append(v___x_4831_, v___y_4833_);
lean_dec_ref(v___y_4833_);
v___x_4835_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_4836_ = lean_string_append(v___x_4834_, v___x_4835_);
v___x_4837_ = lean_string_append(v___x_4801_, v___x_4836_);
lean_dec_ref(v___x_4836_);
v___y_4789_ = v___x_4837_;
goto v___jp_4788_;
}
}
else
{
lean_object* v_val_4849_; lean_object* v_val_4850_; uint8_t v___x_4851_; 
v_val_4849_ = lean_ctor_get(v_lowerBound_4797_, 0);
lean_inc(v_val_4849_);
lean_dec_ref_known(v_lowerBound_4797_, 1);
v_val_4850_ = lean_ctor_get(v_upperBound_4798_, 0);
lean_inc(v_val_4850_);
lean_dec_ref_known(v_upperBound_4798_, 1);
v___x_4851_ = lean_int_dec_lt(v_val_4850_, v_val_4849_);
if (v___x_4851_ == 0)
{
uint8_t v___x_4852_; 
v___x_4852_ = lean_int_dec_eq(v_val_4849_, v_val_4850_);
if (v___x_4852_ == 0)
{
lean_object* v___x_4853_; lean_object* v___y_4855_; lean_object* v_intZero_4870_; uint8_t v_isNeg_4871_; 
v___x_4853_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4870_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4871_ = lean_int_dec_lt(v_val_4849_, v_intZero_4870_);
if (v_isNeg_4871_ == 0)
{
lean_object* v_a_4872_; lean_object* v___x_4873_; 
v_a_4872_ = lean_nat_abs(v_val_4849_);
lean_dec(v_val_4849_);
v___x_4873_ = l_Nat_reprFast(v_a_4872_);
v___y_4855_ = v___x_4873_;
goto v___jp_4854_;
}
else
{
lean_object* v_abs_4874_; lean_object* v_one_4875_; lean_object* v_a_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v_abs_4874_ = lean_nat_abs(v_val_4849_);
lean_dec(v_val_4849_);
v_one_4875_ = lean_unsigned_to_nat(1u);
v_a_4876_ = lean_nat_sub(v_abs_4874_, v_one_4875_);
lean_dec(v_abs_4874_);
v___x_4877_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4878_ = lean_nat_add(v_a_4876_, v_one_4875_);
lean_dec(v_a_4876_);
v___x_4879_ = l_Nat_reprFast(v___x_4878_);
v___x_4880_ = lean_string_append(v___x_4877_, v___x_4879_);
lean_dec_ref(v___x_4879_);
v___y_4855_ = v___x_4880_;
goto v___jp_4854_;
}
v___jp_4854_:
{
lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v_intZero_4859_; uint8_t v_isNeg_4860_; 
v___x_4856_ = lean_string_append(v___x_4853_, v___y_4855_);
lean_dec_ref(v___y_4855_);
v___x_4857_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_4858_ = lean_string_append(v___x_4856_, v___x_4857_);
v_intZero_4859_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4860_ = lean_int_dec_lt(v_val_4850_, v_intZero_4859_);
if (v_isNeg_4860_ == 0)
{
lean_object* v_a_4861_; lean_object* v___x_4862_; 
v_a_4861_ = lean_nat_abs(v_val_4850_);
lean_dec(v_val_4850_);
v___x_4862_ = l_Nat_reprFast(v_a_4861_);
v___y_4803_ = v___x_4858_;
v___y_4804_ = v___x_4862_;
goto v___jp_4802_;
}
else
{
lean_object* v_abs_4863_; lean_object* v_one_4864_; lean_object* v_a_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
v_abs_4863_ = lean_nat_abs(v_val_4850_);
lean_dec(v_val_4850_);
v_one_4864_ = lean_unsigned_to_nat(1u);
v_a_4865_ = lean_nat_sub(v_abs_4863_, v_one_4864_);
lean_dec(v_abs_4863_);
v___x_4866_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4867_ = lean_nat_add(v_a_4865_, v_one_4864_);
lean_dec(v_a_4865_);
v___x_4868_ = l_Nat_reprFast(v___x_4867_);
v___x_4869_ = lean_string_append(v___x_4866_, v___x_4868_);
lean_dec_ref(v___x_4868_);
v___y_4803_ = v___x_4858_;
v___y_4804_ = v___x_4869_;
goto v___jp_4802_;
}
}
}
else
{
lean_object* v___x_4881_; lean_object* v___y_4883_; lean_object* v_intZero_4888_; uint8_t v_isNeg_4889_; 
lean_dec(v_val_4850_);
v___x_4881_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_4888_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4889_ = lean_int_dec_lt(v_val_4849_, v_intZero_4888_);
if (v_isNeg_4889_ == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4891_; 
v_a_4890_ = lean_nat_abs(v_val_4849_);
lean_dec(v_val_4849_);
v___x_4891_ = l_Nat_reprFast(v_a_4890_);
v___y_4883_ = v___x_4891_;
goto v___jp_4882_;
}
else
{
lean_object* v_abs_4892_; lean_object* v_one_4893_; lean_object* v_a_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v_abs_4892_ = lean_nat_abs(v_val_4849_);
lean_dec(v_val_4849_);
v_one_4893_ = lean_unsigned_to_nat(1u);
v_a_4894_ = lean_nat_sub(v_abs_4892_, v_one_4893_);
lean_dec(v_abs_4892_);
v___x_4895_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4896_ = lean_nat_add(v_a_4894_, v_one_4893_);
lean_dec(v_a_4894_);
v___x_4897_ = l_Nat_reprFast(v___x_4896_);
v___x_4898_ = lean_string_append(v___x_4895_, v___x_4897_);
lean_dec_ref(v___x_4897_);
v___y_4883_ = v___x_4898_;
goto v___jp_4882_;
}
v___jp_4882_:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4884_ = lean_string_append(v___x_4881_, v___y_4883_);
lean_dec_ref(v___y_4883_);
v___x_4885_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_4886_ = lean_string_append(v___x_4884_, v___x_4885_);
v___x_4887_ = lean_string_append(v___x_4801_, v___x_4886_);
lean_dec_ref(v___x_4886_);
v___y_4789_ = v___x_4887_;
goto v___jp_4788_;
}
}
}
else
{
lean_object* v___x_4899_; lean_object* v___x_4900_; 
lean_dec(v_val_4850_);
lean_dec(v_val_4849_);
v___x_4899_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_4900_ = lean_string_append(v___x_4801_, v___x_4899_);
v___y_4789_ = v___x_4900_;
goto v___jp_4788_;
}
}
}
v___jp_4788_:
{
lean_object* v___x_4791_; 
if (v_isShared_4787_ == 0)
{
lean_ctor_set(v___x_4786_, 1, v_a_4781_);
lean_ctor_set(v___x_4786_, 0, v___y_4789_);
v___x_4791_ = v___x_4786_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___y_4789_);
lean_ctor_set(v_reuseFailAlloc_4793_, 1, v_a_4781_);
v___x_4791_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
v_a_4780_ = v_tail_4784_;
v_a_4781_ = v___x_4791_;
goto _start;
}
}
v___jp_4802_:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4805_ = lean_string_append(v___y_4803_, v___y_4804_);
lean_dec_ref(v___y_4804_);
v___x_4806_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4807_ = lean_string_append(v___x_4805_, v___x_4806_);
v___x_4808_ = lean_string_append(v___x_4801_, v___x_4807_);
lean_dec_ref(v___x_4807_);
v___y_4789_ = v___x_4808_;
goto v___jp_4788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object* v_cls_4902_, lean_object* v_msg_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v_ref_4909_; lean_object* v___x_4910_; lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4955_; 
v_ref_4909_ = lean_ctor_get(v___y_4906_, 2);
v___x_4910_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4913_ = v___x_4910_;
v_isShared_4914_ = v_isSharedCheck_4955_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___x_4910_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4955_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4915_; lean_object* v_traceState_4916_; lean_object* v_env_4917_; lean_object* v_nextMacroScope_4918_; lean_object* v_ngen_4919_; lean_object* v_auxDeclNGen_4920_; lean_object* v_cache_4921_; lean_object* v_messages_4922_; lean_object* v_infoState_4923_; lean_object* v_snapshotTasks_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4954_; 
v___x_4915_ = lean_st_ref_take(v___y_4907_);
v_traceState_4916_ = lean_ctor_get(v___x_4915_, 4);
v_env_4917_ = lean_ctor_get(v___x_4915_, 0);
v_nextMacroScope_4918_ = lean_ctor_get(v___x_4915_, 1);
v_ngen_4919_ = lean_ctor_get(v___x_4915_, 2);
v_auxDeclNGen_4920_ = lean_ctor_get(v___x_4915_, 3);
v_cache_4921_ = lean_ctor_get(v___x_4915_, 5);
v_messages_4922_ = lean_ctor_get(v___x_4915_, 6);
v_infoState_4923_ = lean_ctor_get(v___x_4915_, 7);
v_snapshotTasks_4924_ = lean_ctor_get(v___x_4915_, 8);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4926_ = v___x_4915_;
v_isShared_4927_ = v_isSharedCheck_4954_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_snapshotTasks_4924_);
lean_inc(v_infoState_4923_);
lean_inc(v_messages_4922_);
lean_inc(v_cache_4921_);
lean_inc(v_traceState_4916_);
lean_inc(v_auxDeclNGen_4920_);
lean_inc(v_ngen_4919_);
lean_inc(v_nextMacroScope_4918_);
lean_inc(v_env_4917_);
lean_dec(v___x_4915_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4954_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
uint64_t v_tid_4928_; lean_object* v_traces_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4953_; 
v_tid_4928_ = lean_ctor_get_uint64(v_traceState_4916_, sizeof(void*)*1);
v_traces_4929_ = lean_ctor_get(v_traceState_4916_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v_traceState_4916_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4931_ = v_traceState_4916_;
v_isShared_4932_ = v_isSharedCheck_4953_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_traces_4929_);
lean_dec(v_traceState_4916_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4953_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4933_; double v___x_4934_; uint8_t v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4943_; 
v___x_4933_ = lean_box(0);
v___x_4934_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4935_ = 0;
v___x_4936_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4937_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4937_, 0, v_cls_4902_);
lean_ctor_set(v___x_4937_, 1, v___x_4933_);
lean_ctor_set(v___x_4937_, 2, v___x_4936_);
lean_ctor_set_float(v___x_4937_, sizeof(void*)*3, v___x_4934_);
lean_ctor_set_float(v___x_4937_, sizeof(void*)*3 + 8, v___x_4934_);
lean_ctor_set_uint8(v___x_4937_, sizeof(void*)*3 + 16, v___x_4935_);
v___x_4938_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4939_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4937_);
lean_ctor_set(v___x_4939_, 1, v_a_4911_);
lean_ctor_set(v___x_4939_, 2, v___x_4938_);
lean_inc(v_ref_4909_);
v___x_4940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4940_, 0, v_ref_4909_);
lean_ctor_set(v___x_4940_, 1, v___x_4939_);
v___x_4941_ = l_Lean_PersistentArray_push___redArg(v_traces_4929_, v___x_4940_);
if (v_isShared_4932_ == 0)
{
lean_ctor_set(v___x_4931_, 0, v___x_4941_);
v___x_4943_ = v___x_4931_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4941_);
lean_ctor_set_uint64(v_reuseFailAlloc_4952_, sizeof(void*)*1, v_tid_4928_);
v___x_4943_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
lean_object* v___x_4945_; 
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 4, v___x_4943_);
v___x_4945_ = v___x_4926_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_env_4917_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_nextMacroScope_4918_);
lean_ctor_set(v_reuseFailAlloc_4951_, 2, v_ngen_4919_);
lean_ctor_set(v_reuseFailAlloc_4951_, 3, v_auxDeclNGen_4920_);
lean_ctor_set(v_reuseFailAlloc_4951_, 4, v___x_4943_);
lean_ctor_set(v_reuseFailAlloc_4951_, 5, v_cache_4921_);
lean_ctor_set(v_reuseFailAlloc_4951_, 6, v_messages_4922_);
lean_ctor_set(v_reuseFailAlloc_4951_, 7, v_infoState_4923_);
lean_ctor_set(v_reuseFailAlloc_4951_, 8, v_snapshotTasks_4924_);
v___x_4945_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4949_; 
v___x_4946_ = lean_st_ref_put(v___y_4907_, v___x_4945_);
v___x_4947_ = lean_box(0);
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 0, v___x_4947_);
v___x_4949_ = v___x_4913_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4947_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg___boxed(lean_object* v_cls_4956_, lean_object* v_msg_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4956_, v_msg_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
lean_dec(v___y_4959_);
lean_dec_ref(v___y_4958_);
return v_res_4963_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1(void){
_start:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4965_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__0));
v___x_4966_ = l_Lean_stringToMessageData(v___x_4965_);
return v___x_4966_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1(void){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4968_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__0));
v___x_4969_ = l_Lean_stringToMessageData(v___x_4968_);
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega(lean_object* v_p_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, uint8_t v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_){
_start:
{
lean_object* v___y_4982_; lean_object* v___y_4983_; lean_object* v___y_4984_; uint8_t v___y_4985_; lean_object* v___y_4986_; lean_object* v___y_4987_; lean_object* v___y_4988_; lean_object* v___y_4989_; lean_object* v___y_4990_; lean_object* v_toCold_4996_; lean_object* v_options_4997_; uint8_t v_hasTrace_4998_; 
v_toCold_4996_ = lean_ctor_get(v_a_4978_, 0);
v_options_4997_ = lean_ctor_get(v_toCold_4996_, 2);
v_hasTrace_4998_ = lean_ctor_get_uint8(v_options_4997_, sizeof(void*)*1);
if (v_hasTrace_4998_ == 0)
{
v___y_4982_ = v_a_4971_;
v___y_4983_ = v_a_4972_;
v___y_4984_ = v_a_4973_;
v___y_4985_ = v_a_4974_;
v___y_4986_ = v_a_4975_;
v___y_4987_ = v_a_4976_;
v___y_4988_ = v_a_4977_;
v___y_4989_ = v_a_4978_;
v___y_4990_ = v_a_4979_;
goto v___jp_4981_;
}
else
{
lean_object* v_inheritedTraceOptions_4999_; lean_object* v_cls_5000_; lean_object* v___x_5001_; uint8_t v___x_5002_; 
v_inheritedTraceOptions_4999_ = lean_ctor_get(v_toCold_4996_, 11);
v_cls_5000_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_5001_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_5002_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4999_, v_options_4997_, v___x_5001_);
if (v___x_5002_ == 0)
{
v___y_4982_ = v_a_4971_;
v___y_4983_ = v_a_4972_;
v___y_4984_ = v_a_4973_;
v___y_4985_ = v_a_4974_;
v___y_4986_ = v_a_4975_;
v___y_4987_ = v_a_4976_;
v___y_4988_ = v_a_4977_;
v___y_4989_ = v_a_4978_;
v___y_4990_ = v_a_4979_;
goto v___jp_4981_;
}
else
{
lean_object* v_constraints_5003_; uint8_t v_possible_5004_; lean_object* v___x_5005_; lean_object* v___y_5007_; 
v_constraints_5003_ = lean_ctor_get(v_p_4970_, 2);
v_possible_5004_ = lean_ctor_get_uint8(v_p_4970_, sizeof(void*)*7);
v___x_5005_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1);
if (v_possible_5004_ == 0)
{
lean_object* v___x_5020_; 
v___x_5020_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
v___y_5007_ = v___x_5020_;
goto v___jp_5006_;
}
else
{
uint8_t v___x_5021_; 
v___x_5021_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_4970_);
if (v___x_5021_ == 0)
{
lean_object* v_buckets_5022_; lean_object* v___x_5023_; lean_object* v___y_5025_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; uint8_t v___x_5032_; 
v_buckets_5022_ = lean_ctor_get(v_constraints_5003_, 1);
v___x_5023_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5029_ = lean_box(0);
v___x_5030_ = lean_array_get_size(v_buckets_5022_);
v___x_5031_ = lean_unsigned_to_nat(0u);
v___x_5032_ = lean_nat_dec_lt(v___x_5031_, v___x_5030_);
if (v___x_5032_ == 0)
{
v___y_5025_ = v___x_5029_;
goto v___jp_5024_;
}
else
{
size_t v___x_5033_; size_t v___x_5034_; lean_object* v___x_5035_; 
v___x_5033_ = lean_usize_of_nat(v___x_5030_);
v___x_5034_ = ((size_t)0ULL);
v___x_5035_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5022_, v___x_5033_, v___x_5034_, v___x_5029_);
v___y_5025_ = v___x_5035_;
goto v___jp_5024_;
}
v___jp_5024_:
{
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; 
v___x_5026_ = lean_box(0);
v___x_5027_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5025_, v___x_5026_);
v___x_5028_ = l_String_intercalate(v___x_5023_, v___x_5027_);
v___y_5007_ = v___x_5028_;
goto v___jp_5006_;
}
}
else
{
lean_object* v___x_5036_; 
v___x_5036_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_5007_ = v___x_5036_;
goto v___jp_5006_;
}
}
v___jp_5006_:
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; 
v___x_5008_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5008_, 0, v___y_5007_);
v___x_5009_ = l_Lean_MessageData_ofFormat(v___x_5008_);
v___x_5010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5005_);
lean_ctor_set(v___x_5010_, 1, v___x_5009_);
v___x_5011_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5000_, v___x_5010_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_dec_ref_known(v___x_5011_, 1);
v___y_4982_ = v_a_4971_;
v___y_4983_ = v_a_4972_;
v___y_4984_ = v_a_4973_;
v___y_4985_ = v_a_4974_;
v___y_4986_ = v_a_4975_;
v___y_4987_ = v_a_4976_;
v___y_4988_ = v_a_4977_;
v___y_4989_ = v_a_4978_;
v___y_4990_ = v_a_4979_;
goto v___jp_4981_;
}
else
{
lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5019_; 
lean_dec_ref(v_p_4970_);
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5019_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_5014_ = v___x_5011_;
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_dec(v___x_5011_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5017_; 
if (v_isShared_5015_ == 0)
{
v___x_5017_ = v___x_5014_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_a_5012_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
}
}
}
}
v___jp_4981_:
{
uint8_t v_possible_4991_; 
v_possible_4991_ = lean_ctor_get_uint8(v_p_4970_, sizeof(void*)*7);
if (v_possible_4991_ == 0)
{
lean_object* v___x_4992_; 
v___x_4992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4992_, 0, v_p_4970_);
return v___x_4992_;
}
else
{
lean_object* v___x_4993_; 
v___x_4993_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_4970_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_object* v_a_4994_; lean_object* v___x_4995_; 
v_a_4994_ = lean_ctor_get(v___x_4993_, 0);
lean_inc(v_a_4994_);
lean_dec_ref_known(v___x_4993_, 1);
v___x_4995_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_a_4994_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
return v___x_4995_;
}
else
{
return v___x_4993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination(lean_object* v_p_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, uint8_t v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_){
_start:
{
lean_object* v___y_5049_; lean_object* v___y_5050_; lean_object* v___y_5051_; uint8_t v___y_5052_; lean_object* v___y_5053_; lean_object* v___y_5054_; lean_object* v___y_5055_; lean_object* v___y_5056_; lean_object* v___y_5057_; uint8_t v_possible_5061_; 
v_possible_5061_ = lean_ctor_get_uint8(v_p_5037_, sizeof(void*)*7);
if (v_possible_5061_ == 0)
{
lean_object* v___x_5062_; 
v___x_5062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5062_, 0, v_p_5037_);
return v___x_5062_;
}
else
{
lean_object* v_constraints_5063_; uint8_t v___x_5064_; 
v_constraints_5063_ = lean_ctor_get(v_p_5037_, 2);
v___x_5064_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_5037_);
if (v___x_5064_ == 0)
{
lean_object* v_toCold_5065_; lean_object* v_options_5066_; uint8_t v_hasTrace_5067_; 
v_toCold_5065_ = lean_ctor_get(v_a_5045_, 0);
v_options_5066_ = lean_ctor_get(v_toCold_5065_, 2);
v_hasTrace_5067_ = lean_ctor_get_uint8(v_options_5066_, sizeof(void*)*1);
if (v_hasTrace_5067_ == 0)
{
v___y_5049_ = v_a_5038_;
v___y_5050_ = v_a_5039_;
v___y_5051_ = v_a_5040_;
v___y_5052_ = v_a_5041_;
v___y_5053_ = v_a_5042_;
v___y_5054_ = v_a_5043_;
v___y_5055_ = v_a_5044_;
v___y_5056_ = v_a_5045_;
v___y_5057_ = v_a_5046_;
goto v___jp_5048_;
}
else
{
lean_object* v_inheritedTraceOptions_5068_; lean_object* v_cls_5069_; lean_object* v___x_5070_; uint8_t v___x_5071_; 
v_inheritedTraceOptions_5068_ = lean_ctor_get(v_toCold_5065_, 11);
v_cls_5069_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_5070_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_5071_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5068_, v_options_5066_, v___x_5070_);
if (v___x_5071_ == 0)
{
v___y_5049_ = v_a_5038_;
v___y_5050_ = v_a_5039_;
v___y_5051_ = v_a_5040_;
v___y_5052_ = v_a_5041_;
v___y_5053_ = v_a_5042_;
v___y_5054_ = v_a_5043_;
v___y_5055_ = v_a_5044_;
v___y_5056_ = v_a_5045_;
v___y_5057_ = v_a_5046_;
goto v___jp_5048_;
}
else
{
lean_object* v___x_5072_; lean_object* v___y_5074_; 
v___x_5072_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1);
if (v___x_5064_ == 0)
{
lean_object* v_buckets_5087_; lean_object* v___x_5088_; lean_object* v___y_5090_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; uint8_t v___x_5097_; 
v_buckets_5087_ = lean_ctor_get(v_constraints_5063_, 1);
v___x_5088_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5094_ = lean_box(0);
v___x_5095_ = lean_array_get_size(v_buckets_5087_);
v___x_5096_ = lean_unsigned_to_nat(0u);
v___x_5097_ = lean_nat_dec_lt(v___x_5096_, v___x_5095_);
if (v___x_5097_ == 0)
{
v___y_5090_ = v___x_5094_;
goto v___jp_5089_;
}
else
{
size_t v___x_5098_; size_t v___x_5099_; lean_object* v___x_5100_; 
v___x_5098_ = lean_usize_of_nat(v___x_5095_);
v___x_5099_ = ((size_t)0ULL);
v___x_5100_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5087_, v___x_5098_, v___x_5099_, v___x_5094_);
v___y_5090_ = v___x_5100_;
goto v___jp_5089_;
}
v___jp_5089_:
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5091_ = lean_box(0);
v___x_5092_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5090_, v___x_5091_);
v___x_5093_ = l_String_intercalate(v___x_5088_, v___x_5092_);
v___y_5074_ = v___x_5093_;
goto v___jp_5073_;
}
}
else
{
lean_object* v___x_5101_; 
v___x_5101_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_5074_ = v___x_5101_;
goto v___jp_5073_;
}
v___jp_5073_:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
v___x_5075_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5075_, 0, v___y_5074_);
v___x_5076_ = l_Lean_MessageData_ofFormat(v___x_5075_);
v___x_5077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5077_, 0, v___x_5072_);
lean_ctor_set(v___x_5077_, 1, v___x_5076_);
v___x_5078_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5069_, v___x_5077_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_);
if (lean_obj_tag(v___x_5078_) == 0)
{
lean_dec_ref_known(v___x_5078_, 1);
v___y_5049_ = v_a_5038_;
v___y_5050_ = v_a_5039_;
v___y_5051_ = v_a_5040_;
v___y_5052_ = v_a_5041_;
v___y_5053_ = v_a_5042_;
v___y_5054_ = v_a_5043_;
v___y_5055_ = v_a_5044_;
v___y_5056_ = v_a_5045_;
v___y_5057_ = v_a_5046_;
goto v___jp_5048_;
}
else
{
lean_object* v_a_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5086_; 
lean_dec_ref(v_p_5037_);
v_a_5079_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5081_ = v___x_5078_;
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_a_5079_);
lean_dec(v___x_5078_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___x_5084_; 
if (v_isShared_5082_ == 0)
{
v___x_5084_ = v___x_5081_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5102_; 
v___x_5102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5102_, 0, v_p_5037_);
return v___x_5102_;
}
}
v___jp_5048_:
{
lean_object* v___x_5058_; 
v___x_5058_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_5037_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_object* v_a_5059_; lean_object* v___x_5060_; 
v_a_5059_ = lean_ctor_get(v___x_5058_, 0);
lean_inc(v_a_5059_);
lean_dec_ref_known(v___x_5058_, 1);
v___x_5060_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_a_5059_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_);
return v___x_5060_;
}
else
{
return v___x_5058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___boxed(lean_object* v_p_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_){
_start:
{
uint8_t v_a_boxed_5114_; lean_object* v_res_5115_; 
v_a_boxed_5114_ = lean_unbox(v_a_5107_);
v_res_5115_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_p_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_boxed_5114_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_, v_a_5112_);
lean_dec(v_a_5112_);
lean_dec_ref(v_a_5111_);
lean_dec(v_a_5110_);
lean_dec_ref(v_a_5109_);
lean_dec(v_a_5108_);
lean_dec_ref(v_a_5106_);
lean_dec(v_a_5105_);
lean_dec(v_a_5104_);
return v_res_5115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___boxed(lean_object* v_p_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_){
_start:
{
uint8_t v_a_boxed_5127_; lean_object* v_res_5128_; 
v_a_boxed_5127_ = lean_unbox(v_a_5120_);
v_res_5128_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_p_5116_, v_a_5117_, v_a_5118_, v_a_5119_, v_a_boxed_5127_, v_a_5121_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_);
lean_dec(v_a_5125_);
lean_dec_ref(v_a_5124_);
lean_dec(v_a_5123_);
lean_dec_ref(v_a_5122_);
lean_dec(v_a_5121_);
lean_dec_ref(v_a_5119_);
lean_dec(v_a_5118_);
lean_dec(v_a_5117_);
return v_res_5128_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(lean_object* v_cls_5129_, lean_object* v_msg_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, uint8_t v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_){
_start:
{
lean_object* v___x_5141_; 
v___x_5141_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5129_, v_msg_5130_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_);
return v___x_5141_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___boxed(lean_object* v_cls_5142_, lean_object* v_msg_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_){
_start:
{
uint8_t v___y_16276__boxed_5154_; lean_object* v_res_5155_; 
v___y_16276__boxed_5154_ = lean_unbox(v___y_5147_);
v_res_5155_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(v_cls_5142_, v_msg_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_16276__boxed_5154_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_);
lean_dec(v___y_5152_);
lean_dec_ref(v___y_5151_);
lean_dec(v___y_5150_);
lean_dec_ref(v___y_5149_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5146_);
lean_dec(v___y_5145_);
lean_dec(v___y_5144_);
return v_res_5155_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Omega_Core(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_();
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
