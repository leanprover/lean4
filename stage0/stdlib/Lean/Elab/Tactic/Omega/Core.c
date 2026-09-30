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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_instMonadEIO___redArg();
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
static const lean_ctor_object l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4;
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
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2));
v___x_569_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3);
v___x_572_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2));
v___x_573_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_571_);
lean_ctor_set(v___x_573_, 2, v___x_570_);
lean_ctor_set(v___x_573_, 3, v___x_570_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(lean_object* v_s_574_, lean_object* v_replacement_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_577_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4);
v___x_578_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_574_, v_replacement_575_, v___x_577_, v___x_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___boxed(lean_object* v_s_579_, lean_object* v_replacement_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v_s_579_, v_replacement_580_);
lean_dec_ref(v_replacement_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(lean_object* v_s_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_585_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__0));
v___x_586_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__1));
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_string_utf8_byte_size(v_s_584_);
v___x_589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_589_, 0, v_s_584_);
lean_ctor_set(v___x_589_, 1, v___x_587_);
lean_ctor_set(v___x_589_, 2, v___x_588_);
v___x_590_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v___x_589_, v___x_586_);
v___x_591_ = lean_string_append(v___x_585_, v___x_590_);
lean_dec_ref(v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0(lean_object* v_s_592_, lean_object* v_pattern_593_, lean_object* v_replacement_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v_s_592_, v_replacement_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___boxed(lean_object* v_s_596_, lean_object* v_pattern_597_, lean_object* v_replacement_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0(v_s_596_, v_pattern_597_, v_replacement_598_);
lean_dec_ref(v_replacement_598_);
lean_dec_ref(v_pattern_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0(lean_object* v_s_600_, lean_object* v_replacement_601_, lean_object* v_inst_602_, lean_object* v_R_603_, lean_object* v_a_604_, lean_object* v_b_605_, lean_object* v_c_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_600_, v_replacement_601_, v_a_604_, v_b_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___boxed(lean_object* v_s_608_, lean_object* v_replacement_609_, lean_object* v_inst_610_, lean_object* v_R_611_, lean_object* v_a_612_, lean_object* v_b_613_, lean_object* v_c_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0(v_s_608_, v_replacement_609_, v_inst_610_, v_R_611_, v_a_612_, v_b_613_, v_c_614_);
lean_dec_ref(v_replacement_609_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_618_) == 0)
{
return v_x_617_;
}
else
{
lean_object* v_head_619_; lean_object* v_tail_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_head_619_ = lean_ctor_get(v_x_618_, 0);
v_tail_620_ = lean_ctor_get(v_x_618_, 1);
v___x_621_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_622_ = lean_string_append(v_x_617_, v___x_621_);
v___x_623_ = l_Int_repr(v_head_619_);
v___x_624_ = lean_string_append(v___x_622_, v___x_623_);
lean_dec_ref(v___x_623_);
v_x_617_ = v___x_624_;
v_x_618_ = v_tail_620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___boxed(lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v_x_626_, v_x_627_);
lean_dec(v_x_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(lean_object* v_x_632_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_object* v___x_633_; 
v___x_633_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__0));
return v___x_633_;
}
else
{
lean_object* v_tail_634_; 
v_tail_634_ = lean_ctor_get(v_x_632_, 1);
if (lean_obj_tag(v_tail_634_) == 0)
{
lean_object* v_head_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_head_635_ = lean_ctor_get(v_x_632_, 0);
v___x_636_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v___x_637_ = l_Int_repr(v_head_635_);
v___x_638_ = lean_string_append(v___x_636_, v___x_637_);
lean_dec_ref(v___x_637_);
v___x_639_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_640_ = lean_string_append(v___x_638_, v___x_639_);
return v___x_640_;
}
else
{
lean_object* v_head_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint32_t v___x_646_; lean_object* v___x_647_; 
v_head_641_ = lean_ctor_get(v_x_632_, 0);
v___x_642_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v___x_643_ = l_Int_repr(v_head_641_);
v___x_644_ = lean_string_append(v___x_642_, v___x_643_);
lean_dec_ref(v___x_643_);
v___x_645_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v___x_644_, v_tail_634_);
v___x_646_ = 93;
v___x_647_ = lean_string_push(v___x_645_, v___x_646_);
return v___x_647_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___boxed(lean_object* v_x_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_648_);
lean_dec(v_x_648_);
return v_res_649_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
if (lean_obj_tag(v_x_650_) == 0)
{
if (lean_obj_tag(v_x_651_) == 0)
{
uint8_t v___x_652_; 
v___x_652_ = 1;
return v___x_652_;
}
else
{
uint8_t v___x_653_; 
v___x_653_ = 0;
return v___x_653_;
}
}
else
{
if (lean_obj_tag(v_x_651_) == 0)
{
uint8_t v___x_654_; 
v___x_654_ = 0;
return v___x_654_;
}
else
{
lean_object* v_head_655_; lean_object* v_tail_656_; lean_object* v_head_657_; lean_object* v_tail_658_; uint8_t v___x_659_; 
v_head_655_ = lean_ctor_get(v_x_650_, 0);
v_tail_656_ = lean_ctor_get(v_x_650_, 1);
v_head_657_ = lean_ctor_get(v_x_651_, 0);
v_tail_658_ = lean_ctor_get(v_x_651_, 1);
v___x_659_ = lean_int_dec_eq(v_head_655_, v_head_657_);
if (v___x_659_ == 0)
{
return v___x_659_;
}
else
{
v_x_650_ = v_tail_656_;
v_x_651_ = v_tail_658_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1___boxed(lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
uint8_t v_res_663_; lean_object* v_r_664_; 
v_res_663_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_661_, v_x_662_);
lean_dec(v_x_662_);
lean_dec(v_x_661_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString(lean_object* v_s_682_, lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
switch(lean_obj_tag(v_x_684_))
{
case 0:
{
lean_object* v_i_685_; lean_object* v_lowerBound_686_; lean_object* v_upperBound_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___y_692_; lean_object* v___y_699_; lean_object* v___y_700_; 
v_i_685_ = lean_ctor_get(v_x_684_, 2);
lean_inc(v_i_685_);
lean_dec_ref_known(v_x_684_, 3);
v_lowerBound_686_ = lean_ctor_get(v_s_682_, 0);
lean_inc(v_lowerBound_686_);
v_upperBound_687_ = lean_ctor_get(v_s_682_, 1);
lean_inc(v_upperBound_687_);
lean_dec_ref(v_s_682_);
v___x_688_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_683_);
lean_dec(v_x_683_);
v___x_689_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_690_ = lean_string_append(v___x_688_, v___x_689_);
if (lean_obj_tag(v_lowerBound_686_) == 0)
{
if (lean_obj_tag(v_upperBound_687_) == 0)
{
lean_object* v___x_704_; 
v___x_704_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_692_ = v___x_704_;
goto v___jp_691_;
}
else
{
lean_object* v_val_705_; lean_object* v___x_706_; lean_object* v___y_708_; lean_object* v_intZero_712_; uint8_t v_isNeg_713_; 
v_val_705_ = lean_ctor_get(v_upperBound_687_, 0);
lean_inc(v_val_705_);
lean_dec_ref_known(v_upperBound_687_, 1);
v___x_706_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_712_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_713_ = lean_int_dec_lt(v_val_705_, v_intZero_712_);
if (v_isNeg_713_ == 0)
{
lean_object* v_a_714_; lean_object* v___x_715_; 
v_a_714_ = lean_nat_abs(v_val_705_);
lean_dec(v_val_705_);
v___x_715_ = l_Nat_reprFast(v_a_714_);
v___y_708_ = v___x_715_;
goto v___jp_707_;
}
else
{
lean_object* v_abs_716_; lean_object* v_one_717_; lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_abs_716_ = lean_nat_abs(v_val_705_);
lean_dec(v_val_705_);
v_one_717_ = lean_unsigned_to_nat(1u);
v_a_718_ = lean_nat_sub(v_abs_716_, v_one_717_);
lean_dec(v_abs_716_);
v___x_719_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_720_ = lean_nat_add(v_a_718_, v_one_717_);
lean_dec(v_a_718_);
v___x_721_ = l_Nat_reprFast(v___x_720_);
v___x_722_ = lean_string_append(v___x_719_, v___x_721_);
lean_dec_ref(v___x_721_);
v___y_708_ = v___x_722_;
goto v___jp_707_;
}
v___jp_707_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_709_ = lean_string_append(v___x_706_, v___y_708_);
lean_dec_ref(v___y_708_);
v___x_710_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_711_ = lean_string_append(v___x_709_, v___x_710_);
v___y_692_ = v___x_711_;
goto v___jp_691_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_687_) == 0)
{
lean_object* v_val_723_; lean_object* v___x_724_; lean_object* v___y_726_; lean_object* v_intZero_730_; uint8_t v_isNeg_731_; 
v_val_723_ = lean_ctor_get(v_lowerBound_686_, 0);
lean_inc(v_val_723_);
lean_dec_ref_known(v_lowerBound_686_, 1);
v___x_724_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_730_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_731_ = lean_int_dec_lt(v_val_723_, v_intZero_730_);
if (v_isNeg_731_ == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; 
v_a_732_ = lean_nat_abs(v_val_723_);
lean_dec(v_val_723_);
v___x_733_ = l_Nat_reprFast(v_a_732_);
v___y_726_ = v___x_733_;
goto v___jp_725_;
}
else
{
lean_object* v_abs_734_; lean_object* v_one_735_; lean_object* v_a_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_abs_734_ = lean_nat_abs(v_val_723_);
lean_dec(v_val_723_);
v_one_735_ = lean_unsigned_to_nat(1u);
v_a_736_ = lean_nat_sub(v_abs_734_, v_one_735_);
lean_dec(v_abs_734_);
v___x_737_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_738_ = lean_nat_add(v_a_736_, v_one_735_);
lean_dec(v_a_736_);
v___x_739_ = l_Nat_reprFast(v___x_738_);
v___x_740_ = lean_string_append(v___x_737_, v___x_739_);
lean_dec_ref(v___x_739_);
v___y_726_ = v___x_740_;
goto v___jp_725_;
}
v___jp_725_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = lean_string_append(v___x_724_, v___y_726_);
lean_dec_ref(v___y_726_);
v___x_728_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_729_ = lean_string_append(v___x_727_, v___x_728_);
v___y_692_ = v___x_729_;
goto v___jp_691_;
}
}
else
{
lean_object* v_val_741_; lean_object* v_val_742_; uint8_t v___x_743_; 
v_val_741_ = lean_ctor_get(v_lowerBound_686_, 0);
lean_inc(v_val_741_);
lean_dec_ref_known(v_lowerBound_686_, 1);
v_val_742_ = lean_ctor_get(v_upperBound_687_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v_upperBound_687_, 1);
v___x_743_ = lean_int_dec_lt(v_val_742_, v_val_741_);
if (v___x_743_ == 0)
{
uint8_t v___x_744_; 
v___x_744_ = lean_int_dec_eq(v_val_741_, v_val_742_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___y_747_; lean_object* v_intZero_762_; uint8_t v_isNeg_763_; 
v___x_745_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_762_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_763_ = lean_int_dec_lt(v_val_741_, v_intZero_762_);
if (v_isNeg_763_ == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_nat_abs(v_val_741_);
lean_dec(v_val_741_);
v___x_765_ = l_Nat_reprFast(v_a_764_);
v___y_747_ = v___x_765_;
goto v___jp_746_;
}
else
{
lean_object* v_abs_766_; lean_object* v_one_767_; lean_object* v_a_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_abs_766_ = lean_nat_abs(v_val_741_);
lean_dec(v_val_741_);
v_one_767_ = lean_unsigned_to_nat(1u);
v_a_768_ = lean_nat_sub(v_abs_766_, v_one_767_);
lean_dec(v_abs_766_);
v___x_769_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_770_ = lean_nat_add(v_a_768_, v_one_767_);
lean_dec(v_a_768_);
v___x_771_ = l_Nat_reprFast(v___x_770_);
v___x_772_ = lean_string_append(v___x_769_, v___x_771_);
lean_dec_ref(v___x_771_);
v___y_747_ = v___x_772_;
goto v___jp_746_;
}
v___jp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_intZero_751_; uint8_t v_isNeg_752_; 
v___x_748_ = lean_string_append(v___x_745_, v___y_747_);
lean_dec_ref(v___y_747_);
v___x_749_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_750_ = lean_string_append(v___x_748_, v___x_749_);
v_intZero_751_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_752_ = lean_int_dec_lt(v_val_742_, v_intZero_751_);
if (v_isNeg_752_ == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; 
v_a_753_ = lean_nat_abs(v_val_742_);
lean_dec(v_val_742_);
v___x_754_ = l_Nat_reprFast(v_a_753_);
v___y_699_ = v___x_750_;
v___y_700_ = v___x_754_;
goto v___jp_698_;
}
else
{
lean_object* v_abs_755_; lean_object* v_one_756_; lean_object* v_a_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_abs_755_ = lean_nat_abs(v_val_742_);
lean_dec(v_val_742_);
v_one_756_ = lean_unsigned_to_nat(1u);
v_a_757_ = lean_nat_sub(v_abs_755_, v_one_756_);
lean_dec(v_abs_755_);
v___x_758_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_759_ = lean_nat_add(v_a_757_, v_one_756_);
lean_dec(v_a_757_);
v___x_760_ = l_Nat_reprFast(v___x_759_);
v___x_761_ = lean_string_append(v___x_758_, v___x_760_);
lean_dec_ref(v___x_760_);
v___y_699_ = v___x_750_;
v___y_700_ = v___x_761_;
goto v___jp_698_;
}
}
}
else
{
lean_object* v___x_773_; lean_object* v___y_775_; lean_object* v_intZero_779_; uint8_t v_isNeg_780_; 
lean_dec(v_val_742_);
v___x_773_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_779_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_780_ = lean_int_dec_lt(v_val_741_, v_intZero_779_);
if (v_isNeg_780_ == 0)
{
lean_object* v_a_781_; lean_object* v___x_782_; 
v_a_781_ = lean_nat_abs(v_val_741_);
lean_dec(v_val_741_);
v___x_782_ = l_Nat_reprFast(v_a_781_);
v___y_775_ = v___x_782_;
goto v___jp_774_;
}
else
{
lean_object* v_abs_783_; lean_object* v_one_784_; lean_object* v_a_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_abs_783_ = lean_nat_abs(v_val_741_);
lean_dec(v_val_741_);
v_one_784_ = lean_unsigned_to_nat(1u);
v_a_785_ = lean_nat_sub(v_abs_783_, v_one_784_);
lean_dec(v_abs_783_);
v___x_786_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_787_ = lean_nat_add(v_a_785_, v_one_784_);
lean_dec(v_a_785_);
v___x_788_ = l_Nat_reprFast(v___x_787_);
v___x_789_ = lean_string_append(v___x_786_, v___x_788_);
lean_dec_ref(v___x_788_);
v___y_775_ = v___x_789_;
goto v___jp_774_;
}
v___jp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_string_append(v___x_773_, v___y_775_);
lean_dec_ref(v___y_775_);
v___x_777_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_778_ = lean_string_append(v___x_776_, v___x_777_);
v___y_692_ = v___x_778_;
goto v___jp_691_;
}
}
}
else
{
lean_object* v___x_790_; 
lean_dec(v_val_742_);
lean_dec(v_val_741_);
v___x_790_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_692_ = v___x_790_;
goto v___jp_691_;
}
}
}
v___jp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_693_ = lean_string_append(v___x_690_, v___y_692_);
lean_dec_ref(v___y_692_);
v___x_694_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__1));
v___x_695_ = lean_string_append(v___x_693_, v___x_694_);
v___x_696_ = l_Nat_reprFast(v_i_685_);
v___x_697_ = lean_string_append(v___x_695_, v___x_696_);
lean_dec_ref(v___x_696_);
return v___x_697_;
}
v___jp_698_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_string_append(v___y_699_, v___y_700_);
lean_dec_ref(v___y_700_);
v___x_702_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_703_ = lean_string_append(v___x_701_, v___x_702_);
v___y_692_ = v___x_703_;
goto v___jp_691_;
}
}
case 1:
{
lean_object* v_s_791_; lean_object* v_c_792_; lean_object* v_j_793_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; uint8_t v___y_851_; uint8_t v___x_914_; 
v_s_791_ = lean_ctor_get(v_x_684_, 0);
lean_inc_ref(v_s_791_);
v_c_792_ = lean_ctor_get(v_x_684_, 1);
lean_inc(v_c_792_);
v_j_793_ = lean_ctor_get(v_x_684_, 2);
lean_inc_ref(v_j_793_);
lean_dec_ref_known(v_x_684_, 3);
v___x_914_ = l_Lean_Omega_instBEqConstraint_beq(v_s_682_, v_s_791_);
if (v___x_914_ == 0)
{
v___y_851_ = v___x_914_;
goto v___jp_850_;
}
else
{
uint8_t v___x_915_; 
v___x_915_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_683_, v_c_792_);
v___y_851_ = v___x_915_;
goto v___jp_850_;
}
v___jp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_797_ = lean_string_append(v___y_795_, v___y_796_);
lean_dec_ref(v___y_796_);
v___x_798_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9));
v___x_799_ = lean_string_append(v___x_797_, v___x_798_);
v___x_800_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_791_, v_c_792_, v_j_793_);
v___x_801_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_800_);
v___x_802_ = lean_string_append(v___x_799_, v___x_801_);
lean_dec_ref(v___x_801_);
return v___x_802_;
}
v___jp_803_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_inc_ref(v___y_805_);
v___x_807_ = lean_string_append(v___y_805_, v___y_806_);
lean_dec_ref(v___y_806_);
v___x_808_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_809_ = lean_string_append(v___x_807_, v___x_808_);
v___y_795_ = v___y_804_;
v___y_796_ = v___x_809_;
goto v___jp_794_;
}
v___jp_810_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_inc_ref(v___y_811_);
v___x_814_ = lean_string_append(v___y_811_, v___y_813_);
lean_dec_ref(v___y_813_);
v___x_815_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_816_ = lean_string_append(v___x_814_, v___x_815_);
v___y_795_ = v___y_812_;
v___y_796_ = v___x_816_;
goto v___jp_794_;
}
v___jp_817_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_string_append(v___y_818_, v___y_820_);
lean_dec_ref(v___y_820_);
v___x_822_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_823_ = lean_string_append(v___x_821_, v___x_822_);
v___y_795_ = v___y_819_;
v___y_796_ = v___x_823_;
goto v___jp_794_;
}
v___jp_824_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v_intZero_832_; uint8_t v_isNeg_833_; 
lean_inc_ref(v___y_826_);
v___x_829_ = lean_string_append(v___y_826_, v___y_828_);
lean_dec_ref(v___y_828_);
v___x_830_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_831_ = lean_string_append(v___x_829_, v___x_830_);
v_intZero_832_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_833_ = lean_int_dec_lt(v___y_825_, v_intZero_832_);
if (v_isNeg_833_ == 0)
{
lean_object* v_a_834_; lean_object* v___x_835_; 
v_a_834_ = lean_nat_abs(v___y_825_);
lean_dec(v___y_825_);
v___x_835_ = l_Nat_reprFast(v_a_834_);
v___y_818_ = v___x_831_;
v___y_819_ = v___y_827_;
v___y_820_ = v___x_835_;
goto v___jp_817_;
}
else
{
lean_object* v_abs_836_; lean_object* v_one_837_; lean_object* v_a_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_abs_836_ = lean_nat_abs(v___y_825_);
lean_dec(v___y_825_);
v_one_837_ = lean_unsigned_to_nat(1u);
v_a_838_ = lean_nat_sub(v_abs_836_, v_one_837_);
lean_dec(v_abs_836_);
v___x_839_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_840_ = lean_nat_add(v_a_838_, v_one_837_);
lean_dec(v_a_838_);
v___x_841_ = l_Nat_reprFast(v___x_840_);
v___x_842_ = lean_string_append(v___x_839_, v___x_841_);
lean_dec_ref(v___x_841_);
v___y_818_ = v___x_831_;
v___y_819_ = v___y_827_;
v___y_820_ = v___x_842_;
goto v___jp_817_;
}
}
v___jp_843_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_inc_ref(v___y_844_);
v___x_847_ = lean_string_append(v___y_844_, v___y_846_);
lean_dec_ref(v___y_846_);
v___x_848_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_849_ = lean_string_append(v___x_847_, v___x_848_);
v___y_795_ = v___y_845_;
v___y_796_ = v___x_849_;
goto v___jp_794_;
}
v___jp_850_:
{
if (v___y_851_ == 0)
{
lean_object* v_lowerBound_852_; lean_object* v_upperBound_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_lowerBound_852_ = lean_ctor_get(v_s_682_, 0);
lean_inc(v_lowerBound_852_);
v_upperBound_853_ = lean_ctor_get(v_s_682_, 1);
lean_inc(v_upperBound_853_);
lean_dec_ref(v_s_682_);
v___x_854_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_683_);
lean_dec(v_x_683_);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_856_ = lean_string_append(v___x_854_, v___x_855_);
if (lean_obj_tag(v_lowerBound_852_) == 0)
{
if (lean_obj_tag(v_upperBound_853_) == 0)
{
lean_object* v___x_857_; 
v___x_857_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_795_ = v___x_856_;
v___y_796_ = v___x_857_;
goto v___jp_794_;
}
else
{
lean_object* v_val_858_; lean_object* v___x_859_; lean_object* v_intZero_860_; uint8_t v_isNeg_861_; 
v_val_858_ = lean_ctor_get(v_upperBound_853_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v_upperBound_853_, 1);
v___x_859_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_860_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_861_ = lean_int_dec_lt(v_val_858_, v_intZero_860_);
if (v_isNeg_861_ == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; 
v_a_862_ = lean_nat_abs(v_val_858_);
lean_dec(v_val_858_);
v___x_863_ = l_Nat_reprFast(v_a_862_);
v___y_804_ = v___x_856_;
v___y_805_ = v___x_859_;
v___y_806_ = v___x_863_;
goto v___jp_803_;
}
else
{
lean_object* v_abs_864_; lean_object* v_one_865_; lean_object* v_a_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_abs_864_ = lean_nat_abs(v_val_858_);
lean_dec(v_val_858_);
v_one_865_ = lean_unsigned_to_nat(1u);
v_a_866_ = lean_nat_sub(v_abs_864_, v_one_865_);
lean_dec(v_abs_864_);
v___x_867_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_868_ = lean_nat_add(v_a_866_, v_one_865_);
lean_dec(v_a_866_);
v___x_869_ = l_Nat_reprFast(v___x_868_);
v___x_870_ = lean_string_append(v___x_867_, v___x_869_);
lean_dec_ref(v___x_869_);
v___y_804_ = v___x_856_;
v___y_805_ = v___x_859_;
v___y_806_ = v___x_870_;
goto v___jp_803_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_853_) == 0)
{
lean_object* v_val_871_; lean_object* v___x_872_; lean_object* v_intZero_873_; uint8_t v_isNeg_874_; 
v_val_871_ = lean_ctor_get(v_lowerBound_852_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v_lowerBound_852_, 1);
v___x_872_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_873_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_874_ = lean_int_dec_lt(v_val_871_, v_intZero_873_);
if (v_isNeg_874_ == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; 
v_a_875_ = lean_nat_abs(v_val_871_);
lean_dec(v_val_871_);
v___x_876_ = l_Nat_reprFast(v_a_875_);
v___y_811_ = v___x_872_;
v___y_812_ = v___x_856_;
v___y_813_ = v___x_876_;
goto v___jp_810_;
}
else
{
lean_object* v_abs_877_; lean_object* v_one_878_; lean_object* v_a_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_abs_877_ = lean_nat_abs(v_val_871_);
lean_dec(v_val_871_);
v_one_878_ = lean_unsigned_to_nat(1u);
v_a_879_ = lean_nat_sub(v_abs_877_, v_one_878_);
lean_dec(v_abs_877_);
v___x_880_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_881_ = lean_nat_add(v_a_879_, v_one_878_);
lean_dec(v_a_879_);
v___x_882_ = l_Nat_reprFast(v___x_881_);
v___x_883_ = lean_string_append(v___x_880_, v___x_882_);
lean_dec_ref(v___x_882_);
v___y_811_ = v___x_872_;
v___y_812_ = v___x_856_;
v___y_813_ = v___x_883_;
goto v___jp_810_;
}
}
else
{
lean_object* v_val_884_; lean_object* v_val_885_; uint8_t v___x_886_; 
v_val_884_ = lean_ctor_get(v_lowerBound_852_, 0);
lean_inc(v_val_884_);
lean_dec_ref_known(v_lowerBound_852_, 1);
v_val_885_ = lean_ctor_get(v_upperBound_853_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v_upperBound_853_, 1);
v___x_886_ = lean_int_dec_lt(v_val_885_, v_val_884_);
if (v___x_886_ == 0)
{
uint8_t v___x_887_; 
v___x_887_ = lean_int_dec_eq(v_val_884_, v_val_885_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v_intZero_889_; uint8_t v_isNeg_890_; 
v___x_888_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_889_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_890_ = lean_int_dec_lt(v_val_884_, v_intZero_889_);
if (v_isNeg_890_ == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; 
v_a_891_ = lean_nat_abs(v_val_884_);
lean_dec(v_val_884_);
v___x_892_ = l_Nat_reprFast(v_a_891_);
v___y_825_ = v_val_885_;
v___y_826_ = v___x_888_;
v___y_827_ = v___x_856_;
v___y_828_ = v___x_892_;
goto v___jp_824_;
}
else
{
lean_object* v_abs_893_; lean_object* v_one_894_; lean_object* v_a_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_abs_893_ = lean_nat_abs(v_val_884_);
lean_dec(v_val_884_);
v_one_894_ = lean_unsigned_to_nat(1u);
v_a_895_ = lean_nat_sub(v_abs_893_, v_one_894_);
lean_dec(v_abs_893_);
v___x_896_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_897_ = lean_nat_add(v_a_895_, v_one_894_);
lean_dec(v_a_895_);
v___x_898_ = l_Nat_reprFast(v___x_897_);
v___x_899_ = lean_string_append(v___x_896_, v___x_898_);
lean_dec_ref(v___x_898_);
v___y_825_ = v_val_885_;
v___y_826_ = v___x_888_;
v___y_827_ = v___x_856_;
v___y_828_ = v___x_899_;
goto v___jp_824_;
}
}
else
{
lean_object* v___x_900_; lean_object* v_intZero_901_; uint8_t v_isNeg_902_; 
lean_dec(v_val_885_);
v___x_900_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_901_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_902_ = lean_int_dec_lt(v_val_884_, v_intZero_901_);
if (v_isNeg_902_ == 0)
{
lean_object* v_a_903_; lean_object* v___x_904_; 
v_a_903_ = lean_nat_abs(v_val_884_);
lean_dec(v_val_884_);
v___x_904_ = l_Nat_reprFast(v_a_903_);
v___y_844_ = v___x_900_;
v___y_845_ = v___x_856_;
v___y_846_ = v___x_904_;
goto v___jp_843_;
}
else
{
lean_object* v_abs_905_; lean_object* v_one_906_; lean_object* v_a_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_abs_905_ = lean_nat_abs(v_val_884_);
lean_dec(v_val_884_);
v_one_906_ = lean_unsigned_to_nat(1u);
v_a_907_ = lean_nat_sub(v_abs_905_, v_one_906_);
lean_dec(v_abs_905_);
v___x_908_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_909_ = lean_nat_add(v_a_907_, v_one_906_);
lean_dec(v_a_907_);
v___x_910_ = l_Nat_reprFast(v___x_909_);
v___x_911_ = lean_string_append(v___x_908_, v___x_910_);
lean_dec_ref(v___x_910_);
v___y_844_ = v___x_900_;
v___y_845_ = v___x_856_;
v___y_846_ = v___x_911_;
goto v___jp_843_;
}
}
}
else
{
lean_object* v___x_912_; 
lean_dec(v_val_885_);
lean_dec(v_val_884_);
v___x_912_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_795_ = v___x_856_;
v___y_796_ = v___x_912_;
goto v___jp_794_;
}
}
}
}
else
{
lean_dec(v_x_683_);
lean_dec_ref(v_s_682_);
v_s_682_ = v_s_791_;
v_x_683_ = v_c_792_;
v_x_684_ = v_j_793_;
goto _start;
}
}
}
case 2:
{
lean_object* v_s_916_; lean_object* v_t_917_; lean_object* v_j_918_; lean_object* v_k_919_; lean_object* v_lowerBound_920_; lean_object* v_upperBound_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___y_926_; lean_object* v___y_939_; lean_object* v___y_940_; 
v_s_916_ = lean_ctor_get(v_x_684_, 0);
lean_inc_ref(v_s_916_);
v_t_917_ = lean_ctor_get(v_x_684_, 1);
lean_inc_ref(v_t_917_);
v_j_918_ = lean_ctor_get(v_x_684_, 3);
lean_inc_ref(v_j_918_);
v_k_919_ = lean_ctor_get(v_x_684_, 4);
lean_inc_ref(v_k_919_);
lean_dec_ref_known(v_x_684_, 5);
v_lowerBound_920_ = lean_ctor_get(v_s_682_, 0);
lean_inc(v_lowerBound_920_);
v_upperBound_921_ = lean_ctor_get(v_s_682_, 1);
lean_inc(v_upperBound_921_);
lean_dec_ref(v_s_682_);
v___x_922_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_683_);
v___x_923_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_924_ = lean_string_append(v___x_922_, v___x_923_);
if (lean_obj_tag(v_lowerBound_920_) == 0)
{
if (lean_obj_tag(v_upperBound_921_) == 0)
{
lean_object* v___x_944_; 
v___x_944_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_926_ = v___x_944_;
goto v___jp_925_;
}
else
{
lean_object* v_val_945_; lean_object* v___x_946_; lean_object* v___y_948_; lean_object* v_intZero_952_; uint8_t v_isNeg_953_; 
v_val_945_ = lean_ctor_get(v_upperBound_921_, 0);
lean_inc(v_val_945_);
lean_dec_ref_known(v_upperBound_921_, 1);
v___x_946_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_952_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_953_ = lean_int_dec_lt(v_val_945_, v_intZero_952_);
if (v_isNeg_953_ == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; 
v_a_954_ = lean_nat_abs(v_val_945_);
lean_dec(v_val_945_);
v___x_955_ = l_Nat_reprFast(v_a_954_);
v___y_948_ = v___x_955_;
goto v___jp_947_;
}
else
{
lean_object* v_abs_956_; lean_object* v_one_957_; lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_abs_956_ = lean_nat_abs(v_val_945_);
lean_dec(v_val_945_);
v_one_957_ = lean_unsigned_to_nat(1u);
v_a_958_ = lean_nat_sub(v_abs_956_, v_one_957_);
lean_dec(v_abs_956_);
v___x_959_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_960_ = lean_nat_add(v_a_958_, v_one_957_);
lean_dec(v_a_958_);
v___x_961_ = l_Nat_reprFast(v___x_960_);
v___x_962_ = lean_string_append(v___x_959_, v___x_961_);
lean_dec_ref(v___x_961_);
v___y_948_ = v___x_962_;
goto v___jp_947_;
}
v___jp_947_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_string_append(v___x_946_, v___y_948_);
lean_dec_ref(v___y_948_);
v___x_950_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_951_ = lean_string_append(v___x_949_, v___x_950_);
v___y_926_ = v___x_951_;
goto v___jp_925_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_921_) == 0)
{
lean_object* v_val_963_; lean_object* v___x_964_; lean_object* v___y_966_; lean_object* v_intZero_970_; uint8_t v_isNeg_971_; 
v_val_963_ = lean_ctor_get(v_lowerBound_920_, 0);
lean_inc(v_val_963_);
lean_dec_ref_known(v_lowerBound_920_, 1);
v___x_964_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_970_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_971_ = lean_int_dec_lt(v_val_963_, v_intZero_970_);
if (v_isNeg_971_ == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_972_ = lean_nat_abs(v_val_963_);
lean_dec(v_val_963_);
v___x_973_ = l_Nat_reprFast(v_a_972_);
v___y_966_ = v___x_973_;
goto v___jp_965_;
}
else
{
lean_object* v_abs_974_; lean_object* v_one_975_; lean_object* v_a_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_abs_974_ = lean_nat_abs(v_val_963_);
lean_dec(v_val_963_);
v_one_975_ = lean_unsigned_to_nat(1u);
v_a_976_ = lean_nat_sub(v_abs_974_, v_one_975_);
lean_dec(v_abs_974_);
v___x_977_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_978_ = lean_nat_add(v_a_976_, v_one_975_);
lean_dec(v_a_976_);
v___x_979_ = l_Nat_reprFast(v___x_978_);
v___x_980_ = lean_string_append(v___x_977_, v___x_979_);
lean_dec_ref(v___x_979_);
v___y_966_ = v___x_980_;
goto v___jp_965_;
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = lean_string_append(v___x_964_, v___y_966_);
lean_dec_ref(v___y_966_);
v___x_968_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_969_ = lean_string_append(v___x_967_, v___x_968_);
v___y_926_ = v___x_969_;
goto v___jp_925_;
}
}
else
{
lean_object* v_val_981_; lean_object* v_val_982_; uint8_t v___x_983_; 
v_val_981_ = lean_ctor_get(v_lowerBound_920_, 0);
lean_inc(v_val_981_);
lean_dec_ref_known(v_lowerBound_920_, 1);
v_val_982_ = lean_ctor_get(v_upperBound_921_, 0);
lean_inc(v_val_982_);
lean_dec_ref_known(v_upperBound_921_, 1);
v___x_983_ = lean_int_dec_lt(v_val_982_, v_val_981_);
if (v___x_983_ == 0)
{
uint8_t v___x_984_; 
v___x_984_ = lean_int_dec_eq(v_val_981_, v_val_982_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___y_987_; lean_object* v_intZero_1002_; uint8_t v_isNeg_1003_; 
v___x_985_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1002_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1003_ = lean_int_dec_lt(v_val_981_, v_intZero_1002_);
if (v_isNeg_1003_ == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_nat_abs(v_val_981_);
lean_dec(v_val_981_);
v___x_1005_ = l_Nat_reprFast(v_a_1004_);
v___y_987_ = v___x_1005_;
goto v___jp_986_;
}
else
{
lean_object* v_abs_1006_; lean_object* v_one_1007_; lean_object* v_a_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_abs_1006_ = lean_nat_abs(v_val_981_);
lean_dec(v_val_981_);
v_one_1007_ = lean_unsigned_to_nat(1u);
v_a_1008_ = lean_nat_sub(v_abs_1006_, v_one_1007_);
lean_dec(v_abs_1006_);
v___x_1009_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1010_ = lean_nat_add(v_a_1008_, v_one_1007_);
lean_dec(v_a_1008_);
v___x_1011_ = l_Nat_reprFast(v___x_1010_);
v___x_1012_ = lean_string_append(v___x_1009_, v___x_1011_);
lean_dec_ref(v___x_1011_);
v___y_987_ = v___x_1012_;
goto v___jp_986_;
}
v___jp_986_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v_intZero_991_; uint8_t v_isNeg_992_; 
v___x_988_ = lean_string_append(v___x_985_, v___y_987_);
lean_dec_ref(v___y_987_);
v___x_989_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_990_ = lean_string_append(v___x_988_, v___x_989_);
v_intZero_991_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_992_ = lean_int_dec_lt(v_val_982_, v_intZero_991_);
if (v_isNeg_992_ == 0)
{
lean_object* v_a_993_; lean_object* v___x_994_; 
v_a_993_ = lean_nat_abs(v_val_982_);
lean_dec(v_val_982_);
v___x_994_ = l_Nat_reprFast(v_a_993_);
v___y_939_ = v___x_990_;
v___y_940_ = v___x_994_;
goto v___jp_938_;
}
else
{
lean_object* v_abs_995_; lean_object* v_one_996_; lean_object* v_a_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_abs_995_ = lean_nat_abs(v_val_982_);
lean_dec(v_val_982_);
v_one_996_ = lean_unsigned_to_nat(1u);
v_a_997_ = lean_nat_sub(v_abs_995_, v_one_996_);
lean_dec(v_abs_995_);
v___x_998_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_999_ = lean_nat_add(v_a_997_, v_one_996_);
lean_dec(v_a_997_);
v___x_1000_ = l_Nat_reprFast(v___x_999_);
v___x_1001_ = lean_string_append(v___x_998_, v___x_1000_);
lean_dec_ref(v___x_1000_);
v___y_939_ = v___x_990_;
v___y_940_ = v___x_1001_;
goto v___jp_938_;
}
}
}
else
{
lean_object* v___x_1013_; lean_object* v___y_1015_; lean_object* v_intZero_1019_; uint8_t v_isNeg_1020_; 
lean_dec(v_val_982_);
v___x_1013_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1019_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1020_ = lean_int_dec_lt(v_val_981_, v_intZero_1019_);
if (v_isNeg_1020_ == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1021_ = lean_nat_abs(v_val_981_);
lean_dec(v_val_981_);
v___x_1022_ = l_Nat_reprFast(v_a_1021_);
v___y_1015_ = v___x_1022_;
goto v___jp_1014_;
}
else
{
lean_object* v_abs_1023_; lean_object* v_one_1024_; lean_object* v_a_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_abs_1023_ = lean_nat_abs(v_val_981_);
lean_dec(v_val_981_);
v_one_1024_ = lean_unsigned_to_nat(1u);
v_a_1025_ = lean_nat_sub(v_abs_1023_, v_one_1024_);
lean_dec(v_abs_1023_);
v___x_1026_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1027_ = lean_nat_add(v_a_1025_, v_one_1024_);
lean_dec(v_a_1025_);
v___x_1028_ = l_Nat_reprFast(v___x_1027_);
v___x_1029_ = lean_string_append(v___x_1026_, v___x_1028_);
lean_dec_ref(v___x_1028_);
v___y_1015_ = v___x_1029_;
goto v___jp_1014_;
}
v___jp_1014_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = lean_string_append(v___x_1013_, v___y_1015_);
lean_dec_ref(v___y_1015_);
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1018_ = lean_string_append(v___x_1016_, v___x_1017_);
v___y_926_ = v___x_1018_;
goto v___jp_925_;
}
}
}
else
{
lean_object* v___x_1030_; 
lean_dec(v_val_982_);
lean_dec(v_val_981_);
v___x_1030_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_926_ = v___x_1030_;
goto v___jp_925_;
}
}
}
v___jp_925_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_927_ = lean_string_append(v___x_924_, v___y_926_);
lean_dec_ref(v___y_926_);
v___x_928_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__10));
v___x_929_ = lean_string_append(v___x_927_, v___x_928_);
lean_inc(v_x_683_);
v___x_930_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_916_, v_x_683_, v_j_918_);
v___x_931_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_930_);
v___x_932_ = lean_string_append(v___x_929_, v___x_931_);
lean_dec_ref(v___x_931_);
v___x_933_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_934_ = lean_string_append(v___x_932_, v___x_933_);
v___x_935_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_917_, v_x_683_, v_k_919_);
v___x_936_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_935_);
v___x_937_ = lean_string_append(v___x_934_, v___x_936_);
lean_dec_ref(v___x_936_);
return v___x_937_;
}
v___jp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_string_append(v___y_939_, v___y_940_);
lean_dec_ref(v___y_940_);
v___x_942_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_943_ = lean_string_append(v___x_941_, v___x_942_);
v___y_926_ = v___x_943_;
goto v___jp_925_;
}
}
case 3:
{
lean_object* v_s_1031_; lean_object* v_t_1032_; lean_object* v_x_1033_; lean_object* v_y_1034_; lean_object* v_a_1035_; lean_object* v_j_1036_; lean_object* v_b_1037_; lean_object* v_k_1038_; lean_object* v_lowerBound_1039_; lean_object* v_upperBound_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___y_1045_; lean_object* v___y_1066_; lean_object* v___y_1067_; 
v_s_1031_ = lean_ctor_get(v_x_684_, 0);
lean_inc_ref(v_s_1031_);
v_t_1032_ = lean_ctor_get(v_x_684_, 1);
lean_inc_ref(v_t_1032_);
v_x_1033_ = lean_ctor_get(v_x_684_, 2);
lean_inc(v_x_1033_);
v_y_1034_ = lean_ctor_get(v_x_684_, 3);
lean_inc(v_y_1034_);
v_a_1035_ = lean_ctor_get(v_x_684_, 4);
lean_inc(v_a_1035_);
v_j_1036_ = lean_ctor_get(v_x_684_, 5);
lean_inc_ref(v_j_1036_);
v_b_1037_ = lean_ctor_get(v_x_684_, 6);
lean_inc(v_b_1037_);
v_k_1038_ = lean_ctor_get(v_x_684_, 7);
lean_inc_ref(v_k_1038_);
lean_dec_ref_known(v_x_684_, 8);
v_lowerBound_1039_ = lean_ctor_get(v_s_682_, 0);
lean_inc(v_lowerBound_1039_);
v_upperBound_1040_ = lean_ctor_get(v_s_682_, 1);
lean_inc(v_upperBound_1040_);
lean_dec_ref(v_s_682_);
v___x_1041_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_683_);
lean_dec(v_x_683_);
v___x_1042_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1043_ = lean_string_append(v___x_1041_, v___x_1042_);
if (lean_obj_tag(v_lowerBound_1039_) == 0)
{
if (lean_obj_tag(v_upperBound_1040_) == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1045_ = v___x_1071_;
goto v___jp_1044_;
}
else
{
lean_object* v_val_1072_; lean_object* v___x_1073_; lean_object* v___y_1075_; lean_object* v_intZero_1079_; uint8_t v_isNeg_1080_; 
v_val_1072_ = lean_ctor_get(v_upperBound_1040_, 0);
lean_inc(v_val_1072_);
lean_dec_ref_known(v_upperBound_1040_, 1);
v___x_1073_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1079_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1080_ = lean_int_dec_lt(v_val_1072_, v_intZero_1079_);
if (v_isNeg_1080_ == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; 
v_a_1081_ = lean_nat_abs(v_val_1072_);
lean_dec(v_val_1072_);
v___x_1082_ = l_Nat_reprFast(v_a_1081_);
v___y_1075_ = v___x_1082_;
goto v___jp_1074_;
}
else
{
lean_object* v_abs_1083_; lean_object* v_one_1084_; lean_object* v_a_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_abs_1083_ = lean_nat_abs(v_val_1072_);
lean_dec(v_val_1072_);
v_one_1084_ = lean_unsigned_to_nat(1u);
v_a_1085_ = lean_nat_sub(v_abs_1083_, v_one_1084_);
lean_dec(v_abs_1083_);
v___x_1086_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1087_ = lean_nat_add(v_a_1085_, v_one_1084_);
lean_dec(v_a_1085_);
v___x_1088_ = l_Nat_reprFast(v___x_1087_);
v___x_1089_ = lean_string_append(v___x_1086_, v___x_1088_);
lean_dec_ref(v___x_1088_);
v___y_1075_ = v___x_1089_;
goto v___jp_1074_;
}
v___jp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = lean_string_append(v___x_1073_, v___y_1075_);
lean_dec_ref(v___y_1075_);
v___x_1077_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1078_ = lean_string_append(v___x_1076_, v___x_1077_);
v___y_1045_ = v___x_1078_;
goto v___jp_1044_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1040_) == 0)
{
lean_object* v_val_1090_; lean_object* v___x_1091_; lean_object* v___y_1093_; lean_object* v_intZero_1097_; uint8_t v_isNeg_1098_; 
v_val_1090_ = lean_ctor_get(v_lowerBound_1039_, 0);
lean_inc(v_val_1090_);
lean_dec_ref_known(v_lowerBound_1039_, 1);
v___x_1091_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1097_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1098_ = lean_int_dec_lt(v_val_1090_, v_intZero_1097_);
if (v_isNeg_1098_ == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1100_; 
v_a_1099_ = lean_nat_abs(v_val_1090_);
lean_dec(v_val_1090_);
v___x_1100_ = l_Nat_reprFast(v_a_1099_);
v___y_1093_ = v___x_1100_;
goto v___jp_1092_;
}
else
{
lean_object* v_abs_1101_; lean_object* v_one_1102_; lean_object* v_a_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_abs_1101_ = lean_nat_abs(v_val_1090_);
lean_dec(v_val_1090_);
v_one_1102_ = lean_unsigned_to_nat(1u);
v_a_1103_ = lean_nat_sub(v_abs_1101_, v_one_1102_);
lean_dec(v_abs_1101_);
v___x_1104_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1105_ = lean_nat_add(v_a_1103_, v_one_1102_);
lean_dec(v_a_1103_);
v___x_1106_ = l_Nat_reprFast(v___x_1105_);
v___x_1107_ = lean_string_append(v___x_1104_, v___x_1106_);
lean_dec_ref(v___x_1106_);
v___y_1093_ = v___x_1107_;
goto v___jp_1092_;
}
v___jp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = lean_string_append(v___x_1091_, v___y_1093_);
lean_dec_ref(v___y_1093_);
v___x_1095_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1096_ = lean_string_append(v___x_1094_, v___x_1095_);
v___y_1045_ = v___x_1096_;
goto v___jp_1044_;
}
}
else
{
lean_object* v_val_1108_; lean_object* v_val_1109_; uint8_t v___x_1110_; 
v_val_1108_ = lean_ctor_get(v_lowerBound_1039_, 0);
lean_inc(v_val_1108_);
lean_dec_ref_known(v_lowerBound_1039_, 1);
v_val_1109_ = lean_ctor_get(v_upperBound_1040_, 0);
lean_inc(v_val_1109_);
lean_dec_ref_known(v_upperBound_1040_, 1);
v___x_1110_ = lean_int_dec_lt(v_val_1109_, v_val_1108_);
if (v___x_1110_ == 0)
{
uint8_t v___x_1111_; 
v___x_1111_ = lean_int_dec_eq(v_val_1108_, v_val_1109_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___y_1114_; lean_object* v_intZero_1129_; uint8_t v_isNeg_1130_; 
v___x_1112_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1129_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1130_ = lean_int_dec_lt(v_val_1108_, v_intZero_1129_);
if (v_isNeg_1130_ == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1132_; 
v_a_1131_ = lean_nat_abs(v_val_1108_);
lean_dec(v_val_1108_);
v___x_1132_ = l_Nat_reprFast(v_a_1131_);
v___y_1114_ = v___x_1132_;
goto v___jp_1113_;
}
else
{
lean_object* v_abs_1133_; lean_object* v_one_1134_; lean_object* v_a_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_abs_1133_ = lean_nat_abs(v_val_1108_);
lean_dec(v_val_1108_);
v_one_1134_ = lean_unsigned_to_nat(1u);
v_a_1135_ = lean_nat_sub(v_abs_1133_, v_one_1134_);
lean_dec(v_abs_1133_);
v___x_1136_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1137_ = lean_nat_add(v_a_1135_, v_one_1134_);
lean_dec(v_a_1135_);
v___x_1138_ = l_Nat_reprFast(v___x_1137_);
v___x_1139_ = lean_string_append(v___x_1136_, v___x_1138_);
lean_dec_ref(v___x_1138_);
v___y_1114_ = v___x_1139_;
goto v___jp_1113_;
}
v___jp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v_intZero_1118_; uint8_t v_isNeg_1119_; 
v___x_1115_ = lean_string_append(v___x_1112_, v___y_1114_);
lean_dec_ref(v___y_1114_);
v___x_1116_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1117_ = lean_string_append(v___x_1115_, v___x_1116_);
v_intZero_1118_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1119_ = lean_int_dec_lt(v_val_1109_, v_intZero_1118_);
if (v_isNeg_1119_ == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; 
v_a_1120_ = lean_nat_abs(v_val_1109_);
lean_dec(v_val_1109_);
v___x_1121_ = l_Nat_reprFast(v_a_1120_);
v___y_1066_ = v___x_1117_;
v___y_1067_ = v___x_1121_;
goto v___jp_1065_;
}
else
{
lean_object* v_abs_1122_; lean_object* v_one_1123_; lean_object* v_a_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_abs_1122_ = lean_nat_abs(v_val_1109_);
lean_dec(v_val_1109_);
v_one_1123_ = lean_unsigned_to_nat(1u);
v_a_1124_ = lean_nat_sub(v_abs_1122_, v_one_1123_);
lean_dec(v_abs_1122_);
v___x_1125_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1126_ = lean_nat_add(v_a_1124_, v_one_1123_);
lean_dec(v_a_1124_);
v___x_1127_ = l_Nat_reprFast(v___x_1126_);
v___x_1128_ = lean_string_append(v___x_1125_, v___x_1127_);
lean_dec_ref(v___x_1127_);
v___y_1066_ = v___x_1117_;
v___y_1067_ = v___x_1128_;
goto v___jp_1065_;
}
}
}
else
{
lean_object* v___x_1140_; lean_object* v___y_1142_; lean_object* v_intZero_1146_; uint8_t v_isNeg_1147_; 
lean_dec(v_val_1109_);
v___x_1140_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1146_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1147_ = lean_int_dec_lt(v_val_1108_, v_intZero_1146_);
if (v_isNeg_1147_ == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1149_; 
v_a_1148_ = lean_nat_abs(v_val_1108_);
lean_dec(v_val_1108_);
v___x_1149_ = l_Nat_reprFast(v_a_1148_);
v___y_1142_ = v___x_1149_;
goto v___jp_1141_;
}
else
{
lean_object* v_abs_1150_; lean_object* v_one_1151_; lean_object* v_a_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_abs_1150_ = lean_nat_abs(v_val_1108_);
lean_dec(v_val_1108_);
v_one_1151_ = lean_unsigned_to_nat(1u);
v_a_1152_ = lean_nat_sub(v_abs_1150_, v_one_1151_);
lean_dec(v_abs_1150_);
v___x_1153_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1154_ = lean_nat_add(v_a_1152_, v_one_1151_);
lean_dec(v_a_1152_);
v___x_1155_ = l_Nat_reprFast(v___x_1154_);
v___x_1156_ = lean_string_append(v___x_1153_, v___x_1155_);
lean_dec_ref(v___x_1155_);
v___y_1142_ = v___x_1156_;
goto v___jp_1141_;
}
v___jp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = lean_string_append(v___x_1140_, v___y_1142_);
lean_dec_ref(v___y_1142_);
v___x_1144_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1145_ = lean_string_append(v___x_1143_, v___x_1144_);
v___y_1045_ = v___x_1145_;
goto v___jp_1044_;
}
}
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_val_1109_);
lean_dec(v_val_1108_);
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1045_ = v___x_1157_;
goto v___jp_1044_;
}
}
}
v___jp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1046_ = lean_string_append(v___x_1043_, v___y_1045_);
lean_dec_ref(v___y_1045_);
v___x_1047_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__11));
v___x_1048_ = lean_string_append(v___x_1046_, v___x_1047_);
v___x_1049_ = l_Int_repr(v_a_1035_);
lean_dec(v_a_1035_);
v___x_1050_ = lean_string_append(v___x_1048_, v___x_1049_);
lean_dec_ref(v___x_1049_);
v___x_1051_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__12));
v___x_1052_ = lean_string_append(v___x_1050_, v___x_1051_);
v___x_1053_ = l_Int_repr(v_b_1037_);
lean_dec(v_b_1037_);
v___x_1054_ = lean_string_append(v___x_1052_, v___x_1053_);
lean_dec_ref(v___x_1053_);
v___x_1055_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__13));
v___x_1056_ = lean_string_append(v___x_1054_, v___x_1055_);
v___x_1057_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_1031_, v_x_1033_, v_j_1036_);
v___x_1058_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1057_);
v___x_1059_ = lean_string_append(v___x_1056_, v___x_1058_);
lean_dec_ref(v___x_1058_);
v___x_1060_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_1061_ = lean_string_append(v___x_1059_, v___x_1060_);
v___x_1062_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_1032_, v_y_1034_, v_k_1038_);
v___x_1063_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1062_);
v___x_1064_ = lean_string_append(v___x_1061_, v___x_1063_);
lean_dec_ref(v___x_1063_);
return v___x_1064_;
}
v___jp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_string_append(v___y_1066_, v___y_1067_);
lean_dec_ref(v___y_1067_);
v___x_1069_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1070_ = lean_string_append(v___x_1068_, v___x_1069_);
v___y_1045_ = v___x_1070_;
goto v___jp_1044_;
}
}
default: 
{
lean_object* v_m_1158_; lean_object* v_r_1159_; lean_object* v_i_1160_; lean_object* v_x_1161_; lean_object* v_j_1162_; lean_object* v_lowerBound_1163_; lean_object* v_upperBound_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___y_1169_; lean_object* v___y_1186_; lean_object* v___y_1187_; 
v_m_1158_ = lean_ctor_get(v_x_684_, 0);
lean_inc(v_m_1158_);
v_r_1159_ = lean_ctor_get(v_x_684_, 1);
lean_inc(v_r_1159_);
v_i_1160_ = lean_ctor_get(v_x_684_, 2);
lean_inc(v_i_1160_);
v_x_1161_ = lean_ctor_get(v_x_684_, 3);
lean_inc(v_x_1161_);
v_j_1162_ = lean_ctor_get(v_x_684_, 4);
lean_inc_ref(v_j_1162_);
lean_dec_ref_known(v_x_684_, 5);
v_lowerBound_1163_ = lean_ctor_get(v_s_682_, 0);
lean_inc(v_lowerBound_1163_);
v_upperBound_1164_ = lean_ctor_get(v_s_682_, 1);
lean_inc(v_upperBound_1164_);
lean_dec_ref(v_s_682_);
v___x_1165_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_683_);
lean_dec(v_x_683_);
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1167_ = lean_string_append(v___x_1165_, v___x_1166_);
if (lean_obj_tag(v_lowerBound_1163_) == 0)
{
if (lean_obj_tag(v_upperBound_1164_) == 0)
{
lean_object* v___x_1191_; 
v___x_1191_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1169_ = v___x_1191_;
goto v___jp_1168_;
}
else
{
lean_object* v_val_1192_; lean_object* v___x_1193_; lean_object* v___y_1195_; lean_object* v_intZero_1199_; uint8_t v_isNeg_1200_; 
v_val_1192_ = lean_ctor_get(v_upperBound_1164_, 0);
lean_inc(v_val_1192_);
lean_dec_ref_known(v_upperBound_1164_, 1);
v___x_1193_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1199_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1200_ = lean_int_dec_lt(v_val_1192_, v_intZero_1199_);
if (v_isNeg_1200_ == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1202_; 
v_a_1201_ = lean_nat_abs(v_val_1192_);
lean_dec(v_val_1192_);
v___x_1202_ = l_Nat_reprFast(v_a_1201_);
v___y_1195_ = v___x_1202_;
goto v___jp_1194_;
}
else
{
lean_object* v_abs_1203_; lean_object* v_one_1204_; lean_object* v_a_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_abs_1203_ = lean_nat_abs(v_val_1192_);
lean_dec(v_val_1192_);
v_one_1204_ = lean_unsigned_to_nat(1u);
v_a_1205_ = lean_nat_sub(v_abs_1203_, v_one_1204_);
lean_dec(v_abs_1203_);
v___x_1206_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1207_ = lean_nat_add(v_a_1205_, v_one_1204_);
lean_dec(v_a_1205_);
v___x_1208_ = l_Nat_reprFast(v___x_1207_);
v___x_1209_ = lean_string_append(v___x_1206_, v___x_1208_);
lean_dec_ref(v___x_1208_);
v___y_1195_ = v___x_1209_;
goto v___jp_1194_;
}
v___jp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_string_append(v___x_1193_, v___y_1195_);
lean_dec_ref(v___y_1195_);
v___x_1197_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1198_ = lean_string_append(v___x_1196_, v___x_1197_);
v___y_1169_ = v___x_1198_;
goto v___jp_1168_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1164_) == 0)
{
lean_object* v_val_1210_; lean_object* v___x_1211_; lean_object* v___y_1213_; lean_object* v_intZero_1217_; uint8_t v_isNeg_1218_; 
v_val_1210_ = lean_ctor_get(v_lowerBound_1163_, 0);
lean_inc(v_val_1210_);
lean_dec_ref_known(v_lowerBound_1163_, 1);
v___x_1211_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1217_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1218_ = lean_int_dec_lt(v_val_1210_, v_intZero_1217_);
if (v_isNeg_1218_ == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1220_; 
v_a_1219_ = lean_nat_abs(v_val_1210_);
lean_dec(v_val_1210_);
v___x_1220_ = l_Nat_reprFast(v_a_1219_);
v___y_1213_ = v___x_1220_;
goto v___jp_1212_;
}
else
{
lean_object* v_abs_1221_; lean_object* v_one_1222_; lean_object* v_a_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_abs_1221_ = lean_nat_abs(v_val_1210_);
lean_dec(v_val_1210_);
v_one_1222_ = lean_unsigned_to_nat(1u);
v_a_1223_ = lean_nat_sub(v_abs_1221_, v_one_1222_);
lean_dec(v_abs_1221_);
v___x_1224_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1225_ = lean_nat_add(v_a_1223_, v_one_1222_);
lean_dec(v_a_1223_);
v___x_1226_ = l_Nat_reprFast(v___x_1225_);
v___x_1227_ = lean_string_append(v___x_1224_, v___x_1226_);
lean_dec_ref(v___x_1226_);
v___y_1213_ = v___x_1227_;
goto v___jp_1212_;
}
v___jp_1212_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = lean_string_append(v___x_1211_, v___y_1213_);
lean_dec_ref(v___y_1213_);
v___x_1215_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1216_ = lean_string_append(v___x_1214_, v___x_1215_);
v___y_1169_ = v___x_1216_;
goto v___jp_1168_;
}
}
else
{
lean_object* v_val_1228_; lean_object* v_val_1229_; uint8_t v___x_1230_; 
v_val_1228_ = lean_ctor_get(v_lowerBound_1163_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v_lowerBound_1163_, 1);
v_val_1229_ = lean_ctor_get(v_upperBound_1164_, 0);
lean_inc(v_val_1229_);
lean_dec_ref_known(v_upperBound_1164_, 1);
v___x_1230_ = lean_int_dec_lt(v_val_1229_, v_val_1228_);
if (v___x_1230_ == 0)
{
uint8_t v___x_1231_; 
v___x_1231_ = lean_int_dec_eq(v_val_1228_, v_val_1229_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v___y_1234_; lean_object* v_intZero_1249_; uint8_t v_isNeg_1250_; 
v___x_1232_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1249_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1250_ = lean_int_dec_lt(v_val_1228_, v_intZero_1249_);
if (v_isNeg_1250_ == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1252_; 
v_a_1251_ = lean_nat_abs(v_val_1228_);
lean_dec(v_val_1228_);
v___x_1252_ = l_Nat_reprFast(v_a_1251_);
v___y_1234_ = v___x_1252_;
goto v___jp_1233_;
}
else
{
lean_object* v_abs_1253_; lean_object* v_one_1254_; lean_object* v_a_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_abs_1253_ = lean_nat_abs(v_val_1228_);
lean_dec(v_val_1228_);
v_one_1254_ = lean_unsigned_to_nat(1u);
v_a_1255_ = lean_nat_sub(v_abs_1253_, v_one_1254_);
lean_dec(v_abs_1253_);
v___x_1256_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1257_ = lean_nat_add(v_a_1255_, v_one_1254_);
lean_dec(v_a_1255_);
v___x_1258_ = l_Nat_reprFast(v___x_1257_);
v___x_1259_ = lean_string_append(v___x_1256_, v___x_1258_);
lean_dec_ref(v___x_1258_);
v___y_1234_ = v___x_1259_;
goto v___jp_1233_;
}
v___jp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v_intZero_1238_; uint8_t v_isNeg_1239_; 
v___x_1235_ = lean_string_append(v___x_1232_, v___y_1234_);
lean_dec_ref(v___y_1234_);
v___x_1236_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1237_ = lean_string_append(v___x_1235_, v___x_1236_);
v_intZero_1238_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1239_ = lean_int_dec_lt(v_val_1229_, v_intZero_1238_);
if (v_isNeg_1239_ == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1241_; 
v_a_1240_ = lean_nat_abs(v_val_1229_);
lean_dec(v_val_1229_);
v___x_1241_ = l_Nat_reprFast(v_a_1240_);
v___y_1186_ = v___x_1237_;
v___y_1187_ = v___x_1241_;
goto v___jp_1185_;
}
else
{
lean_object* v_abs_1242_; lean_object* v_one_1243_; lean_object* v_a_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_abs_1242_ = lean_nat_abs(v_val_1229_);
lean_dec(v_val_1229_);
v_one_1243_ = lean_unsigned_to_nat(1u);
v_a_1244_ = lean_nat_sub(v_abs_1242_, v_one_1243_);
lean_dec(v_abs_1242_);
v___x_1245_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1246_ = lean_nat_add(v_a_1244_, v_one_1243_);
lean_dec(v_a_1244_);
v___x_1247_ = l_Nat_reprFast(v___x_1246_);
v___x_1248_ = lean_string_append(v___x_1245_, v___x_1247_);
lean_dec_ref(v___x_1247_);
v___y_1186_ = v___x_1237_;
v___y_1187_ = v___x_1248_;
goto v___jp_1185_;
}
}
}
else
{
lean_object* v___x_1260_; lean_object* v___y_1262_; lean_object* v_intZero_1266_; uint8_t v_isNeg_1267_; 
lean_dec(v_val_1229_);
v___x_1260_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1266_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1267_ = lean_int_dec_lt(v_val_1228_, v_intZero_1266_);
if (v_isNeg_1267_ == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1269_; 
v_a_1268_ = lean_nat_abs(v_val_1228_);
lean_dec(v_val_1228_);
v___x_1269_ = l_Nat_reprFast(v_a_1268_);
v___y_1262_ = v___x_1269_;
goto v___jp_1261_;
}
else
{
lean_object* v_abs_1270_; lean_object* v_one_1271_; lean_object* v_a_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_abs_1270_ = lean_nat_abs(v_val_1228_);
lean_dec(v_val_1228_);
v_one_1271_ = lean_unsigned_to_nat(1u);
v_a_1272_ = lean_nat_sub(v_abs_1270_, v_one_1271_);
lean_dec(v_abs_1270_);
v___x_1273_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1274_ = lean_nat_add(v_a_1272_, v_one_1271_);
lean_dec(v_a_1272_);
v___x_1275_ = l_Nat_reprFast(v___x_1274_);
v___x_1276_ = lean_string_append(v___x_1273_, v___x_1275_);
lean_dec_ref(v___x_1275_);
v___y_1262_ = v___x_1276_;
goto v___jp_1261_;
}
v___jp_1261_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_string_append(v___x_1260_, v___y_1262_);
lean_dec_ref(v___y_1262_);
v___x_1264_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1265_ = lean_string_append(v___x_1263_, v___x_1264_);
v___y_1169_ = v___x_1265_;
goto v___jp_1168_;
}
}
}
else
{
lean_object* v___x_1277_; 
lean_dec(v_val_1229_);
lean_dec(v_val_1228_);
v___x_1277_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1169_ = v___x_1277_;
goto v___jp_1168_;
}
}
}
v___jp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1170_ = lean_string_append(v___x_1167_, v___y_1169_);
lean_dec_ref(v___y_1169_);
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__14));
v___x_1172_ = lean_string_append(v___x_1170_, v___x_1171_);
v___x_1173_ = l_Nat_reprFast(v_m_1158_);
v___x_1174_ = lean_string_append(v___x_1172_, v___x_1173_);
lean_dec_ref(v___x_1173_);
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__15));
v___x_1176_ = lean_string_append(v___x_1174_, v___x_1175_);
v___x_1177_ = l_Nat_reprFast(v_i_1160_);
v___x_1178_ = lean_string_append(v___x_1176_, v___x_1177_);
lean_dec_ref(v___x_1177_);
v___x_1179_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__16));
v___x_1180_ = lean_string_append(v___x_1178_, v___x_1179_);
v___x_1181_ = l_Lean_Omega_Constraint_exact(v_r_1159_);
v___x_1182_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v___x_1181_, v_x_1161_, v_j_1162_);
v___x_1183_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1182_);
v___x_1184_ = lean_string_append(v___x_1180_, v___x_1183_);
lean_dec_ref(v___x_1183_);
return v___x_1184_;
}
v___jp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = lean_string_append(v___y_1186_, v___y_1187_);
lean_dec_ref(v___y_1187_);
v___x_1189_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1190_ = lean_string_append(v___x_1188_, v___x_1189_);
v___y_1169_ = v___x_1190_;
goto v___jp_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_instToString(lean_object* v_s_1278_, lean_object* v_x_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Justification_toString), 3, 2);
lean_closure_set(v___x_1280_, 0, v_s_1278_);
lean_closure_set(v___x_1280_, 1, v_x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(lean_object* v_nilFn_1281_, lean_object* v_consFn_1282_, lean_object* v_x_1283_){
_start:
{
if (lean_obj_tag(v_x_1283_) == 0)
{
lean_dec_ref(v_consFn_1282_);
lean_inc_ref(v_nilFn_1281_);
return v_nilFn_1281_;
}
else
{
lean_object* v_head_1284_; lean_object* v_tail_1285_; lean_object* v___y_1287_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_head_1284_ = lean_ctor_get(v_x_1283_, 0);
v_tail_1285_ = lean_ctor_get(v_x_1283_, 1);
v___x_1290_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1291_ = lean_int_dec_le(v___x_1290_, v_head_1284_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1292_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1293_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1294_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1295_ = lean_int_neg(v_head_1284_);
v___x_1296_ = l_Int_toNat(v___x_1295_);
lean_dec(v___x_1295_);
v___x_1297_ = l_Lean_instToExprInt_mkNat(v___x_1296_);
v___x_1298_ = l_Lean_mkApp3(v___x_1292_, v___x_1293_, v___x_1294_, v___x_1297_);
v___y_1287_ = v___x_1298_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = l_Int_toNat(v_head_1284_);
v___x_1300_ = l_Lean_instToExprInt_mkNat(v___x_1299_);
v___y_1287_ = v___x_1300_;
goto v___jp_1286_;
}
v___jp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_inc_ref(v_consFn_1282_);
v___x_1288_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1281_, v_consFn_1282_, v_tail_1285_);
v___x_1289_ = l_Lean_mkAppB(v_consFn_1282_, v___y_1287_, v___x_1288_);
return v___x_1289_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0___boxed(lean_object* v_nilFn_1301_, lean_object* v_consFn_1302_, lean_object* v_x_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1301_, v_consFn_1302_, v_x_1303_);
lean_dec(v_x_1303_);
lean_dec_ref(v_nilFn_1301_);
return v_res_1304_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_box(0);
v___x_1311_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1));
v___x_1312_ = l_Lean_Expr_const___override(v___x_1311_, v___x_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof(lean_object* v_s_1313_, lean_object* v_x_1314_, lean_object* v_v_1315_, lean_object* v_prf_1316_){
_start:
{
lean_object* v___x_1317_; lean_object* v___y_1319_; lean_object* v_lowerBound_1324_; lean_object* v_upperBound_1325_; lean_object* v___x_1326_; lean_object* v_type_1327_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1335_; 
v___x_1317_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2);
v_lowerBound_1324_ = lean_ctor_get(v_s_1313_, 0);
v_upperBound_1325_ = lean_ctor_get(v_s_1313_, 1);
v___x_1326_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1327_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1324_) == 0)
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1335_ = v___x_1351_;
goto v___jp_1334_;
}
else
{
lean_object* v_val_1352_; lean_object* v___x_1353_; lean_object* v___y_1355_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_val_1352_ = lean_ctor_get(v_lowerBound_1324_, 0);
v___x_1353_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1357_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1358_ = lean_int_dec_le(v___x_1357_, v_val_1352_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1359_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1360_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1361_ = lean_int_neg(v_val_1352_);
v___x_1362_ = l_Int_toNat(v___x_1361_);
lean_dec(v___x_1361_);
v___x_1363_ = l_Lean_instToExprInt_mkNat(v___x_1362_);
v___x_1364_ = l_Lean_mkApp3(v___x_1359_, v_type_1327_, v___x_1360_, v___x_1363_);
v___y_1355_ = v___x_1364_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = l_Int_toNat(v_val_1352_);
v___x_1366_ = l_Lean_instToExprInt_mkNat(v___x_1365_);
v___y_1355_ = v___x_1366_;
goto v___jp_1354_;
}
v___jp_1354_:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_mkAppB(v___x_1353_, v_type_1327_, v___y_1355_);
v___y_1335_ = v___x_1356_;
goto v___jp_1334_;
}
}
v___jp_1318_:
{
lean_object* v_nil_1320_; lean_object* v_cons_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_nil_1320_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1321_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1322_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1320_, v_cons_1321_, v_x_1314_);
v___x_1323_ = l_Lean_mkApp4(v___x_1317_, v___y_1319_, v___x_1322_, v_v_1315_, v_prf_1316_);
return v___x_1323_;
}
v___jp_1328_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_inc_ref(v___y_1329_);
v___x_1332_ = l_Lean_mkAppB(v___y_1329_, v_type_1327_, v___y_1331_);
v___x_1333_ = l_Lean_Expr_app___override(v___y_1330_, v___x_1332_);
v___y_1319_ = v___x_1333_;
goto v___jp_1318_;
}
v___jp_1334_:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_Expr_app___override(v___x_1326_, v___y_1335_);
if (lean_obj_tag(v_upperBound_1325_) == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1338_ = l_Lean_Expr_app___override(v___x_1336_, v___x_1337_);
v___y_1319_ = v___x_1338_;
goto v___jp_1318_;
}
else
{
lean_object* v_val_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_val_1339_ = lean_ctor_get(v_upperBound_1325_, 0);
v___x_1340_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1341_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1342_ = lean_int_dec_le(v___x_1341_, v_val_1339_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1343_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1344_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1345_ = lean_int_neg(v_val_1339_);
v___x_1346_ = l_Int_toNat(v___x_1345_);
lean_dec(v___x_1345_);
v___x_1347_ = l_Lean_instToExprInt_mkNat(v___x_1346_);
v___x_1348_ = l_Lean_mkApp3(v___x_1343_, v_type_1327_, v___x_1344_, v___x_1347_);
v___y_1329_ = v___x_1340_;
v___y_1330_ = v___x_1336_;
v___y_1331_ = v___x_1348_;
goto v___jp_1328_;
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = l_Int_toNat(v_val_1339_);
v___x_1350_ = l_Lean_instToExprInt_mkNat(v___x_1349_);
v___y_1329_ = v___x_1340_;
v___y_1330_ = v___x_1336_;
v___y_1331_ = v___x_1350_;
goto v___jp_1328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___boxed(lean_object* v_s_1367_, lean_object* v_x_1368_, lean_object* v_v_1369_, lean_object* v_prf_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1367_, v_x_1368_, v_v_1369_, v_prf_1370_);
lean_dec(v_x_1368_);
lean_dec_ref(v_s_1367_);
return v_res_1371_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1));
v___x_1380_ = l_Lean_Expr_const___override(v___x_1379_, v___x_1378_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof(lean_object* v_s_1381_, lean_object* v_t_1382_, lean_object* v_x_1383_, lean_object* v_v_1384_, lean_object* v_ps_1385_, lean_object* v_pt_1386_){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1438_; lean_object* v_lowerBound_1456_; lean_object* v_upperBound_1457_; lean_object* v___x_1458_; lean_object* v_type_1459_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1467_; 
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2);
v_lowerBound_1456_ = lean_ctor_get(v_s_1381_, 0);
v_upperBound_1457_ = lean_ctor_get(v_s_1381_, 1);
v___x_1458_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1459_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1456_) == 0)
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1467_ = v___x_1483_;
goto v___jp_1466_;
}
else
{
lean_object* v_val_1484_; lean_object* v___x_1485_; lean_object* v___y_1487_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v_val_1484_ = lean_ctor_get(v_lowerBound_1456_, 0);
v___x_1485_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1489_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1490_ = lean_int_dec_le(v___x_1489_, v_val_1484_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1491_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1492_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1493_ = lean_int_neg(v_val_1484_);
v___x_1494_ = l_Int_toNat(v___x_1493_);
lean_dec(v___x_1493_);
v___x_1495_ = l_Lean_instToExprInt_mkNat(v___x_1494_);
v___x_1496_ = l_Lean_mkApp3(v___x_1491_, v_type_1459_, v___x_1492_, v___x_1495_);
v___y_1487_ = v___x_1496_;
goto v___jp_1486_;
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = l_Int_toNat(v_val_1484_);
v___x_1498_ = l_Lean_instToExprInt_mkNat(v___x_1497_);
v___y_1487_ = v___x_1498_;
goto v___jp_1486_;
}
v___jp_1486_:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_mkAppB(v___x_1485_, v_type_1459_, v___y_1487_);
v___y_1467_ = v___x_1488_;
goto v___jp_1466_;
}
}
v___jp_1389_:
{
lean_object* v_nil_1392_; lean_object* v_cons_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v_nil_1392_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1393_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1394_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1392_, v_cons_1393_, v_x_1383_);
v___x_1395_ = l_Lean_mkApp6(v___x_1388_, v___y_1390_, v___y_1391_, v___x_1394_, v_v_1384_, v_ps_1385_, v_pt_1386_);
return v___x_1395_;
}
v___jp_1396_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_inc_ref(v___y_1397_);
v___x_1402_ = l_Lean_mkAppB(v___y_1397_, v___y_1400_, v___y_1401_);
v___x_1403_ = l_Lean_Expr_app___override(v___y_1399_, v___x_1402_);
v___y_1390_ = v___y_1398_;
v___y_1391_ = v___x_1403_;
goto v___jp_1389_;
}
v___jp_1404_:
{
lean_object* v_upperBound_1410_; lean_object* v___x_1411_; 
v_upperBound_1410_ = lean_ctor_get(v_t_1382_, 1);
lean_inc_ref(v___y_1406_);
v___x_1411_ = l_Lean_Expr_app___override(v___y_1406_, v___y_1409_);
if (lean_obj_tag(v_upperBound_1410_) == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1413_ = l_Lean_Expr_app___override(v___x_1412_, v___y_1408_);
v___x_1414_ = l_Lean_Expr_app___override(v___x_1411_, v___x_1413_);
v___y_1390_ = v___y_1407_;
v___y_1391_ = v___x_1414_;
goto v___jp_1389_;
}
else
{
lean_object* v_val_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_val_1415_ = lean_ctor_get(v_upperBound_1410_, 0);
v___x_1416_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1417_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1418_ = lean_int_dec_le(v___x_1417_, v_val_1415_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1419_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1420_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1405_);
v___x_1421_ = l_Lean_Name_mkStr2(v___y_1405_, v___x_1420_);
v___x_1422_ = l_Lean_Expr_const___override(v___x_1421_, v___x_1387_);
v___x_1423_ = lean_int_neg(v_val_1415_);
v___x_1424_ = l_Int_toNat(v___x_1423_);
lean_dec(v___x_1423_);
v___x_1425_ = l_Lean_instToExprInt_mkNat(v___x_1424_);
lean_inc_ref(v___y_1408_);
v___x_1426_ = l_Lean_mkApp3(v___x_1419_, v___y_1408_, v___x_1422_, v___x_1425_);
v___y_1397_ = v___x_1416_;
v___y_1398_ = v___y_1407_;
v___y_1399_ = v___x_1411_;
v___y_1400_ = v___y_1408_;
v___y_1401_ = v___x_1426_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = l_Int_toNat(v_val_1415_);
v___x_1428_ = l_Lean_instToExprInt_mkNat(v___x_1427_);
v___y_1397_ = v___x_1416_;
v___y_1398_ = v___y_1407_;
v___y_1399_ = v___x_1411_;
v___y_1400_ = v___y_1408_;
v___y_1401_ = v___x_1428_;
goto v___jp_1396_;
}
}
}
v___jp_1429_:
{
lean_object* v___x_1436_; 
lean_inc_ref(v___y_1434_);
lean_inc_ref(v___y_1432_);
v___x_1436_ = l_Lean_mkAppB(v___y_1432_, v___y_1434_, v___y_1435_);
v___y_1405_ = v___y_1430_;
v___y_1406_ = v___y_1431_;
v___y_1407_ = v___y_1433_;
v___y_1408_ = v___y_1434_;
v___y_1409_ = v___x_1436_;
goto v___jp_1404_;
}
v___jp_1437_:
{
lean_object* v_lowerBound_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v_type_1442_; 
v_lowerBound_1439_ = lean_ctor_get(v_t_1382_, 0);
v___x_1440_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1441_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1442_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1439_) == 0)
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1405_ = v___x_1441_;
v___y_1406_ = v___x_1440_;
v___y_1407_ = v___y_1438_;
v___y_1408_ = v_type_1442_;
v___y_1409_ = v___x_1443_;
goto v___jp_1404_;
}
else
{
lean_object* v_val_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v_val_1444_ = lean_ctor_get(v_lowerBound_1439_, 0);
v___x_1445_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1446_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1447_ = lean_int_dec_le(v___x_1446_, v_val_1444_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1448_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1449_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1450_ = lean_int_neg(v_val_1444_);
v___x_1451_ = l_Int_toNat(v___x_1450_);
lean_dec(v___x_1450_);
v___x_1452_ = l_Lean_instToExprInt_mkNat(v___x_1451_);
v___x_1453_ = l_Lean_mkApp3(v___x_1448_, v_type_1442_, v___x_1449_, v___x_1452_);
v___y_1430_ = v___x_1441_;
v___y_1431_ = v___x_1440_;
v___y_1432_ = v___x_1445_;
v___y_1433_ = v___y_1438_;
v___y_1434_ = v_type_1442_;
v___y_1435_ = v___x_1453_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = l_Int_toNat(v_val_1444_);
v___x_1455_ = l_Lean_instToExprInt_mkNat(v___x_1454_);
v___y_1430_ = v___x_1441_;
v___y_1431_ = v___x_1440_;
v___y_1432_ = v___x_1445_;
v___y_1433_ = v___y_1438_;
v___y_1434_ = v_type_1442_;
v___y_1435_ = v___x_1455_;
goto v___jp_1429_;
}
}
}
v___jp_1460_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_inc_ref(v___y_1461_);
v___x_1464_ = l_Lean_mkAppB(v___y_1461_, v_type_1459_, v___y_1463_);
v___x_1465_ = l_Lean_Expr_app___override(v___y_1462_, v___x_1464_);
v___y_1438_ = v___x_1465_;
goto v___jp_1437_;
}
v___jp_1466_:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_Expr_app___override(v___x_1458_, v___y_1467_);
if (lean_obj_tag(v_upperBound_1457_) == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1470_ = l_Lean_Expr_app___override(v___x_1468_, v___x_1469_);
v___y_1438_ = v___x_1470_;
goto v___jp_1437_;
}
else
{
lean_object* v_val_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v_val_1471_ = lean_ctor_get(v_upperBound_1457_, 0);
v___x_1472_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1473_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1474_ = lean_int_dec_le(v___x_1473_, v_val_1471_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1475_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1476_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1477_ = lean_int_neg(v_val_1471_);
v___x_1478_ = l_Int_toNat(v___x_1477_);
lean_dec(v___x_1477_);
v___x_1479_ = l_Lean_instToExprInt_mkNat(v___x_1478_);
v___x_1480_ = l_Lean_mkApp3(v___x_1475_, v_type_1459_, v___x_1476_, v___x_1479_);
v___y_1461_ = v___x_1472_;
v___y_1462_ = v___x_1468_;
v___y_1463_ = v___x_1480_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = l_Int_toNat(v_val_1471_);
v___x_1482_ = l_Lean_instToExprInt_mkNat(v___x_1481_);
v___y_1461_ = v___x_1472_;
v___y_1462_ = v___x_1468_;
v___y_1463_ = v___x_1482_;
goto v___jp_1460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___boxed(lean_object* v_s_1499_, lean_object* v_t_1500_, lean_object* v_x_1501_, lean_object* v_v_1502_, lean_object* v_ps_1503_, lean_object* v_pt_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1499_, v_t_1500_, v_x_1501_, v_v_1502_, v_ps_1503_, v_pt_1504_);
lean_dec(v_x_1501_);
lean_dec_ref(v_t_1500_);
lean_dec_ref(v_s_1499_);
return v_res_1505_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = lean_box(0);
v___x_1512_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1));
v___x_1513_ = l_Lean_Expr_const___override(v___x_1512_, v___x_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof(lean_object* v_s_1514_, lean_object* v_t_1515_, lean_object* v_a_1516_, lean_object* v_x_1517_, lean_object* v_b_1518_, lean_object* v_y_1519_, lean_object* v_v_1520_, lean_object* v_px_1521_, lean_object* v_py_1522_){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1609_; lean_object* v_lowerBound_1627_; lean_object* v_upperBound_1628_; lean_object* v___x_1629_; lean_object* v_type_1630_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1638_; 
v___x_1523_ = lean_box(0);
v___x_1524_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2);
v_lowerBound_1627_ = lean_ctor_get(v_s_1514_, 0);
v_upperBound_1628_ = lean_ctor_get(v_s_1514_, 1);
v___x_1629_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1630_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1627_) == 0)
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1638_ = v___x_1654_;
goto v___jp_1637_;
}
else
{
lean_object* v_val_1655_; lean_object* v___x_1656_; lean_object* v___y_1658_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v_val_1655_ = lean_ctor_get(v_lowerBound_1627_, 0);
v___x_1656_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1660_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1661_ = lean_int_dec_le(v___x_1660_, v_val_1655_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1662_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1663_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1664_ = lean_int_neg(v_val_1655_);
v___x_1665_ = l_Int_toNat(v___x_1664_);
lean_dec(v___x_1664_);
v___x_1666_ = l_Lean_instToExprInt_mkNat(v___x_1665_);
v___x_1667_ = l_Lean_mkApp3(v___x_1662_, v_type_1630_, v___x_1663_, v___x_1666_);
v___y_1658_ = v___x_1667_;
goto v___jp_1657_;
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = l_Int_toNat(v_val_1655_);
v___x_1669_ = l_Lean_instToExprInt_mkNat(v___x_1668_);
v___y_1658_ = v___x_1669_;
goto v___jp_1657_;
}
v___jp_1657_:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_mkAppB(v___x_1656_, v_type_1630_, v___y_1658_);
v___y_1638_ = v___x_1659_;
goto v___jp_1637_;
}
}
v___jp_1525_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v___y_1529_, v___y_1530_, v_y_1519_);
v___x_1534_ = l_Lean_mkApp9(v___x_1524_, v___y_1531_, v___y_1526_, v___y_1528_, v___y_1527_, v___y_1532_, v___x_1533_, v_v_1520_, v_px_1521_, v_py_1522_);
return v___x_1534_;
}
v___jp_1535_:
{
lean_object* v_type_1539_; lean_object* v_nil_1540_; lean_object* v_cons_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v_type_1539_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_nil_1540_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1541_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1542_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1540_, v_cons_1541_, v_x_1517_);
v___x_1543_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1544_ = lean_int_dec_le(v___x_1543_, v_b_1518_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1545_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1546_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1547_ = lean_int_neg(v_b_1518_);
v___x_1548_ = l_Int_toNat(v___x_1547_);
lean_dec(v___x_1547_);
v___x_1549_ = l_Lean_instToExprInt_mkNat(v___x_1548_);
v___x_1550_ = l_Lean_mkApp3(v___x_1545_, v_type_1539_, v___x_1546_, v___x_1549_);
v___y_1526_ = v___y_1536_;
v___y_1527_ = v___x_1542_;
v___y_1528_ = v___y_1538_;
v___y_1529_ = v_nil_1540_;
v___y_1530_ = v_cons_1541_;
v___y_1531_ = v___y_1537_;
v___y_1532_ = v___x_1550_;
goto v___jp_1525_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = l_Int_toNat(v_b_1518_);
v___x_1552_ = l_Lean_instToExprInt_mkNat(v___x_1551_);
v___y_1526_ = v___y_1536_;
v___y_1527_ = v___x_1542_;
v___y_1528_ = v___y_1538_;
v___y_1529_ = v_nil_1540_;
v___y_1530_ = v_cons_1541_;
v___y_1531_ = v___y_1537_;
v___y_1532_ = v___x_1552_;
goto v___jp_1525_;
}
}
v___jp_1553_:
{
lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1556_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1557_ = lean_int_dec_le(v___x_1556_, v_a_1516_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1558_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1559_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1560_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1561_ = lean_int_neg(v_a_1516_);
v___x_1562_ = l_Int_toNat(v___x_1561_);
lean_dec(v___x_1561_);
v___x_1563_ = l_Lean_instToExprInt_mkNat(v___x_1562_);
v___x_1564_ = l_Lean_mkApp3(v___x_1558_, v___x_1559_, v___x_1560_, v___x_1563_);
v___y_1536_ = v___y_1555_;
v___y_1537_ = v___y_1554_;
v___y_1538_ = v___x_1564_;
goto v___jp_1535_;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = l_Int_toNat(v_a_1516_);
v___x_1566_ = l_Lean_instToExprInt_mkNat(v___x_1565_);
v___y_1536_ = v___y_1555_;
v___y_1537_ = v___y_1554_;
v___y_1538_ = v___x_1566_;
goto v___jp_1535_;
}
}
v___jp_1567_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_inc_ref(v___y_1571_);
v___x_1573_ = l_Lean_mkAppB(v___y_1571_, v___y_1569_, v___y_1572_);
v___x_1574_ = l_Lean_Expr_app___override(v___y_1568_, v___x_1573_);
v___y_1554_ = v___y_1570_;
v___y_1555_ = v___x_1574_;
goto v___jp_1553_;
}
v___jp_1575_:
{
lean_object* v_upperBound_1581_; lean_object* v___x_1582_; 
v_upperBound_1581_ = lean_ctor_get(v_t_1515_, 1);
lean_inc_ref(v___y_1576_);
v___x_1582_ = l_Lean_Expr_app___override(v___y_1576_, v___y_1580_);
if (lean_obj_tag(v_upperBound_1581_) == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1583_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1584_ = l_Lean_Expr_app___override(v___x_1583_, v___y_1577_);
v___x_1585_ = l_Lean_Expr_app___override(v___x_1582_, v___x_1584_);
v___y_1554_ = v___y_1579_;
v___y_1555_ = v___x_1585_;
goto v___jp_1553_;
}
else
{
lean_object* v_val_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v_val_1586_ = lean_ctor_get(v_upperBound_1581_, 0);
v___x_1587_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1588_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1589_ = lean_int_dec_le(v___x_1588_, v_val_1586_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1590_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1591_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1578_);
v___x_1592_ = l_Lean_Name_mkStr2(v___y_1578_, v___x_1591_);
v___x_1593_ = l_Lean_Expr_const___override(v___x_1592_, v___x_1523_);
v___x_1594_ = lean_int_neg(v_val_1586_);
v___x_1595_ = l_Int_toNat(v___x_1594_);
lean_dec(v___x_1594_);
v___x_1596_ = l_Lean_instToExprInt_mkNat(v___x_1595_);
lean_inc_ref(v___y_1577_);
v___x_1597_ = l_Lean_mkApp3(v___x_1590_, v___y_1577_, v___x_1593_, v___x_1596_);
v___y_1568_ = v___x_1582_;
v___y_1569_ = v___y_1577_;
v___y_1570_ = v___y_1579_;
v___y_1571_ = v___x_1587_;
v___y_1572_ = v___x_1597_;
goto v___jp_1567_;
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = l_Int_toNat(v_val_1586_);
v___x_1599_ = l_Lean_instToExprInt_mkNat(v___x_1598_);
v___y_1568_ = v___x_1582_;
v___y_1569_ = v___y_1577_;
v___y_1570_ = v___y_1579_;
v___y_1571_ = v___x_1587_;
v___y_1572_ = v___x_1599_;
goto v___jp_1567_;
}
}
}
v___jp_1600_:
{
lean_object* v___x_1607_; 
lean_inc_ref(v___y_1603_);
lean_inc_ref(v___y_1602_);
v___x_1607_ = l_Lean_mkAppB(v___y_1602_, v___y_1603_, v___y_1606_);
v___y_1576_ = v___y_1601_;
v___y_1577_ = v___y_1603_;
v___y_1578_ = v___y_1604_;
v___y_1579_ = v___y_1605_;
v___y_1580_ = v___x_1607_;
goto v___jp_1575_;
}
v___jp_1608_:
{
lean_object* v_lowerBound_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v_type_1613_; 
v_lowerBound_1610_ = lean_ctor_get(v_t_1515_, 0);
v___x_1611_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1612_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1613_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1610_) == 0)
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1576_ = v___x_1611_;
v___y_1577_ = v_type_1613_;
v___y_1578_ = v___x_1612_;
v___y_1579_ = v___y_1609_;
v___y_1580_ = v___x_1614_;
goto v___jp_1575_;
}
else
{
lean_object* v_val_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v_val_1615_ = lean_ctor_get(v_lowerBound_1610_, 0);
v___x_1616_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1617_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1618_ = lean_int_dec_le(v___x_1617_, v_val_1615_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1619_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1620_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1621_ = lean_int_neg(v_val_1615_);
v___x_1622_ = l_Int_toNat(v___x_1621_);
lean_dec(v___x_1621_);
v___x_1623_ = l_Lean_instToExprInt_mkNat(v___x_1622_);
v___x_1624_ = l_Lean_mkApp3(v___x_1619_, v_type_1613_, v___x_1620_, v___x_1623_);
v___y_1601_ = v___x_1611_;
v___y_1602_ = v___x_1616_;
v___y_1603_ = v_type_1613_;
v___y_1604_ = v___x_1612_;
v___y_1605_ = v___y_1609_;
v___y_1606_ = v___x_1624_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = l_Int_toNat(v_val_1615_);
v___x_1626_ = l_Lean_instToExprInt_mkNat(v___x_1625_);
v___y_1601_ = v___x_1611_;
v___y_1602_ = v___x_1616_;
v___y_1603_ = v_type_1613_;
v___y_1604_ = v___x_1612_;
v___y_1605_ = v___y_1609_;
v___y_1606_ = v___x_1626_;
goto v___jp_1600_;
}
}
}
v___jp_1631_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_inc_ref(v___y_1633_);
v___x_1635_ = l_Lean_mkAppB(v___y_1633_, v_type_1630_, v___y_1634_);
v___x_1636_ = l_Lean_Expr_app___override(v___y_1632_, v___x_1635_);
v___y_1609_ = v___x_1636_;
goto v___jp_1608_;
}
v___jp_1637_:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Expr_app___override(v___x_1629_, v___y_1638_);
if (lean_obj_tag(v_upperBound_1628_) == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1641_ = l_Lean_Expr_app___override(v___x_1639_, v___x_1640_);
v___y_1609_ = v___x_1641_;
goto v___jp_1608_;
}
else
{
lean_object* v_val_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v_val_1642_ = lean_ctor_get(v_upperBound_1628_, 0);
v___x_1643_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1644_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1645_ = lean_int_dec_le(v___x_1644_, v_val_1642_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1646_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1647_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1648_ = lean_int_neg(v_val_1642_);
v___x_1649_ = l_Int_toNat(v___x_1648_);
lean_dec(v___x_1648_);
v___x_1650_ = l_Lean_instToExprInt_mkNat(v___x_1649_);
v___x_1651_ = l_Lean_mkApp3(v___x_1646_, v_type_1630_, v___x_1647_, v___x_1650_);
v___y_1632_ = v___x_1639_;
v___y_1633_ = v___x_1643_;
v___y_1634_ = v___x_1651_;
goto v___jp_1631_;
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = l_Int_toNat(v_val_1642_);
v___x_1653_ = l_Lean_instToExprInt_mkNat(v___x_1652_);
v___y_1632_ = v___x_1639_;
v___y_1633_ = v___x_1643_;
v___y_1634_ = v___x_1653_;
goto v___jp_1631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___boxed(lean_object* v_s_1670_, lean_object* v_t_1671_, lean_object* v_a_1672_, lean_object* v_x_1673_, lean_object* v_b_1674_, lean_object* v_y_1675_, lean_object* v_v_1676_, lean_object* v_px_1677_, lean_object* v_py_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1670_, v_t_1671_, v_a_1672_, v_x_1673_, v_b_1674_, v_y_1675_, v_v_1676_, v_px_1677_, v_py_1678_);
lean_dec(v_y_1675_);
lean_dec(v_b_1674_);
lean_dec(v_x_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_t_1671_);
lean_dec_ref(v_s_1670_);
return v_res_1679_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_1686_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2));
v___x_1687_ = l_Lean_Expr_const___override(v___x_1686_, v___x_1685_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = lean_box(0);
v___x_1692_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5));
v___x_1693_ = l_Lean_Expr_const___override(v___x_1692_, v___x_1691_);
return v___x_1693_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = lean_box(0);
v___x_1698_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8));
v___x_1699_ = l_Lean_Expr_const___override(v___x_1698_, v___x_1697_);
return v___x_1699_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = lean_box(0);
v___x_1708_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12));
v___x_1709_ = l_Lean_Expr_const___override(v___x_1708_, v___x_1707_);
return v___x_1709_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = lean_box(0);
v___x_1717_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15));
v___x_1718_ = l_Lean_Expr_const___override(v___x_1717_, v___x_1716_);
return v___x_1718_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_box(0);
v___x_1725_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18));
v___x_1726_ = l_Lean_Expr_const___override(v___x_1725_, v___x_1724_);
return v___x_1726_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = lean_box(0);
v___x_1733_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21));
v___x_1734_ = l_Lean_Expr_const___override(v___x_1733_, v___x_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof(lean_object* v_m_1735_, lean_object* v_r_1736_, lean_object* v_i_1737_, lean_object* v_x_1738_, lean_object* v_v_1739_, lean_object* v_w_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_m_1746_; lean_object* v___y_1748_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v_m_1746_ = l_Lean_mkNatLit(v_m_1735_);
v___x_1776_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1777_ = lean_int_dec_le(v___x_1776_, v_r_1736_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1778_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1779_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1780_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1781_ = lean_int_neg(v_r_1736_);
v___x_1782_ = l_Int_toNat(v___x_1781_);
lean_dec(v___x_1781_);
v___x_1783_ = l_Lean_instToExprInt_mkNat(v___x_1782_);
v___x_1784_ = l_Lean_mkApp3(v___x_1778_, v___x_1779_, v___x_1780_, v___x_1783_);
v___y_1748_ = v___x_1784_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = l_Int_toNat(v_r_1736_);
v___x_1786_ = l_Lean_instToExprInt_mkNat(v___x_1785_);
v___y_1748_ = v___x_1786_;
goto v___jp_1747_;
}
v___jp_1747_:
{
lean_object* v_i_1749_; lean_object* v_nil_1750_; lean_object* v_cons_1751_; lean_object* v_x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v_i_1749_ = l_Lean_mkNatLit(v_i_1737_);
v_nil_1750_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1751_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v_x_1752_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1750_, v_cons_1751_, v_x_1738_);
v___x_1753_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3);
v___x_1754_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6);
v___x_1755_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9);
v___x_1756_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13);
lean_inc_ref(v_x_1752_);
v___x_1757_ = l_Lean_Expr_app___override(v___x_1756_, v_x_1752_);
lean_inc_ref(v_i_1749_);
v___x_1758_ = l_Lean_mkApp4(v___x_1753_, v___x_1754_, v___x_1755_, v___x_1757_, v_i_1749_);
v___x_1759_ = l_Lean_Meta_mkDecideProof(v___x_1758_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1759_, 1);
v___x_1761_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16);
lean_inc_ref(v_i_1749_);
lean_inc_ref_n(v_v_1739_, 2);
v___x_1762_ = l_Lean_mkAppB(v___x_1761_, v_v_1739_, v_i_1749_);
v___x_1763_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc_ref(v_x_1752_);
lean_inc_ref(v_m_1746_);
v___x_1764_ = l_Lean_mkApp3(v___x_1763_, v_m_1746_, v_x_1752_, v_v_1739_);
v___x_1765_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v___x_1762_, v___x_1764_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1775_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1775_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1775_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1770_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22);
v___x_1771_ = l_Lean_mkApp8(v___x_1770_, v_m_1746_, v___y_1748_, v_i_1749_, v_x_1752_, v_v_1739_, v_a_1760_, v_a_1766_, v_w_1740_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1771_);
v___x_1773_ = v___x_1768_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
else
{
lean_dec(v_a_1760_);
lean_dec_ref(v_x_1752_);
lean_dec_ref(v_i_1749_);
lean_dec_ref(v___y_1748_);
lean_dec_ref(v_m_1746_);
lean_dec_ref(v_w_1740_);
lean_dec_ref(v_v_1739_);
return v___x_1765_;
}
}
else
{
lean_dec_ref(v_x_1752_);
lean_dec_ref(v_i_1749_);
lean_dec_ref(v___y_1748_);
lean_dec_ref(v_m_1746_);
lean_dec_ref(v_w_1740_);
lean_dec_ref(v_v_1739_);
return v___x_1759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___boxed(lean_object* v_m_1787_, lean_object* v_r_1788_, lean_object* v_i_1789_, lean_object* v_x_1790_, lean_object* v_v_1791_, lean_object* v_w_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1787_, v_r_1788_, v_i_1789_, v_x_1790_, v_v_1791_, v_w_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_x_1790_);
lean_dec(v_r_1788_);
return v_res_1798_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0(void){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_instMonadEIO___redArg();
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0);
v___x_1801_ = l_StateRefT_x27_instMonad___redArg(v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(lean_object* v_c_1806_, lean_object* v_v_1807_, lean_object* v_assumptions_1808_, lean_object* v_x_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, uint8_t v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v___x_1820_; lean_object* v_toApplicative_1821_; lean_object* v_toFunctor_1822_; lean_object* v_toSeq_1823_; lean_object* v_toSeqLeft_1824_; lean_object* v_toSeqRight_1825_; lean_object* v___f_1826_; lean_object* v___f_1827_; lean_object* v___f_1828_; lean_object* v___f_1829_; lean_object* v___x_1830_; lean_object* v___f_1831_; lean_object* v___f_1832_; lean_object* v___f_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v_toApplicative_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1932_; 
v___x_1820_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1);
v_toApplicative_1821_ = lean_ctor_get(v___x_1820_, 0);
v_toFunctor_1822_ = lean_ctor_get(v_toApplicative_1821_, 0);
v_toSeq_1823_ = lean_ctor_get(v_toApplicative_1821_, 2);
v_toSeqLeft_1824_ = lean_ctor_get(v_toApplicative_1821_, 3);
v_toSeqRight_1825_ = lean_ctor_get(v_toApplicative_1821_, 4);
v___f_1826_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2));
v___f_1827_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1822_, 2);
v___f_1828_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1828_, 0, v_toFunctor_1822_);
v___f_1829_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1829_, 0, v_toFunctor_1822_);
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___f_1828_);
lean_ctor_set(v___x_1830_, 1, v___f_1829_);
lean_inc(v_toSeqRight_1825_);
v___f_1831_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1831_, 0, v_toSeqRight_1825_);
lean_inc(v_toSeqLeft_1824_);
v___f_1832_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1832_, 0, v_toSeqLeft_1824_);
lean_inc(v_toSeq_1823_);
v___f_1833_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1833_, 0, v_toSeq_1823_);
v___x_1834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1830_);
lean_ctor_set(v___x_1834_, 1, v___f_1826_);
lean_ctor_set(v___x_1834_, 2, v___f_1833_);
lean_ctor_set(v___x_1834_, 3, v___f_1832_);
lean_ctor_set(v___x_1834_, 4, v___f_1831_);
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
lean_ctor_set(v___x_1835_, 1, v___f_1827_);
v___x_1836_ = l_StateRefT_x27_instMonad___redArg(v___x_1835_);
v_toApplicative_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v___x_1836_, 1);
lean_dec(v_unused_1933_);
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1932_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_toApplicative_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1932_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v_toFunctor_1841_; lean_object* v_toSeq_1842_; lean_object* v_toSeqLeft_1843_; lean_object* v_toSeqRight_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1930_; 
v_toFunctor_1841_ = lean_ctor_get(v_toApplicative_1837_, 0);
v_toSeq_1842_ = lean_ctor_get(v_toApplicative_1837_, 2);
v_toSeqLeft_1843_ = lean_ctor_get(v_toApplicative_1837_, 3);
v_toSeqRight_1844_ = lean_ctor_get(v_toApplicative_1837_, 4);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_toApplicative_1837_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v_toApplicative_1837_, 1);
lean_dec(v_unused_1931_);
v___x_1846_ = v_toApplicative_1837_;
v_isShared_1847_ = v_isSharedCheck_1930_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_toSeqRight_1844_);
lean_inc(v_toSeqLeft_1843_);
lean_inc(v_toSeq_1842_);
lean_inc(v_toFunctor_1841_);
lean_dec(v_toApplicative_1837_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1930_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___f_1848_; lean_object* v___f_1849_; lean_object* v___f_1850_; lean_object* v___f_1851_; lean_object* v___x_1852_; lean_object* v___f_1853_; lean_object* v___f_1854_; lean_object* v___f_1855_; lean_object* v___x_1857_; 
v___f_1848_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4));
v___f_1849_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5));
lean_inc_ref(v_toFunctor_1841_);
v___f_1850_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1850_, 0, v_toFunctor_1841_);
v___f_1851_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1851_, 0, v_toFunctor_1841_);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___f_1850_);
lean_ctor_set(v___x_1852_, 1, v___f_1851_);
v___f_1853_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1853_, 0, v_toSeqRight_1844_);
v___f_1854_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1854_, 0, v_toSeqLeft_1843_);
v___f_1855_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1855_, 0, v_toSeq_1842_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 4, v___f_1853_);
lean_ctor_set(v___x_1846_, 3, v___f_1854_);
lean_ctor_set(v___x_1846_, 2, v___f_1855_);
lean_ctor_set(v___x_1846_, 1, v___f_1848_);
lean_ctor_set(v___x_1846_, 0, v___x_1852_);
v___x_1857_ = v___x_1846_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___f_1848_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v___f_1855_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v___f_1854_);
lean_ctor_set(v_reuseFailAlloc_1929_, 4, v___f_1853_);
v___x_1857_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1859_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 1, v___f_1849_);
lean_ctor_set(v___x_1839_, 0, v___x_1857_);
v___x_1859_ = v___x_1839_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1857_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v___f_1849_);
v___x_1859_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1860_ = l_StateRefT_x27_instMonad___redArg(v___x_1859_);
v___x_1861_ = l_ReaderT_instMonad___redArg(v___x_1860_);
v___x_1862_ = l_ReaderT_instMonad___redArg(v___x_1861_);
v___x_1863_ = l_StateRefT_x27_instMonad___redArg(v___x_1862_);
v___x_1864_ = l_StateRefT_x27_instMonad___redArg(v___x_1863_);
switch(lean_obj_tag(v_x_1809_))
{
case 0:
{
lean_object* v_i_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_3776__overap_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
lean_dec_ref(v_v_1807_);
v_i_1865_ = lean_ctor_get(v_x_1809_, 2);
lean_inc(v_i_1865_);
lean_dec_ref_known(v_x_1809_, 3);
v___x_1866_ = l_Lean_instInhabitedExpr;
v___x_1867_ = l_instInhabitedOfMonad___redArg(v___x_1864_, v___x_1866_);
v___x_3776__overap_1868_ = lean_array_get(v___x_1867_, v_assumptions_1808_, v_i_1865_);
lean_dec(v_i_1865_);
lean_dec(v___x_1867_);
v___x_1869_ = lean_box(v_a_1813_);
lean_inc(v_a_1818_);
lean_inc_ref(v_a_1817_);
lean_inc(v_a_1816_);
lean_inc_ref(v_a_1815_);
lean_inc(v_a_1814_);
lean_inc_ref(v_a_1812_);
lean_inc(v_a_1811_);
lean_inc(v_a_1810_);
v___x_1870_ = lean_apply_10(v___x_3776__overap_1868_, v_a_1810_, v_a_1811_, v_a_1812_, v___x_1869_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, lean_box(0));
return v___x_1870_;
}
case 1:
{
lean_object* v_s_1871_; lean_object* v_c_1872_; lean_object* v_j_1873_; lean_object* v___x_1874_; 
lean_dec_ref(v___x_1864_);
v_s_1871_ = lean_ctor_get(v_x_1809_, 0);
lean_inc_ref(v_s_1871_);
v_c_1872_ = lean_ctor_get(v_x_1809_, 1);
lean_inc(v_c_1872_);
v_j_1873_ = lean_ctor_get(v_x_1809_, 2);
lean_inc_ref(v_j_1873_);
lean_dec_ref_known(v_x_1809_, 3);
lean_inc_ref(v_v_1807_);
v___x_1874_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1872_, v_v_1807_, v_assumptions_1808_, v_j_1873_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1883_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1883_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1883_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1879_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1871_, v_c_1872_, v_v_1807_, v_a_1875_);
lean_dec(v_c_1872_);
lean_dec_ref(v_s_1871_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1879_);
v___x_1881_ = v___x_1877_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
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
lean_dec(v_c_1872_);
lean_dec_ref(v_s_1871_);
lean_dec_ref(v_v_1807_);
return v___x_1874_;
}
}
case 2:
{
lean_object* v_s_1884_; lean_object* v_t_1885_; lean_object* v_j_1886_; lean_object* v_k_1887_; lean_object* v___x_1888_; 
lean_dec_ref(v___x_1864_);
v_s_1884_ = lean_ctor_get(v_x_1809_, 0);
lean_inc_ref(v_s_1884_);
v_t_1885_ = lean_ctor_get(v_x_1809_, 1);
lean_inc_ref(v_t_1885_);
v_j_1886_ = lean_ctor_get(v_x_1809_, 3);
lean_inc_ref(v_j_1886_);
v_k_1887_ = lean_ctor_get(v_x_1809_, 4);
lean_inc_ref(v_k_1887_);
lean_dec_ref_known(v_x_1809_, 5);
lean_inc_ref(v_v_1807_);
v___x_1888_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1806_, v_v_1807_, v_assumptions_1808_, v_j_1886_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1890_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
lean_inc_ref(v_v_1807_);
v___x_1890_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1806_, v_v_1807_, v_assumptions_1808_, v_k_1887_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1899_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1895_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1884_, v_t_1885_, v_c_1806_, v_v_1807_, v_a_1889_, v_a_1891_);
lean_dec_ref(v_t_1885_);
lean_dec_ref(v_s_1884_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1895_);
v___x_1897_ = v___x_1893_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
else
{
lean_dec(v_a_1889_);
lean_dec_ref(v_t_1885_);
lean_dec_ref(v_s_1884_);
lean_dec_ref(v_v_1807_);
return v___x_1890_;
}
}
else
{
lean_dec_ref(v_k_1887_);
lean_dec_ref(v_t_1885_);
lean_dec_ref(v_s_1884_);
lean_dec_ref(v_v_1807_);
return v___x_1888_;
}
}
case 3:
{
lean_object* v_s_1900_; lean_object* v_t_1901_; lean_object* v_x_1902_; lean_object* v_y_1903_; lean_object* v_a_1904_; lean_object* v_j_1905_; lean_object* v_b_1906_; lean_object* v_k_1907_; lean_object* v___x_1908_; 
lean_dec_ref(v___x_1864_);
v_s_1900_ = lean_ctor_get(v_x_1809_, 0);
lean_inc_ref(v_s_1900_);
v_t_1901_ = lean_ctor_get(v_x_1809_, 1);
lean_inc_ref(v_t_1901_);
v_x_1902_ = lean_ctor_get(v_x_1809_, 2);
lean_inc(v_x_1902_);
v_y_1903_ = lean_ctor_get(v_x_1809_, 3);
lean_inc(v_y_1903_);
v_a_1904_ = lean_ctor_get(v_x_1809_, 4);
lean_inc(v_a_1904_);
v_j_1905_ = lean_ctor_get(v_x_1809_, 5);
lean_inc_ref(v_j_1905_);
v_b_1906_ = lean_ctor_get(v_x_1809_, 6);
lean_inc(v_b_1906_);
v_k_1907_ = lean_ctor_get(v_x_1809_, 7);
lean_inc_ref(v_k_1907_);
lean_dec_ref_known(v_x_1809_, 8);
lean_inc_ref(v_v_1807_);
v___x_1908_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1902_, v_v_1807_, v_assumptions_1808_, v_j_1905_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1910_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
lean_inc_ref(v_v_1807_);
v___x_1910_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_y_1903_, v_v_1807_, v_assumptions_1808_, v_k_1907_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1919_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1919_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1919_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; lean_object* v___x_1917_; 
v___x_1915_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1900_, v_t_1901_, v_a_1904_, v_x_1902_, v_b_1906_, v_y_1903_, v_v_1807_, v_a_1909_, v_a_1911_);
lean_dec(v_y_1903_);
lean_dec(v_b_1906_);
lean_dec(v_x_1902_);
lean_dec(v_a_1904_);
lean_dec_ref(v_t_1901_);
lean_dec_ref(v_s_1900_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_1915_);
v___x_1917_ = v___x_1913_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
else
{
lean_dec(v_a_1909_);
lean_dec(v_b_1906_);
lean_dec(v_a_1904_);
lean_dec(v_y_1903_);
lean_dec(v_x_1902_);
lean_dec_ref(v_t_1901_);
lean_dec_ref(v_s_1900_);
lean_dec_ref(v_v_1807_);
return v___x_1910_;
}
}
else
{
lean_dec_ref(v_k_1907_);
lean_dec(v_b_1906_);
lean_dec(v_a_1904_);
lean_dec(v_y_1903_);
lean_dec(v_x_1902_);
lean_dec_ref(v_t_1901_);
lean_dec_ref(v_s_1900_);
lean_dec_ref(v_v_1807_);
return v___x_1908_;
}
}
default: 
{
lean_object* v_m_1920_; lean_object* v_r_1921_; lean_object* v_i_1922_; lean_object* v_x_1923_; lean_object* v_j_1924_; lean_object* v___x_1925_; 
lean_dec_ref(v___x_1864_);
v_m_1920_ = lean_ctor_get(v_x_1809_, 0);
lean_inc(v_m_1920_);
v_r_1921_ = lean_ctor_get(v_x_1809_, 1);
lean_inc(v_r_1921_);
v_i_1922_ = lean_ctor_get(v_x_1809_, 2);
lean_inc(v_i_1922_);
v_x_1923_ = lean_ctor_get(v_x_1809_, 3);
lean_inc(v_x_1923_);
v_j_1924_ = lean_ctor_get(v_x_1809_, 4);
lean_inc_ref(v_j_1924_);
lean_dec_ref_known(v_x_1809_, 5);
lean_inc_ref(v_v_1807_);
v___x_1925_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1923_, v_v_1807_, v_assumptions_1808_, v_j_1924_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1927_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1920_, v_r_1921_, v_i_1922_, v_x_1923_, v_v_1807_, v_a_1926_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
lean_dec(v_x_1923_);
lean_dec(v_r_1921_);
return v___x_1927_;
}
else
{
lean_dec(v_x_1923_);
lean_dec(v_i_1922_);
lean_dec(v_r_1921_);
lean_dec(v_m_1920_);
lean_dec_ref(v_v_1807_);
return v___x_1925_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___boxed(lean_object* v_c_1934_, lean_object* v_v_1935_, lean_object* v_assumptions_1936_, lean_object* v_x_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
uint8_t v_a_boxed_1948_; lean_object* v_res_1949_; 
v_a_boxed_1948_ = lean_unbox(v_a_1941_);
v_res_1949_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1934_, v_v_1935_, v_assumptions_1936_, v_x_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_boxed_1948_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec_ref(v_assumptions_1936_);
lean_dec(v_c_1934_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof(lean_object* v_s_1950_, lean_object* v_c_1951_, lean_object* v_v_1952_, lean_object* v_assumptions_1953_, lean_object* v_x_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, uint8_t v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1951_, v_v_1952_, v_assumptions_1953_, v_x_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___boxed(lean_object* v_s_1966_, lean_object* v_c_1967_, lean_object* v_v_1968_, lean_object* v_assumptions_1969_, lean_object* v_x_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
uint8_t v_a_boxed_1981_; lean_object* v_res_1982_; 
v_a_boxed_1981_ = lean_unbox(v_a_1974_);
v_res_1982_ = l_Lean_Elab_Tactic_Omega_Justification_proof(v_s_1966_, v_c_1967_, v_v_1968_, v_assumptions_1969_, v_x_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_boxed_1981_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_assumptions_1969_);
lean_dec(v_c_1967_);
lean_dec_ref(v_s_1966_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_instToString___lam__0(lean_object* v_f_1983_){
_start:
{
lean_object* v_coeffs_1984_; lean_object* v_constraint_1985_; lean_object* v_justification_1986_; lean_object* v___x_1987_; 
v_coeffs_1984_ = lean_ctor_get(v_f_1983_, 0);
lean_inc(v_coeffs_1984_);
v_constraint_1985_ = lean_ctor_get(v_f_1983_, 1);
lean_inc_ref(v_constraint_1985_);
v_justification_1986_ = lean_ctor_get(v_f_1983_, 2);
lean_inc_ref(v_justification_1986_);
lean_dec_ref(v_f_1983_);
v___x_1987_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_1985_, v_coeffs_1984_, v_justification_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_tidy(lean_object* v_f_1990_){
_start:
{
lean_object* v_coeffs_1991_; lean_object* v_constraint_1992_; lean_object* v_justification_1993_; lean_object* v___x_1994_; 
v_coeffs_1991_ = lean_ctor_get(v_f_1990_, 0);
v_constraint_1992_ = lean_ctor_get(v_f_1990_, 1);
v_justification_1993_ = lean_ctor_get(v_f_1990_, 2);
lean_inc_ref(v_justification_1993_);
lean_inc(v_coeffs_1991_);
lean_inc_ref(v_constraint_1992_);
v___x_1994_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(v_constraint_1992_, v_coeffs_1991_, v_justification_1993_);
if (lean_obj_tag(v___x_1994_) == 0)
{
return v_f_1990_;
}
else
{
lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2006_; 
v_isSharedCheck_2006_ = !lean_is_exclusive(v_f_1990_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; lean_object* v_unused_2008_; lean_object* v_unused_2009_; 
v_unused_2007_ = lean_ctor_get(v_f_1990_, 2);
lean_dec(v_unused_2007_);
v_unused_2008_ = lean_ctor_get(v_f_1990_, 1);
lean_dec(v_unused_2008_);
v_unused_2009_ = lean_ctor_get(v_f_1990_, 0);
lean_dec(v_unused_2009_);
v___x_1996_ = v_f_1990_;
v_isShared_1997_ = v_isSharedCheck_2006_;
goto v_resetjp_1995_;
}
else
{
lean_dec(v_f_1990_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2006_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_val_1998_; lean_object* v_snd_1999_; lean_object* v_fst_2000_; lean_object* v_fst_2001_; lean_object* v_snd_2002_; lean_object* v___x_2004_; 
v_val_1998_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v___x_1994_, 1);
v_snd_1999_ = lean_ctor_get(v_val_1998_, 1);
lean_inc(v_snd_1999_);
v_fst_2000_ = lean_ctor_get(v_val_1998_, 0);
lean_inc(v_fst_2000_);
lean_dec(v_val_1998_);
v_fst_2001_ = lean_ctor_get(v_snd_1999_, 0);
lean_inc(v_fst_2001_);
v_snd_2002_ = lean_ctor_get(v_snd_1999_, 1);
lean_inc(v_snd_2002_);
lean_dec(v_snd_1999_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 2, v_snd_2002_);
lean_ctor_set(v___x_1996_, 1, v_fst_2000_);
lean_ctor_set(v___x_1996_, 0, v_fst_2001_);
v___x_2004_ = v___x_1996_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_fst_2001_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_fst_2000_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_snd_2002_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_combo(lean_object* v_a_2010_, lean_object* v_f_2011_, lean_object* v_b_2012_, lean_object* v_g_2013_){
_start:
{
lean_object* v_coeffs_2014_; lean_object* v_constraint_2015_; lean_object* v_justification_2016_; lean_object* v_coeffs_2017_; lean_object* v_constraint_2018_; lean_object* v_justification_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2029_; 
v_coeffs_2014_ = lean_ctor_get(v_f_2011_, 0);
lean_inc(v_coeffs_2014_);
v_constraint_2015_ = lean_ctor_get(v_f_2011_, 1);
lean_inc_ref(v_constraint_2015_);
v_justification_2016_ = lean_ctor_get(v_f_2011_, 2);
lean_inc_ref(v_justification_2016_);
lean_dec_ref(v_f_2011_);
v_coeffs_2017_ = lean_ctor_get(v_g_2013_, 0);
v_constraint_2018_ = lean_ctor_get(v_g_2013_, 1);
v_justification_2019_ = lean_ctor_get(v_g_2013_, 2);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_g_2013_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2021_ = v_g_2013_;
v_isShared_2022_ = v_isSharedCheck_2029_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_justification_2019_);
lean_inc(v_constraint_2018_);
lean_inc(v_coeffs_2017_);
lean_dec(v_g_2013_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2029_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
lean_inc(v_coeffs_2017_);
lean_inc(v_coeffs_2014_);
v___x_2023_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_2010_, v_b_2012_, v_coeffs_2014_, v_coeffs_2017_);
lean_inc_ref(v_constraint_2018_);
lean_inc(v_b_2012_);
lean_inc_ref(v_constraint_2015_);
lean_inc(v_a_2010_);
v___x_2024_ = l_Lean_Omega_Constraint_combo(v_a_2010_, v_constraint_2015_, v_b_2012_, v_constraint_2018_);
v___x_2025_ = lean_alloc_ctor(3, 8, 0);
lean_ctor_set(v___x_2025_, 0, v_constraint_2015_);
lean_ctor_set(v___x_2025_, 1, v_constraint_2018_);
lean_ctor_set(v___x_2025_, 2, v_coeffs_2014_);
lean_ctor_set(v___x_2025_, 3, v_coeffs_2017_);
lean_ctor_set(v___x_2025_, 4, v_a_2010_);
lean_ctor_set(v___x_2025_, 5, v_justification_2016_);
lean_ctor_set(v___x_2025_, 6, v_b_2012_);
lean_ctor_set(v___x_2025_, 7, v_justification_2019_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 2, v___x_2025_);
lean_ctor_set(v___x_2021_, 1, v___x_2024_);
lean_ctor_set(v___x_2021_, 0, v___x_2023_);
v___x_2027_ = v___x_2021_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__10));
v___x_2056_ = l_Lean_mkAtom(v___x_2055_);
return v___x_2056_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11);
v___x_2058_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2059_ = lean_array_push(v___x_2058_, v___x_2057_);
return v___x_2059_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2060_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12);
v___x_2061_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9));
v___x_2062_ = lean_box(2);
v___x_2063_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v___x_2061_);
lean_ctor_set(v___x_2063_, 2, v___x_2060_);
return v___x_2063_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13);
v___x_2065_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2066_ = lean_array_push(v___x_2065_, v___x_2064_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2067_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14);
v___x_2068_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7));
v___x_2069_ = lean_box(2);
v___x_2070_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v___x_2068_);
lean_ctor_set(v___x_2070_, 2, v___x_2067_);
return v___x_2070_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15);
v___x_2072_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2073_ = lean_array_push(v___x_2072_, v___x_2071_);
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2074_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16);
v___x_2075_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5));
v___x_2076_ = lean_box(2);
v___x_2077_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v___x_2075_);
lean_ctor_set(v___x_2077_, 2, v___x_2074_);
return v___x_2077_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17);
v___x_2079_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2080_ = lean_array_push(v___x_2079_, v___x_2078_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2081_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18);
v___x_2082_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2));
v___x_2083_ = lean_box(2);
v___x_2084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___x_2082_);
lean_ctor_set(v___x_2084_, 2, v___x_2081_);
return v___x_2084_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam(void){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19);
return v___x_2085_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_isEmpty(lean_object* v_p_2086_){
_start:
{
lean_object* v_constraints_2087_; lean_object* v_size_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v_constraints_2087_ = lean_ctor_get(v_p_2086_, 2);
v_size_2088_ = lean_ctor_get(v_constraints_2087_, 0);
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = lean_nat_dec_eq(v_size_2088_, v___x_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_isEmpty___boxed(lean_object* v_p_2091_){
_start:
{
uint8_t v_res_2092_; lean_object* v_r_2093_; 
v_res_2092_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2091_);
lean_dec_ref(v_p_2091_);
v_r_2093_ = lean_box(v_res_2092_);
return v_r_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object* v_a_2094_, lean_object* v_b_2095_, lean_object* v_d_2096_){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v_a_2094_);
lean_ctor_set(v___x_2097_, 1, v_b_2095_);
v___x_2098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v_d_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object* v___x_2099_, lean_object* v_x_2100_){
_start:
{
lean_object* v_snd_2101_; lean_object* v_constraint_2102_; lean_object* v_fst_2103_; lean_object* v_lowerBound_2104_; lean_object* v_upperBound_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___y_2110_; lean_object* v___y_2111_; 
v_snd_2101_ = lean_ctor_get(v_x_2100_, 1);
v_constraint_2102_ = lean_ctor_get(v_snd_2101_, 1);
lean_inc_ref(v_constraint_2102_);
v_fst_2103_ = lean_ctor_get(v_x_2100_, 0);
lean_inc(v_fst_2103_);
lean_dec_ref(v_x_2100_);
v_lowerBound_2104_ = lean_ctor_get(v_constraint_2102_, 0);
lean_inc(v_lowerBound_2104_);
v_upperBound_2105_ = lean_ctor_get(v_constraint_2102_, 1);
lean_inc(v_upperBound_2105_);
lean_dec_ref(v_constraint_2102_);
v___x_2106_ = l_List_toString___redArg(v___x_2099_, v_fst_2103_);
v___x_2107_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_2108_ = lean_string_append(v___x_2106_, v___x_2107_);
if (lean_obj_tag(v_lowerBound_2104_) == 0)
{
if (lean_obj_tag(v_upperBound_2105_) == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_2117_ = lean_string_append(v___x_2108_, v___x_2116_);
return v___x_2117_;
}
else
{
lean_object* v_val_2118_; lean_object* v___x_2119_; lean_object* v___y_2121_; lean_object* v_intZero_2126_; uint8_t v_isNeg_2127_; 
v_val_2118_ = lean_ctor_get(v_upperBound_2105_, 0);
lean_inc(v_val_2118_);
lean_dec_ref_known(v_upperBound_2105_, 1);
v___x_2119_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_2126_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2127_ = lean_int_dec_lt(v_val_2118_, v_intZero_2126_);
if (v_isNeg_2127_ == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; 
v_a_2128_ = lean_nat_abs(v_val_2118_);
lean_dec(v_val_2118_);
v___x_2129_ = l_Nat_reprFast(v_a_2128_);
v___y_2121_ = v___x_2129_;
goto v___jp_2120_;
}
else
{
lean_object* v_abs_2130_; lean_object* v_one_2131_; lean_object* v_a_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v_abs_2130_ = lean_nat_abs(v_val_2118_);
lean_dec(v_val_2118_);
v_one_2131_ = lean_unsigned_to_nat(1u);
v_a_2132_ = lean_nat_sub(v_abs_2130_, v_one_2131_);
lean_dec(v_abs_2130_);
v___x_2133_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2134_ = lean_nat_add(v_a_2132_, v_one_2131_);
lean_dec(v_a_2132_);
v___x_2135_ = l_Nat_reprFast(v___x_2134_);
v___x_2136_ = lean_string_append(v___x_2133_, v___x_2135_);
lean_dec_ref(v___x_2135_);
v___y_2121_ = v___x_2136_;
goto v___jp_2120_;
}
v___jp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2122_ = lean_string_append(v___x_2119_, v___y_2121_);
lean_dec_ref(v___y_2121_);
v___x_2123_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2124_ = lean_string_append(v___x_2122_, v___x_2123_);
v___x_2125_ = lean_string_append(v___x_2108_, v___x_2124_);
lean_dec_ref(v___x_2124_);
return v___x_2125_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_2105_) == 0)
{
lean_object* v_val_2137_; lean_object* v___x_2138_; lean_object* v___y_2140_; lean_object* v_intZero_2145_; uint8_t v_isNeg_2146_; 
v_val_2137_ = lean_ctor_get(v_lowerBound_2104_, 0);
lean_inc(v_val_2137_);
lean_dec_ref_known(v_lowerBound_2104_, 1);
v___x_2138_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2145_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2146_ = lean_int_dec_lt(v_val_2137_, v_intZero_2145_);
if (v_isNeg_2146_ == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; 
v_a_2147_ = lean_nat_abs(v_val_2137_);
lean_dec(v_val_2137_);
v___x_2148_ = l_Nat_reprFast(v_a_2147_);
v___y_2140_ = v___x_2148_;
goto v___jp_2139_;
}
else
{
lean_object* v_abs_2149_; lean_object* v_one_2150_; lean_object* v_a_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v_abs_2149_ = lean_nat_abs(v_val_2137_);
lean_dec(v_val_2137_);
v_one_2150_ = lean_unsigned_to_nat(1u);
v_a_2151_ = lean_nat_sub(v_abs_2149_, v_one_2150_);
lean_dec(v_abs_2149_);
v___x_2152_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2153_ = lean_nat_add(v_a_2151_, v_one_2150_);
lean_dec(v_a_2151_);
v___x_2154_ = l_Nat_reprFast(v___x_2153_);
v___x_2155_ = lean_string_append(v___x_2152_, v___x_2154_);
lean_dec_ref(v___x_2154_);
v___y_2140_ = v___x_2155_;
goto v___jp_2139_;
}
v___jp_2139_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2141_ = lean_string_append(v___x_2138_, v___y_2140_);
lean_dec_ref(v___y_2140_);
v___x_2142_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_2143_ = lean_string_append(v___x_2141_, v___x_2142_);
v___x_2144_ = lean_string_append(v___x_2108_, v___x_2143_);
lean_dec_ref(v___x_2143_);
return v___x_2144_;
}
}
else
{
lean_object* v_val_2156_; lean_object* v_val_2157_; uint8_t v___x_2158_; 
v_val_2156_ = lean_ctor_get(v_lowerBound_2104_, 0);
lean_inc(v_val_2156_);
lean_dec_ref_known(v_lowerBound_2104_, 1);
v_val_2157_ = lean_ctor_get(v_upperBound_2105_, 0);
lean_inc(v_val_2157_);
lean_dec_ref_known(v_upperBound_2105_, 1);
v___x_2158_ = lean_int_dec_lt(v_val_2157_, v_val_2156_);
if (v___x_2158_ == 0)
{
uint8_t v___x_2159_; 
v___x_2159_ = lean_int_dec_eq(v_val_2156_, v_val_2157_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___y_2162_; lean_object* v_intZero_2177_; uint8_t v_isNeg_2178_; 
v___x_2160_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2177_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2178_ = lean_int_dec_lt(v_val_2156_, v_intZero_2177_);
if (v_isNeg_2178_ == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; 
v_a_2179_ = lean_nat_abs(v_val_2156_);
lean_dec(v_val_2156_);
v___x_2180_ = l_Nat_reprFast(v_a_2179_);
v___y_2162_ = v___x_2180_;
goto v___jp_2161_;
}
else
{
lean_object* v_abs_2181_; lean_object* v_one_2182_; lean_object* v_a_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_abs_2181_ = lean_nat_abs(v_val_2156_);
lean_dec(v_val_2156_);
v_one_2182_ = lean_unsigned_to_nat(1u);
v_a_2183_ = lean_nat_sub(v_abs_2181_, v_one_2182_);
lean_dec(v_abs_2181_);
v___x_2184_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2185_ = lean_nat_add(v_a_2183_, v_one_2182_);
lean_dec(v_a_2183_);
v___x_2186_ = l_Nat_reprFast(v___x_2185_);
v___x_2187_ = lean_string_append(v___x_2184_, v___x_2186_);
lean_dec_ref(v___x_2186_);
v___y_2162_ = v___x_2187_;
goto v___jp_2161_;
}
v___jp_2161_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v_intZero_2166_; uint8_t v_isNeg_2167_; 
v___x_2163_ = lean_string_append(v___x_2160_, v___y_2162_);
lean_dec_ref(v___y_2162_);
v___x_2164_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_2165_ = lean_string_append(v___x_2163_, v___x_2164_);
v_intZero_2166_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2167_ = lean_int_dec_lt(v_val_2157_, v_intZero_2166_);
if (v_isNeg_2167_ == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2169_; 
v_a_2168_ = lean_nat_abs(v_val_2157_);
lean_dec(v_val_2157_);
v___x_2169_ = l_Nat_reprFast(v_a_2168_);
v___y_2110_ = v___x_2165_;
v___y_2111_ = v___x_2169_;
goto v___jp_2109_;
}
else
{
lean_object* v_abs_2170_; lean_object* v_one_2171_; lean_object* v_a_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v_abs_2170_ = lean_nat_abs(v_val_2157_);
lean_dec(v_val_2157_);
v_one_2171_ = lean_unsigned_to_nat(1u);
v_a_2172_ = lean_nat_sub(v_abs_2170_, v_one_2171_);
lean_dec(v_abs_2170_);
v___x_2173_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2174_ = lean_nat_add(v_a_2172_, v_one_2171_);
lean_dec(v_a_2172_);
v___x_2175_ = l_Nat_reprFast(v___x_2174_);
v___x_2176_ = lean_string_append(v___x_2173_, v___x_2175_);
lean_dec_ref(v___x_2175_);
v___y_2110_ = v___x_2165_;
v___y_2111_ = v___x_2176_;
goto v___jp_2109_;
}
}
}
else
{
lean_object* v___x_2188_; lean_object* v___y_2190_; lean_object* v_intZero_2195_; uint8_t v_isNeg_2196_; 
lean_dec(v_val_2157_);
v___x_2188_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_2195_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2196_ = lean_int_dec_lt(v_val_2156_, v_intZero_2195_);
if (v_isNeg_2196_ == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2198_; 
v_a_2197_ = lean_nat_abs(v_val_2156_);
lean_dec(v_val_2156_);
v___x_2198_ = l_Nat_reprFast(v_a_2197_);
v___y_2190_ = v___x_2198_;
goto v___jp_2189_;
}
else
{
lean_object* v_abs_2199_; lean_object* v_one_2200_; lean_object* v_a_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v_abs_2199_ = lean_nat_abs(v_val_2156_);
lean_dec(v_val_2156_);
v_one_2200_ = lean_unsigned_to_nat(1u);
v_a_2201_ = lean_nat_sub(v_abs_2199_, v_one_2200_);
lean_dec(v_abs_2199_);
v___x_2202_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2203_ = lean_nat_add(v_a_2201_, v_one_2200_);
lean_dec(v_a_2201_);
v___x_2204_ = l_Nat_reprFast(v___x_2203_);
v___x_2205_ = lean_string_append(v___x_2202_, v___x_2204_);
lean_dec_ref(v___x_2204_);
v___y_2190_ = v___x_2205_;
goto v___jp_2189_;
}
v___jp_2189_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2191_ = lean_string_append(v___x_2188_, v___y_2190_);
lean_dec_ref(v___y_2190_);
v___x_2192_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_2193_ = lean_string_append(v___x_2191_, v___x_2192_);
v___x_2194_ = lean_string_append(v___x_2108_, v___x_2193_);
lean_dec_ref(v___x_2193_);
return v___x_2194_;
}
}
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec(v_val_2157_);
lean_dec(v_val_2156_);
v___x_2206_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_2207_ = lean_string_append(v___x_2108_, v___x_2206_);
return v___x_2207_;
}
}
}
v___jp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2112_ = lean_string_append(v___y_2110_, v___y_2111_);
lean_dec_ref(v___y_2111_);
v___x_2113_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2114_ = lean_string_append(v___x_2112_, v___x_2113_);
v___x_2115_ = lean_string_append(v___x_2108_, v___x_2114_);
lean_dec_ref(v___x_2114_);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2(lean_object* v___x_2208_, lean_object* v___f_2209_, lean_object* v_l_2210_, lean_object* v_acc_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2208_, v___f_2209_, v_acc_2211_, v_l_2210_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3(lean_object* v___f_2234_, lean_object* v___f_2235_, lean_object* v_p_2236_){
_start:
{
uint8_t v_possible_2237_; 
v_possible_2237_ = lean_ctor_get_uint8(v_p_2236_, sizeof(void*)*7);
if (v_possible_2237_ == 0)
{
lean_object* v___x_2238_; 
lean_dec_ref(v_p_2236_);
lean_dec_ref(v___f_2235_);
lean_dec_ref(v___f_2234_);
v___x_2238_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
return v___x_2238_;
}
else
{
lean_object* v_constraints_2239_; uint8_t v___x_2240_; 
v_constraints_2239_ = lean_ctor_get(v_p_2236_, 2);
lean_inc_ref(v_constraints_2239_);
v___x_2240_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2236_);
lean_dec_ref(v_p_2236_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; lean_object* v_buckets_2242_; lean_object* v___x_2243_; lean_object* v___y_2245_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2241_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10));
v_buckets_2242_ = lean_ctor_get(v_constraints_2239_, 1);
lean_inc_ref(v_buckets_2242_);
lean_dec_ref(v_constraints_2239_);
v___x_2243_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_2249_ = lean_box(0);
v___x_2250_ = lean_array_get_size(v_buckets_2242_);
v___x_2251_ = lean_unsigned_to_nat(0u);
v___x_2252_ = lean_nat_dec_lt(v___x_2251_, v___x_2250_);
if (v___x_2252_ == 0)
{
lean_dec_ref(v_buckets_2242_);
lean_dec_ref(v___f_2235_);
v___y_2245_ = v___x_2249_;
goto v___jp_2244_;
}
else
{
lean_object* v___f_2253_; size_t v___x_2254_; size_t v___x_2255_; lean_object* v___x_2256_; 
v___f_2253_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2), 4, 2);
lean_closure_set(v___f_2253_, 0, v___x_2241_);
lean_closure_set(v___f_2253_, 1, v___f_2235_);
v___x_2254_ = lean_usize_of_nat(v___x_2250_);
v___x_2255_ = ((size_t)0ULL);
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2241_, v___f_2253_, v_buckets_2242_, v___x_2254_, v___x_2255_, v___x_2249_);
v___y_2245_ = v___x_2256_;
goto v___jp_2244_;
}
v___jp_2244_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2246_ = lean_box(0);
v___x_2247_ = l_List_mapTR_loop___redArg(v___f_2234_, v___y_2245_, v___x_2246_);
v___x_2248_ = l_String_intercalate(v___x_2243_, v___x_2247_);
return v___x_2248_;
}
}
else
{
lean_object* v___x_2257_; 
lean_dec_ref(v_constraints_2239_);
lean_dec_ref(v___f_2235_);
lean_dec_ref(v___f_2234_);
v___x_2257_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
return v___x_2257_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = lean_box(0);
v___x_2273_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1));
v___x_2274_ = l_Lean_Expr_const___override(v___x_2273_, v___x_2272_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = lean_box(0);
v___x_2281_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5));
v___x_2282_ = l_Lean_Expr_const___override(v___x_2281_, v___x_2280_);
return v___x_2282_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = lean_box(0);
v___x_2290_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8));
v___x_2291_ = l_Lean_Expr_const___override(v___x_2290_, v___x_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse(lean_object* v_s_2292_, lean_object* v_x_2293_, lean_object* v_j_2294_, lean_object* v_assumptions_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, uint8_t v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2297_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2308_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc_n(v_a_2307_, 2);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_2293_, v_a_2307_, v_assumptions_2295_, v_j_2294_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2310_; lean_object* v_lowerBound_2311_; lean_object* v_upperBound_2312_; lean_object* v_nil_2313_; lean_object* v_cons_2314_; lean_object* v___x_2315_; lean_object* v___y_2317_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___x_2340_; lean_object* v___y_2342_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_lowerBound_2311_ = lean_ctor_get(v_s_2292_, 0);
v_upperBound_2312_ = lean_ctor_get(v_s_2292_, 1);
v_nil_2313_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2314_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2315_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2313_, v_cons_2314_, v_x_2293_);
v___x_2340_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
if (lean_obj_tag(v_lowerBound_2311_) == 0)
{
lean_object* v___x_2358_; 
v___x_2358_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_2342_ = v___x_2358_;
goto v___jp_2341_;
}
else
{
lean_object* v_val_2359_; lean_object* v___x_2360_; lean_object* v___y_2362_; lean_object* v___x_2364_; uint8_t v___x_2365_; 
v_val_2359_ = lean_ctor_get(v_lowerBound_2311_, 0);
v___x_2360_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2364_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2365_ = lean_int_dec_le(v___x_2364_, v_val_2359_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2366_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2367_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2368_ = lean_int_neg(v_val_2359_);
v___x_2369_ = l_Int_toNat(v___x_2368_);
lean_dec(v___x_2368_);
v___x_2370_ = l_Lean_instToExprInt_mkNat(v___x_2369_);
v___x_2371_ = l_Lean_mkApp3(v___x_2366_, v___x_2310_, v___x_2367_, v___x_2370_);
v___y_2362_ = v___x_2371_;
goto v___jp_2361_;
}
else
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = l_Int_toNat(v_val_2359_);
v___x_2373_ = l_Lean_instToExprInt_mkNat(v___x_2372_);
v___y_2362_ = v___x_2373_;
goto v___jp_2361_;
}
v___jp_2361_:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_mkAppB(v___x_2360_, v___x_2310_, v___y_2362_);
v___y_2342_ = v___x_2363_;
goto v___jp_2341_;
}
}
v___jp_2316_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2318_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2);
lean_inc_ref(v___y_2317_);
v___x_2319_ = l_Lean_Expr_app___override(v___x_2318_, v___y_2317_);
v___x_2320_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6);
v___x_2321_ = l_Lean_Meta_mkEq(v___x_2319_, v___x_2320_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2323_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = l_Lean_Meta_mkDecideProof(v_a_2322_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2333_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2333_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2333_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2328_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9);
v___x_2329_ = l_Lean_mkApp5(v___x_2328_, v___y_2317_, v_a_2324_, v___x_2315_, v_a_2307_, v_a_2309_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2329_);
v___x_2331_ = v___x_2326_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
else
{
lean_dec_ref(v___y_2317_);
lean_dec_ref(v___x_2315_);
lean_dec(v_a_2309_);
lean_dec(v_a_2307_);
return v___x_2323_;
}
}
else
{
lean_dec_ref(v___y_2317_);
lean_dec_ref(v___x_2315_);
lean_dec(v_a_2309_);
lean_dec(v_a_2307_);
return v___x_2321_;
}
}
v___jp_2334_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_inc_ref(v___y_2335_);
v___x_2338_ = l_Lean_mkAppB(v___y_2335_, v___x_2310_, v___y_2337_);
v___x_2339_ = l_Lean_Expr_app___override(v___y_2336_, v___x_2338_);
v___y_2317_ = v___x_2339_;
goto v___jp_2316_;
}
v___jp_2341_:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_Expr_app___override(v___x_2340_, v___y_2342_);
if (lean_obj_tag(v_upperBound_2312_) == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_2345_ = l_Lean_Expr_app___override(v___x_2343_, v___x_2344_);
v___y_2317_ = v___x_2345_;
goto v___jp_2316_;
}
else
{
lean_object* v_val_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_val_2346_ = lean_ctor_get(v_upperBound_2312_, 0);
v___x_2347_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2348_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2349_ = lean_int_dec_le(v___x_2348_, v_val_2346_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2350_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2351_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2352_ = lean_int_neg(v_val_2346_);
v___x_2353_ = l_Int_toNat(v___x_2352_);
lean_dec(v___x_2352_);
v___x_2354_ = l_Lean_instToExprInt_mkNat(v___x_2353_);
v___x_2355_ = l_Lean_mkApp3(v___x_2350_, v___x_2310_, v___x_2351_, v___x_2354_);
v___y_2335_ = v___x_2347_;
v___y_2336_ = v___x_2343_;
v___y_2337_ = v___x_2355_;
goto v___jp_2334_;
}
else
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = l_Int_toNat(v_val_2346_);
v___x_2357_ = l_Lean_instToExprInt_mkNat(v___x_2356_);
v___y_2335_ = v___x_2347_;
v___y_2336_ = v___x_2343_;
v___y_2337_ = v___x_2357_;
goto v___jp_2334_;
}
}
}
}
else
{
lean_dec(v_a_2307_);
return v___x_2308_;
}
}
else
{
lean_dec_ref(v_j_2294_);
return v___x_2306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed(lean_object* v_s_2374_, lean_object* v_x_2375_, lean_object* v_j_2376_, lean_object* v_assumptions_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
uint8_t v_a_boxed_2388_; lean_object* v_res_2389_; 
v_a_boxed_2388_ = lean_unbox(v_a_2381_);
v_res_2389_ = l_Lean_Elab_Tactic_Omega_Problem_proveFalse(v_s_2374_, v_x_2375_, v_j_2376_, v_assumptions_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_boxed_2388_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_assumptions_2377_);
lean_dec(v_x_2375_);
lean_dec_ref(v_s_2374_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0(lean_object* v_constraint_2390_, lean_object* v_coeffs_2391_, lean_object* v_justification_2392_, lean_object* v_x_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_2390_, v_coeffs_2391_, v_justification_2392_);
return v___x_2394_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(lean_object* v_a_2395_, lean_object* v_x_2396_){
_start:
{
if (lean_obj_tag(v_x_2396_) == 0)
{
uint8_t v___x_2397_; 
v___x_2397_ = 0;
return v___x_2397_;
}
else
{
lean_object* v_key_2398_; lean_object* v_tail_2399_; uint8_t v___x_2400_; 
v_key_2398_ = lean_ctor_get(v_x_2396_, 0);
v_tail_2399_ = lean_ctor_get(v_x_2396_, 2);
v___x_2400_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2398_, v_a_2395_);
if (v___x_2400_ == 0)
{
v_x_2396_ = v_tail_2399_;
goto _start;
}
else
{
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg___boxed(lean_object* v_a_2402_, lean_object* v_x_2403_){
_start:
{
uint8_t v_res_2404_; lean_object* v_r_2405_; 
v_res_2404_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2402_, v_x_2403_);
lean_dec(v_x_2403_);
lean_dec(v_a_2402_);
v_r_2405_ = lean_box(v_res_2404_);
return v_r_2405_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(uint64_t v_x_2406_, lean_object* v_x_2407_){
_start:
{
if (lean_obj_tag(v_x_2407_) == 0)
{
return v_x_2406_;
}
else
{
lean_object* v_head_2408_; lean_object* v_tail_2409_; lean_object* v_intZero_2410_; uint8_t v_isNeg_2411_; 
v_head_2408_ = lean_ctor_get(v_x_2407_, 0);
v_tail_2409_ = lean_ctor_get(v_x_2407_, 1);
v_intZero_2410_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2411_ = lean_int_dec_lt(v_head_2408_, v_intZero_2410_);
if (v_isNeg_2411_ == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint64_t v___x_2415_; uint64_t v___x_2416_; 
v_a_2412_ = lean_nat_abs(v_head_2408_);
v___x_2413_ = lean_unsigned_to_nat(2u);
v___x_2414_ = lean_nat_mul(v___x_2413_, v_a_2412_);
lean_dec(v_a_2412_);
v___x_2415_ = lean_uint64_of_nat(v___x_2414_);
lean_dec(v___x_2414_);
v___x_2416_ = lean_uint64_mix_hash(v_x_2406_, v___x_2415_);
v_x_2406_ = v___x_2416_;
v_x_2407_ = v_tail_2409_;
goto _start;
}
else
{
lean_object* v_abs_2418_; lean_object* v_one_2419_; lean_object* v_a_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; uint64_t v___x_2424_; uint64_t v___x_2425_; 
v_abs_2418_ = lean_nat_abs(v_head_2408_);
v_one_2419_ = lean_unsigned_to_nat(1u);
v_a_2420_ = lean_nat_sub(v_abs_2418_, v_one_2419_);
lean_dec(v_abs_2418_);
v___x_2421_ = lean_unsigned_to_nat(2u);
v___x_2422_ = lean_nat_mul(v___x_2421_, v_a_2420_);
lean_dec(v_a_2420_);
v___x_2423_ = lean_nat_add(v___x_2422_, v_one_2419_);
lean_dec(v___x_2422_);
v___x_2424_ = lean_uint64_of_nat(v___x_2423_);
lean_dec(v___x_2423_);
v___x_2425_ = lean_uint64_mix_hash(v_x_2406_, v___x_2424_);
v_x_2406_ = v___x_2425_;
v_x_2407_ = v_tail_2409_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0___boxed(lean_object* v_x_2427_, lean_object* v_x_2428_){
_start:
{
uint64_t v_x_806__boxed_2429_; uint64_t v_res_2430_; lean_object* v_r_2431_; 
v_x_806__boxed_2429_ = lean_unbox_uint64(v_x_2427_);
lean_dec_ref(v_x_2427_);
v_res_2430_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v_x_806__boxed_2429_, v_x_2428_);
lean_dec(v_x_2428_);
v_r_2431_ = lean_box_uint64(v_res_2430_);
return v_r_2431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_2432_, lean_object* v_x_2433_){
_start:
{
if (lean_obj_tag(v_x_2433_) == 0)
{
return v_x_2432_;
}
else
{
lean_object* v_key_2434_; lean_object* v_value_2435_; lean_object* v_tail_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2460_; 
v_key_2434_ = lean_ctor_get(v_x_2433_, 0);
v_value_2435_ = lean_ctor_get(v_x_2433_, 1);
v_tail_2436_ = lean_ctor_get(v_x_2433_, 2);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_x_2433_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2438_ = v_x_2433_;
v_isShared_2439_ = v_isSharedCheck_2460_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_tail_2436_);
lean_inc(v_value_2435_);
lean_inc(v_key_2434_);
lean_dec(v_x_2433_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2460_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; uint64_t v___x_2441_; uint64_t v___x_2442_; uint64_t v___x_2443_; uint64_t v___x_2444_; uint64_t v_fold_2445_; uint64_t v___x_2446_; uint64_t v___x_2447_; uint64_t v___x_2448_; size_t v___x_2449_; size_t v___x_2450_; size_t v___x_2451_; size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2440_ = lean_array_get_size(v_x_2432_);
v___x_2441_ = 7ULL;
v___x_2442_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2441_, v_key_2434_);
v___x_2443_ = 32ULL;
v___x_2444_ = lean_uint64_shift_right(v___x_2442_, v___x_2443_);
v_fold_2445_ = lean_uint64_xor(v___x_2442_, v___x_2444_);
v___x_2446_ = 16ULL;
v___x_2447_ = lean_uint64_shift_right(v_fold_2445_, v___x_2446_);
v___x_2448_ = lean_uint64_xor(v_fold_2445_, v___x_2447_);
v___x_2449_ = lean_uint64_to_usize(v___x_2448_);
v___x_2450_ = lean_usize_of_nat(v___x_2440_);
v___x_2451_ = ((size_t)1ULL);
v___x_2452_ = lean_usize_sub(v___x_2450_, v___x_2451_);
v___x_2453_ = lean_usize_land(v___x_2449_, v___x_2452_);
v___x_2454_ = lean_array_uget_borrowed(v_x_2432_, v___x_2453_);
lean_inc(v___x_2454_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 2, v___x_2454_);
v___x_2456_ = v___x_2438_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_key_2434_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_value_2435_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_array_uset(v_x_2432_, v___x_2453_, v___x_2456_);
v_x_2432_ = v___x_2457_;
v_x_2433_ = v_tail_2436_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(lean_object* v_i_2461_, lean_object* v_source_2462_, lean_object* v_target_2463_){
_start:
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = lean_array_get_size(v_source_2462_);
v___x_2465_ = lean_nat_dec_lt(v_i_2461_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_dec_ref(v_source_2462_);
lean_dec(v_i_2461_);
return v_target_2463_;
}
else
{
lean_object* v_es_2466_; lean_object* v___x_2467_; lean_object* v_source_2468_; lean_object* v_target_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_es_2466_ = lean_array_fget(v_source_2462_, v_i_2461_);
v___x_2467_ = lean_box(0);
v_source_2468_ = lean_array_fset(v_source_2462_, v_i_2461_, v___x_2467_);
v_target_2469_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_target_2463_, v_es_2466_);
v___x_2470_ = lean_unsigned_to_nat(1u);
v___x_2471_ = lean_nat_add(v_i_2461_, v___x_2470_);
lean_dec(v_i_2461_);
v_i_2461_ = v___x_2471_;
v_source_2462_ = v_source_2468_;
v_target_2463_ = v_target_2469_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(lean_object* v_data_2473_){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v_nbuckets_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2474_ = lean_array_get_size(v_data_2473_);
v___x_2475_ = lean_unsigned_to_nat(2u);
v_nbuckets_2476_ = lean_nat_mul(v___x_2474_, v___x_2475_);
v___x_2477_ = lean_unsigned_to_nat(0u);
v___x_2478_ = lean_box(0);
v___x_2479_ = lean_mk_array(v_nbuckets_2476_, v___x_2478_);
v___x_2480_ = lean_array_propagate_mark(v_data_2473_, v___x_2479_);
v___x_2481_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v___x_2477_, v_data_2473_, v___x_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(lean_object* v_m_2482_, lean_object* v_a_2483_, lean_object* v_b_2484_){
_start:
{
lean_object* v_size_2485_; lean_object* v_buckets_2486_; lean_object* v___x_2487_; uint64_t v___x_2488_; uint64_t v___x_2489_; uint64_t v___x_2490_; uint64_t v___x_2491_; uint64_t v_fold_2492_; uint64_t v___x_2493_; uint64_t v___x_2494_; uint64_t v___x_2495_; size_t v___x_2496_; size_t v___x_2497_; size_t v___x_2498_; size_t v___x_2499_; size_t v___x_2500_; lean_object* v_bkt_2501_; uint8_t v___x_2502_; 
v_size_2485_ = lean_ctor_get(v_m_2482_, 0);
v_buckets_2486_ = lean_ctor_get(v_m_2482_, 1);
v___x_2487_ = lean_array_get_size(v_buckets_2486_);
v___x_2488_ = 7ULL;
v___x_2489_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2488_, v_a_2483_);
v___x_2490_ = 32ULL;
v___x_2491_ = lean_uint64_shift_right(v___x_2489_, v___x_2490_);
v_fold_2492_ = lean_uint64_xor(v___x_2489_, v___x_2491_);
v___x_2493_ = 16ULL;
v___x_2494_ = lean_uint64_shift_right(v_fold_2492_, v___x_2493_);
v___x_2495_ = lean_uint64_xor(v_fold_2492_, v___x_2494_);
v___x_2496_ = lean_uint64_to_usize(v___x_2495_);
v___x_2497_ = lean_usize_of_nat(v___x_2487_);
v___x_2498_ = ((size_t)1ULL);
v___x_2499_ = lean_usize_sub(v___x_2497_, v___x_2498_);
v___x_2500_ = lean_usize_land(v___x_2496_, v___x_2499_);
v_bkt_2501_ = lean_array_uget_borrowed(v_buckets_2486_, v___x_2500_);
v___x_2502_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2483_, v_bkt_2501_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2523_; 
lean_inc_ref(v_buckets_2486_);
lean_inc(v_size_2485_);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_m_2482_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; lean_object* v_unused_2525_; 
v_unused_2524_ = lean_ctor_get(v_m_2482_, 1);
lean_dec(v_unused_2524_);
v_unused_2525_ = lean_ctor_get(v_m_2482_, 0);
lean_dec(v_unused_2525_);
v___x_2504_ = v_m_2482_;
v_isShared_2505_ = v_isSharedCheck_2523_;
goto v_resetjp_2503_;
}
else
{
lean_dec(v_m_2482_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2523_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v_size_x27_2507_; lean_object* v___x_2508_; lean_object* v_buckets_x27_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v___x_2506_ = lean_unsigned_to_nat(1u);
v_size_x27_2507_ = lean_nat_add(v_size_2485_, v___x_2506_);
lean_dec(v_size_2485_);
lean_inc(v_bkt_2501_);
v___x_2508_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2508_, 0, v_a_2483_);
lean_ctor_set(v___x_2508_, 1, v_b_2484_);
lean_ctor_set(v___x_2508_, 2, v_bkt_2501_);
v_buckets_x27_2509_ = lean_array_uset(v_buckets_2486_, v___x_2500_, v___x_2508_);
v___x_2510_ = lean_unsigned_to_nat(4u);
v___x_2511_ = lean_nat_mul(v_size_x27_2507_, v___x_2510_);
v___x_2512_ = lean_unsigned_to_nat(3u);
v___x_2513_ = lean_nat_div(v___x_2511_, v___x_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_array_get_size(v_buckets_x27_2509_);
v___x_2515_ = lean_nat_dec_le(v___x_2513_, v___x_2514_);
lean_dec(v___x_2513_);
if (v___x_2515_ == 0)
{
lean_object* v_val_2516_; lean_object* v___x_2518_; 
v_val_2516_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2509_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 1, v_val_2516_);
lean_ctor_set(v___x_2504_, 0, v_size_x27_2507_);
v___x_2518_ = v___x_2504_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_size_x27_2507_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_val_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
else
{
lean_object* v___x_2521_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 1, v_buckets_x27_2509_);
lean_ctor_set(v___x_2504_, 0, v_size_x27_2507_);
v___x_2521_ = v___x_2504_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_size_x27_2507_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_buckets_x27_2509_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_dec(v_b_2484_);
lean_dec(v_a_2483_);
return v_m_2482_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(lean_object* v_a_2526_, lean_object* v_b_2527_, lean_object* v_x_2528_){
_start:
{
if (lean_obj_tag(v_x_2528_) == 0)
{
lean_dec(v_b_2527_);
lean_dec(v_a_2526_);
return v_x_2528_;
}
else
{
lean_object* v_key_2529_; lean_object* v_value_2530_; lean_object* v_tail_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2543_; 
v_key_2529_ = lean_ctor_get(v_x_2528_, 0);
v_value_2530_ = lean_ctor_get(v_x_2528_, 1);
v_tail_2531_ = lean_ctor_get(v_x_2528_, 2);
v_isSharedCheck_2543_ = !lean_is_exclusive(v_x_2528_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2533_ = v_x_2528_;
v_isShared_2534_ = v_isSharedCheck_2543_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_tail_2531_);
lean_inc(v_value_2530_);
lean_inc(v_key_2529_);
lean_dec(v_x_2528_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2543_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
uint8_t v___x_2535_; 
v___x_2535_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2529_, v_a_2526_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2538_; 
v___x_2536_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2526_, v_b_2527_, v_tail_2531_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 2, v___x_2536_);
v___x_2538_ = v___x_2533_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_key_2529_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_value_2530_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
else
{
lean_object* v___x_2541_; 
lean_dec(v_value_2530_);
lean_dec(v_key_2529_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v_b_2527_);
lean_ctor_set(v___x_2533_, 0, v_a_2526_);
v___x_2541_ = v___x_2533_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2526_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_b_2527_);
lean_ctor_set(v_reuseFailAlloc_2542_, 2, v_tail_2531_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(lean_object* v_m_2544_, lean_object* v_a_2545_, lean_object* v_b_2546_){
_start:
{
lean_object* v_size_2547_; lean_object* v_buckets_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2592_; 
v_size_2547_ = lean_ctor_get(v_m_2544_, 0);
v_buckets_2548_ = lean_ctor_get(v_m_2544_, 1);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_m_2544_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2550_ = v_m_2544_;
v_isShared_2551_ = v_isSharedCheck_2592_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_buckets_2548_);
lean_inc(v_size_2547_);
lean_dec(v_m_2544_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2592_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; uint64_t v___x_2553_; uint64_t v___x_2554_; uint64_t v___x_2555_; uint64_t v___x_2556_; uint64_t v_fold_2557_; uint64_t v___x_2558_; uint64_t v___x_2559_; uint64_t v___x_2560_; size_t v___x_2561_; size_t v___x_2562_; size_t v___x_2563_; size_t v___x_2564_; size_t v___x_2565_; lean_object* v_bkt_2566_; uint8_t v___x_2567_; 
v___x_2552_ = lean_array_get_size(v_buckets_2548_);
v___x_2553_ = 7ULL;
v___x_2554_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2553_, v_a_2545_);
v___x_2555_ = 32ULL;
v___x_2556_ = lean_uint64_shift_right(v___x_2554_, v___x_2555_);
v_fold_2557_ = lean_uint64_xor(v___x_2554_, v___x_2556_);
v___x_2558_ = 16ULL;
v___x_2559_ = lean_uint64_shift_right(v_fold_2557_, v___x_2558_);
v___x_2560_ = lean_uint64_xor(v_fold_2557_, v___x_2559_);
v___x_2561_ = lean_uint64_to_usize(v___x_2560_);
v___x_2562_ = lean_usize_of_nat(v___x_2552_);
v___x_2563_ = ((size_t)1ULL);
v___x_2564_ = lean_usize_sub(v___x_2562_, v___x_2563_);
v___x_2565_ = lean_usize_land(v___x_2561_, v___x_2564_);
v_bkt_2566_ = lean_array_uget_borrowed(v_buckets_2548_, v___x_2565_);
v___x_2567_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2545_, v_bkt_2566_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; lean_object* v_size_x27_2569_; lean_object* v___x_2570_; lean_object* v_buckets_x27_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2568_ = lean_unsigned_to_nat(1u);
v_size_x27_2569_ = lean_nat_add(v_size_2547_, v___x_2568_);
lean_dec(v_size_2547_);
lean_inc(v_bkt_2566_);
v___x_2570_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2570_, 0, v_a_2545_);
lean_ctor_set(v___x_2570_, 1, v_b_2546_);
lean_ctor_set(v___x_2570_, 2, v_bkt_2566_);
v_buckets_x27_2571_ = lean_array_uset(v_buckets_2548_, v___x_2565_, v___x_2570_);
v___x_2572_ = lean_unsigned_to_nat(4u);
v___x_2573_ = lean_nat_mul(v_size_x27_2569_, v___x_2572_);
v___x_2574_ = lean_unsigned_to_nat(3u);
v___x_2575_ = lean_nat_div(v___x_2573_, v___x_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_array_get_size(v_buckets_x27_2571_);
v___x_2577_ = lean_nat_dec_le(v___x_2575_, v___x_2576_);
lean_dec(v___x_2575_);
if (v___x_2577_ == 0)
{
lean_object* v_val_2578_; lean_object* v___x_2580_; 
v_val_2578_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2571_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 1, v_val_2578_);
lean_ctor_set(v___x_2550_, 0, v_size_x27_2569_);
v___x_2580_ = v___x_2550_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_size_x27_2569_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_val_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
else
{
lean_object* v___x_2583_; 
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 1, v_buckets_x27_2571_);
lean_ctor_set(v___x_2550_, 0, v_size_x27_2569_);
v___x_2583_ = v___x_2550_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_size_x27_2569_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_buckets_x27_2571_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
else
{
lean_object* v___x_2585_; lean_object* v_buckets_x27_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
lean_inc(v_bkt_2566_);
v___x_2585_ = lean_box(0);
v_buckets_x27_2586_ = lean_array_uset(v_buckets_2548_, v___x_2565_, v___x_2585_);
v___x_2587_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2545_, v_b_2546_, v_bkt_2566_);
v___x_2588_ = lean_array_uset(v_buckets_x27_2586_, v___x_2565_, v___x_2587_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 1, v___x_2588_);
v___x_2590_ = v___x_2550_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_size_2547_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(lean_object* v_p_2593_, lean_object* v_x_2594_){
_start:
{
lean_object* v_coeffs_2595_; lean_object* v_constraint_2596_; lean_object* v_justification_2597_; uint8_t v___x_2598_; 
v_coeffs_2595_ = lean_ctor_get(v_x_2594_, 0);
lean_inc(v_coeffs_2595_);
v_constraint_2596_ = lean_ctor_get(v_x_2594_, 1);
lean_inc_ref(v_constraint_2596_);
v_justification_2597_ = lean_ctor_get(v_x_2594_, 2);
v___x_2598_ = l_Lean_Omega_Constraint_isImpossible(v_constraint_2596_);
if (v___x_2598_ == 0)
{
lean_object* v_assumptions_2599_; lean_object* v_numVars_2600_; lean_object* v_constraints_2601_; lean_object* v_equalities_2602_; lean_object* v_eliminations_2603_; uint8_t v_possible_2604_; lean_object* v_proveFalse_x3f_2605_; lean_object* v_explanation_x3f_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2624_; 
v_assumptions_2599_ = lean_ctor_get(v_p_2593_, 0);
v_numVars_2600_ = lean_ctor_get(v_p_2593_, 1);
v_constraints_2601_ = lean_ctor_get(v_p_2593_, 2);
v_equalities_2602_ = lean_ctor_get(v_p_2593_, 3);
v_eliminations_2603_ = lean_ctor_get(v_p_2593_, 4);
v_possible_2604_ = lean_ctor_get_uint8(v_p_2593_, sizeof(void*)*7);
v_proveFalse_x3f_2605_ = lean_ctor_get(v_p_2593_, 5);
v_explanation_x3f_2606_ = lean_ctor_get(v_p_2593_, 6);
v_isSharedCheck_2624_ = !lean_is_exclusive(v_p_2593_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2608_ = v_p_2593_;
v_isShared_2609_ = v_isSharedCheck_2624_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_explanation_x3f_2606_);
lean_inc(v_proveFalse_x3f_2605_);
lean_inc(v_eliminations_2603_);
lean_inc(v_equalities_2602_);
lean_inc(v_constraints_2601_);
lean_inc(v_numVars_2600_);
lean_inc(v_assumptions_2599_);
lean_dec(v_p_2593_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2624_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___y_2611_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2622_ = l_List_lengthTR___redArg(v_coeffs_2595_);
v___x_2623_ = lean_nat_dec_le(v_numVars_2600_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_dec(v___x_2622_);
v___y_2611_ = v_numVars_2600_;
goto v___jp_2610_;
}
else
{
lean_dec(v_numVars_2600_);
v___y_2611_ = v___x_2622_;
goto v___jp_2610_;
}
v___jp_2610_:
{
lean_object* v___x_2612_; uint8_t v___x_2613_; 
lean_inc(v_coeffs_2595_);
v___x_2612_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_constraints_2601_, v_coeffs_2595_, v_x_2594_);
v___x_2613_ = l_Lean_Omega_Constraint_isExact(v_constraint_2596_);
lean_dec_ref(v_constraint_2596_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2615_; 
lean_dec(v_coeffs_2595_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 2, v___x_2612_);
lean_ctor_set(v___x_2608_, 1, v___y_2611_);
v___x_2615_ = v___x_2608_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_assumptions_2599_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v___y_2611_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2616_, 3, v_equalities_2602_);
lean_ctor_set(v_reuseFailAlloc_2616_, 4, v_eliminations_2603_);
lean_ctor_set(v_reuseFailAlloc_2616_, 5, v_proveFalse_x3f_2605_);
lean_ctor_set(v_reuseFailAlloc_2616_, 6, v_explanation_x3f_2606_);
lean_ctor_set_uint8(v_reuseFailAlloc_2616_, sizeof(void*)*7, v_possible_2604_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
else
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2617_ = lean_box(0);
v___x_2618_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_equalities_2602_, v_coeffs_2595_, v___x_2617_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 3, v___x_2618_);
lean_ctor_set(v___x_2608_, 2, v___x_2612_);
lean_ctor_set(v___x_2608_, 1, v___y_2611_);
v___x_2620_ = v___x_2608_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_assumptions_2599_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v___y_2611_);
lean_ctor_set(v_reuseFailAlloc_2621_, 2, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2621_, 3, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2621_, 4, v_eliminations_2603_);
lean_ctor_set(v_reuseFailAlloc_2621_, 5, v_proveFalse_x3f_2605_);
lean_ctor_set(v_reuseFailAlloc_2621_, 6, v_explanation_x3f_2606_);
lean_ctor_set_uint8(v_reuseFailAlloc_2621_, sizeof(void*)*7, v_possible_2604_);
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
lean_object* v_assumptions_2625_; lean_object* v_numVars_2626_; lean_object* v_constraints_2627_; lean_object* v_equalities_2628_; lean_object* v_eliminations_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2641_; 
lean_inc_ref(v_justification_2597_);
lean_dec_ref(v_x_2594_);
v_assumptions_2625_ = lean_ctor_get(v_p_2593_, 0);
v_numVars_2626_ = lean_ctor_get(v_p_2593_, 1);
v_constraints_2627_ = lean_ctor_get(v_p_2593_, 2);
v_equalities_2628_ = lean_ctor_get(v_p_2593_, 3);
v_eliminations_2629_ = lean_ctor_get(v_p_2593_, 4);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_p_2593_);
if (v_isSharedCheck_2641_ == 0)
{
lean_object* v_unused_2642_; lean_object* v_unused_2643_; 
v_unused_2642_ = lean_ctor_get(v_p_2593_, 6);
lean_dec(v_unused_2642_);
v_unused_2643_ = lean_ctor_get(v_p_2593_, 5);
lean_dec(v_unused_2643_);
v___x_2631_ = v_p_2593_;
v_isShared_2632_ = v_isSharedCheck_2641_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_eliminations_2629_);
lean_inc(v_equalities_2628_);
lean_inc(v_constraints_2627_);
lean_inc(v_numVars_2626_);
lean_inc(v_assumptions_2625_);
lean_dec(v_p_2593_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2641_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___f_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
lean_inc_ref(v_justification_2597_);
lean_inc(v_coeffs_2595_);
lean_inc_ref(v_constraint_2596_);
v___f_2633_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0), 4, 3);
lean_closure_set(v___f_2633_, 0, v_constraint_2596_);
lean_closure_set(v___f_2633_, 1, v_coeffs_2595_);
lean_closure_set(v___f_2633_, 2, v_justification_2597_);
v___x_2634_ = 0;
lean_inc_ref(v_assumptions_2625_);
v___x_2635_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed), 14, 4);
lean_closure_set(v___x_2635_, 0, v_constraint_2596_);
lean_closure_set(v___x_2635_, 1, v_coeffs_2595_);
lean_closure_set(v___x_2635_, 2, v_justification_2597_);
lean_closure_set(v___x_2635_, 3, v_assumptions_2625_);
v___x_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
v___x_2637_ = lean_mk_thunk(v___f_2633_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 6, v___x_2637_);
lean_ctor_set(v___x_2631_, 5, v___x_2636_);
v___x_2639_ = v___x_2631_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_assumptions_2625_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_numVars_2626_);
lean_ctor_set(v_reuseFailAlloc_2640_, 2, v_constraints_2627_);
lean_ctor_set(v_reuseFailAlloc_2640_, 3, v_equalities_2628_);
lean_ctor_set(v_reuseFailAlloc_2640_, 4, v_eliminations_2629_);
lean_ctor_set(v_reuseFailAlloc_2640_, 5, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2640_, 6, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_ctor_set_uint8(v___x_2639_, sizeof(void*)*7, v___x_2634_);
return v___x_2639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0(lean_object* v_00_u03b2_2644_, lean_object* v_m_2645_, lean_object* v_a_2646_, lean_object* v_b_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_m_2645_, v_a_2646_, v_b_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1(lean_object* v_00_u03b2_2649_, lean_object* v_m_2650_, lean_object* v_a_2651_, lean_object* v_b_2652_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_m_2650_, v_a_2651_, v_b_2652_);
return v___x_2653_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_object* v_00_u03b2_2654_, lean_object* v_a_2655_, lean_object* v_x_2656_){
_start:
{
uint8_t v___x_2657_; 
v___x_2657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2655_, v_x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2658_, lean_object* v_a_2659_, lean_object* v_x_2660_){
_start:
{
uint8_t v_res_2661_; lean_object* v_r_2662_; 
v_res_2661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(v_00_u03b2_2658_, v_a_2659_, v_x_2660_);
lean_dec(v_x_2660_);
lean_dec(v_a_2659_);
v_r_2662_ = lean_box(v_res_2661_);
return v_r_2662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2(lean_object* v_00_u03b2_2663_, lean_object* v_data_2664_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_data_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3(lean_object* v_00_u03b2_2666_, lean_object* v_a_2667_, lean_object* v_b_2668_, lean_object* v_x_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2667_, v_b_2668_, v_x_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2671_, lean_object* v_i_2672_, lean_object* v_source_2673_, lean_object* v_target_2674_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v_i_2672_, v_source_2673_, v_target_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2676_, lean_object* v_x_2677_, lean_object* v_x_2678_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_x_2677_, v_x_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(lean_object* v_a_2680_, lean_object* v_x_2681_){
_start:
{
if (lean_obj_tag(v_x_2681_) == 0)
{
lean_object* v___x_2682_; 
v___x_2682_ = lean_box(0);
return v___x_2682_;
}
else
{
lean_object* v_key_2683_; lean_object* v_value_2684_; lean_object* v_tail_2685_; uint8_t v___x_2686_; 
v_key_2683_ = lean_ctor_get(v_x_2681_, 0);
v_value_2684_ = lean_ctor_get(v_x_2681_, 1);
v_tail_2685_ = lean_ctor_get(v_x_2681_, 2);
v___x_2686_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2683_, v_a_2680_);
if (v___x_2686_ == 0)
{
v_x_2681_ = v_tail_2685_;
goto _start;
}
else
{
lean_object* v___x_2688_; 
lean_inc(v_value_2684_);
v___x_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2688_, 0, v_value_2684_);
return v___x_2688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg___boxed(lean_object* v_a_2689_, lean_object* v_x_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2689_, v_x_2690_);
lean_dec(v_x_2690_);
lean_dec(v_a_2689_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(lean_object* v_m_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v_buckets_2694_; lean_object* v___x_2695_; uint64_t v___x_2696_; uint64_t v___x_2697_; uint64_t v___x_2698_; uint64_t v___x_2699_; uint64_t v_fold_2700_; uint64_t v___x_2701_; uint64_t v___x_2702_; uint64_t v___x_2703_; size_t v___x_2704_; size_t v___x_2705_; size_t v___x_2706_; size_t v___x_2707_; size_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v_buckets_2694_ = lean_ctor_get(v_m_2692_, 1);
v___x_2695_ = lean_array_get_size(v_buckets_2694_);
v___x_2696_ = 7ULL;
v___x_2697_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2696_, v_a_2693_);
v___x_2698_ = 32ULL;
v___x_2699_ = lean_uint64_shift_right(v___x_2697_, v___x_2698_);
v_fold_2700_ = lean_uint64_xor(v___x_2697_, v___x_2699_);
v___x_2701_ = 16ULL;
v___x_2702_ = lean_uint64_shift_right(v_fold_2700_, v___x_2701_);
v___x_2703_ = lean_uint64_xor(v_fold_2700_, v___x_2702_);
v___x_2704_ = lean_uint64_to_usize(v___x_2703_);
v___x_2705_ = lean_usize_of_nat(v___x_2695_);
v___x_2706_ = ((size_t)1ULL);
v___x_2707_ = lean_usize_sub(v___x_2705_, v___x_2706_);
v___x_2708_ = lean_usize_land(v___x_2704_, v___x_2707_);
v___x_2709_ = lean_array_uget_borrowed(v_buckets_2694_, v___x_2708_);
v___x_2710_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2693_, v___x_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg___boxed(lean_object* v_m_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2711_, v_a_2712_);
lean_dec(v_a_2712_);
lean_dec_ref(v_m_2711_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addConstraint(lean_object* v_p_2714_, lean_object* v_x_2715_){
_start:
{
uint8_t v_possible_2716_; 
v_possible_2716_ = lean_ctor_get_uint8(v_p_2714_, sizeof(void*)*7);
if (v_possible_2716_ == 0)
{
lean_dec_ref(v_x_2715_);
return v_p_2714_;
}
else
{
lean_object* v_coeffs_2717_; lean_object* v_constraint_2718_; lean_object* v_justification_2719_; lean_object* v_constraints_2720_; lean_object* v___x_2721_; 
v_coeffs_2717_ = lean_ctor_get(v_x_2715_, 0);
v_constraint_2718_ = lean_ctor_get(v_x_2715_, 1);
v_justification_2719_ = lean_ctor_get(v_x_2715_, 2);
v_constraints_2720_ = lean_ctor_get(v_p_2714_, 2);
v___x_2721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2720_, v_coeffs_2717_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_lowerBound_2722_; 
v_lowerBound_2722_ = lean_ctor_get(v_constraint_2718_, 0);
if (lean_obj_tag(v_lowerBound_2722_) == 0)
{
lean_object* v_upperBound_2723_; 
v_upperBound_2723_ = lean_ctor_get(v_constraint_2718_, 1);
if (lean_obj_tag(v_upperBound_2723_) == 0)
{
lean_dec_ref(v_x_2715_);
return v_p_2714_;
}
else
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2714_, v_x_2715_);
return v___x_2724_;
}
}
else
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2714_, v_x_2715_);
return v___x_2725_;
}
}
else
{
lean_object* v_val_2726_; lean_object* v_coeffs_2727_; lean_object* v_constraint_2728_; lean_object* v_justification_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2744_; 
v_val_2726_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_val_2726_);
lean_dec_ref_known(v___x_2721_, 1);
v_coeffs_2727_ = lean_ctor_get(v_val_2726_, 0);
v_constraint_2728_ = lean_ctor_get(v_val_2726_, 1);
v_justification_2729_ = lean_ctor_get(v_val_2726_, 2);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_val_2726_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2731_ = v_val_2726_;
v_isShared_2732_ = v_isSharedCheck_2744_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_justification_2729_);
lean_inc(v_constraint_2728_);
lean_inc(v_coeffs_2727_);
lean_dec(v_val_2726_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2744_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2733_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc(v_coeffs_2717_);
v___x_2734_ = l_instDecidableEqList___redArg(v___x_2733_, v_coeffs_2717_, v_coeffs_2727_);
if (v___x_2734_ == 0)
{
lean_del_object(v___x_2731_);
lean_dec_ref(v_justification_2729_);
lean_dec_ref(v_constraint_2728_);
lean_dec_ref(v_x_2715_);
return v_p_2714_;
}
else
{
lean_object* v_r_2735_; uint8_t v___x_2736_; 
lean_inc_ref_n(v_constraint_2728_, 2);
lean_inc_ref(v_constraint_2718_);
v_r_2735_ = l_Lean_Omega_Constraint_combine(v_constraint_2718_, v_constraint_2728_);
lean_inc_ref(v_r_2735_);
v___x_2736_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2735_, v_constraint_2728_);
if (v___x_2736_ == 0)
{
uint8_t v___x_2737_; 
lean_inc_ref(v_constraint_2718_);
lean_inc_ref(v_r_2735_);
v___x_2737_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2735_, v_constraint_2718_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
lean_inc_ref(v_justification_2719_);
lean_inc_ref(v_constraint_2718_);
lean_inc_n(v_coeffs_2717_, 2);
lean_dec_ref(v_x_2715_);
v___x_2738_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_2738_, 0, v_constraint_2718_);
lean_ctor_set(v___x_2738_, 1, v_constraint_2728_);
lean_ctor_set(v___x_2738_, 2, v_coeffs_2717_);
lean_ctor_set(v___x_2738_, 3, v_justification_2719_);
lean_ctor_set(v___x_2738_, 4, v_justification_2729_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 2, v___x_2738_);
lean_ctor_set(v___x_2731_, 1, v_r_2735_);
lean_ctor_set(v___x_2731_, 0, v_coeffs_2717_);
v___x_2740_ = v___x_2731_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_coeffs_2717_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_r_2735_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2714_, v___x_2740_);
return v___x_2741_;
}
}
else
{
lean_object* v___x_2743_; 
lean_dec_ref(v_r_2735_);
lean_del_object(v___x_2731_);
lean_dec_ref(v_justification_2729_);
lean_dec_ref(v_constraint_2728_);
v___x_2743_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2714_, v_x_2715_);
return v___x_2743_;
}
}
else
{
lean_dec_ref(v_r_2735_);
lean_del_object(v___x_2731_);
lean_dec_ref(v_justification_2729_);
lean_dec_ref(v_constraint_2728_);
lean_dec_ref(v_x_2715_);
return v_p_2714_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(lean_object* v_00_u03b2_2745_, lean_object* v_m_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2746_, v_a_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___boxed(lean_object* v_00_u03b2_2749_, lean_object* v_m_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(v_00_u03b2_2749_, v_m_2750_, v_a_2751_);
lean_dec(v_a_2751_);
lean_dec_ref(v_m_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(lean_object* v_00_u03b2_2753_, lean_object* v_a_2754_, lean_object* v_x_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2754_, v_x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2757_, lean_object* v_a_2758_, lean_object* v_x_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(v_00_u03b2_2757_, v_a_2758_, v_x_2759_);
lean_dec(v_x_2759_);
lean_dec(v_a_2758_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(lean_object* v_x_2761_, lean_object* v_x_2762_){
_start:
{
if (lean_obj_tag(v_x_2762_) == 0)
{
return v_x_2761_;
}
else
{
if (lean_obj_tag(v_x_2761_) == 0)
{
lean_object* v_key_2763_; lean_object* v_tail_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_key_2763_ = lean_ctor_get(v_x_2762_, 0);
lean_inc_n(v_key_2763_, 2);
v_tail_2764_ = lean_ctor_get(v_x_2762_, 2);
lean_inc(v_tail_2764_);
lean_dec_ref_known(v_x_2762_, 3);
v___x_2765_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2763_);
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v_key_2763_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
v_x_2761_ = v___x_2767_;
v_x_2762_ = v_tail_2764_;
goto _start;
}
else
{
lean_object* v_val_2769_; lean_object* v_key_2770_; lean_object* v_tail_2771_; lean_object* v_fst_2772_; lean_object* v_snd_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2794_; 
v_val_2769_ = lean_ctor_get(v_x_2761_, 0);
lean_inc(v_val_2769_);
v_key_2770_ = lean_ctor_get(v_x_2762_, 0);
lean_inc(v_key_2770_);
v_tail_2771_ = lean_ctor_get(v_x_2762_, 2);
lean_inc(v_tail_2771_);
lean_dec_ref_known(v_x_2762_, 3);
v_fst_2772_ = lean_ctor_get(v_val_2769_, 0);
v_snd_2773_ = lean_ctor_get(v_val_2769_, 1);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_val_2769_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2775_ = v_val_2769_;
v_isShared_2776_ = v_isSharedCheck_2794_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_snd_2773_);
lean_inc(v_fst_2772_);
lean_dec(v_val_2769_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2794_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2777_ = lean_unsigned_to_nat(2u);
v___x_2778_ = lean_nat_dec_le(v___x_2777_, v_snd_2773_);
if (v___x_2778_ == 0)
{
lean_del_object(v___x_2775_);
lean_dec(v_snd_2773_);
lean_dec(v_fst_2772_);
lean_dec(v_key_2770_);
v_x_2762_ = v_tail_2771_;
goto _start;
}
else
{
lean_object* v_m_x27_2780_; uint8_t v___x_2787_; 
lean_inc(v_key_2770_);
v_m_x27_2780_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2770_);
v___x_2787_ = lean_nat_dec_lt(v_m_x27_2780_, v_snd_2773_);
if (v___x_2787_ == 0)
{
uint8_t v___x_2788_; 
v___x_2788_ = lean_nat_dec_eq(v_m_x27_2780_, v_snd_2773_);
lean_dec(v_snd_2773_);
if (v___x_2788_ == 0)
{
lean_dec(v_m_x27_2780_);
lean_del_object(v___x_2775_);
lean_dec(v_fst_2772_);
lean_dec(v_key_2770_);
v_x_2762_ = v_tail_2771_;
goto _start;
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
lean_inc(v_key_2770_);
v___x_2790_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_key_2770_);
v___x_2791_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_fst_2772_);
v___x_2792_ = lean_nat_dec_lt(v___x_2790_, v___x_2791_);
lean_dec(v___x_2791_);
lean_dec(v___x_2790_);
if (v___x_2792_ == 0)
{
lean_dec(v_m_x27_2780_);
lean_del_object(v___x_2775_);
lean_dec(v_key_2770_);
v_x_2762_ = v_tail_2771_;
goto _start;
}
else
{
lean_dec_ref_known(v_x_2761_, 1);
goto v___jp_2781_;
}
}
}
else
{
lean_dec(v_snd_2773_);
lean_dec(v_fst_2772_);
lean_dec_ref_known(v_x_2761_, 1);
goto v___jp_2781_;
}
v___jp_2781_:
{
lean_object* v___x_2783_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 1, v_m_x27_2780_);
lean_ctor_set(v___x_2775_, 0, v_key_2770_);
v___x_2783_ = v___x_2775_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_key_2770_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_m_x27_2780_);
v___x_2783_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
v_x_2761_ = v___x_2784_;
v_x_2762_ = v_tail_2771_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(lean_object* v_as_2795_, size_t v_i_2796_, size_t v_stop_2797_, lean_object* v_b_2798_){
_start:
{
uint8_t v___x_2799_; 
v___x_2799_ = lean_usize_dec_eq(v_i_2796_, v_stop_2797_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; lean_object* v___x_2801_; size_t v___x_2802_; size_t v___x_2803_; 
v___x_2800_ = lean_array_uget_borrowed(v_as_2795_, v_i_2796_);
lean_inc(v___x_2800_);
v___x_2801_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(v_b_2798_, v___x_2800_);
v___x_2802_ = ((size_t)1ULL);
v___x_2803_ = lean_usize_add(v_i_2796_, v___x_2802_);
v_i_2796_ = v___x_2803_;
v_b_2798_ = v___x_2801_;
goto _start;
}
else
{
return v_b_2798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1___boxed(lean_object* v_as_2805_, lean_object* v_i_2806_, lean_object* v_stop_2807_, lean_object* v_b_2808_){
_start:
{
size_t v_i_boxed_2809_; size_t v_stop_boxed_2810_; lean_object* v_res_2811_; 
v_i_boxed_2809_ = lean_unbox_usize(v_i_2806_);
lean_dec(v_i_2806_);
v_stop_boxed_2810_ = lean_unbox_usize(v_stop_2807_);
lean_dec(v_stop_2807_);
v_res_2811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_as_2805_, v_i_boxed_2809_, v_stop_boxed_2810_, v_b_2808_);
lean_dec_ref(v_as_2805_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality(lean_object* v_p_2812_){
_start:
{
lean_object* v_equalities_2813_; lean_object* v_buckets_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; 
v_equalities_2813_ = lean_ctor_get(v_p_2812_, 3);
v_buckets_2814_ = lean_ctor_get(v_equalities_2813_, 1);
v___x_2815_ = lean_box(0);
v___x_2816_ = lean_unsigned_to_nat(0u);
v___x_2817_ = lean_array_get_size(v_buckets_2814_);
v___x_2818_ = lean_nat_dec_lt(v___x_2816_, v___x_2817_);
if (v___x_2818_ == 0)
{
return v___x_2815_;
}
else
{
size_t v___x_2819_; size_t v___x_2820_; lean_object* v___x_2821_; 
v___x_2819_ = ((size_t)0ULL);
v___x_2820_ = lean_usize_of_nat(v___x_2817_);
v___x_2821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2814_, v___x_2819_, v___x_2820_, v___x_2815_);
return v___x_2821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality___boxed(lean_object* v_p_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_2822_);
lean_dec_ref(v_p_2822_);
return v_res_2823_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_unsigned_to_nat(1u);
v___x_2825_ = lean_nat_to_int(v___x_2824_);
return v___x_2825_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2827_ = lean_int_neg(v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(lean_object* v_as_2828_, size_t v_i_2829_, size_t v_stop_2830_, lean_object* v_b_2831_){
_start:
{
uint8_t v___x_2832_; 
v___x_2832_ = lean_usize_dec_eq(v_i_2829_, v_stop_2830_);
if (v___x_2832_ == 0)
{
size_t v___x_2833_; size_t v___x_2834_; lean_object* v___x_2835_; lean_object* v_snd_2836_; lean_object* v_fst_2837_; lean_object* v_fst_2838_; lean_object* v_snd_2839_; lean_object* v_coeffs_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2833_ = ((size_t)1ULL);
v___x_2834_ = lean_usize_sub(v_i_2829_, v___x_2833_);
v___x_2835_ = lean_array_uget_borrowed(v_as_2828_, v___x_2834_);
v_snd_2836_ = lean_ctor_get(v___x_2835_, 1);
v_fst_2837_ = lean_ctor_get(v___x_2835_, 0);
v_fst_2838_ = lean_ctor_get(v_snd_2836_, 0);
v_snd_2839_ = lean_ctor_get(v_snd_2836_, 1);
v_coeffs_2840_ = lean_ctor_get(v_b_2831_, 0);
lean_inc(v_fst_2838_);
v___x_2841_ = l_Lean_Omega_IntList_get(v_coeffs_2840_, v_fst_2838_);
v___x_2842_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2843_ = lean_int_dec_eq(v___x_2841_, v___x_2842_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2844_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2845_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2846_ = lean_int_mul(v___x_2845_, v_snd_2839_);
v___x_2847_ = lean_int_mul(v___x_2846_, v___x_2841_);
lean_dec(v___x_2841_);
lean_dec(v___x_2846_);
lean_inc(v_fst_2837_);
v___x_2848_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v___x_2847_, v_fst_2837_, v___x_2844_, v_b_2831_);
v_i_2829_ = v___x_2834_;
v_b_2831_ = v___x_2848_;
goto _start;
}
else
{
lean_dec(v___x_2841_);
v_i_2829_ = v___x_2834_;
goto _start;
}
}
else
{
return v_b_2831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___boxed(lean_object* v_as_2851_, lean_object* v_i_2852_, lean_object* v_stop_2853_, lean_object* v_b_2854_){
_start:
{
size_t v_i_boxed_2855_; size_t v_stop_boxed_2856_; lean_object* v_res_2857_; 
v_i_boxed_2855_ = lean_unbox_usize(v_i_2852_);
lean_dec(v_i_2852_);
v_stop_boxed_2856_ = lean_unbox_usize(v_stop_2853_);
lean_dec(v_stop_2853_);
v_res_2857_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v_as_2851_, v_i_boxed_2855_, v_stop_boxed_2856_, v_b_2854_);
lean_dec_ref(v_as_2851_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(lean_object* v_init_2858_, lean_object* v_l_2859_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2860_ = lean_array_mk(v_l_2859_);
v___x_2861_ = lean_array_get_size(v___x_2860_);
v___x_2862_ = lean_unsigned_to_nat(0u);
v___x_2863_ = lean_nat_dec_lt(v___x_2862_, v___x_2861_);
if (v___x_2863_ == 0)
{
lean_dec_ref(v___x_2860_);
return v_init_2858_;
}
else
{
size_t v___x_2864_; size_t v___x_2865_; lean_object* v___x_2866_; 
v___x_2864_ = lean_usize_of_nat(v___x_2861_);
v___x_2865_ = ((size_t)0ULL);
v___x_2866_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v___x_2860_, v___x_2864_, v___x_2865_, v_init_2858_);
lean_dec_ref(v___x_2860_);
return v___x_2866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(lean_object* v_p_2867_, lean_object* v_f_2868_){
_start:
{
lean_object* v_eliminations_2869_; lean_object* v___x_2870_; 
v_eliminations_2869_ = lean_ctor_get(v_p_2867_, 4);
lean_inc(v_eliminations_2869_);
lean_dec_ref(v_p_2867_);
v___x_2870_ = l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(v_f_2868_, v_eliminations_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__0(lean_object* v_x_2871_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(lean_object* v___y_2873_, lean_object* v_sign_2874_, lean_object* v_val_2875_, lean_object* v_x_2876_, lean_object* v_x_2877_){
_start:
{
if (lean_obj_tag(v_x_2877_) == 0)
{
lean_dec_ref(v_val_2875_);
lean_dec(v___y_2873_);
return v_x_2876_;
}
else
{
lean_object* v_key_2878_; lean_object* v_value_2879_; lean_object* v_tail_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v_key_2878_ = lean_ctor_get(v_x_2877_, 0);
lean_inc(v_key_2878_);
v_value_2879_ = lean_ctor_get(v_x_2877_, 1);
lean_inc(v_value_2879_);
v_tail_2880_ = lean_ctor_get(v_x_2877_, 2);
lean_inc(v_tail_2880_);
lean_dec_ref_known(v_x_2877_, 3);
lean_inc(v___y_2873_);
v___x_2881_ = l_Lean_Omega_IntList_get(v_key_2878_, v___y_2873_);
lean_dec(v_key_2878_);
v___x_2882_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2883_ = lean_int_dec_eq(v___x_2881_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v_k_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2884_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2885_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2886_ = lean_int_mul(v___x_2885_, v_sign_2874_);
v_k_2887_ = lean_int_mul(v___x_2886_, v___x_2881_);
lean_dec(v___x_2881_);
lean_dec(v___x_2886_);
lean_inc_ref(v_val_2875_);
v___x_2888_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_k_2887_, v_val_2875_, v___x_2884_, v_value_2879_);
v___x_2889_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_2888_);
v___x_2890_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2876_, v___x_2889_);
v_x_2876_ = v___x_2890_;
v_x_2877_ = v_tail_2880_;
goto _start;
}
else
{
lean_object* v___x_2892_; 
lean_dec(v___x_2881_);
v___x_2892_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2876_, v_value_2879_);
v_x_2876_ = v___x_2892_;
v_x_2877_ = v_tail_2880_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0___boxed(lean_object* v___y_2894_, lean_object* v_sign_2895_, lean_object* v_val_2896_, lean_object* v_x_2897_, lean_object* v_x_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2894_, v_sign_2895_, v_val_2896_, v_x_2897_, v_x_2898_);
lean_dec(v_sign_2895_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object* v___y_2900_, lean_object* v_sign_2901_, lean_object* v_val_2902_, lean_object* v_as_2903_, size_t v_i_2904_, size_t v_stop_2905_, lean_object* v_b_2906_){
_start:
{
uint8_t v___x_2907_; 
v___x_2907_ = lean_usize_dec_eq(v_i_2904_, v_stop_2905_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; lean_object* v___x_2909_; size_t v___x_2910_; size_t v___x_2911_; 
v___x_2908_ = lean_array_uget_borrowed(v_as_2903_, v_i_2904_);
lean_inc(v___x_2908_);
lean_inc_ref(v_val_2902_);
lean_inc(v___y_2900_);
v___x_2909_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2900_, v_sign_2901_, v_val_2902_, v_b_2906_, v___x_2908_);
v___x_2910_ = ((size_t)1ULL);
v___x_2911_ = lean_usize_add(v_i_2904_, v___x_2910_);
v_i_2904_ = v___x_2911_;
v_b_2906_ = v___x_2909_;
goto _start;
}
else
{
lean_dec_ref(v_val_2902_);
lean_dec(v___y_2900_);
return v_b_2906_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1___boxed(lean_object* v___y_2913_, lean_object* v_sign_2914_, lean_object* v_val_2915_, lean_object* v_as_2916_, lean_object* v_i_2917_, lean_object* v_stop_2918_, lean_object* v_b_2919_){
_start:
{
size_t v_i_boxed_2920_; size_t v_stop_boxed_2921_; lean_object* v_res_2922_; 
v_i_boxed_2920_ = lean_unbox_usize(v_i_2917_);
lean_dec(v_i_2917_);
v_stop_boxed_2921_ = lean_unbox_usize(v_stop_2918_);
lean_dec(v_stop_2918_);
v_res_2922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2913_, v_sign_2914_, v_val_2915_, v_as_2916_, v_i_boxed_2920_, v_stop_boxed_2921_, v_b_2919_);
lean_dec_ref(v_as_2916_);
lean_dec(v_sign_2914_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
if (lean_obj_tag(v_a_2923_) == 0)
{
lean_object* v___x_2925_; 
lean_dec(v_a_2924_);
v___x_2925_ = lean_box(0);
return v___x_2925_;
}
else
{
lean_object* v_head_2926_; lean_object* v_tail_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; uint8_t v___x_2930_; 
v_head_2926_ = lean_ctor_get(v_a_2923_, 0);
v_tail_2927_ = lean_ctor_get(v_a_2923_, 1);
v___x_2928_ = lean_nat_abs(v_head_2926_);
v___x_2929_ = lean_unsigned_to_nat(1u);
v___x_2930_ = lean_nat_dec_eq(v___x_2928_, v___x_2929_);
lean_dec(v___x_2928_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; 
v___x_2931_ = lean_nat_add(v_a_2924_, v___x_2929_);
lean_dec(v_a_2924_);
v_a_2923_ = v_tail_2927_;
v_a_2924_ = v___x_2931_;
goto _start;
}
else
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2933_, 0, v_a_2924_);
return v___x_2933_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2___boxed(lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(v_a_2934_, v_a_2935_);
lean_dec(v_a_2934_);
return v_res_2936_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1(void){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_unsigned_to_nat(16u);
v___x_2940_ = lean_mk_array(v___x_2939_, v___x_2938_);
return v___x_2940_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2941_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1);
v___x_2942_ = lean_unsigned_to_nat(0u);
v___x_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
lean_ctor_set(v___x_2943_, 1, v___x_2941_);
return v___x_2943_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3(void){
_start:
{
lean_object* v___f_2944_; lean_object* v___x_2945_; 
v___f_2944_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0));
v___x_2945_ = lean_mk_thunk(v___f_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(lean_object* v_p_2946_, lean_object* v_c_2947_){
_start:
{
lean_object* v___y_2949_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_unsigned_to_nat(0u);
v___x_2993_ = l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(v_c_2947_, v___x_2992_);
if (lean_obj_tag(v___x_2993_) == 0)
{
v___y_2949_ = v___x_2992_;
goto v___jp_2948_;
}
else
{
lean_object* v_val_2994_; 
v_val_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_val_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v___y_2949_ = v_val_2994_;
goto v___jp_2948_;
}
v___jp_2948_:
{
lean_object* v_assumptions_2950_; lean_object* v_constraints_2951_; lean_object* v_eliminations_2952_; lean_object* v___x_2953_; 
v_assumptions_2950_ = lean_ctor_get(v_p_2946_, 0);
v_constraints_2951_ = lean_ctor_get(v_p_2946_, 2);
lean_inc_ref(v_constraints_2951_);
v_eliminations_2952_ = lean_ctor_get(v_p_2946_, 4);
v___x_2953_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2951_, v_c_2947_);
if (lean_obj_tag(v___x_2953_) == 1)
{
lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2984_; 
lean_inc(v_eliminations_2952_);
lean_inc_ref(v_assumptions_2950_);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_p_2946_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; lean_object* v_unused_2986_; lean_object* v_unused_2987_; lean_object* v_unused_2988_; lean_object* v_unused_2989_; lean_object* v_unused_2990_; lean_object* v_unused_2991_; 
v_unused_2985_ = lean_ctor_get(v_p_2946_, 6);
lean_dec(v_unused_2985_);
v_unused_2986_ = lean_ctor_get(v_p_2946_, 5);
lean_dec(v_unused_2986_);
v_unused_2987_ = lean_ctor_get(v_p_2946_, 4);
lean_dec(v_unused_2987_);
v_unused_2988_ = lean_ctor_get(v_p_2946_, 3);
lean_dec(v_unused_2988_);
v_unused_2989_ = lean_ctor_get(v_p_2946_, 2);
lean_dec(v_unused_2989_);
v_unused_2990_ = lean_ctor_get(v_p_2946_, 1);
lean_dec(v_unused_2990_);
v_unused_2991_ = lean_ctor_get(v_p_2946_, 0);
lean_dec(v_unused_2991_);
v___x_2955_ = v_p_2946_;
v_isShared_2956_ = v_isSharedCheck_2984_;
goto v_resetjp_2954_;
}
else
{
lean_dec(v_p_2946_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2984_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_val_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v_buckets_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2982_; 
v_val_2957_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_val_2957_);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2958_ = lean_unsigned_to_nat(0u);
v___x_2959_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v_buckets_2960_ = lean_ctor_get(v_constraints_2951_, 1);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_constraints_2951_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v_constraints_2951_, 0);
lean_dec(v_unused_2983_);
v___x_2962_ = v_constraints_2951_;
v_isShared_2963_ = v_isSharedCheck_2982_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_buckets_2960_);
lean_dec(v_constraints_2951_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2982_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; lean_object* v_sign_2965_; lean_object* v___x_2967_; 
lean_inc_n(v___y_2949_, 2);
v___x_2964_ = l_Lean_Omega_IntList_get(v_c_2947_, v___y_2949_);
v_sign_2965_ = l_Int_sign(v___x_2964_);
lean_dec(v___x_2964_);
lean_inc(v_sign_2965_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 1, v_sign_2965_);
lean_ctor_set(v___x_2962_, 0, v___y_2949_);
v___x_2967_ = v___x_2962_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___y_2949_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_sign_2965_);
v___x_2967_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v_init_2974_; 
lean_inc(v_val_2957_);
v___x_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2968_, 0, v_val_2957_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
lean_ctor_set(v___x_2969_, 1, v_eliminations_2952_);
v___x_2970_ = 1;
v___x_2971_ = lean_box(0);
v___x_2972_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 6, v___x_2972_);
lean_ctor_set(v___x_2955_, 5, v___x_2971_);
lean_ctor_set(v___x_2955_, 4, v___x_2969_);
lean_ctor_set(v___x_2955_, 3, v___x_2959_);
lean_ctor_set(v___x_2955_, 2, v___x_2959_);
lean_ctor_set(v___x_2955_, 1, v___x_2958_);
v_init_2974_ = v___x_2955_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_assumptions_2950_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_2980_, 2, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_2980_, 3, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_2980_, 4, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2980_, 5, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_2980_, 6, v___x_2972_);
v_init_2974_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; uint8_t v___x_2976_; 
lean_ctor_set_uint8(v_init_2974_, sizeof(void*)*7, v___x_2970_);
v___x_2975_ = lean_array_get_size(v_buckets_2960_);
v___x_2976_ = lean_nat_dec_lt(v___x_2958_, v___x_2975_);
if (v___x_2976_ == 0)
{
lean_dec(v_sign_2965_);
lean_dec_ref(v_buckets_2960_);
lean_dec(v_val_2957_);
lean_dec(v___y_2949_);
return v_init_2974_;
}
else
{
size_t v___x_2977_; size_t v___x_2978_; lean_object* v___x_2979_; 
v___x_2977_ = ((size_t)0ULL);
v___x_2978_ = lean_usize_of_nat(v___x_2975_);
v___x_2979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2949_, v_sign_2965_, v_val_2957_, v_buckets_2960_, v___x_2977_, v___x_2978_, v_init_2974_);
lean_dec_ref(v_buckets_2960_);
lean_dec(v_sign_2965_);
return v___x_2979_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2953_);
lean_dec_ref(v_constraints_2951_);
lean_dec(v___y_2949_);
return v_p_2946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___boxed(lean_object* v_p_2995_, lean_object* v_c_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_2995_, v_c_2996_);
lean_dec(v_c_2996_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(lean_object* v_msgData_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v___x_3004_; lean_object* v_env_3005_; lean_object* v___x_3006_; lean_object* v_toCold_3007_; lean_object* v_mctx_3008_; lean_object* v_lctx_3009_; lean_object* v_options_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3004_ = lean_st_ref_get(v___y_3002_);
v_env_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc_ref(v_env_3005_);
lean_dec(v___x_3004_);
v___x_3006_ = lean_st_ref_get(v___y_3000_);
v_toCold_3007_ = lean_ctor_get(v___y_3001_, 0);
v_mctx_3008_ = lean_ctor_get(v___x_3006_, 0);
lean_inc_ref(v_mctx_3008_);
lean_dec(v___x_3006_);
v_lctx_3009_ = lean_ctor_get(v___y_2999_, 2);
v_options_3010_ = lean_ctor_get(v_toCold_3007_, 2);
lean_inc_ref(v_options_3010_);
lean_inc_ref(v_lctx_3009_);
v___x_3011_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3011_, 0, v_env_3005_);
lean_ctor_set(v___x_3011_, 1, v_mctx_3008_);
lean_ctor_set(v___x_3011_, 2, v_lctx_3009_);
lean_ctor_set(v___x_3011_, 3, v_options_3010_);
v___x_3012_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
lean_ctor_set(v___x_3012_, 1, v_msgData_2998_);
v___x_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0___boxed(lean_object* v_msgData_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msgData_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(lean_object* v_msg_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_ref_3027_; lean_object* v___x_3028_; lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3037_; 
v_ref_3027_ = lean_ctor_get(v___y_3024_, 2);
v___x_3028_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3037_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3037_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3033_; lean_object* v___x_3035_; 
lean_inc(v_ref_3027_);
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v_ref_3027_);
lean_ctor_set(v___x_3033_, 1, v_a_3029_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set_tag(v___x_3031_, 1);
lean_ctor_set(v___x_3031_, 0, v___x_3033_);
v___x_3035_ = v___x_3031_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg___boxed(lean_object* v_msg_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
return v_res_3044_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0));
v___x_3047_ = l_Lean_stringToMessageData(v___x_3046_);
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2));
v___x_3050_ = l_Lean_stringToMessageData(v___x_3049_);
return v___x_3050_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4));
v___x_3053_ = l_Lean_stringToMessageData(v___x_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(lean_object* v_p_3054_, lean_object* v_c_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, uint8_t v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_constraints_3066_; lean_object* v___x_3067_; 
v_constraints_3066_ = lean_ctor_get(v_p_3054_, 2);
v___x_3067_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_3066_, v_c_3055_);
if (lean_obj_tag(v___x_3067_) == 1)
{
lean_object* v_val_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3167_; 
v_val_3068_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3070_ = v___x_3067_;
v_isShared_3071_ = v_isSharedCheck_3167_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_val_3068_);
lean_dec(v___x_3067_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3167_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v_constraint_3072_; lean_object* v_lowerBound_3073_; 
v_constraint_3072_ = lean_ctor_get(v_val_3068_, 1);
v_lowerBound_3073_ = lean_ctor_get(v_constraint_3072_, 0);
lean_inc(v_lowerBound_3073_);
if (lean_obj_tag(v_lowerBound_3073_) == 1)
{
lean_object* v_upperBound_3074_; 
lean_del_object(v___x_3070_);
v_upperBound_3074_ = lean_ctor_get(v_constraint_3072_, 1);
lean_inc(v_upperBound_3074_);
if (lean_obj_tag(v_upperBound_3074_) == 1)
{
lean_object* v_coeffs_3075_; lean_object* v_justification_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3154_; 
v_coeffs_3075_ = lean_ctor_get(v_val_3068_, 0);
v_justification_3076_ = lean_ctor_get(v_val_3068_, 2);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_val_3068_);
if (v_isSharedCheck_3154_ == 0)
{
lean_object* v_unused_3155_; 
v_unused_3155_ = lean_ctor_get(v_val_3068_, 1);
lean_dec(v_unused_3155_);
v___x_3078_ = v_val_3068_;
v_isShared_3079_ = v_isSharedCheck_3154_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_justification_3076_);
lean_inc(v_coeffs_3075_);
lean_dec(v_val_3068_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3154_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v_val_3080_; lean_object* v_val_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v_m_3084_; lean_object* v___x_3085_; 
v_val_3080_ = lean_ctor_get(v_lowerBound_3073_, 0);
lean_inc(v_val_3080_);
lean_dec_ref_known(v_lowerBound_3073_, 1);
v_val_3081_ = lean_ctor_get(v_upperBound_3074_, 0);
lean_inc(v_val_3081_);
lean_dec_ref_known(v_upperBound_3074_, 1);
lean_inc(v_c_3055_);
v___x_3082_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_c_3055_);
v___x_3083_ = lean_unsigned_to_nat(1u);
v_m_3084_ = lean_nat_add(v___x_3082_, v___x_3083_);
lean_dec(v___x_3082_);
v___x_3085_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3057_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v_nil_3089_; lean_object* v_cons_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3085_, 1);
v___x_3087_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc(v_m_3084_);
v___x_3088_ = l_Lean_mkNatLit(v_m_3084_);
v_nil_3089_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3090_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3091_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3089_, v_cons_3090_, v_c_3055_);
lean_dec(v_c_3055_);
v___x_3092_ = l_Lean_mkApp3(v___x_3087_, v___x_3088_, v___x_3091_, v_a_3086_);
v___x_3093_ = l_Lean_Elab_Tactic_Omega_lookup(v___x_3092_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3137_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3137_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3137_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v_fst_3098_; lean_object* v_snd_3099_; uint8_t v___x_3112_; 
v_fst_3098_ = lean_ctor_get(v_a_3094_, 0);
lean_inc(v_fst_3098_);
v_snd_3099_ = lean_ctor_get(v_a_3094_, 1);
lean_inc(v_snd_3099_);
lean_dec(v_a_3094_);
v___x_3112_ = lean_int_dec_eq(v_val_3081_, v_val_3080_);
lean_dec(v_val_3081_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_dec(v_snd_3099_);
lean_dec(v_fst_3098_);
lean_del_object(v___x_3096_);
lean_dec(v_m_3084_);
lean_dec(v_val_3080_);
lean_del_object(v___x_3078_);
lean_dec_ref(v_justification_3076_);
lean_dec(v_coeffs_3075_);
lean_dec_ref(v_p_3054_);
v___x_3113_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1);
v___x_3114_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3113_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
return v___x_3114_;
}
else
{
if (lean_obj_tag(v_snd_3099_) == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec(v_fst_3098_);
lean_del_object(v___x_3096_);
lean_dec(v_m_3084_);
lean_dec(v_val_3080_);
lean_del_object(v___x_3078_);
lean_dec_ref(v_justification_3076_);
lean_dec(v_coeffs_3075_);
lean_dec_ref(v_p_3054_);
v___x_3115_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3);
v___x_3116_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3115_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3116_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3116_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
else
{
lean_object* v_val_3125_; uint8_t v___x_3126_; 
v_val_3125_ = lean_ctor_get(v_snd_3099_, 0);
lean_inc(v_val_3125_);
lean_dec_ref_known(v_snd_3099_, 1);
v___x_3126_ = l_List_isEmpty___redArg(v_val_3125_);
lean_dec(v_val_3125_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_fst_3098_);
lean_del_object(v___x_3096_);
lean_dec(v_m_3084_);
lean_dec(v_val_3080_);
lean_del_object(v___x_3078_);
lean_dec_ref(v_justification_3076_);
lean_dec(v_coeffs_3075_);
lean_dec_ref(v_p_3054_);
v___x_3127_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5);
v___x_3128_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3127_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3128_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3128_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
else
{
goto v___jp_3100_;
}
}
}
v___jp_3100_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3106_; 
lean_inc(v_coeffs_3075_);
lean_inc_n(v_m_3084_, 2);
v___x_3101_ = l_Lean_Omega_bmod__coeffs(v_m_3084_, v_fst_3098_, v_coeffs_3075_);
v___x_3102_ = l_Int_bmod(v_val_3080_, v_m_3084_);
v___x_3103_ = l_Lean_Omega_Constraint_exact(v___x_3102_);
v___x_3104_ = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(v___x_3104_, 0, v_m_3084_);
lean_ctor_set(v___x_3104_, 1, v_val_3080_);
lean_ctor_set(v___x_3104_, 2, v_fst_3098_);
lean_ctor_set(v___x_3104_, 3, v_coeffs_3075_);
lean_ctor_set(v___x_3104_, 4, v_justification_3076_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 2, v___x_3104_);
lean_ctor_set(v___x_3078_, 1, v___x_3103_);
lean_ctor_set(v___x_3078_, 0, v___x_3101_);
v___x_3106_ = v___x_3078_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3111_, 2, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
v___x_3107_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_3054_, v___x_3106_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3107_);
v___x_3109_ = v___x_3096_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec(v_m_3084_);
lean_dec(v_val_3081_);
lean_dec(v_val_3080_);
lean_del_object(v___x_3078_);
lean_dec_ref(v_justification_3076_);
lean_dec(v_coeffs_3075_);
lean_dec_ref(v_p_3054_);
v_a_3138_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3093_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3093_);
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
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec(v_m_3084_);
lean_dec(v_val_3081_);
lean_dec(v_val_3080_);
lean_del_object(v___x_3078_);
lean_dec_ref(v_justification_3076_);
lean_dec(v_coeffs_3075_);
lean_dec(v_c_3055_);
lean_dec_ref(v_p_3054_);
v_a_3146_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3085_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3085_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
}
else
{
lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec(v_upperBound_3074_);
lean_dec(v_val_3068_);
lean_dec(v_c_3055_);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_lowerBound_3073_);
if (v_isSharedCheck_3162_ == 0)
{
lean_object* v_unused_3163_; 
v_unused_3163_ = lean_ctor_get(v_lowerBound_3073_, 0);
lean_dec(v_unused_3163_);
v___x_3157_ = v_lowerBound_3073_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_dec(v_lowerBound_3073_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
lean_ctor_set_tag(v___x_3157_, 0);
lean_ctor_set(v___x_3157_, 0, v_p_3054_);
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_p_3054_);
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
else
{
lean_object* v___x_3165_; 
lean_dec(v_lowerBound_3073_);
lean_dec(v_val_3068_);
lean_dec(v_c_3055_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set_tag(v___x_3070_, 0);
lean_ctor_set(v___x_3070_, 0, v_p_3054_);
v___x_3165_ = v___x_3070_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_p_3054_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_object* v___x_3168_; 
lean_dec(v___x_3067_);
lean_dec(v_c_3055_);
v___x_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3168_, 0, v_p_3054_);
return v___x_3168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___boxed(lean_object* v_p_3169_, lean_object* v_c_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_){
_start:
{
uint8_t v_a_boxed_3181_; lean_object* v_res_3182_; 
v_a_boxed_3181_ = lean_unbox(v_a_3174_);
v_res_3182_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3169_, v_c_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_boxed_3181_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_a_3175_);
lean_dec_ref(v_a_3173_);
lean_dec(v_a_3172_);
lean_dec(v_a_3171_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_object* v_00_u03b1_3183_, lean_object* v_msg_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, uint8_t v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3184_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___boxed(lean_object* v_00_u03b1_3196_, lean_object* v_msg_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
uint8_t v___y_9312__boxed_3208_; lean_object* v_res_3209_; 
v___y_9312__boxed_3208_ = lean_unbox(v___y_3201_);
v_res_3209_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(v_00_u03b1_3196_, v_msg_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_9312__boxed_3208_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec(v___y_3198_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality(lean_object* v_p_3210_, lean_object* v_c_3211_, lean_object* v_m_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, uint8_t v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v___x_3223_; uint8_t v___x_3224_; 
v___x_3223_ = lean_unsigned_to_nat(1u);
v___x_3224_ = lean_nat_dec_eq(v_m_3212_, v___x_3223_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3210_, v_c_3211_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
return v___x_3225_;
}
else
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_3210_, v_c_3211_);
lean_dec(v_c_3211_);
v___x_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
return v___x_3227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality___boxed(lean_object* v_p_3228_, lean_object* v_c_3229_, lean_object* v_m_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
uint8_t v_a_boxed_3241_; lean_object* v_res_3242_; 
v_a_boxed_3241_ = lean_unbox(v_a_3234_);
v_res_3242_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3228_, v_c_3229_, v_m_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_boxed_3241_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
lean_dec(v_a_3239_);
lean_dec_ref(v_a_3238_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3233_);
lean_dec(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec(v_m_3230_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(lean_object* v_p_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, uint8_t v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
uint8_t v_possible_3254_; 
v_possible_3254_ = lean_ctor_get_uint8(v_p_3243_, sizeof(void*)*7);
if (v_possible_3254_ == 0)
{
lean_object* v___x_3255_; 
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v_p_3243_);
return v___x_3255_;
}
else
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_3243_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_p_3243_);
return v___x_3257_;
}
else
{
lean_object* v_val_3258_; lean_object* v_fst_3259_; lean_object* v_snd_3260_; lean_object* v___x_3261_; 
v_val_3258_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_val_3258_);
lean_dec_ref_known(v___x_3256_, 1);
v_fst_3259_ = lean_ctor_get(v_val_3258_, 0);
lean_inc(v_fst_3259_);
v_snd_3260_ = lean_ctor_get(v_val_3258_, 1);
lean_inc(v_snd_3260_);
lean_dec(v_val_3258_);
v___x_3261_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3243_, v_fst_3259_, v_snd_3260_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
lean_dec(v_snd_3260_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v_a_3262_; 
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_a_3262_);
lean_dec_ref_known(v___x_3261_, 1);
v_p_3243_ = v_a_3262_;
goto _start;
}
else
{
return v___x_3261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities___boxed(lean_object* v_p_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_){
_start:
{
uint8_t v_a_boxed_3275_; lean_object* v_res_3276_; 
v_a_boxed_3275_ = lean_unbox(v_a_3268_);
v_res_3276_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_boxed_3275_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_);
lean_dec(v_a_3273_);
lean_dec_ref(v_a_3272_);
lean_dec(v_a_3271_);
lean_dec_ref(v_a_3270_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec(v_a_3265_);
return v_res_3276_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2(void){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3283_ = lean_box(0);
v___x_3284_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1));
v___x_3285_ = l_Lean_Expr_const___override(v___x_3284_, v___x_3283_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object* v_c_3286_, lean_object* v_x_3287_, lean_object* v_p_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, uint8_t v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3290_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3299_, 1);
v___x_3301_ = lean_box(v_a_3292_);
lean_inc(v_a_3297_);
lean_inc_ref(v_a_3296_);
lean_inc(v_a_3295_);
lean_inc_ref(v_a_3294_);
lean_inc(v_a_3293_);
lean_inc_ref(v_a_3291_);
lean_inc(v_a_3290_);
lean_inc(v_a_3289_);
v___x_3302_ = lean_apply_10(v_p_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v___x_3301_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, lean_box(0));
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3328_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3305_ = v___x_3302_;
v_isShared_3306_ = v_isSharedCheck_3328_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3302_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3328_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3307_; lean_object* v___y_3309_; lean_object* v___x_3317_; uint8_t v___x_3318_; 
v___x_3307_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2);
v___x_3317_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3318_ = lean_int_dec_le(v___x_3317_, v_c_3286_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3319_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3320_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3321_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3322_ = lean_int_neg(v_c_3286_);
v___x_3323_ = l_Int_toNat(v___x_3322_);
lean_dec(v___x_3322_);
v___x_3324_ = l_Lean_instToExprInt_mkNat(v___x_3323_);
v___x_3325_ = l_Lean_mkApp3(v___x_3319_, v___x_3320_, v___x_3321_, v___x_3324_);
v___y_3309_ = v___x_3325_;
goto v___jp_3308_;
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = l_Int_toNat(v_c_3286_);
v___x_3327_ = l_Lean_instToExprInt_mkNat(v___x_3326_);
v___y_3309_ = v___x_3327_;
goto v___jp_3308_;
}
v___jp_3308_:
{
lean_object* v_nil_3310_; lean_object* v_cons_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v_nil_3310_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3311_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3312_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3310_, v_cons_3311_, v_x_3287_);
v___x_3313_ = l_Lean_mkApp4(v___x_3307_, v___y_3309_, v___x_3312_, v_a_3300_, v_a_3303_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set(v___x_3305_, 0, v___x_3313_);
v___x_3315_ = v___x_3305_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
else
{
lean_dec(v_a_3300_);
return v___x_3302_;
}
}
else
{
lean_dec_ref(v_p_3288_);
return v___x_3299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object* v_c_3329_, lean_object* v_x_3330_, lean_object* v_p_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
uint8_t v_a_boxed_3342_; lean_object* v_res_3343_; 
v_a_boxed_3342_ = lean_unbox(v_a_3335_);
v_res_3343_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(v_c_3329_, v_x_3330_, v_p_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_boxed_3342_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3339_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3334_);
lean_dec(v_a_3333_);
lean_dec(v_a_3332_);
lean_dec(v_x_3330_);
lean_dec(v_c_3329_);
return v_res_3343_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = lean_box(0);
v___x_3351_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1));
v___x_3352_ = l_Lean_Expr_const___override(v___x_3351_, v___x_3350_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(lean_object* v_c_3353_, lean_object* v_x_3354_, lean_object* v_p_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, uint8_t v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v___x_3366_; 
v___x_3366_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3357_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
lean_dec_ref_known(v___x_3366_, 1);
v___x_3368_ = lean_box(v_a_3359_);
lean_inc(v_a_3364_);
lean_inc_ref(v_a_3363_);
lean_inc(v_a_3362_);
lean_inc_ref(v_a_3361_);
lean_inc(v_a_3360_);
lean_inc_ref(v_a_3358_);
lean_inc(v_a_3357_);
lean_inc(v_a_3356_);
v___x_3369_ = lean_apply_10(v_p_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v___x_3368_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, lean_box(0));
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3395_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3372_ = v___x_3369_;
v_isShared_3373_ = v_isSharedCheck_3395_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3369_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3395_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3374_; lean_object* v___y_3376_; lean_object* v___x_3384_; uint8_t v___x_3385_; 
v___x_3374_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2);
v___x_3384_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3385_ = lean_int_dec_le(v___x_3384_, v_c_3353_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3386_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3387_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3388_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3389_ = lean_int_neg(v_c_3353_);
v___x_3390_ = l_Int_toNat(v___x_3389_);
lean_dec(v___x_3389_);
v___x_3391_ = l_Lean_instToExprInt_mkNat(v___x_3390_);
v___x_3392_ = l_Lean_mkApp3(v___x_3386_, v___x_3387_, v___x_3388_, v___x_3391_);
v___y_3376_ = v___x_3392_;
goto v___jp_3375_;
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = l_Int_toNat(v_c_3353_);
v___x_3394_ = l_Lean_instToExprInt_mkNat(v___x_3393_);
v___y_3376_ = v___x_3394_;
goto v___jp_3375_;
}
v___jp_3375_:
{
lean_object* v_nil_3377_; lean_object* v_cons_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3382_; 
v_nil_3377_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3378_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3379_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3377_, v_cons_3378_, v_x_3354_);
v___x_3380_ = l_Lean_mkApp4(v___x_3374_, v___y_3376_, v___x_3379_, v_a_3367_, v_a_3370_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___x_3380_);
v___x_3382_ = v___x_3372_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_dec(v_a_3367_);
return v___x_3369_;
}
}
else
{
lean_dec_ref(v_p_3355_);
return v___x_3366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed(lean_object* v_c_3396_, lean_object* v_x_3397_, lean_object* v_p_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
uint8_t v_a_boxed_3409_; lean_object* v_res_3410_; 
v_a_boxed_3409_ = lean_unbox(v_a_3402_);
v_res_3410_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(v_c_3396_, v_x_3397_, v_p_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_boxed_3409_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3401_);
lean_dec(v_a_3400_);
lean_dec(v_a_3399_);
lean_dec(v_x_3397_);
lean_dec(v_c_3396_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(lean_object* v_prf_x3f_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, uint8_t v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
if (lean_obj_tag(v_prf_x3f_3411_) == 0)
{
lean_object* v___x_3422_; uint8_t v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3422_ = lean_box(0);
v___x_3423_ = 0;
v___x_3424_ = lean_box(0);
v___x_3425_ = l_Lean_Meta_mkFreshExprMVar(v___x_3422_, v___x_3423_, v___x_3424_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; uint8_t v___x_3427_; lean_object* v___x_3428_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v___x_3427_ = 0;
v___x_3428_ = l_Lean_Meta_mkSorry(v_a_3426_, v___x_3427_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
return v___x_3428_;
}
else
{
return v___x_3425_;
}
}
else
{
lean_object* v_val_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v_val_3429_ = lean_ctor_get(v_prf_x3f_3411_, 0);
lean_inc(v_val_3429_);
lean_dec_ref_known(v_prf_x3f_3411_, 1);
v___x_3430_ = lean_box(v___y_3415_);
lean_inc(v___y_3420_);
lean_inc_ref(v___y_3419_);
lean_inc(v___y_3418_);
lean_inc_ref(v___y_3417_);
lean_inc(v___y_3416_);
lean_inc_ref(v___y_3414_);
lean_inc(v___y_3413_);
lean_inc(v___y_3412_);
v___x_3431_ = lean_apply_10(v_val_3429_, v___y_3412_, v___y_3413_, v___y_3414_, v___x_3430_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, lean_box(0));
return v___x_3431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed(lean_object* v_prf_x3f_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
uint8_t v___y_833__boxed_3443_; lean_object* v_res_3444_; 
v___y_833__boxed_3443_ = lean_unbox(v___y_3436_);
v_res_3444_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(v_prf_x3f_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_833__boxed_3443_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec(v___y_3433_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality(lean_object* v_p_3445_, lean_object* v_const_3446_, lean_object* v_coeffs_3447_, lean_object* v_prf_x3f_3448_){
_start:
{
lean_object* v_assumptions_3449_; lean_object* v_numVars_3450_; lean_object* v_constraints_3451_; lean_object* v_equalities_3452_; lean_object* v_eliminations_3453_; uint8_t v_possible_3454_; lean_object* v_proveFalse_x3f_3455_; lean_object* v_explanation_x3f_3456_; lean_object* v_prf_3457_; lean_object* v_i_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v_p_x27_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v_f_3467_; lean_object* v_f_3468_; lean_object* v_f_3469_; lean_object* v___x_3470_; 
v_assumptions_3449_ = lean_ctor_get(v_p_3445_, 0);
v_numVars_3450_ = lean_ctor_get(v_p_3445_, 1);
v_constraints_3451_ = lean_ctor_get(v_p_3445_, 2);
v_equalities_3452_ = lean_ctor_get(v_p_3445_, 3);
v_eliminations_3453_ = lean_ctor_get(v_p_3445_, 4);
v_possible_3454_ = lean_ctor_get_uint8(v_p_3445_, sizeof(void*)*7);
v_proveFalse_x3f_3455_ = lean_ctor_get(v_p_3445_, 5);
v_explanation_x3f_3456_ = lean_ctor_get(v_p_3445_, 6);
v_prf_3457_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3457_, 0, v_prf_x3f_3448_);
v_i_3458_ = lean_array_get_size(v_assumptions_3449_);
lean_inc_n(v_coeffs_3447_, 2);
lean_inc(v_const_3446_);
v___x_3459_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed), 13, 3);
lean_closure_set(v___x_3459_, 0, v_const_3446_);
lean_closure_set(v___x_3459_, 1, v_coeffs_3447_);
lean_closure_set(v___x_3459_, 2, v_prf_3457_);
lean_inc_ref(v_assumptions_3449_);
v___x_3460_ = lean_array_push(v_assumptions_3449_, v___x_3459_);
lean_inc_ref(v_explanation_x3f_3456_);
lean_inc(v_proveFalse_x3f_3455_);
lean_inc(v_eliminations_3453_);
lean_inc_ref(v_equalities_3452_);
lean_inc_ref(v_constraints_3451_);
lean_inc(v_numVars_3450_);
v_p_x27_3461_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3461_, 0, v___x_3460_);
lean_ctor_set(v_p_x27_3461_, 1, v_numVars_3450_);
lean_ctor_set(v_p_x27_3461_, 2, v_constraints_3451_);
lean_ctor_set(v_p_x27_3461_, 3, v_equalities_3452_);
lean_ctor_set(v_p_x27_3461_, 4, v_eliminations_3453_);
lean_ctor_set(v_p_x27_3461_, 5, v_proveFalse_x3f_3455_);
lean_ctor_set(v_p_x27_3461_, 6, v_explanation_x3f_3456_);
lean_ctor_set_uint8(v_p_x27_3461_, sizeof(void*)*7, v_possible_3454_);
v___x_3462_ = lean_int_neg(v_const_3446_);
lean_dec(v_const_3446_);
v___x_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
v___x_3464_ = lean_box(0);
v___x_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3463_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
lean_inc_ref(v___x_3465_);
v___x_3466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
lean_ctor_set(v___x_3466_, 1, v_coeffs_3447_);
lean_ctor_set(v___x_3466_, 2, v_i_3458_);
v_f_3467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3467_, 0, v_coeffs_3447_);
lean_ctor_set(v_f_3467_, 1, v___x_3465_);
lean_ctor_set(v_f_3467_, 2, v___x_3466_);
v_f_3468_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3445_, v_f_3467_);
v_f_3469_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3468_);
v___x_3470_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3461_, v_f_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality(lean_object* v_p_3471_, lean_object* v_const_3472_, lean_object* v_coeffs_3473_, lean_object* v_prf_x3f_3474_){
_start:
{
lean_object* v_assumptions_3475_; lean_object* v_numVars_3476_; lean_object* v_constraints_3477_; lean_object* v_equalities_3478_; lean_object* v_eliminations_3479_; uint8_t v_possible_3480_; lean_object* v_proveFalse_x3f_3481_; lean_object* v_explanation_x3f_3482_; lean_object* v_prf_3483_; lean_object* v_i_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v_p_x27_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v_f_3492_; lean_object* v_f_3493_; lean_object* v_f_3494_; lean_object* v___x_3495_; 
v_assumptions_3475_ = lean_ctor_get(v_p_3471_, 0);
v_numVars_3476_ = lean_ctor_get(v_p_3471_, 1);
v_constraints_3477_ = lean_ctor_get(v_p_3471_, 2);
v_equalities_3478_ = lean_ctor_get(v_p_3471_, 3);
v_eliminations_3479_ = lean_ctor_get(v_p_3471_, 4);
v_possible_3480_ = lean_ctor_get_uint8(v_p_3471_, sizeof(void*)*7);
v_proveFalse_x3f_3481_ = lean_ctor_get(v_p_3471_, 5);
v_explanation_x3f_3482_ = lean_ctor_get(v_p_3471_, 6);
v_prf_3483_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3483_, 0, v_prf_x3f_3474_);
v_i_3484_ = lean_array_get_size(v_assumptions_3475_);
lean_inc_n(v_coeffs_3473_, 2);
lean_inc(v_const_3472_);
v___x_3485_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed), 13, 3);
lean_closure_set(v___x_3485_, 0, v_const_3472_);
lean_closure_set(v___x_3485_, 1, v_coeffs_3473_);
lean_closure_set(v___x_3485_, 2, v_prf_3483_);
lean_inc_ref(v_assumptions_3475_);
v___x_3486_ = lean_array_push(v_assumptions_3475_, v___x_3485_);
lean_inc_ref(v_explanation_x3f_3482_);
lean_inc(v_proveFalse_x3f_3481_);
lean_inc(v_eliminations_3479_);
lean_inc_ref(v_equalities_3478_);
lean_inc_ref(v_constraints_3477_);
lean_inc(v_numVars_3476_);
v_p_x27_3487_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3487_, 0, v___x_3486_);
lean_ctor_set(v_p_x27_3487_, 1, v_numVars_3476_);
lean_ctor_set(v_p_x27_3487_, 2, v_constraints_3477_);
lean_ctor_set(v_p_x27_3487_, 3, v_equalities_3478_);
lean_ctor_set(v_p_x27_3487_, 4, v_eliminations_3479_);
lean_ctor_set(v_p_x27_3487_, 5, v_proveFalse_x3f_3481_);
lean_ctor_set(v_p_x27_3487_, 6, v_explanation_x3f_3482_);
lean_ctor_set_uint8(v_p_x27_3487_, sizeof(void*)*7, v_possible_3480_);
v___x_3488_ = lean_int_neg(v_const_3472_);
lean_dec(v_const_3472_);
v___x_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
lean_inc_ref(v___x_3489_);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
lean_inc_ref(v___x_3490_);
v___x_3491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
lean_ctor_set(v___x_3491_, 1, v_coeffs_3473_);
lean_ctor_set(v___x_3491_, 2, v_i_3484_);
v_f_3492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3492_, 0, v_coeffs_3473_);
lean_ctor_set(v_f_3492_, 1, v___x_3490_);
lean_ctor_set(v_f_3492_, 2, v___x_3491_);
v_f_3493_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3471_, v_f_3492_);
v_f_3494_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3493_);
v___x_3495_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3487_, v_f_3494_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(lean_object* v_x_3496_, lean_object* v_x_3497_){
_start:
{
if (lean_obj_tag(v_x_3497_) == 0)
{
return v_x_3496_;
}
else
{
lean_object* v_head_3498_; lean_object* v_snd_3499_; lean_object* v_tail_3500_; lean_object* v_fst_3501_; lean_object* v_fst_3502_; lean_object* v_snd_3503_; lean_object* v___x_3504_; 
v_head_3498_ = lean_ctor_get(v_x_3497_, 0);
lean_inc(v_head_3498_);
v_snd_3499_ = lean_ctor_get(v_head_3498_, 1);
lean_inc(v_snd_3499_);
v_tail_3500_ = lean_ctor_get(v_x_3497_, 1);
lean_inc(v_tail_3500_);
lean_dec_ref_known(v_x_3497_, 2);
v_fst_3501_ = lean_ctor_get(v_head_3498_, 0);
lean_inc(v_fst_3501_);
lean_dec(v_head_3498_);
v_fst_3502_ = lean_ctor_get(v_snd_3499_, 0);
lean_inc(v_fst_3502_);
v_snd_3503_ = lean_ctor_get(v_snd_3499_, 1);
lean_inc(v_snd_3503_);
lean_dec(v_snd_3499_);
v___x_3504_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality(v_x_3496_, v_fst_3501_, v_fst_3502_, v_snd_3503_);
v_x_3496_ = v___x_3504_;
v_x_3497_ = v_tail_3500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequalities(lean_object* v_p_3506_, lean_object* v_ineqs_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(v_p_3506_, v_ineqs_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(lean_object* v_x_3509_, lean_object* v_x_3510_){
_start:
{
if (lean_obj_tag(v_x_3510_) == 0)
{
return v_x_3509_;
}
else
{
lean_object* v_head_3511_; lean_object* v_snd_3512_; lean_object* v_tail_3513_; lean_object* v_fst_3514_; lean_object* v_fst_3515_; lean_object* v_snd_3516_; lean_object* v___x_3517_; 
v_head_3511_ = lean_ctor_get(v_x_3510_, 0);
lean_inc(v_head_3511_);
v_snd_3512_ = lean_ctor_get(v_head_3511_, 1);
lean_inc(v_snd_3512_);
v_tail_3513_ = lean_ctor_get(v_x_3510_, 1);
lean_inc(v_tail_3513_);
lean_dec_ref_known(v_x_3510_, 2);
v_fst_3514_ = lean_ctor_get(v_head_3511_, 0);
lean_inc(v_fst_3514_);
lean_dec(v_head_3511_);
v_fst_3515_ = lean_ctor_get(v_snd_3512_, 0);
lean_inc(v_fst_3515_);
v_snd_3516_ = lean_ctor_get(v_snd_3512_, 1);
lean_inc(v_snd_3516_);
lean_dec(v_snd_3512_);
v___x_3517_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality(v_x_3509_, v_fst_3514_, v_fst_3515_, v_snd_3516_);
v_x_3509_ = v___x_3517_;
v_x_3510_ = v_tail_3513_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEqualities(lean_object* v_p_3519_, lean_object* v_eqs_3520_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(v_p_3519_, v_eqs_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0(lean_object* v___x_3528_, lean_object* v_x_3529_){
_start:
{
lean_object* v_constraint_3530_; lean_object* v_coeffs_3531_; lean_object* v_lowerBound_3532_; lean_object* v_upperBound_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___y_3538_; lean_object* v___y_3539_; 
v_constraint_3530_ = lean_ctor_get(v_x_3529_, 1);
lean_inc_ref(v_constraint_3530_);
v_coeffs_3531_ = lean_ctor_get(v_x_3529_, 0);
lean_inc(v_coeffs_3531_);
lean_dec_ref(v_x_3529_);
v_lowerBound_3532_ = lean_ctor_get(v_constraint_3530_, 0);
lean_inc(v_lowerBound_3532_);
v_upperBound_3533_ = lean_ctor_get(v_constraint_3530_, 1);
lean_inc(v_upperBound_3533_);
lean_dec_ref(v_constraint_3530_);
v___x_3534_ = l_List_toString___redArg(v___x_3528_, v_coeffs_3531_);
v___x_3535_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3536_ = lean_string_append(v___x_3534_, v___x_3535_);
if (lean_obj_tag(v_lowerBound_3532_) == 0)
{
if (lean_obj_tag(v_upperBound_3533_) == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3545_ = lean_string_append(v___x_3536_, v___x_3544_);
return v___x_3545_;
}
else
{
lean_object* v_val_3546_; lean_object* v___x_3547_; lean_object* v___y_3549_; lean_object* v_intZero_3554_; uint8_t v_isNeg_3555_; 
v_val_3546_ = lean_ctor_get(v_upperBound_3533_, 0);
lean_inc(v_val_3546_);
lean_dec_ref_known(v_upperBound_3533_, 1);
v___x_3547_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3554_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3555_ = lean_int_dec_lt(v_val_3546_, v_intZero_3554_);
if (v_isNeg_3555_ == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3557_; 
v_a_3556_ = lean_nat_abs(v_val_3546_);
lean_dec(v_val_3546_);
v___x_3557_ = l_Nat_reprFast(v_a_3556_);
v___y_3549_ = v___x_3557_;
goto v___jp_3548_;
}
else
{
lean_object* v_abs_3558_; lean_object* v_one_3559_; lean_object* v_a_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v_abs_3558_ = lean_nat_abs(v_val_3546_);
lean_dec(v_val_3546_);
v_one_3559_ = lean_unsigned_to_nat(1u);
v_a_3560_ = lean_nat_sub(v_abs_3558_, v_one_3559_);
lean_dec(v_abs_3558_);
v___x_3561_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3562_ = lean_nat_add(v_a_3560_, v_one_3559_);
lean_dec(v_a_3560_);
v___x_3563_ = l_Nat_reprFast(v___x_3562_);
v___x_3564_ = lean_string_append(v___x_3561_, v___x_3563_);
lean_dec_ref(v___x_3563_);
v___y_3549_ = v___x_3564_;
goto v___jp_3548_;
}
v___jp_3548_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3550_ = lean_string_append(v___x_3547_, v___y_3549_);
lean_dec_ref(v___y_3549_);
v___x_3551_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3552_ = lean_string_append(v___x_3550_, v___x_3551_);
v___x_3553_ = lean_string_append(v___x_3536_, v___x_3552_);
lean_dec_ref(v___x_3552_);
return v___x_3553_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3533_) == 0)
{
lean_object* v_val_3565_; lean_object* v___x_3566_; lean_object* v___y_3568_; lean_object* v_intZero_3573_; uint8_t v_isNeg_3574_; 
v_val_3565_ = lean_ctor_get(v_lowerBound_3532_, 0);
lean_inc(v_val_3565_);
lean_dec_ref_known(v_lowerBound_3532_, 1);
v___x_3566_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3573_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3574_ = lean_int_dec_lt(v_val_3565_, v_intZero_3573_);
if (v_isNeg_3574_ == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3576_; 
v_a_3575_ = lean_nat_abs(v_val_3565_);
lean_dec(v_val_3565_);
v___x_3576_ = l_Nat_reprFast(v_a_3575_);
v___y_3568_ = v___x_3576_;
goto v___jp_3567_;
}
else
{
lean_object* v_abs_3577_; lean_object* v_one_3578_; lean_object* v_a_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v_abs_3577_ = lean_nat_abs(v_val_3565_);
lean_dec(v_val_3565_);
v_one_3578_ = lean_unsigned_to_nat(1u);
v_a_3579_ = lean_nat_sub(v_abs_3577_, v_one_3578_);
lean_dec(v_abs_3577_);
v___x_3580_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3581_ = lean_nat_add(v_a_3579_, v_one_3578_);
lean_dec(v_a_3579_);
v___x_3582_ = l_Nat_reprFast(v___x_3581_);
v___x_3583_ = lean_string_append(v___x_3580_, v___x_3582_);
lean_dec_ref(v___x_3582_);
v___y_3568_ = v___x_3583_;
goto v___jp_3567_;
}
v___jp_3567_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3569_ = lean_string_append(v___x_3566_, v___y_3568_);
lean_dec_ref(v___y_3568_);
v___x_3570_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3571_ = lean_string_append(v___x_3569_, v___x_3570_);
v___x_3572_ = lean_string_append(v___x_3536_, v___x_3571_);
lean_dec_ref(v___x_3571_);
return v___x_3572_;
}
}
else
{
lean_object* v_val_3584_; lean_object* v_val_3585_; uint8_t v___x_3586_; 
v_val_3584_ = lean_ctor_get(v_lowerBound_3532_, 0);
lean_inc(v_val_3584_);
lean_dec_ref_known(v_lowerBound_3532_, 1);
v_val_3585_ = lean_ctor_get(v_upperBound_3533_, 0);
lean_inc(v_val_3585_);
lean_dec_ref_known(v_upperBound_3533_, 1);
v___x_3586_ = lean_int_dec_lt(v_val_3585_, v_val_3584_);
if (v___x_3586_ == 0)
{
uint8_t v___x_3587_; 
v___x_3587_ = lean_int_dec_eq(v_val_3584_, v_val_3585_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; lean_object* v___y_3590_; lean_object* v_intZero_3605_; uint8_t v_isNeg_3606_; 
v___x_3588_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3605_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3606_ = lean_int_dec_lt(v_val_3584_, v_intZero_3605_);
if (v_isNeg_3606_ == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3608_; 
v_a_3607_ = lean_nat_abs(v_val_3584_);
lean_dec(v_val_3584_);
v___x_3608_ = l_Nat_reprFast(v_a_3607_);
v___y_3590_ = v___x_3608_;
goto v___jp_3589_;
}
else
{
lean_object* v_abs_3609_; lean_object* v_one_3610_; lean_object* v_a_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v_abs_3609_ = lean_nat_abs(v_val_3584_);
lean_dec(v_val_3584_);
v_one_3610_ = lean_unsigned_to_nat(1u);
v_a_3611_ = lean_nat_sub(v_abs_3609_, v_one_3610_);
lean_dec(v_abs_3609_);
v___x_3612_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3613_ = lean_nat_add(v_a_3611_, v_one_3610_);
lean_dec(v_a_3611_);
v___x_3614_ = l_Nat_reprFast(v___x_3613_);
v___x_3615_ = lean_string_append(v___x_3612_, v___x_3614_);
lean_dec_ref(v___x_3614_);
v___y_3590_ = v___x_3615_;
goto v___jp_3589_;
}
v___jp_3589_:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v_intZero_3594_; uint8_t v_isNeg_3595_; 
v___x_3591_ = lean_string_append(v___x_3588_, v___y_3590_);
lean_dec_ref(v___y_3590_);
v___x_3592_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3593_ = lean_string_append(v___x_3591_, v___x_3592_);
v_intZero_3594_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3595_ = lean_int_dec_lt(v_val_3585_, v_intZero_3594_);
if (v_isNeg_3595_ == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3597_; 
v_a_3596_ = lean_nat_abs(v_val_3585_);
lean_dec(v_val_3585_);
v___x_3597_ = l_Nat_reprFast(v_a_3596_);
v___y_3538_ = v___x_3593_;
v___y_3539_ = v___x_3597_;
goto v___jp_3537_;
}
else
{
lean_object* v_abs_3598_; lean_object* v_one_3599_; lean_object* v_a_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v_abs_3598_ = lean_nat_abs(v_val_3585_);
lean_dec(v_val_3585_);
v_one_3599_ = lean_unsigned_to_nat(1u);
v_a_3600_ = lean_nat_sub(v_abs_3598_, v_one_3599_);
lean_dec(v_abs_3598_);
v___x_3601_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3602_ = lean_nat_add(v_a_3600_, v_one_3599_);
lean_dec(v_a_3600_);
v___x_3603_ = l_Nat_reprFast(v___x_3602_);
v___x_3604_ = lean_string_append(v___x_3601_, v___x_3603_);
lean_dec_ref(v___x_3603_);
v___y_3538_ = v___x_3593_;
v___y_3539_ = v___x_3604_;
goto v___jp_3537_;
}
}
}
else
{
lean_object* v___x_3616_; lean_object* v___y_3618_; lean_object* v_intZero_3623_; uint8_t v_isNeg_3624_; 
lean_dec(v_val_3585_);
v___x_3616_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3623_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3624_ = lean_int_dec_lt(v_val_3584_, v_intZero_3623_);
if (v_isNeg_3624_ == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3626_; 
v_a_3625_ = lean_nat_abs(v_val_3584_);
lean_dec(v_val_3584_);
v___x_3626_ = l_Nat_reprFast(v_a_3625_);
v___y_3618_ = v___x_3626_;
goto v___jp_3617_;
}
else
{
lean_object* v_abs_3627_; lean_object* v_one_3628_; lean_object* v_a_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v_abs_3627_ = lean_nat_abs(v_val_3584_);
lean_dec(v_val_3584_);
v_one_3628_ = lean_unsigned_to_nat(1u);
v_a_3629_ = lean_nat_sub(v_abs_3627_, v_one_3628_);
lean_dec(v_abs_3627_);
v___x_3630_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3631_ = lean_nat_add(v_a_3629_, v_one_3628_);
lean_dec(v_a_3629_);
v___x_3632_ = l_Nat_reprFast(v___x_3631_);
v___x_3633_ = lean_string_append(v___x_3630_, v___x_3632_);
lean_dec_ref(v___x_3632_);
v___y_3618_ = v___x_3633_;
goto v___jp_3617_;
}
v___jp_3617_:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3619_ = lean_string_append(v___x_3616_, v___y_3618_);
lean_dec_ref(v___y_3618_);
v___x_3620_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3621_ = lean_string_append(v___x_3619_, v___x_3620_);
v___x_3622_ = lean_string_append(v___x_3536_, v___x_3621_);
lean_dec_ref(v___x_3621_);
return v___x_3622_;
}
}
}
else
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
lean_dec(v_val_3585_);
lean_dec(v_val_3584_);
v___x_3634_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3635_ = lean_string_append(v___x_3536_, v___x_3634_);
return v___x_3635_;
}
}
}
v___jp_3537_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3540_ = lean_string_append(v___y_3538_, v___y_3539_);
lean_dec_ref(v___y_3539_);
v___x_3541_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3542_ = lean_string_append(v___x_3540_, v___x_3541_);
v___x_3543_ = lean_string_append(v___x_3536_, v___x_3542_);
lean_dec_ref(v___x_3542_);
return v___x_3543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1(lean_object* v___x_3636_, lean_object* v_x_3637_){
_start:
{
lean_object* v_fst_3638_; lean_object* v_constraint_3639_; lean_object* v_coeffs_3640_; lean_object* v_lowerBound_3641_; lean_object* v_upperBound_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___y_3647_; lean_object* v___y_3648_; 
v_fst_3638_ = lean_ctor_get(v_x_3637_, 0);
lean_inc(v_fst_3638_);
lean_dec_ref(v_x_3637_);
v_constraint_3639_ = lean_ctor_get(v_fst_3638_, 1);
lean_inc_ref(v_constraint_3639_);
v_coeffs_3640_ = lean_ctor_get(v_fst_3638_, 0);
lean_inc(v_coeffs_3640_);
lean_dec(v_fst_3638_);
v_lowerBound_3641_ = lean_ctor_get(v_constraint_3639_, 0);
lean_inc(v_lowerBound_3641_);
v_upperBound_3642_ = lean_ctor_get(v_constraint_3639_, 1);
lean_inc(v_upperBound_3642_);
lean_dec_ref(v_constraint_3639_);
v___x_3643_ = l_List_toString___redArg(v___x_3636_, v_coeffs_3640_);
v___x_3644_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3645_ = lean_string_append(v___x_3643_, v___x_3644_);
if (lean_obj_tag(v_lowerBound_3641_) == 0)
{
if (lean_obj_tag(v_upperBound_3642_) == 0)
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3654_ = lean_string_append(v___x_3645_, v___x_3653_);
return v___x_3654_;
}
else
{
lean_object* v_val_3655_; lean_object* v___x_3656_; lean_object* v___y_3658_; lean_object* v_intZero_3663_; uint8_t v_isNeg_3664_; 
v_val_3655_ = lean_ctor_get(v_upperBound_3642_, 0);
lean_inc(v_val_3655_);
lean_dec_ref_known(v_upperBound_3642_, 1);
v___x_3656_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3663_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3664_ = lean_int_dec_lt(v_val_3655_, v_intZero_3663_);
if (v_isNeg_3664_ == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3666_; 
v_a_3665_ = lean_nat_abs(v_val_3655_);
lean_dec(v_val_3655_);
v___x_3666_ = l_Nat_reprFast(v_a_3665_);
v___y_3658_ = v___x_3666_;
goto v___jp_3657_;
}
else
{
lean_object* v_abs_3667_; lean_object* v_one_3668_; lean_object* v_a_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v_abs_3667_ = lean_nat_abs(v_val_3655_);
lean_dec(v_val_3655_);
v_one_3668_ = lean_unsigned_to_nat(1u);
v_a_3669_ = lean_nat_sub(v_abs_3667_, v_one_3668_);
lean_dec(v_abs_3667_);
v___x_3670_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3671_ = lean_nat_add(v_a_3669_, v_one_3668_);
lean_dec(v_a_3669_);
v___x_3672_ = l_Nat_reprFast(v___x_3671_);
v___x_3673_ = lean_string_append(v___x_3670_, v___x_3672_);
lean_dec_ref(v___x_3672_);
v___y_3658_ = v___x_3673_;
goto v___jp_3657_;
}
v___jp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3659_ = lean_string_append(v___x_3656_, v___y_3658_);
lean_dec_ref(v___y_3658_);
v___x_3660_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3661_ = lean_string_append(v___x_3659_, v___x_3660_);
v___x_3662_ = lean_string_append(v___x_3645_, v___x_3661_);
lean_dec_ref(v___x_3661_);
return v___x_3662_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3642_) == 0)
{
lean_object* v_val_3674_; lean_object* v___x_3675_; lean_object* v___y_3677_; lean_object* v_intZero_3682_; uint8_t v_isNeg_3683_; 
v_val_3674_ = lean_ctor_get(v_lowerBound_3641_, 0);
lean_inc(v_val_3674_);
lean_dec_ref_known(v_lowerBound_3641_, 1);
v___x_3675_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3682_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3683_ = lean_int_dec_lt(v_val_3674_, v_intZero_3682_);
if (v_isNeg_3683_ == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3685_; 
v_a_3684_ = lean_nat_abs(v_val_3674_);
lean_dec(v_val_3674_);
v___x_3685_ = l_Nat_reprFast(v_a_3684_);
v___y_3677_ = v___x_3685_;
goto v___jp_3676_;
}
else
{
lean_object* v_abs_3686_; lean_object* v_one_3687_; lean_object* v_a_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v_abs_3686_ = lean_nat_abs(v_val_3674_);
lean_dec(v_val_3674_);
v_one_3687_ = lean_unsigned_to_nat(1u);
v_a_3688_ = lean_nat_sub(v_abs_3686_, v_one_3687_);
lean_dec(v_abs_3686_);
v___x_3689_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3690_ = lean_nat_add(v_a_3688_, v_one_3687_);
lean_dec(v_a_3688_);
v___x_3691_ = l_Nat_reprFast(v___x_3690_);
v___x_3692_ = lean_string_append(v___x_3689_, v___x_3691_);
lean_dec_ref(v___x_3691_);
v___y_3677_ = v___x_3692_;
goto v___jp_3676_;
}
v___jp_3676_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3678_ = lean_string_append(v___x_3675_, v___y_3677_);
lean_dec_ref(v___y_3677_);
v___x_3679_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3680_ = lean_string_append(v___x_3678_, v___x_3679_);
v___x_3681_ = lean_string_append(v___x_3645_, v___x_3680_);
lean_dec_ref(v___x_3680_);
return v___x_3681_;
}
}
else
{
lean_object* v_val_3693_; lean_object* v_val_3694_; uint8_t v___x_3695_; 
v_val_3693_ = lean_ctor_get(v_lowerBound_3641_, 0);
lean_inc(v_val_3693_);
lean_dec_ref_known(v_lowerBound_3641_, 1);
v_val_3694_ = lean_ctor_get(v_upperBound_3642_, 0);
lean_inc(v_val_3694_);
lean_dec_ref_known(v_upperBound_3642_, 1);
v___x_3695_ = lean_int_dec_lt(v_val_3694_, v_val_3693_);
if (v___x_3695_ == 0)
{
uint8_t v___x_3696_; 
v___x_3696_ = lean_int_dec_eq(v_val_3693_, v_val_3694_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3697_; lean_object* v___y_3699_; lean_object* v_intZero_3714_; uint8_t v_isNeg_3715_; 
v___x_3697_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3714_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3715_ = lean_int_dec_lt(v_val_3693_, v_intZero_3714_);
if (v_isNeg_3715_ == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; 
v_a_3716_ = lean_nat_abs(v_val_3693_);
lean_dec(v_val_3693_);
v___x_3717_ = l_Nat_reprFast(v_a_3716_);
v___y_3699_ = v___x_3717_;
goto v___jp_3698_;
}
else
{
lean_object* v_abs_3718_; lean_object* v_one_3719_; lean_object* v_a_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v_abs_3718_ = lean_nat_abs(v_val_3693_);
lean_dec(v_val_3693_);
v_one_3719_ = lean_unsigned_to_nat(1u);
v_a_3720_ = lean_nat_sub(v_abs_3718_, v_one_3719_);
lean_dec(v_abs_3718_);
v___x_3721_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3722_ = lean_nat_add(v_a_3720_, v_one_3719_);
lean_dec(v_a_3720_);
v___x_3723_ = l_Nat_reprFast(v___x_3722_);
v___x_3724_ = lean_string_append(v___x_3721_, v___x_3723_);
lean_dec_ref(v___x_3723_);
v___y_3699_ = v___x_3724_;
goto v___jp_3698_;
}
v___jp_3698_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v_intZero_3703_; uint8_t v_isNeg_3704_; 
v___x_3700_ = lean_string_append(v___x_3697_, v___y_3699_);
lean_dec_ref(v___y_3699_);
v___x_3701_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3702_ = lean_string_append(v___x_3700_, v___x_3701_);
v_intZero_3703_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3704_ = lean_int_dec_lt(v_val_3694_, v_intZero_3703_);
if (v_isNeg_3704_ == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3706_; 
v_a_3705_ = lean_nat_abs(v_val_3694_);
lean_dec(v_val_3694_);
v___x_3706_ = l_Nat_reprFast(v_a_3705_);
v___y_3647_ = v___x_3702_;
v___y_3648_ = v___x_3706_;
goto v___jp_3646_;
}
else
{
lean_object* v_abs_3707_; lean_object* v_one_3708_; lean_object* v_a_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v_abs_3707_ = lean_nat_abs(v_val_3694_);
lean_dec(v_val_3694_);
v_one_3708_ = lean_unsigned_to_nat(1u);
v_a_3709_ = lean_nat_sub(v_abs_3707_, v_one_3708_);
lean_dec(v_abs_3707_);
v___x_3710_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3711_ = lean_nat_add(v_a_3709_, v_one_3708_);
lean_dec(v_a_3709_);
v___x_3712_ = l_Nat_reprFast(v___x_3711_);
v___x_3713_ = lean_string_append(v___x_3710_, v___x_3712_);
lean_dec_ref(v___x_3712_);
v___y_3647_ = v___x_3702_;
v___y_3648_ = v___x_3713_;
goto v___jp_3646_;
}
}
}
else
{
lean_object* v___x_3725_; lean_object* v___y_3727_; lean_object* v_intZero_3732_; uint8_t v_isNeg_3733_; 
lean_dec(v_val_3694_);
v___x_3725_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3732_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3733_ = lean_int_dec_lt(v_val_3693_, v_intZero_3732_);
if (v_isNeg_3733_ == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; 
v_a_3734_ = lean_nat_abs(v_val_3693_);
lean_dec(v_val_3693_);
v___x_3735_ = l_Nat_reprFast(v_a_3734_);
v___y_3727_ = v___x_3735_;
goto v___jp_3726_;
}
else
{
lean_object* v_abs_3736_; lean_object* v_one_3737_; lean_object* v_a_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_abs_3736_ = lean_nat_abs(v_val_3693_);
lean_dec(v_val_3693_);
v_one_3737_ = lean_unsigned_to_nat(1u);
v_a_3738_ = lean_nat_sub(v_abs_3736_, v_one_3737_);
lean_dec(v_abs_3736_);
v___x_3739_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3740_ = lean_nat_add(v_a_3738_, v_one_3737_);
lean_dec(v_a_3738_);
v___x_3741_ = l_Nat_reprFast(v___x_3740_);
v___x_3742_ = lean_string_append(v___x_3739_, v___x_3741_);
lean_dec_ref(v___x_3741_);
v___y_3727_ = v___x_3742_;
goto v___jp_3726_;
}
v___jp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3728_ = lean_string_append(v___x_3725_, v___y_3727_);
lean_dec_ref(v___y_3727_);
v___x_3729_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3730_ = lean_string_append(v___x_3728_, v___x_3729_);
v___x_3731_ = lean_string_append(v___x_3645_, v___x_3730_);
lean_dec_ref(v___x_3730_);
return v___x_3731_;
}
}
}
else
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
lean_dec(v_val_3694_);
lean_dec(v_val_3693_);
v___x_3743_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3744_ = lean_string_append(v___x_3645_, v___x_3743_);
return v___x_3744_;
}
}
}
v___jp_3646_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3649_ = lean_string_append(v___y_3647_, v___y_3648_);
lean_dec_ref(v___y_3648_);
v___x_3650_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3651_ = lean_string_append(v___x_3649_, v___x_3650_);
v___x_3652_ = lean_string_append(v___x_3645_, v___x_3651_);
lean_dec_ref(v___x_3651_);
return v___x_3652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2(lean_object* v___f_3749_, lean_object* v___f_3750_, lean_object* v___f_3751_, lean_object* v_d_3752_){
_start:
{
lean_object* v_var_3753_; lean_object* v_irrelevant_3754_; lean_object* v_lowerBounds_3755_; lean_object* v_upperBounds_3756_; lean_object* v___x_3757_; lean_object* v_irrelevant_3758_; lean_object* v_lowerBounds_3759_; lean_object* v_upperBounds_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v_var_3753_ = lean_ctor_get(v_d_3752_, 0);
lean_inc(v_var_3753_);
v_irrelevant_3754_ = lean_ctor_get(v_d_3752_, 1);
lean_inc(v_irrelevant_3754_);
v_lowerBounds_3755_ = lean_ctor_get(v_d_3752_, 2);
lean_inc(v_lowerBounds_3755_);
v_upperBounds_3756_ = lean_ctor_get(v_d_3752_, 3);
lean_inc(v_upperBounds_3756_);
lean_dec_ref(v_d_3752_);
v___x_3757_ = lean_box(0);
v_irrelevant_3758_ = l_List_mapTR_loop___redArg(v___f_3749_, v_irrelevant_3754_, v___x_3757_);
lean_inc_ref(v___f_3750_);
v_lowerBounds_3759_ = l_List_mapTR_loop___redArg(v___f_3750_, v_lowerBounds_3755_, v___x_3757_);
v_upperBounds_3760_ = l_List_mapTR_loop___redArg(v___f_3750_, v_upperBounds_3756_, v___x_3757_);
v___x_3761_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0));
v___x_3762_ = l_Nat_reprFast(v_var_3753_);
v___x_3763_ = lean_string_append(v___x_3761_, v___x_3762_);
lean_dec_ref(v___x_3762_);
v___x_3764_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_3765_ = lean_string_append(v___x_3763_, v___x_3764_);
v___x_3766_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1));
lean_inc_ref_n(v___f_3751_, 2);
v___x_3767_ = l_List_toString___redArg(v___f_3751_, v_irrelevant_3758_);
v___x_3768_ = lean_string_append(v___x_3766_, v___x_3767_);
lean_dec_ref(v___x_3767_);
v___x_3769_ = lean_string_append(v___x_3768_, v___x_3764_);
v___x_3770_ = lean_string_append(v___x_3765_, v___x_3769_);
lean_dec_ref(v___x_3769_);
v___x_3771_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2));
v___x_3772_ = l_List_toString___redArg(v___f_3751_, v_lowerBounds_3759_);
v___x_3773_ = lean_string_append(v___x_3771_, v___x_3772_);
lean_dec_ref(v___x_3772_);
v___x_3774_ = lean_string_append(v___x_3773_, v___x_3764_);
v___x_3775_ = lean_string_append(v___x_3770_, v___x_3774_);
lean_dec_ref(v___x_3774_);
v___x_3776_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3));
v___x_3777_ = l_List_toString___redArg(v___f_3751_, v_upperBounds_3760_);
v___x_3778_ = lean_string_append(v___x_3776_, v___x_3777_);
lean_dec_ref(v___x_3777_);
v___x_3779_ = lean_string_append(v___x_3775_, v___x_3778_);
lean_dec_ref(v___x_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(lean_object* v_d_3790_){
_start:
{
lean_object* v_lowerBounds_3791_; lean_object* v_upperBounds_3792_; uint8_t v___x_3793_; 
v_lowerBounds_3791_ = lean_ctor_get(v_d_3790_, 2);
v_upperBounds_3792_ = lean_ctor_get(v_d_3790_, 3);
v___x_3793_ = l_List_isEmpty___redArg(v_lowerBounds_3791_);
if (v___x_3793_ == 0)
{
return v___x_3793_;
}
else
{
uint8_t v___x_3794_; 
v___x_3794_ = l_List_isEmpty___redArg(v_upperBounds_3792_);
return v___x_3794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty___boxed(lean_object* v_d_3795_){
_start:
{
uint8_t v_res_3796_; lean_object* v_r_3797_; 
v_res_3796_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v_d_3795_);
lean_dec_ref(v_d_3795_);
v_r_3797_ = lean_box(v_res_3796_);
return v_r_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(lean_object* v_d_3798_){
_start:
{
lean_object* v_lowerBounds_3799_; lean_object* v_upperBounds_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_lowerBounds_3799_ = lean_ctor_get(v_d_3798_, 2);
v_upperBounds_3800_ = lean_ctor_get(v_d_3798_, 3);
v___x_3801_ = l_List_lengthTR___redArg(v_lowerBounds_3799_);
v___x_3802_ = l_List_lengthTR___redArg(v_upperBounds_3800_);
v___x_3803_ = lean_nat_mul(v___x_3801_, v___x_3802_);
lean_dec(v___x_3802_);
lean_dec(v___x_3801_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size___boxed(lean_object* v_d_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_d_3804_);
lean_dec_ref(v_d_3804_);
return v_res_3805_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(lean_object* v_d_3806_){
_start:
{
uint8_t v_lowerExact_3807_; 
v_lowerExact_3807_ = lean_ctor_get_uint8(v_d_3806_, sizeof(void*)*4);
if (v_lowerExact_3807_ == 0)
{
uint8_t v_upperExact_3808_; 
v_upperExact_3808_ = lean_ctor_get_uint8(v_d_3806_, sizeof(void*)*4 + 1);
return v_upperExact_3808_;
}
else
{
return v_lowerExact_3807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact___boxed(lean_object* v_d_3809_){
_start:
{
uint8_t v_res_3810_; lean_object* v_r_3811_; 
v_res_3810_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_d_3809_);
lean_dec_ref(v_d_3809_);
v_r_3811_ = lean_box(v_res_3810_);
return v_r_3811_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(lean_object* v_x_3812_, lean_object* v_x_3813_){
_start:
{
if (lean_obj_tag(v_x_3813_) == 0)
{
return v_x_3812_;
}
else
{
lean_object* v_head_3814_; lean_object* v_tail_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v_head_3814_ = lean_ctor_get(v_x_3813_, 0);
v_tail_3815_ = lean_ctor_get(v_x_3813_, 1);
v___x_3816_ = lean_box(0);
v___x_3817_ = 1;
lean_inc(v_head_3814_);
v___x_3818_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3818_, 0, v_head_3814_);
lean_ctor_set(v___x_3818_, 1, v___x_3816_);
lean_ctor_set(v___x_3818_, 2, v___x_3816_);
lean_ctor_set(v___x_3818_, 3, v___x_3816_);
lean_ctor_set_uint8(v___x_3818_, sizeof(void*)*4, v___x_3817_);
lean_ctor_set_uint8(v___x_3818_, sizeof(void*)*4 + 1, v___x_3817_);
v___x_3819_ = lean_array_push(v_x_3812_, v___x_3818_);
v_x_3812_ = v___x_3819_;
v_x_3813_ = v_tail_3815_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2___boxed(lean_object* v_x_3821_, lean_object* v_x_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v_x_3821_, v_x_3822_);
lean_dec(v_x_3822_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object* v___x_3824_, lean_object* v_b_3825_, lean_object* v___x_3826_, uint8_t v___x_3827_, lean_object* v_____r_3828_, lean_object* v_d_x27_3829_){
_start:
{
lean_object* v_upperBound_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3857_; 
v_upperBound_3830_ = lean_ctor_get(v___x_3824_, 1);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3857_ == 0)
{
lean_object* v_unused_3858_; 
v_unused_3858_ = lean_ctor_get(v___x_3824_, 0);
lean_dec(v_unused_3858_);
v___x_3832_ = v___x_3824_;
v_isShared_3833_ = v_isSharedCheck_3857_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_upperBound_3830_);
lean_dec(v___x_3824_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3857_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
if (lean_obj_tag(v_upperBound_3830_) == 0)
{
lean_del_object(v___x_3832_);
lean_dec(v___x_3826_);
lean_dec_ref(v_b_3825_);
return v_d_x27_3829_;
}
else
{
lean_object* v_var_3834_; lean_object* v_irrelevant_3835_; lean_object* v_lowerBounds_3836_; lean_object* v_upperBounds_3837_; uint8_t v_lowerExact_3838_; uint8_t v_upperExact_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3856_; 
lean_dec_ref_known(v_upperBound_3830_, 1);
v_var_3834_ = lean_ctor_get(v_d_x27_3829_, 0);
v_irrelevant_3835_ = lean_ctor_get(v_d_x27_3829_, 1);
v_lowerBounds_3836_ = lean_ctor_get(v_d_x27_3829_, 2);
v_upperBounds_3837_ = lean_ctor_get(v_d_x27_3829_, 3);
v_lowerExact_3838_ = lean_ctor_get_uint8(v_d_x27_3829_, sizeof(void*)*4);
v_upperExact_3839_ = lean_ctor_get_uint8(v_d_x27_3829_, sizeof(void*)*4 + 1);
v_isSharedCheck_3856_ = !lean_is_exclusive(v_d_x27_3829_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3841_ = v_d_x27_3829_;
v_isShared_3842_ = v_isSharedCheck_3856_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_upperBounds_3837_);
lean_inc(v_lowerBounds_3836_);
lean_inc(v_irrelevant_3835_);
lean_inc(v_var_3834_);
lean_dec(v_d_x27_3829_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3856_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
lean_inc(v___x_3826_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 1, v___x_3826_);
lean_ctor_set(v___x_3832_, 0, v_b_3825_);
v___x_3844_ = v___x_3832_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_b_3825_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v___x_3826_);
v___x_3844_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
lean_object* v___x_3845_; 
v___x_3845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
lean_ctor_set(v___x_3845_, 1, v_upperBounds_3837_);
if (v_upperExact_3839_ == 0)
{
lean_object* v___x_3847_; 
lean_dec(v___x_3826_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 3, v___x_3845_);
v___x_3847_ = v___x_3841_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_var_3834_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_irrelevant_3835_);
lean_ctor_set(v_reuseFailAlloc_3848_, 2, v_lowerBounds_3836_);
lean_ctor_set(v_reuseFailAlloc_3848_, 3, v___x_3845_);
lean_ctor_set_uint8(v_reuseFailAlloc_3848_, sizeof(void*)*4, v_lowerExact_3838_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_ctor_set_uint8(v___x_3847_, sizeof(void*)*4 + 1, v___x_3827_);
return v___x_3847_;
}
}
else
{
lean_object* v___x_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; lean_object* v___x_3853_; 
v___x_3849_ = lean_nat_abs(v___x_3826_);
lean_dec(v___x_3826_);
v___x_3850_ = lean_unsigned_to_nat(1u);
v___x_3851_ = lean_nat_dec_eq(v___x_3849_, v___x_3850_);
lean_dec(v___x_3849_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 3, v___x_3845_);
v___x_3853_ = v___x_3841_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_var_3834_);
lean_ctor_set(v_reuseFailAlloc_3854_, 1, v_irrelevant_3835_);
lean_ctor_set(v_reuseFailAlloc_3854_, 2, v_lowerBounds_3836_);
lean_ctor_set(v_reuseFailAlloc_3854_, 3, v___x_3845_);
lean_ctor_set_uint8(v_reuseFailAlloc_3854_, sizeof(void*)*4, v_lowerExact_3838_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_ctor_set_uint8(v___x_3853_, sizeof(void*)*4 + 1, v___x_3851_);
return v___x_3853_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0___boxed(lean_object* v___x_3859_, lean_object* v_b_3860_, lean_object* v___x_3861_, lean_object* v___x_3862_, lean_object* v_____r_3863_, lean_object* v_d_x27_3864_){
_start:
{
uint8_t v___x_1958__boxed_3865_; lean_object* v_res_3866_; 
v___x_1958__boxed_3865_ = lean_unbox(v___x_3862_);
v_res_3866_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3859_, v_b_3860_, v___x_3861_, v___x_1958__boxed_3865_, v_____r_3863_, v_d_x27_3864_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(lean_object* v_upperBound_3867_, lean_object* v_coeffs_3868_, lean_object* v_constraint_3869_, lean_object* v_b_3870_, lean_object* v_a_3871_, lean_object* v_b_3872_){
_start:
{
lean_object* v_a_3874_; uint8_t v___x_3878_; 
v___x_3878_ = lean_nat_dec_lt(v_a_3871_, v_upperBound_3867_);
if (v___x_3878_ == 0)
{
lean_dec(v_a_3871_);
lean_dec_ref(v_b_3870_);
lean_dec_ref(v_constraint_3869_);
return v_b_3872_;
}
else
{
lean_object* v___x_3879_; uint8_t v___x_3880_; 
v___x_3879_ = lean_array_get_size(v_b_3872_);
v___x_3880_ = lean_nat_dec_lt(v_a_3871_, v___x_3879_);
if (v___x_3880_ == 0)
{
v_a_3874_ = v_b_3872_;
goto v___jp_3873_;
}
else
{
lean_object* v___x_3881_; lean_object* v_v_3882_; lean_object* v___x_3883_; lean_object* v_xs_x27_3884_; lean_object* v___y_3886_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
lean_inc(v_a_3871_);
v___x_3881_ = l_Lean_Omega_IntList_get(v_coeffs_3868_, v_a_3871_);
v_v_3882_ = lean_array_fget(v_b_3872_, v_a_3871_);
v___x_3883_ = lean_box(0);
v_xs_x27_3884_ = lean_array_fset(v_b_3872_, v_a_3871_, v___x_3883_);
v___x_3888_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3889_ = lean_int_dec_eq(v___x_3881_, v___x_3888_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; lean_object* v_lowerBound_3891_; 
lean_inc_ref(v_constraint_3869_);
lean_inc(v___x_3881_);
v___x_3890_ = l_Lean_Omega_Constraint_scale(v___x_3881_, v_constraint_3869_);
v_lowerBound_3891_ = lean_ctor_get(v___x_3890_, 0);
if (lean_obj_tag(v_lowerBound_3891_) == 0)
{
lean_object* v___x_3892_; 
lean_inc_ref(v_b_3870_);
v___x_3892_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3890_, v_b_3870_, v___x_3881_, v___x_3889_, v___x_3883_, v_v_3882_);
v___y_3886_ = v___x_3892_;
goto v___jp_3885_;
}
else
{
lean_object* v_var_3893_; lean_object* v_irrelevant_3894_; lean_object* v_lowerBounds_3895_; lean_object* v_upperBounds_3896_; uint8_t v_lowerExact_3897_; uint8_t v_upperExact_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3913_; 
v_var_3893_ = lean_ctor_get(v_v_3882_, 0);
v_irrelevant_3894_ = lean_ctor_get(v_v_3882_, 1);
v_lowerBounds_3895_ = lean_ctor_get(v_v_3882_, 2);
v_upperBounds_3896_ = lean_ctor_get(v_v_3882_, 3);
v_lowerExact_3897_ = lean_ctor_get_uint8(v_v_3882_, sizeof(void*)*4);
v_upperExact_3898_ = lean_ctor_get_uint8(v_v_3882_, sizeof(void*)*4 + 1);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_v_3882_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3900_ = v_v_3882_;
v_isShared_3901_ = v_isSharedCheck_3913_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_upperBounds_3896_);
lean_inc(v_lowerBounds_3895_);
lean_inc(v_irrelevant_3894_);
lean_inc(v_var_3893_);
lean_dec(v_v_3882_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3913_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; uint8_t v___y_3905_; 
lean_inc(v___x_3881_);
lean_inc_ref(v_b_3870_);
v___x_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3902_, 0, v_b_3870_);
lean_ctor_set(v___x_3902_, 1, v___x_3881_);
v___x_3903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
lean_ctor_set(v___x_3903_, 1, v_lowerBounds_3895_);
if (v_lowerExact_3897_ == 0)
{
v___y_3905_ = v___x_3889_;
goto v___jp_3904_;
}
else
{
lean_object* v___x_3910_; lean_object* v___x_3911_; uint8_t v___x_3912_; 
v___x_3910_ = lean_nat_abs(v___x_3881_);
v___x_3911_ = lean_unsigned_to_nat(1u);
v___x_3912_ = lean_nat_dec_eq(v___x_3910_, v___x_3911_);
lean_dec(v___x_3910_);
v___y_3905_ = v___x_3912_;
goto v___jp_3904_;
}
v___jp_3904_:
{
lean_object* v___x_3907_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 2, v___x_3903_);
v___x_3907_ = v___x_3900_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_var_3893_);
lean_ctor_set(v_reuseFailAlloc_3909_, 1, v_irrelevant_3894_);
lean_ctor_set(v_reuseFailAlloc_3909_, 2, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3909_, 3, v_upperBounds_3896_);
lean_ctor_set_uint8(v_reuseFailAlloc_3909_, sizeof(void*)*4 + 1, v_upperExact_3898_);
v___x_3907_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3908_; 
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*4, v___y_3905_);
lean_inc_ref(v_b_3870_);
v___x_3908_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3890_, v_b_3870_, v___x_3881_, v___x_3889_, v___x_3883_, v___x_3907_);
v___y_3886_ = v___x_3908_;
goto v___jp_3885_;
}
}
}
}
}
else
{
lean_object* v_var_3914_; lean_object* v_irrelevant_3915_; lean_object* v_lowerBounds_3916_; lean_object* v_upperBounds_3917_; uint8_t v_lowerExact_3918_; uint8_t v_upperExact_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3927_; 
lean_dec(v___x_3881_);
v_var_3914_ = lean_ctor_get(v_v_3882_, 0);
v_irrelevant_3915_ = lean_ctor_get(v_v_3882_, 1);
v_lowerBounds_3916_ = lean_ctor_get(v_v_3882_, 2);
v_upperBounds_3917_ = lean_ctor_get(v_v_3882_, 3);
v_lowerExact_3918_ = lean_ctor_get_uint8(v_v_3882_, sizeof(void*)*4);
v_upperExact_3919_ = lean_ctor_get_uint8(v_v_3882_, sizeof(void*)*4 + 1);
v_isSharedCheck_3927_ = !lean_is_exclusive(v_v_3882_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3921_ = v_v_3882_;
v_isShared_3922_ = v_isSharedCheck_3927_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_upperBounds_3917_);
lean_inc(v_lowerBounds_3916_);
lean_inc(v_irrelevant_3915_);
lean_inc(v_var_3914_);
lean_dec(v_v_3882_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3927_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; lean_object* v___x_3925_; 
lean_inc_ref(v_b_3870_);
v___x_3923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3923_, 0, v_b_3870_);
lean_ctor_set(v___x_3923_, 1, v_irrelevant_3915_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 1, v___x_3923_);
v___x_3925_ = v___x_3921_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_var_3914_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v___x_3923_);
lean_ctor_set(v_reuseFailAlloc_3926_, 2, v_lowerBounds_3916_);
lean_ctor_set(v_reuseFailAlloc_3926_, 3, v_upperBounds_3917_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, sizeof(void*)*4, v_lowerExact_3918_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, sizeof(void*)*4 + 1, v_upperExact_3919_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
v___y_3886_ = v___x_3925_;
goto v___jp_3885_;
}
}
}
v___jp_3885_:
{
lean_object* v___x_3887_; 
v___x_3887_ = lean_array_fset(v_xs_x27_3884_, v_a_3871_, v___y_3886_);
v_a_3874_ = v___x_3887_;
goto v___jp_3873_;
}
}
}
v___jp_3873_:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = lean_unsigned_to_nat(1u);
v___x_3876_ = lean_nat_add(v_a_3871_, v___x_3875_);
lean_dec(v_a_3871_);
v_a_3871_ = v___x_3876_;
v_b_3872_ = v_a_3874_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___boxed(lean_object* v_upperBound_3928_, lean_object* v_coeffs_3929_, lean_object* v_constraint_3930_, lean_object* v_b_3931_, lean_object* v_a_3932_, lean_object* v_b_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3928_, v_coeffs_3929_, v_constraint_3930_, v_b_3931_, v_a_3932_, v_b_3933_);
lean_dec(v_coeffs_3929_);
lean_dec(v_upperBound_3928_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(lean_object* v_n_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
if (lean_obj_tag(v_a_3936_) == 0)
{
lean_object* v___x_3938_; 
v___x_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3938_, 0, v_a_3937_);
return v___x_3938_;
}
else
{
lean_object* v_value_3939_; lean_object* v_tail_3940_; lean_object* v_coeffs_3941_; lean_object* v_constraint_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v_value_3939_ = lean_ctor_get(v_a_3936_, 1);
lean_inc(v_value_3939_);
v_tail_3940_ = lean_ctor_get(v_a_3936_, 2);
lean_inc(v_tail_3940_);
lean_dec_ref_known(v_a_3936_, 3);
v_coeffs_3941_ = lean_ctor_get(v_value_3939_, 0);
lean_inc(v_coeffs_3941_);
v_constraint_3942_ = lean_ctor_get(v_value_3939_, 1);
lean_inc_ref(v_constraint_3942_);
v___x_3943_ = lean_unsigned_to_nat(0u);
v___x_3944_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_n_3935_, v_coeffs_3941_, v_constraint_3942_, v_value_3939_, v___x_3943_, v_a_3937_);
lean_dec(v_coeffs_3941_);
v_a_3936_ = v_tail_3940_;
v_a_3937_ = v___x_3944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1___boxed(lean_object* v_n_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3946_, v_a_3947_, v_a_3948_);
lean_dec(v_n_3946_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(lean_object* v_n_3950_, lean_object* v_as_3951_, size_t v_sz_3952_, size_t v_i_3953_, lean_object* v_b_3954_){
_start:
{
uint8_t v___x_3955_; 
v___x_3955_ = lean_usize_dec_lt(v_i_3953_, v_sz_3952_);
if (v___x_3955_ == 0)
{
return v_b_3954_;
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3957_; 
v_a_3956_ = lean_array_uget_borrowed(v_as_3951_, v_i_3953_);
lean_inc(v_a_3956_);
v___x_3957_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3950_, v_a_3956_, v_b_3954_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3957_, 1);
return v_a_3958_;
}
else
{
lean_object* v_a_3959_; size_t v___x_3960_; size_t v___x_3961_; 
v_a_3959_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3959_);
lean_dec_ref_known(v___x_3957_, 1);
v___x_3960_ = ((size_t)1ULL);
v___x_3961_ = lean_usize_add(v_i_3953_, v___x_3960_);
v_i_3953_ = v___x_3961_;
v_b_3954_ = v_a_3959_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3___boxed(lean_object* v_n_3963_, lean_object* v_as_3964_, lean_object* v_sz_3965_, lean_object* v_i_3966_, lean_object* v_b_3967_){
_start:
{
size_t v_sz_boxed_3968_; size_t v_i_boxed_3969_; lean_object* v_res_3970_; 
v_sz_boxed_3968_ = lean_unbox_usize(v_sz_3965_);
lean_dec(v_sz_3965_);
v_i_boxed_3969_ = lean_unbox_usize(v_i_3966_);
lean_dec(v_i_3966_);
v_res_3970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_n_3963_, v_as_3964_, v_sz_boxed_3968_, v_i_boxed_3969_, v_b_3967_);
lean_dec_ref(v_as_3964_);
lean_dec(v_n_3963_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(lean_object* v_p_3973_){
_start:
{
lean_object* v_constraints_3974_; lean_object* v_numVars_3975_; lean_object* v_buckets_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v_data_3979_; size_t v_sz_3980_; size_t v___x_3981_; lean_object* v___x_3982_; 
v_constraints_3974_ = lean_ctor_get(v_p_3973_, 2);
lean_inc_ref(v_constraints_3974_);
v_numVars_3975_ = lean_ctor_get(v_p_3973_, 1);
lean_inc_n(v_numVars_3975_, 2);
lean_dec_ref(v_p_3973_);
v_buckets_3976_ = lean_ctor_get(v_constraints_3974_, 1);
lean_inc_ref(v_buckets_3976_);
lean_dec_ref(v_constraints_3974_);
v___x_3977_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_3978_ = l_List_range(v_numVars_3975_);
v_data_3979_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v___x_3977_, v___x_3978_);
lean_dec(v___x_3978_);
v_sz_3980_ = lean_array_size(v_buckets_3976_);
v___x_3981_ = ((size_t)0ULL);
v___x_3982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_numVars_3975_, v_buckets_3976_, v_sz_3980_, v___x_3981_, v_data_3979_);
lean_dec_ref(v_buckets_3976_);
lean_dec(v_numVars_3975_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(lean_object* v_upperBound_3983_, lean_object* v_coeffs_3984_, lean_object* v_constraint_3985_, lean_object* v_b_3986_, lean_object* v_inst_3987_, lean_object* v_R_3988_, lean_object* v_a_3989_, lean_object* v_b_3990_, lean_object* v_c_3991_){
_start:
{
lean_object* v___x_3992_; 
v___x_3992_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3983_, v_coeffs_3984_, v_constraint_3985_, v_b_3986_, v_a_3989_, v_b_3990_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___boxed(lean_object* v_upperBound_3993_, lean_object* v_coeffs_3994_, lean_object* v_constraint_3995_, lean_object* v_b_3996_, lean_object* v_inst_3997_, lean_object* v_R_3998_, lean_object* v_a_3999_, lean_object* v_b_4000_, lean_object* v_c_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(v_upperBound_3993_, v_coeffs_3994_, v_constraint_3995_, v_b_3996_, v_inst_3997_, v_R_3998_, v_a_3999_, v_b_4000_, v_c_4001_);
lean_dec(v_coeffs_3994_);
lean_dec(v_upperBound_3993_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(lean_object* v_cls_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v_toCold_4012_; lean_object* v_options_4013_; uint8_t v_hasTrace_4014_; 
v_toCold_4012_ = lean_ctor_get(v___y_4009_, 0);
v_options_4013_ = lean_ctor_get(v_toCold_4012_, 2);
v_hasTrace_4014_ = lean_ctor_get_uint8(v_options_4013_, sizeof(void*)*1);
if (v_hasTrace_4014_ == 0)
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
lean_dec(v_cls_4006_);
v___x_4015_ = lean_box(v_hasTrace_4014_);
v___x_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
return v___x_4016_;
}
else
{
lean_object* v_inheritedTraceOptions_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; uint8_t v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v_inheritedTraceOptions_4017_ = lean_ctor_get(v_toCold_4012_, 11);
v___x_4018_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4019_ = l_Lean_Name_append(v___x_4018_, v_cls_4006_);
v___x_4020_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4017_, v_options_4013_, v___x_4019_);
lean_dec(v___x_4019_);
v___x_4021_ = lean_box(v___x_4020_);
v___x_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
return v___x_4022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___boxed(lean_object* v_cls_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(lean_object* v___x_4030_, lean_object* v_fst_4031_, lean_object* v_snd_4032_, lean_object* v_fst_4033_, lean_object* v_____r_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4030_);
v___x_4041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4041_, 0, v_fst_4031_);
lean_ctor_set(v___x_4041_, 1, v_snd_4032_);
v___x_4042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4042_, 0, v_fst_4033_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4040_);
lean_ctor_set(v___x_4043_, 1, v___x_4042_);
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
v___x_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0___boxed(lean_object* v___x_4046_, lean_object* v_fst_4047_, lean_object* v_snd_4048_, lean_object* v_fst_4049_, lean_object* v_____r_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4046_, v_fst_4047_, v_snd_4048_, v_fst_4049_, v_____r_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
return v_res_4056_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4057_; double v___x_4058_; 
v___x_4057_ = lean_unsigned_to_nat(0u);
v___x_4058_ = lean_float_of_nat(v___x_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(lean_object* v_cls_4061_, lean_object* v_msg_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v_ref_4068_; lean_object* v___x_4069_; lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4115_; 
v_ref_4068_ = lean_ctor_get(v___y_4065_, 2);
v___x_4069_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4072_ = v___x_4069_;
v_isShared_4073_ = v_isSharedCheck_4115_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4069_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4115_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4074_; lean_object* v_traceState_4075_; lean_object* v_env_4076_; lean_object* v_nextMacroScope_4077_; lean_object* v_ngen_4078_; lean_object* v_auxDeclNGen_4079_; lean_object* v_cache_4080_; lean_object* v_recordedDeps_4081_; lean_object* v_messages_4082_; lean_object* v_infoState_4083_; lean_object* v_snapshotTasks_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4114_; 
v___x_4074_ = lean_st_ref_take(v___y_4066_);
v_traceState_4075_ = lean_ctor_get(v___x_4074_, 4);
v_env_4076_ = lean_ctor_get(v___x_4074_, 0);
v_nextMacroScope_4077_ = lean_ctor_get(v___x_4074_, 1);
v_ngen_4078_ = lean_ctor_get(v___x_4074_, 2);
v_auxDeclNGen_4079_ = lean_ctor_get(v___x_4074_, 3);
v_cache_4080_ = lean_ctor_get(v___x_4074_, 5);
v_recordedDeps_4081_ = lean_ctor_get(v___x_4074_, 6);
v_messages_4082_ = lean_ctor_get(v___x_4074_, 7);
v_infoState_4083_ = lean_ctor_get(v___x_4074_, 8);
v_snapshotTasks_4084_ = lean_ctor_get(v___x_4074_, 9);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4086_ = v___x_4074_;
v_isShared_4087_ = v_isSharedCheck_4114_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_snapshotTasks_4084_);
lean_inc(v_infoState_4083_);
lean_inc(v_messages_4082_);
lean_inc(v_recordedDeps_4081_);
lean_inc(v_cache_4080_);
lean_inc(v_traceState_4075_);
lean_inc(v_auxDeclNGen_4079_);
lean_inc(v_ngen_4078_);
lean_inc(v_nextMacroScope_4077_);
lean_inc(v_env_4076_);
lean_dec(v___x_4074_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4114_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
uint64_t v_tid_4088_; lean_object* v_traces_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4113_; 
v_tid_4088_ = lean_ctor_get_uint64(v_traceState_4075_, sizeof(void*)*1);
v_traces_4089_ = lean_ctor_get(v_traceState_4075_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v_traceState_4075_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4091_ = v_traceState_4075_;
v_isShared_4092_ = v_isSharedCheck_4113_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_traces_4089_);
lean_dec(v_traceState_4075_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4113_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; double v___x_4095_; uint8_t v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4104_; 
v___x_4093_ = lean_box(0);
v___x_4094_ = lean_box(0);
v___x_4095_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4096_ = 0;
v___x_4097_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4098_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4098_, 0, v_cls_4061_);
lean_ctor_set(v___x_4098_, 1, v___x_4094_);
lean_ctor_set(v___x_4098_, 2, v___x_4097_);
lean_ctor_set_float(v___x_4098_, sizeof(void*)*3, v___x_4095_);
lean_ctor_set_float(v___x_4098_, sizeof(void*)*3 + 8, v___x_4095_);
lean_ctor_set_uint8(v___x_4098_, sizeof(void*)*3 + 16, v___x_4096_);
v___x_4099_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4100_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4098_);
lean_ctor_set(v___x_4100_, 1, v_a_4070_);
lean_ctor_set(v___x_4100_, 2, v___x_4099_);
lean_inc(v_ref_4068_);
v___x_4101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4101_, 0, v_ref_4068_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = l_Lean_PersistentArray_push___redArg(v_traces_4089_, v___x_4101_);
if (v_isShared_4092_ == 0)
{
lean_ctor_set(v___x_4091_, 0, v___x_4102_);
v___x_4104_ = v___x_4091_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4102_);
lean_ctor_set_uint64(v_reuseFailAlloc_4112_, sizeof(void*)*1, v_tid_4088_);
v___x_4104_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_object* v___x_4106_; 
if (v_isShared_4087_ == 0)
{
lean_ctor_set(v___x_4086_, 4, v___x_4104_);
v___x_4106_ = v___x_4086_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_env_4076_);
lean_ctor_set(v_reuseFailAlloc_4111_, 1, v_nextMacroScope_4077_);
lean_ctor_set(v_reuseFailAlloc_4111_, 2, v_ngen_4078_);
lean_ctor_set(v_reuseFailAlloc_4111_, 3, v_auxDeclNGen_4079_);
lean_ctor_set(v_reuseFailAlloc_4111_, 4, v___x_4104_);
lean_ctor_set(v_reuseFailAlloc_4111_, 5, v_cache_4080_);
lean_ctor_set(v_reuseFailAlloc_4111_, 6, v_recordedDeps_4081_);
lean_ctor_set(v_reuseFailAlloc_4111_, 7, v_messages_4082_);
lean_ctor_set(v_reuseFailAlloc_4111_, 8, v_infoState_4083_);
lean_ctor_set(v_reuseFailAlloc_4111_, 9, v_snapshotTasks_4084_);
v___x_4106_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
lean_object* v___x_4107_; lean_object* v___x_4109_; 
v___x_4107_ = lean_st_ref_put(v___y_4066_, v___x_4106_);
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 0, v___x_4093_);
v___x_4109_ = v___x_4072_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4093_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___boxed(lean_object* v_cls_4116_, lean_object* v_msg_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4116_, v_msg_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
return v_res_4123_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v_cls_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v_cls_4124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4125_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4126_ = l_Lean_Name_append(v___x_4125_, v_cls_4124_);
return v___x_4126_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4128_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__1));
v___x_4129_ = l_Lean_stringToMessageData(v___x_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(lean_object* v_upperBound_4130_, lean_object* v___y_4131_, lean_object* v_a_4132_, lean_object* v_b_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v_a_4140_; lean_object* v___y_4145_; uint8_t v___x_4164_; 
v___x_4164_ = lean_nat_dec_lt(v_a_4132_, v_upperBound_4130_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4165_; 
lean_dec(v_a_4132_);
v___x_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4165_, 0, v_b_4133_);
return v___x_4165_;
}
else
{
lean_object* v_snd_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4237_; 
v_snd_4166_ = lean_ctor_get(v_b_4133_, 1);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_b_4133_);
if (v_isSharedCheck_4237_ == 0)
{
lean_object* v_unused_4238_; 
v_unused_4238_ = lean_ctor_get(v_b_4133_, 0);
lean_dec(v_unused_4238_);
v___x_4168_ = v_b_4133_;
v_isShared_4169_ = v_isSharedCheck_4237_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_snd_4166_);
lean_dec(v_b_4133_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4237_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v_snd_4170_; lean_object* v_fst_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4236_; 
v_snd_4170_ = lean_ctor_get(v_snd_4166_, 1);
v_fst_4171_ = lean_ctor_get(v_snd_4166_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v_snd_4166_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4173_ = v_snd_4166_;
v_isShared_4174_ = v_isSharedCheck_4236_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_snd_4170_);
lean_inc(v_fst_4171_);
lean_dec(v_snd_4166_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4236_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v_fst_4175_; lean_object* v_snd_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4235_; 
v_fst_4175_ = lean_ctor_get(v_snd_4170_, 0);
v_snd_4176_ = lean_ctor_get(v_snd_4170_, 1);
v_isSharedCheck_4235_ = !lean_is_exclusive(v_snd_4170_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4178_ = v_snd_4170_;
v_isShared_4179_ = v_isSharedCheck_4235_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_snd_4176_);
lean_inc(v_fst_4175_);
lean_dec(v_snd_4170_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4235_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4180_; lean_object* v_bestIdx_4191_; lean_object* v_cls_4192_; lean_object* v___x_4193_; uint8_t v___x_4197_; lean_object* v___x_4198_; uint8_t v___x_4199_; uint8_t v___y_4229_; 
v___x_4180_ = lean_box(0);
v_bestIdx_4191_ = lean_unsigned_to_nat(0u);
v_cls_4192_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4193_ = lean_array_fget_borrowed(v___y_4131_, v_a_4132_);
v___x_4197_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4193_);
v___x_4198_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4193_);
v___x_4199_ = lean_nat_dec_eq(v___x_4198_, v_bestIdx_4191_);
if (v___x_4199_ == 0)
{
uint8_t v___x_4234_; 
v___x_4234_ = lean_unbox(v_snd_4176_);
if (v___x_4234_ == 0)
{
if (v___x_4197_ == 0)
{
goto v___jp_4231_;
}
else
{
lean_del_object(v___x_4178_);
lean_del_object(v___x_4173_);
lean_del_object(v___x_4168_);
goto v___jp_4200_;
}
}
else
{
goto v___jp_4231_;
}
}
else
{
lean_del_object(v___x_4178_);
lean_del_object(v___x_4173_);
lean_del_object(v___x_4168_);
goto v___jp_4200_;
}
v___jp_4181_:
{
lean_object* v___x_4183_; 
if (v_isShared_4179_ == 0)
{
v___x_4183_ = v___x_4178_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_fst_4175_);
lean_ctor_set(v_reuseFailAlloc_4190_, 1, v_snd_4176_);
v___x_4183_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4185_; 
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 1, v___x_4183_);
v___x_4185_ = v___x_4173_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_fst_4171_);
lean_ctor_set(v_reuseFailAlloc_4189_, 1, v___x_4183_);
v___x_4185_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
lean_object* v___x_4187_; 
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 1, v___x_4185_);
lean_ctor_set(v___x_4168_, 0, v___x_4180_);
v___x_4187_ = v___x_4168_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4180_);
lean_ctor_set(v_reuseFailAlloc_4188_, 1, v___x_4185_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
v_a_4140_ = v___x_4187_;
goto v___jp_4139_;
}
}
}
}
v___jp_4194_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = lean_box(0);
lean_inc(v___x_4193_);
v___x_4196_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4193_, v_fst_4175_, v_snd_4176_, v_fst_4171_, v___x_4195_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
v___y_4145_ = v___x_4196_;
goto v___jp_4144_;
}
v___jp_4200_:
{
if (v___x_4199_ == 0)
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_dec(v_snd_4176_);
lean_dec(v_fst_4175_);
lean_dec(v_fst_4171_);
v___x_4201_ = lean_box(v___x_4197_);
v___x_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4198_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
lean_inc(v_a_4132_);
v___x_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4203_, 0, v_a_4132_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4180_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v_a_4140_ = v___x_4204_;
goto v___jp_4139_;
}
else
{
lean_object* v_toCold_4205_; lean_object* v_options_4206_; uint8_t v_hasTrace_4207_; 
lean_dec(v___x_4198_);
v_toCold_4205_ = lean_ctor_get(v___y_4136_, 0);
v_options_4206_ = lean_ctor_get(v_toCold_4205_, 2);
v_hasTrace_4207_ = lean_ctor_get_uint8(v_options_4206_, sizeof(void*)*1);
if (v_hasTrace_4207_ == 0)
{
goto v___jp_4194_;
}
else
{
lean_object* v_inheritedTraceOptions_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; 
v_inheritedTraceOptions_4208_ = lean_ctor_get(v_toCold_4205_, 11);
v___x_4209_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_4210_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4208_, v_options_4206_, v___x_4209_);
if (v___x_4210_ == 0)
{
goto v___jp_4194_;
}
else
{
lean_object* v_var_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v_var_4211_ = lean_ctor_get(v___x_4193_, 0);
v___x_4212_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4211_);
v___x_4213_ = l_Nat_reprFast(v_var_4211_);
v___x_4214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
v___x_4215_ = l_Lean_MessageData_ofFormat(v___x_4214_);
v___x_4216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4212_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
v___x_4217_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4192_, v___x_4216_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4219_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4218_);
lean_dec_ref_known(v___x_4217_, 1);
lean_inc(v___x_4193_);
v___x_4219_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4193_, v_fst_4175_, v_snd_4176_, v_fst_4171_, v_a_4218_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
v___y_4145_ = v___x_4219_;
goto v___jp_4144_;
}
else
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4227_; 
lean_dec(v_snd_4176_);
lean_dec(v_fst_4175_);
lean_dec(v_fst_4171_);
lean_dec(v_a_4132_);
v_a_4220_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4222_ = v___x_4217_;
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4217_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4220_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
}
}
}
v___jp_4228_:
{
if (v___y_4229_ == 0)
{
lean_dec(v___x_4198_);
goto v___jp_4181_;
}
else
{
uint8_t v___x_4230_; 
v___x_4230_ = lean_nat_dec_lt(v___x_4198_, v_fst_4175_);
if (v___x_4230_ == 0)
{
lean_dec(v___x_4198_);
goto v___jp_4181_;
}
else
{
lean_del_object(v___x_4178_);
lean_del_object(v___x_4173_);
lean_del_object(v___x_4168_);
goto v___jp_4200_;
}
}
}
v___jp_4231_:
{
if (v___x_4197_ == 0)
{
uint8_t v___x_4232_; 
v___x_4232_ = lean_unbox(v_snd_4176_);
if (v___x_4232_ == 0)
{
v___y_4229_ = v___x_4164_;
goto v___jp_4228_;
}
else
{
v___y_4229_ = v___x_4197_;
goto v___jp_4228_;
}
}
else
{
uint8_t v___x_4233_; 
v___x_4233_ = lean_unbox(v_snd_4176_);
v___y_4229_ = v___x_4233_;
goto v___jp_4228_;
}
}
}
}
}
}
v___jp_4139_:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4141_ = lean_unsigned_to_nat(1u);
v___x_4142_ = lean_nat_add(v_a_4132_, v___x_4141_);
lean_dec(v_a_4132_);
v_a_4132_ = v___x_4142_;
v_b_4133_ = v_a_4140_;
goto _start;
}
v___jp_4144_:
{
if (lean_obj_tag(v___y_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4155_; 
v_a_4146_ = lean_ctor_get(v___y_4145_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___y_4145_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4148_ = v___y_4145_;
v_isShared_4149_ = v_isSharedCheck_4155_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___y_4145_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4155_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
if (lean_obj_tag(v_a_4146_) == 0)
{
lean_object* v_a_4150_; lean_object* v___x_4152_; 
lean_dec(v_a_4132_);
v_a_4150_ = lean_ctor_get(v_a_4146_, 0);
lean_inc(v_a_4150_);
lean_dec_ref_known(v_a_4146_, 1);
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 0, v_a_4150_);
v___x_4152_ = v___x_4148_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
else
{
lean_object* v_a_4154_; 
lean_del_object(v___x_4148_);
v_a_4154_ = lean_ctor_get(v_a_4146_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v_a_4146_, 1);
v_a_4140_ = v_a_4154_;
goto v___jp_4139_;
}
}
}
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_dec(v_a_4132_);
v_a_4156_ = lean_ctor_get(v___y_4145_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___y_4145_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___y_4145_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___y_4145_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___boxed(lean_object* v_upperBound_4239_, lean_object* v___y_4240_, lean_object* v_a_4241_, lean_object* v_b_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4239_, v___y_4240_, v_a_4241_, v_b_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec_ref(v___y_4240_);
lean_dec(v_upperBound_4239_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(lean_object* v_as_4249_, size_t v_i_4250_, size_t v_stop_4251_, lean_object* v_b_4252_){
_start:
{
lean_object* v___y_4254_; uint8_t v___x_4258_; 
v___x_4258_ = lean_usize_dec_eq(v_i_4250_, v_stop_4251_);
if (v___x_4258_ == 0)
{
lean_object* v___x_4259_; uint8_t v___x_4262_; 
v___x_4259_ = lean_array_uget_borrowed(v_as_4249_, v_i_4250_);
v___x_4262_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v___x_4259_);
if (v___x_4262_ == 0)
{
goto v___jp_4260_;
}
else
{
if (v___x_4258_ == 0)
{
v___y_4254_ = v_b_4252_;
goto v___jp_4253_;
}
else
{
goto v___jp_4260_;
}
}
v___jp_4260_:
{
lean_object* v___x_4261_; 
lean_inc(v___x_4259_);
v___x_4261_ = lean_array_push(v_b_4252_, v___x_4259_);
v___y_4254_ = v___x_4261_;
goto v___jp_4253_;
}
}
else
{
return v_b_4252_;
}
v___jp_4253_:
{
size_t v___x_4255_; size_t v___x_4256_; 
v___x_4255_ = ((size_t)1ULL);
v___x_4256_ = lean_usize_add(v_i_4250_, v___x_4255_);
v_i_4250_ = v___x_4256_;
v_b_4252_ = v___y_4254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___boxed(lean_object* v_as_4263_, lean_object* v_i_4264_, lean_object* v_stop_4265_, lean_object* v_b_4266_){
_start:
{
size_t v_i_boxed_4267_; size_t v_stop_boxed_4268_; lean_object* v_res_4269_; 
v_i_boxed_4267_ = lean_unbox_usize(v_i_4264_);
lean_dec(v_i_4264_);
v_stop_boxed_4268_ = lean_unbox_usize(v_stop_4265_);
lean_dec(v_stop_4265_);
v_res_4269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_as_4263_, v_i_boxed_4267_, v_stop_boxed_4268_, v_b_4266_);
lean_dec_ref(v_as_4263_);
return v_res_4269_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2(void){
_start:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4273_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__1));
v___x_4274_ = l_Lean_MessageData_ofFormat(v___x_4273_);
return v___x_4274_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4275_ = lean_box(1);
v___x_4276_ = l_Lean_MessageData_ofFormat(v___x_4275_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(lean_object* v_a_4278_, lean_object* v_a_4279_){
_start:
{
if (lean_obj_tag(v_a_4278_) == 0)
{
lean_object* v___x_4280_; 
v___x_4280_ = l_List_reverse___redArg(v_a_4279_);
return v___x_4280_;
}
else
{
lean_object* v_head_4281_; lean_object* v_snd_4282_; lean_object* v_tail_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4330_; 
v_head_4281_ = lean_ctor_get(v_a_4278_, 0);
lean_inc(v_head_4281_);
v_snd_4282_ = lean_ctor_get(v_head_4281_, 1);
lean_inc(v_snd_4282_);
v_tail_4283_ = lean_ctor_get(v_a_4278_, 1);
v_isSharedCheck_4330_ = !lean_is_exclusive(v_a_4278_);
if (v_isSharedCheck_4330_ == 0)
{
lean_object* v_unused_4331_; 
v_unused_4331_ = lean_ctor_get(v_a_4278_, 0);
lean_dec(v_unused_4331_);
v___x_4285_ = v_a_4278_;
v_isShared_4286_ = v_isSharedCheck_4330_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_tail_4283_);
lean_dec(v_a_4278_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4330_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v_fst_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4328_; 
v_fst_4287_ = lean_ctor_get(v_head_4281_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v_head_4281_);
if (v_isSharedCheck_4328_ == 0)
{
lean_object* v_unused_4329_; 
v_unused_4329_ = lean_ctor_get(v_head_4281_, 1);
lean_dec(v_unused_4329_);
v___x_4289_ = v_head_4281_;
v_isShared_4290_ = v_isSharedCheck_4328_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_fst_4287_);
lean_dec(v_head_4281_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4328_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v_fst_4291_; lean_object* v_snd_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4327_; 
v_fst_4291_ = lean_ctor_get(v_snd_4282_, 0);
v_snd_4292_ = lean_ctor_get(v_snd_4282_, 1);
v_isSharedCheck_4327_ = !lean_is_exclusive(v_snd_4282_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4294_ = v_snd_4282_;
v_isShared_4295_ = v_isSharedCheck_4327_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_snd_4292_);
lean_inc(v_fst_4291_);
lean_dec(v_snd_4282_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4327_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4301_; 
v___x_4296_ = l_Nat_reprFast(v_fst_4287_);
v___x_4297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4296_);
v___x_4298_ = l_Lean_MessageData_ofFormat(v___x_4297_);
v___x_4299_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2);
if (v_isShared_4295_ == 0)
{
lean_ctor_set_tag(v___x_4294_, 7);
lean_ctor_set(v___x_4294_, 1, v___x_4299_);
lean_ctor_set(v___x_4294_, 0, v___x_4298_);
v___x_4301_ = v___x_4294_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v___x_4298_);
lean_ctor_set(v_reuseFailAlloc_4326_, 1, v___x_4299_);
v___x_4301_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
lean_object* v___x_4302_; lean_object* v___x_4304_; 
v___x_4302_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3);
if (v_isShared_4290_ == 0)
{
lean_ctor_set_tag(v___x_4289_, 7);
lean_ctor_set(v___x_4289_, 1, v___x_4302_);
lean_ctor_set(v___x_4289_, 0, v___x_4301_);
v___x_4304_ = v___x_4289_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4301_);
lean_ctor_set(v_reuseFailAlloc_4325_, 1, v___x_4302_);
v___x_4304_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___y_4311_; uint8_t v___x_4322_; 
v___x_4305_ = l_Nat_reprFast(v_fst_4291_);
v___x_4306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
v___x_4307_ = l_Lean_MessageData_ofFormat(v___x_4306_);
v___x_4308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
lean_ctor_set(v___x_4308_, 1, v___x_4299_);
v___x_4309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
lean_ctor_set(v___x_4309_, 1, v___x_4302_);
v___x_4322_ = lean_unbox(v_snd_4292_);
lean_dec(v_snd_4292_);
if (v___x_4322_ == 0)
{
lean_object* v___x_4323_; 
v___x_4323_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__4));
v___y_4311_ = v___x_4323_;
goto v___jp_4310_;
}
else
{
lean_object* v___x_4324_; 
v___x_4324_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4));
v___y_4311_ = v___x_4324_;
goto v___jp_4310_;
}
v___jp_4310_:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4319_; 
lean_inc_ref(v___y_4311_);
v___x_4312_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4312_, 0, v___y_4311_);
v___x_4313_ = l_Lean_MessageData_ofFormat(v___x_4312_);
v___x_4314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4309_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
v___x_4315_ = l_Lean_MessageData_paren(v___x_4314_);
v___x_4316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4304_);
lean_ctor_set(v___x_4316_, 1, v___x_4315_);
v___x_4317_ = l_Lean_MessageData_paren(v___x_4316_);
if (v_isShared_4286_ == 0)
{
lean_ctor_set(v___x_4285_, 1, v_a_4279_);
lean_ctor_set(v___x_4285_, 0, v___x_4317_);
v___x_4319_ = v___x_4285_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4317_);
lean_ctor_set(v_reuseFailAlloc_4321_, 1, v_a_4279_);
v___x_4319_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
v_a_4278_ = v_tail_4283_;
v_a_4279_ = v___x_4319_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(size_t v_sz_4332_, size_t v_i_4333_, lean_object* v_bs_4334_){
_start:
{
uint8_t v___x_4335_; 
v___x_4335_ = lean_usize_dec_lt(v_i_4333_, v_sz_4332_);
if (v___x_4335_ == 0)
{
return v_bs_4334_;
}
else
{
lean_object* v_v_4336_; lean_object* v_var_4337_; lean_object* v___x_4338_; lean_object* v_bs_x27_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; size_t v___x_4345_; size_t v___x_4346_; lean_object* v___x_4347_; 
v_v_4336_ = lean_array_uget(v_bs_4334_, v_i_4333_);
v_var_4337_ = lean_ctor_get(v_v_4336_, 0);
lean_inc(v_var_4337_);
v___x_4338_ = lean_unsigned_to_nat(0u);
v_bs_x27_4339_ = lean_array_uset(v_bs_4334_, v_i_4333_, v___x_4338_);
v___x_4340_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_v_4336_);
v___x_4341_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_v_4336_);
lean_dec(v_v_4336_);
v___x_4342_ = lean_box(v___x_4341_);
v___x_4343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4340_);
lean_ctor_set(v___x_4343_, 1, v___x_4342_);
v___x_4344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4344_, 0, v_var_4337_);
lean_ctor_set(v___x_4344_, 1, v___x_4343_);
v___x_4345_ = ((size_t)1ULL);
v___x_4346_ = lean_usize_add(v_i_4333_, v___x_4345_);
v___x_4347_ = lean_array_uset(v_bs_x27_4339_, v_i_4333_, v___x_4344_);
v_i_4333_ = v___x_4346_;
v_bs_4334_ = v___x_4347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___boxed(lean_object* v_sz_4349_, lean_object* v_i_4350_, lean_object* v_bs_4351_){
_start:
{
size_t v_sz_boxed_4352_; size_t v_i_boxed_4353_; lean_object* v_res_4354_; 
v_sz_boxed_4352_ = lean_unbox_usize(v_sz_4349_);
lean_dec(v_sz_4349_);
v_i_boxed_4353_ = lean_unbox_usize(v_i_4350_);
lean_dec(v_i_4350_);
v_res_4354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_boxed_4352_, v_i_boxed_4353_, v_bs_4351_);
return v_res_4354_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1(void){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4356_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0));
v___x_4357_ = l_Lean_stringToMessageData(v___x_4356_);
return v___x_4357_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4(void){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4361_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3));
v___x_4362_ = l_Lean_stringToMessageData(v___x_4361_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(lean_object* v_data_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
lean_object* v___x_4369_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v_bestIdx_4375_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4503_; lean_object* v___x_4527_; lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4369_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default));
v_bestIdx_4375_ = lean_unsigned_to_nat(0u);
v___x_4527_ = lean_array_get_size(v_data_4363_);
v___x_4528_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_4529_ = lean_nat_dec_lt(v_bestIdx_4375_, v___x_4527_);
if (v___x_4529_ == 0)
{
v___y_4503_ = v___x_4528_;
goto v___jp_4502_;
}
else
{
uint8_t v___x_4530_; 
v___x_4530_ = lean_nat_dec_le(v___x_4527_, v___x_4527_);
if (v___x_4530_ == 0)
{
if (v___x_4529_ == 0)
{
v___y_4503_ = v___x_4528_;
goto v___jp_4502_;
}
else
{
size_t v___x_4531_; size_t v___x_4532_; lean_object* v___x_4533_; 
v___x_4531_ = ((size_t)0ULL);
v___x_4532_ = lean_usize_of_nat(v___x_4527_);
v___x_4533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4363_, v___x_4531_, v___x_4532_, v___x_4528_);
v___y_4503_ = v___x_4533_;
goto v___jp_4502_;
}
}
else
{
size_t v___x_4534_; size_t v___x_4535_; lean_object* v___x_4536_; 
v___x_4534_ = ((size_t)0ULL);
v___x_4535_ = lean_usize_of_nat(v___x_4527_);
v___x_4536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4363_, v___x_4534_, v___x_4535_, v___x_4528_);
v___y_4503_ = v___x_4536_;
goto v___jp_4502_;
}
}
v___jp_4370_:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = lean_array_get(v___x_4369_, v___y_4371_, v___y_4372_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
v___x_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4373_);
return v___x_4374_;
}
v___jp_4376_:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; uint8_t v___x_4386_; 
v___x_4384_ = lean_array_get_borrowed(v___x_4369_, v___y_4377_, v_bestIdx_4375_);
v___x_4385_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4384_);
v___x_4386_ = lean_nat_dec_eq(v___x_4385_, v_bestIdx_4375_);
if (v___x_4386_ == 0)
{
lean_object* v___x_4387_; lean_object* v___x_4388_; uint8_t v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4387_ = lean_unsigned_to_nat(1u);
v___x_4388_ = lean_array_get_size(v___y_4377_);
v___x_4389_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4384_);
v___x_4390_ = lean_box(0);
v___x_4391_ = lean_box(v___x_4389_);
v___x_4392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4385_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4393_, 0, v_bestIdx_4375_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
v___x_4394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4390_);
lean_ctor_set(v___x_4394_, 1, v___x_4393_);
v___x_4395_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v___x_4388_, v___y_4377_, v___x_4387_, v___x_4394_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4450_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4398_ = v___x_4395_;
v_isShared_4399_ = v_isSharedCheck_4450_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4395_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4450_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v_fst_4400_; 
v_fst_4400_ = lean_ctor_get(v_a_4396_, 0);
if (lean_obj_tag(v_fst_4400_) == 0)
{
lean_object* v_snd_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4444_; 
lean_del_object(v___x_4398_);
v_snd_4401_ = lean_ctor_get(v_a_4396_, 1);
v_isSharedCheck_4444_ = !lean_is_exclusive(v_a_4396_);
if (v_isSharedCheck_4444_ == 0)
{
lean_object* v_unused_4445_; 
v_unused_4445_ = lean_ctor_get(v_a_4396_, 0);
lean_dec(v_unused_4445_);
v___x_4403_ = v_a_4396_;
v_isShared_4404_ = v_isSharedCheck_4444_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_snd_4401_);
lean_dec(v_a_4396_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4444_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v_fst_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4442_; 
v_fst_4405_ = lean_ctor_get(v_snd_4401_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_snd_4401_);
if (v_isSharedCheck_4442_ == 0)
{
lean_object* v_unused_4443_; 
v_unused_4443_ = lean_ctor_get(v_snd_4401_, 1);
lean_dec(v_unused_4443_);
v___x_4407_ = v_snd_4401_;
v_isShared_4408_ = v_isSharedCheck_4442_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_fst_4405_);
lean_dec(v_snd_4401_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4442_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4409_; 
lean_inc_ref(v___y_4378_);
lean_inc(v___y_4383_);
lean_inc_ref(v___y_4382_);
lean_inc(v___y_4381_);
lean_inc_ref(v___y_4380_);
v___x_4409_ = lean_apply_5(v___y_4378_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, lean_box(0));
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; uint8_t v___x_4411_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___x_4411_ = lean_unbox(v_a_4410_);
lean_dec(v_a_4410_);
if (v___x_4411_ == 0)
{
lean_del_object(v___x_4407_);
lean_del_object(v___x_4403_);
lean_dec(v___y_4379_);
v___y_4371_ = v___y_4377_;
v___y_4372_ = v_fst_4405_;
goto v___jp_4370_;
}
else
{
lean_object* v___x_4412_; lean_object* v_var_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4419_; 
v___x_4412_ = lean_array_get_borrowed(v___x_4369_, v___y_4377_, v_fst_4405_);
v_var_4413_ = lean_ctor_get(v___x_4412_, 0);
v___x_4414_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4413_);
v___x_4415_ = l_Nat_reprFast(v_var_4413_);
v___x_4416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4415_);
v___x_4417_ = l_Lean_MessageData_ofFormat(v___x_4416_);
if (v_isShared_4408_ == 0)
{
lean_ctor_set_tag(v___x_4407_, 7);
lean_ctor_set(v___x_4407_, 1, v___x_4417_);
lean_ctor_set(v___x_4407_, 0, v___x_4414_);
v___x_4419_ = v___x_4407_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4414_);
lean_ctor_set(v_reuseFailAlloc_4433_, 1, v___x_4417_);
v___x_4419_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
lean_object* v___x_4420_; lean_object* v___x_4422_; 
v___x_4420_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
if (v_isShared_4404_ == 0)
{
lean_ctor_set_tag(v___x_4403_, 7);
lean_ctor_set(v___x_4403_, 1, v___x_4420_);
lean_ctor_set(v___x_4403_, 0, v___x_4419_);
v___x_4422_ = v___x_4403_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4419_);
lean_ctor_set(v_reuseFailAlloc_4432_, 1, v___x_4420_);
v___x_4422_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
lean_object* v___x_4423_; 
v___x_4423_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4379_, v___x_4422_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_dec_ref_known(v___x_4423_, 1);
v___y_4371_ = v___y_4377_;
v___y_4372_ = v_fst_4405_;
goto v___jp_4370_;
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec(v_fst_4405_);
lean_dec_ref(v___y_4377_);
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4423_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4423_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_del_object(v___x_4407_);
lean_dec(v_fst_4405_);
lean_del_object(v___x_4403_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4377_);
v_a_4434_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4409_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4409_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
}
}
else
{
lean_object* v_val_4446_; lean_object* v___x_4448_; 
lean_inc_ref(v_fst_4400_);
lean_dec(v_a_4396_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4377_);
v_val_4446_ = lean_ctor_get(v_fst_4400_, 0);
lean_inc(v_val_4446_);
lean_dec_ref_known(v_fst_4400_, 1);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 0, v_val_4446_);
v___x_4448_ = v___x_4398_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_val_4446_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4377_);
v_a_4451_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4395_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4395_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
else
{
lean_object* v___x_4459_; 
lean_inc(v___x_4384_);
lean_dec(v___x_4385_);
lean_dec_ref(v___y_4377_);
lean_inc_ref(v___y_4378_);
lean_inc(v___y_4383_);
lean_inc_ref(v___y_4382_);
lean_inc(v___y_4381_);
lean_inc_ref(v___y_4380_);
v___x_4459_ = lean_apply_5(v___y_4378_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, lean_box(0));
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4493_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4462_ = v___x_4459_;
v_isShared_4463_ = v_isSharedCheck_4493_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4459_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4493_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
uint8_t v___x_4464_; 
v___x_4464_ = lean_unbox(v_a_4460_);
lean_dec(v_a_4460_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4466_; 
lean_dec(v___y_4379_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v___x_4384_);
v___x_4466_ = v___x_4462_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4384_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
else
{
lean_object* v_var_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
lean_del_object(v___x_4462_);
v_var_4468_ = lean_ctor_get(v___x_4384_, 0);
v___x_4469_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4468_);
v___x_4470_ = l_Nat_reprFast(v_var_4468_);
v___x_4471_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
v___x_4472_ = l_Lean_MessageData_ofFormat(v___x_4471_);
v___x_4473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4469_);
lean_ctor_set(v___x_4473_, 1, v___x_4472_);
v___x_4474_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
v___x_4475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4473_);
lean_ctor_set(v___x_4475_, 1, v___x_4474_);
v___x_4476_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4379_, v___x_4475_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4483_ == 0)
{
lean_object* v_unused_4484_; 
v_unused_4484_ = lean_ctor_get(v___x_4476_, 0);
lean_dec(v_unused_4484_);
v___x_4478_ = v___x_4476_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_dec(v___x_4476_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 0, v___x_4384_);
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___x_4384_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
else
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
lean_dec(v___x_4384_);
v_a_4485_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v___x_4476_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4476_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v___x_4384_);
lean_dec(v___y_4379_);
v_a_4494_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4459_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4459_);
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
v___jp_4502_:
{
lean_object* v_cls_4504_; lean_object* v___f_4505_; lean_object* v___x_4506_; lean_object* v_a_4507_; uint8_t v___x_4508_; 
v_cls_4504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___f_4505_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2));
v___x_4506_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4504_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
v_a_4507_ = lean_ctor_get(v___x_4506_, 0);
lean_inc(v_a_4507_);
lean_dec_ref(v___x_4506_);
v___x_4508_ = lean_unbox(v_a_4507_);
lean_dec(v_a_4507_);
if (v___x_4508_ == 0)
{
v___y_4377_ = v___y_4503_;
v___y_4378_ = v___f_4505_;
v___y_4379_ = v_cls_4504_;
v___y_4380_ = v_a_4364_;
v___y_4381_ = v_a_4365_;
v___y_4382_ = v_a_4366_;
v___y_4383_ = v_a_4367_;
goto v___jp_4376_;
}
else
{
lean_object* v___x_4509_; size_t v_sz_4510_; size_t v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4509_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4);
v_sz_4510_ = lean_array_size(v___y_4503_);
v___x_4511_ = ((size_t)0ULL);
lean_inc_ref(v___y_4503_);
v___x_4512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_4510_, v___x_4511_, v___y_4503_);
v___x_4513_ = lean_array_to_list(v___x_4512_);
v___x_4514_ = lean_box(0);
v___x_4515_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v___x_4513_, v___x_4514_);
v___x_4516_ = l_Lean_MessageData_ofList(v___x_4515_);
v___x_4517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4509_);
lean_ctor_set(v___x_4517_, 1, v___x_4516_);
v___x_4518_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4504_, v___x_4517_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_dec_ref_known(v___x_4518_, 1);
v___y_4377_ = v___y_4503_;
v___y_4378_ = v___f_4505_;
v___y_4379_ = v_cls_4504_;
v___y_4380_ = v_a_4364_;
v___y_4381_ = v_a_4365_;
v___y_4382_ = v_a_4366_;
v___y_4383_ = v_a_4367_;
goto v___jp_4376_;
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec_ref(v___y_4503_);
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4518_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4518_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object* v_data_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
lean_dec(v_a_4539_);
lean_dec_ref(v_a_4538_);
lean_dec_ref(v_data_4537_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object* v_upperBound_4544_, lean_object* v___y_4545_, lean_object* v_inst_4546_, lean_object* v_R_4547_, lean_object* v_a_4548_, lean_object* v_b_4549_, lean_object* v_c_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
lean_object* v___x_4556_; 
v___x_4556_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4544_, v___y_4545_, v_a_4548_, v_b_4549_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object* v_upperBound_4557_, lean_object* v___y_4558_, lean_object* v_inst_4559_, lean_object* v_R_4560_, lean_object* v_a_4561_, lean_object* v_b_4562_, lean_object* v_c_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_upperBound_4557_, v___y_4558_, v_inst_4559_, v_R_4560_, v_a_4561_, v_b_4562_, v_c_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_);
lean_dec(v___y_4567_);
lean_dec_ref(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec_ref(v___y_4558_);
lean_dec(v_upperBound_4557_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(lean_object* v_snd_4570_, lean_object* v_fst_4571_, lean_object* v_as_x27_4572_, lean_object* v_b_4573_){
_start:
{
if (lean_obj_tag(v_as_x27_4572_) == 0)
{
lean_object* v___x_4575_; 
lean_dec_ref(v_fst_4571_);
v___x_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4575_, 0, v_b_4573_);
return v___x_4575_;
}
else
{
lean_object* v_head_4576_; lean_object* v_tail_4577_; lean_object* v_fst_4578_; lean_object* v_snd_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v_head_4576_ = lean_ctor_get(v_as_x27_4572_, 0);
v_tail_4577_ = lean_ctor_get(v_as_x27_4572_, 1);
v_fst_4578_ = lean_ctor_get(v_head_4576_, 0);
v_snd_4579_ = lean_ctor_get(v_head_4576_, 1);
v___x_4580_ = lean_int_neg(v_snd_4570_);
lean_inc(v_fst_4578_);
lean_inc_ref(v_fst_4571_);
lean_inc(v_snd_4579_);
v___x_4581_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_snd_4579_, v_fst_4571_, v___x_4580_, v_fst_4578_);
v___x_4582_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_4581_);
v___x_4583_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_b_4573_, v___x_4582_);
v_as_x27_4572_ = v_tail_4577_;
v_b_4573_ = v___x_4583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg___boxed(lean_object* v_snd_4585_, lean_object* v_fst_4586_, lean_object* v_as_x27_4587_, lean_object* v_b_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4585_, v_fst_4586_, v_as_x27_4587_, v_b_4588_);
lean_dec(v_as_x27_4587_);
lean_dec(v_snd_4585_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(lean_object* v_upperBounds_4591_, lean_object* v_as_x27_4592_, lean_object* v_b_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_){
_start:
{
if (lean_obj_tag(v_as_x27_4592_) == 0)
{
lean_object* v___x_4599_; 
v___x_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4599_, 0, v_b_4593_);
return v___x_4599_;
}
else
{
lean_object* v_head_4600_; lean_object* v_tail_4601_; lean_object* v_fst_4602_; lean_object* v_snd_4603_; lean_object* v___x_4604_; lean_object* v_a_4605_; 
v_head_4600_ = lean_ctor_get(v_as_x27_4592_, 0);
v_tail_4601_ = lean_ctor_get(v_as_x27_4592_, 1);
v_fst_4602_ = lean_ctor_get(v_head_4600_, 0);
v_snd_4603_ = lean_ctor_get(v_head_4600_, 1);
lean_inc(v_fst_4602_);
v___x_4604_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4603_, v_fst_4602_, v_upperBounds_4591_, v_b_4593_);
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
lean_inc(v_a_4605_);
lean_dec_ref(v___x_4604_);
v_as_x27_4592_ = v_tail_4601_;
v_b_4593_ = v_a_4605_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg___boxed(lean_object* v_upperBounds_4607_, lean_object* v_as_x27_4608_, lean_object* v_b_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4607_, v_as_x27_4608_, v_b_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v_as_x27_4608_);
lean_dec(v_upperBounds_4607_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(lean_object* v_as_x27_4616_, lean_object* v_b_4617_){
_start:
{
if (lean_obj_tag(v_as_x27_4616_) == 0)
{
lean_object* v___x_4619_; 
v___x_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4619_, 0, v_b_4617_);
return v___x_4619_;
}
else
{
lean_object* v_head_4620_; lean_object* v_tail_4621_; lean_object* v___x_4622_; 
v_head_4620_ = lean_ctor_get(v_as_x27_4616_, 0);
v_tail_4621_ = lean_ctor_get(v_as_x27_4616_, 1);
lean_inc(v_head_4620_);
v___x_4622_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_b_4617_, v_head_4620_);
v_as_x27_4616_ = v_tail_4621_;
v_b_4617_ = v___x_4622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg___boxed(lean_object* v_as_x27_4624_, lean_object* v_b_4625_, lean_object* v___y_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4624_, v_b_4625_);
lean_dec(v_as_x27_4624_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(lean_object* v_p_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_){
_start:
{
lean_object* v_data_4634_; lean_object* v___x_4635_; 
lean_inc_ref(v_p_4628_);
v_data_4634_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(v_p_4628_);
v___x_4635_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4634_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
lean_dec_ref(v_data_4634_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v_a_4636_; lean_object* v_irrelevant_4637_; lean_object* v_lowerBounds_4638_; lean_object* v_upperBounds_4639_; lean_object* v_assumptions_4640_; lean_object* v_eliminations_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4656_; 
v_a_4636_ = lean_ctor_get(v___x_4635_, 0);
lean_inc(v_a_4636_);
lean_dec_ref_known(v___x_4635_, 1);
v_irrelevant_4637_ = lean_ctor_get(v_a_4636_, 1);
lean_inc(v_irrelevant_4637_);
v_lowerBounds_4638_ = lean_ctor_get(v_a_4636_, 2);
lean_inc(v_lowerBounds_4638_);
v_upperBounds_4639_ = lean_ctor_get(v_a_4636_, 3);
lean_inc(v_upperBounds_4639_);
lean_dec(v_a_4636_);
v_assumptions_4640_ = lean_ctor_get(v_p_4628_, 0);
v_eliminations_4641_ = lean_ctor_get(v_p_4628_, 4);
v_isSharedCheck_4656_ = !lean_is_exclusive(v_p_4628_);
if (v_isSharedCheck_4656_ == 0)
{
lean_object* v_unused_4657_; lean_object* v_unused_4658_; lean_object* v_unused_4659_; lean_object* v_unused_4660_; lean_object* v_unused_4661_; 
v_unused_4657_ = lean_ctor_get(v_p_4628_, 6);
lean_dec(v_unused_4657_);
v_unused_4658_ = lean_ctor_get(v_p_4628_, 5);
lean_dec(v_unused_4658_);
v_unused_4659_ = lean_ctor_get(v_p_4628_, 3);
lean_dec(v_unused_4659_);
v_unused_4660_ = lean_ctor_get(v_p_4628_, 2);
lean_dec(v_unused_4660_);
v_unused_4661_ = lean_ctor_get(v_p_4628_, 1);
lean_dec(v_unused_4661_);
v___x_4643_ = v_p_4628_;
v_isShared_4644_ = v_isSharedCheck_4656_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_eliminations_4641_);
lean_inc(v_assumptions_4640_);
lean_dec(v_p_4628_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4656_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; uint8_t v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4651_; 
v___x_4645_ = lean_unsigned_to_nat(0u);
v___x_4646_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v___x_4647_ = 1;
v___x_4648_ = lean_box(0);
v___x_4649_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_4644_ == 0)
{
lean_ctor_set(v___x_4643_, 6, v___x_4649_);
lean_ctor_set(v___x_4643_, 5, v___x_4648_);
lean_ctor_set(v___x_4643_, 3, v___x_4646_);
lean_ctor_set(v___x_4643_, 2, v___x_4646_);
lean_ctor_set(v___x_4643_, 1, v___x_4645_);
v___x_4651_ = v___x_4643_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_assumptions_4640_);
lean_ctor_set(v_reuseFailAlloc_4655_, 1, v___x_4645_);
lean_ctor_set(v_reuseFailAlloc_4655_, 2, v___x_4646_);
lean_ctor_set(v_reuseFailAlloc_4655_, 3, v___x_4646_);
lean_ctor_set(v_reuseFailAlloc_4655_, 4, v_eliminations_4641_);
lean_ctor_set(v_reuseFailAlloc_4655_, 5, v___x_4648_);
lean_ctor_set(v_reuseFailAlloc_4655_, 6, v___x_4649_);
v___x_4651_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
lean_object* v___x_4652_; lean_object* v_a_4653_; lean_object* v___x_4654_; 
lean_ctor_set_uint8(v___x_4651_, sizeof(void*)*7, v___x_4647_);
v___x_4652_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_irrelevant_4637_, v___x_4651_);
lean_dec(v_irrelevant_4637_);
v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
lean_inc(v_a_4653_);
lean_dec_ref(v___x_4652_);
v___x_4654_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4639_, v_lowerBounds_4638_, v_a_4653_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
lean_dec(v_lowerBounds_4638_);
lean_dec(v_upperBounds_4639_);
return v___x_4654_;
}
}
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
lean_dec_ref(v_p_4628_);
v_a_4662_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4635_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4635_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4662_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin___boxed(lean_object* v_p_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_);
lean_dec(v_a_4674_);
lean_dec_ref(v_a_4673_);
lean_dec(v_a_4672_);
lean_dec_ref(v_a_4671_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(lean_object* v_snd_4677_, lean_object* v_fst_4678_, lean_object* v_as_4679_, lean_object* v_as_x27_4680_, lean_object* v_b_4681_, lean_object* v_a_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
lean_object* v___x_4688_; 
v___x_4688_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4677_, v_fst_4678_, v_as_x27_4680_, v_b_4681_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___boxed(lean_object* v_snd_4689_, lean_object* v_fst_4690_, lean_object* v_as_4691_, lean_object* v_as_x27_4692_, lean_object* v_b_4693_, lean_object* v_a_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(v_snd_4689_, v_fst_4690_, v_as_4691_, v_as_x27_4692_, v_b_4693_, v_a_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec(v_as_x27_4692_);
lean_dec(v_as_4691_);
lean_dec(v_snd_4689_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(lean_object* v_as_4701_, lean_object* v_as_x27_4702_, lean_object* v_b_4703_, lean_object* v_a_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v___x_4710_; 
v___x_4710_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4702_, v_b_4703_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___boxed(lean_object* v_as_4711_, lean_object* v_as_x27_4712_, lean_object* v_b_4713_, lean_object* v_a_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
lean_object* v_res_4720_; 
v_res_4720_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(v_as_4711_, v_as_x27_4712_, v_b_4713_, v_a_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v_as_x27_4712_);
lean_dec(v_as_4711_);
return v_res_4720_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(lean_object* v_upperBounds_4721_, lean_object* v_as_4722_, lean_object* v_as_x27_4723_, lean_object* v_b_4724_, lean_object* v_a_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
lean_object* v___x_4731_; 
v___x_4731_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4721_, v_as_x27_4723_, v_b_4724_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
return v___x_4731_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___boxed(lean_object* v_upperBounds_4732_, lean_object* v_as_4733_, lean_object* v_as_x27_4734_, lean_object* v_b_4735_, lean_object* v_a_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(v_upperBounds_4732_, v_as_4733_, v_as_x27_4734_, v_b_4735_, v_a_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v_as_x27_4734_);
lean_dec(v_as_4733_);
lean_dec(v_upperBounds_4732_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object* v_x_4743_, lean_object* v_x_4744_){
_start:
{
if (lean_obj_tag(v_x_4744_) == 0)
{
lean_inc(v_x_4743_);
return v_x_4743_;
}
else
{
lean_object* v_key_4745_; lean_object* v_value_4746_; lean_object* v_tail_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
v_key_4745_ = lean_ctor_get(v_x_4744_, 0);
v_value_4746_ = lean_ctor_get(v_x_4744_, 1);
v_tail_4747_ = lean_ctor_get(v_x_4744_, 2);
v___x_4748_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4743_, v_tail_4747_);
lean_inc(v_value_4746_);
lean_inc(v_key_4745_);
v___x_4749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4749_, 0, v_key_4745_);
lean_ctor_set(v___x_4749_, 1, v_value_4746_);
v___x_4750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
lean_ctor_set(v___x_4750_, 1, v___x_4748_);
return v___x_4750_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2___boxed(lean_object* v_x_4751_, lean_object* v_x_4752_){
_start:
{
lean_object* v_res_4753_; 
v_res_4753_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4751_, v_x_4752_);
lean_dec(v_x_4752_);
lean_dec(v_x_4751_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object* v_as_4754_, size_t v_i_4755_, size_t v_stop_4756_, lean_object* v_b_4757_){
_start:
{
uint8_t v___x_4758_; 
v___x_4758_ = lean_usize_dec_eq(v_i_4755_, v_stop_4756_);
if (v___x_4758_ == 0)
{
size_t v___x_4759_; size_t v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___x_4759_ = ((size_t)1ULL);
v___x_4760_ = lean_usize_sub(v_i_4755_, v___x_4759_);
v___x_4761_ = lean_array_uget_borrowed(v_as_4754_, v___x_4760_);
v___x_4762_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_b_4757_, v___x_4761_);
lean_dec(v_b_4757_);
v_i_4755_ = v___x_4760_;
v_b_4757_ = v___x_4762_;
goto _start;
}
else
{
return v_b_4757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object* v_as_4764_, lean_object* v_i_4765_, lean_object* v_stop_4766_, lean_object* v_b_4767_){
_start:
{
size_t v_i_boxed_4768_; size_t v_stop_boxed_4769_; lean_object* v_res_4770_; 
v_i_boxed_4768_ = lean_unbox_usize(v_i_4765_);
lean_dec(v_i_4765_);
v_stop_boxed_4769_ = lean_unbox_usize(v_stop_4766_);
lean_dec(v_stop_4766_);
v_res_4770_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_as_4764_, v_i_boxed_4768_, v_stop_boxed_4769_, v_b_4767_);
lean_dec_ref(v_as_4764_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object* v_a_4771_, lean_object* v_a_4772_){
_start:
{
if (lean_obj_tag(v_a_4771_) == 0)
{
lean_object* v___x_4773_; 
v___x_4773_ = l_List_reverse___redArg(v_a_4772_);
return v___x_4773_;
}
else
{
lean_object* v_head_4774_; lean_object* v_tail_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4892_; 
v_head_4774_ = lean_ctor_get(v_a_4771_, 0);
v_tail_4775_ = lean_ctor_get(v_a_4771_, 1);
v_isSharedCheck_4892_ = !lean_is_exclusive(v_a_4771_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4777_ = v_a_4771_;
v_isShared_4778_ = v_isSharedCheck_4892_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_tail_4775_);
lean_inc(v_head_4774_);
lean_dec(v_a_4771_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4892_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___y_4780_; lean_object* v_snd_4785_; lean_object* v_constraint_4786_; lean_object* v_fst_4787_; lean_object* v_lowerBound_4788_; lean_object* v_upperBound_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___y_4794_; lean_object* v___y_4795_; 
v_snd_4785_ = lean_ctor_get(v_head_4774_, 1);
v_constraint_4786_ = lean_ctor_get(v_snd_4785_, 1);
lean_inc_ref(v_constraint_4786_);
v_fst_4787_ = lean_ctor_get(v_head_4774_, 0);
lean_inc(v_fst_4787_);
lean_dec(v_head_4774_);
v_lowerBound_4788_ = lean_ctor_get(v_constraint_4786_, 0);
lean_inc(v_lowerBound_4788_);
v_upperBound_4789_ = lean_ctor_get(v_constraint_4786_, 1);
lean_inc(v_upperBound_4789_);
lean_dec_ref(v_constraint_4786_);
v___x_4790_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_fst_4787_);
lean_dec(v_fst_4787_);
v___x_4791_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_4792_ = lean_string_append(v___x_4790_, v___x_4791_);
if (lean_obj_tag(v_lowerBound_4788_) == 0)
{
if (lean_obj_tag(v_upperBound_4789_) == 0)
{
lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4800_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_4801_ = lean_string_append(v___x_4792_, v___x_4800_);
v___y_4780_ = v___x_4801_;
goto v___jp_4779_;
}
else
{
lean_object* v_val_4802_; lean_object* v___x_4803_; lean_object* v___y_4805_; lean_object* v_intZero_4810_; uint8_t v_isNeg_4811_; 
v_val_4802_ = lean_ctor_get(v_upperBound_4789_, 0);
lean_inc(v_val_4802_);
lean_dec_ref_known(v_upperBound_4789_, 1);
v___x_4803_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_4810_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4811_ = lean_int_dec_lt(v_val_4802_, v_intZero_4810_);
if (v_isNeg_4811_ == 0)
{
lean_object* v_a_4812_; lean_object* v___x_4813_; 
v_a_4812_ = lean_nat_abs(v_val_4802_);
lean_dec(v_val_4802_);
v___x_4813_ = l_Nat_reprFast(v_a_4812_);
v___y_4805_ = v___x_4813_;
goto v___jp_4804_;
}
else
{
lean_object* v_abs_4814_; lean_object* v_one_4815_; lean_object* v_a_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
v_abs_4814_ = lean_nat_abs(v_val_4802_);
lean_dec(v_val_4802_);
v_one_4815_ = lean_unsigned_to_nat(1u);
v_a_4816_ = lean_nat_sub(v_abs_4814_, v_one_4815_);
lean_dec(v_abs_4814_);
v___x_4817_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4818_ = lean_nat_add(v_a_4816_, v_one_4815_);
lean_dec(v_a_4816_);
v___x_4819_ = l_Nat_reprFast(v___x_4818_);
v___x_4820_ = lean_string_append(v___x_4817_, v___x_4819_);
lean_dec_ref(v___x_4819_);
v___y_4805_ = v___x_4820_;
goto v___jp_4804_;
}
v___jp_4804_:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4806_ = lean_string_append(v___x_4803_, v___y_4805_);
lean_dec_ref(v___y_4805_);
v___x_4807_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4808_ = lean_string_append(v___x_4806_, v___x_4807_);
v___x_4809_ = lean_string_append(v___x_4792_, v___x_4808_);
lean_dec_ref(v___x_4808_);
v___y_4780_ = v___x_4809_;
goto v___jp_4779_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_4789_) == 0)
{
lean_object* v_val_4821_; lean_object* v___x_4822_; lean_object* v___y_4824_; lean_object* v_intZero_4829_; uint8_t v_isNeg_4830_; 
v_val_4821_ = lean_ctor_get(v_lowerBound_4788_, 0);
lean_inc(v_val_4821_);
lean_dec_ref_known(v_lowerBound_4788_, 1);
v___x_4822_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4829_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4830_ = lean_int_dec_lt(v_val_4821_, v_intZero_4829_);
if (v_isNeg_4830_ == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4832_; 
v_a_4831_ = lean_nat_abs(v_val_4821_);
lean_dec(v_val_4821_);
v___x_4832_ = l_Nat_reprFast(v_a_4831_);
v___y_4824_ = v___x_4832_;
goto v___jp_4823_;
}
else
{
lean_object* v_abs_4833_; lean_object* v_one_4834_; lean_object* v_a_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v_abs_4833_ = lean_nat_abs(v_val_4821_);
lean_dec(v_val_4821_);
v_one_4834_ = lean_unsigned_to_nat(1u);
v_a_4835_ = lean_nat_sub(v_abs_4833_, v_one_4834_);
lean_dec(v_abs_4833_);
v___x_4836_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4837_ = lean_nat_add(v_a_4835_, v_one_4834_);
lean_dec(v_a_4835_);
v___x_4838_ = l_Nat_reprFast(v___x_4837_);
v___x_4839_ = lean_string_append(v___x_4836_, v___x_4838_);
lean_dec_ref(v___x_4838_);
v___y_4824_ = v___x_4839_;
goto v___jp_4823_;
}
v___jp_4823_:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4825_ = lean_string_append(v___x_4822_, v___y_4824_);
lean_dec_ref(v___y_4824_);
v___x_4826_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_4827_ = lean_string_append(v___x_4825_, v___x_4826_);
v___x_4828_ = lean_string_append(v___x_4792_, v___x_4827_);
lean_dec_ref(v___x_4827_);
v___y_4780_ = v___x_4828_;
goto v___jp_4779_;
}
}
else
{
lean_object* v_val_4840_; lean_object* v_val_4841_; uint8_t v___x_4842_; 
v_val_4840_ = lean_ctor_get(v_lowerBound_4788_, 0);
lean_inc(v_val_4840_);
lean_dec_ref_known(v_lowerBound_4788_, 1);
v_val_4841_ = lean_ctor_get(v_upperBound_4789_, 0);
lean_inc(v_val_4841_);
lean_dec_ref_known(v_upperBound_4789_, 1);
v___x_4842_ = lean_int_dec_lt(v_val_4841_, v_val_4840_);
if (v___x_4842_ == 0)
{
uint8_t v___x_4843_; 
v___x_4843_ = lean_int_dec_eq(v_val_4840_, v_val_4841_);
if (v___x_4843_ == 0)
{
lean_object* v___x_4844_; lean_object* v___y_4846_; lean_object* v_intZero_4861_; uint8_t v_isNeg_4862_; 
v___x_4844_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4861_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4862_ = lean_int_dec_lt(v_val_4840_, v_intZero_4861_);
if (v_isNeg_4862_ == 0)
{
lean_object* v_a_4863_; lean_object* v___x_4864_; 
v_a_4863_ = lean_nat_abs(v_val_4840_);
lean_dec(v_val_4840_);
v___x_4864_ = l_Nat_reprFast(v_a_4863_);
v___y_4846_ = v___x_4864_;
goto v___jp_4845_;
}
else
{
lean_object* v_abs_4865_; lean_object* v_one_4866_; lean_object* v_a_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; 
v_abs_4865_ = lean_nat_abs(v_val_4840_);
lean_dec(v_val_4840_);
v_one_4866_ = lean_unsigned_to_nat(1u);
v_a_4867_ = lean_nat_sub(v_abs_4865_, v_one_4866_);
lean_dec(v_abs_4865_);
v___x_4868_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4869_ = lean_nat_add(v_a_4867_, v_one_4866_);
lean_dec(v_a_4867_);
v___x_4870_ = l_Nat_reprFast(v___x_4869_);
v___x_4871_ = lean_string_append(v___x_4868_, v___x_4870_);
lean_dec_ref(v___x_4870_);
v___y_4846_ = v___x_4871_;
goto v___jp_4845_;
}
v___jp_4845_:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v_intZero_4850_; uint8_t v_isNeg_4851_; 
v___x_4847_ = lean_string_append(v___x_4844_, v___y_4846_);
lean_dec_ref(v___y_4846_);
v___x_4848_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_4849_ = lean_string_append(v___x_4847_, v___x_4848_);
v_intZero_4850_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4851_ = lean_int_dec_lt(v_val_4841_, v_intZero_4850_);
if (v_isNeg_4851_ == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4853_; 
v_a_4852_ = lean_nat_abs(v_val_4841_);
lean_dec(v_val_4841_);
v___x_4853_ = l_Nat_reprFast(v_a_4852_);
v___y_4794_ = v___x_4849_;
v___y_4795_ = v___x_4853_;
goto v___jp_4793_;
}
else
{
lean_object* v_abs_4854_; lean_object* v_one_4855_; lean_object* v_a_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v_abs_4854_ = lean_nat_abs(v_val_4841_);
lean_dec(v_val_4841_);
v_one_4855_ = lean_unsigned_to_nat(1u);
v_a_4856_ = lean_nat_sub(v_abs_4854_, v_one_4855_);
lean_dec(v_abs_4854_);
v___x_4857_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4858_ = lean_nat_add(v_a_4856_, v_one_4855_);
lean_dec(v_a_4856_);
v___x_4859_ = l_Nat_reprFast(v___x_4858_);
v___x_4860_ = lean_string_append(v___x_4857_, v___x_4859_);
lean_dec_ref(v___x_4859_);
v___y_4794_ = v___x_4849_;
v___y_4795_ = v___x_4860_;
goto v___jp_4793_;
}
}
}
else
{
lean_object* v___x_4872_; lean_object* v___y_4874_; lean_object* v_intZero_4879_; uint8_t v_isNeg_4880_; 
lean_dec(v_val_4841_);
v___x_4872_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_4879_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4880_ = lean_int_dec_lt(v_val_4840_, v_intZero_4879_);
if (v_isNeg_4880_ == 0)
{
lean_object* v_a_4881_; lean_object* v___x_4882_; 
v_a_4881_ = lean_nat_abs(v_val_4840_);
lean_dec(v_val_4840_);
v___x_4882_ = l_Nat_reprFast(v_a_4881_);
v___y_4874_ = v___x_4882_;
goto v___jp_4873_;
}
else
{
lean_object* v_abs_4883_; lean_object* v_one_4884_; lean_object* v_a_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; 
v_abs_4883_ = lean_nat_abs(v_val_4840_);
lean_dec(v_val_4840_);
v_one_4884_ = lean_unsigned_to_nat(1u);
v_a_4885_ = lean_nat_sub(v_abs_4883_, v_one_4884_);
lean_dec(v_abs_4883_);
v___x_4886_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4887_ = lean_nat_add(v_a_4885_, v_one_4884_);
lean_dec(v_a_4885_);
v___x_4888_ = l_Nat_reprFast(v___x_4887_);
v___x_4889_ = lean_string_append(v___x_4886_, v___x_4888_);
lean_dec_ref(v___x_4888_);
v___y_4874_ = v___x_4889_;
goto v___jp_4873_;
}
v___jp_4873_:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4875_ = lean_string_append(v___x_4872_, v___y_4874_);
lean_dec_ref(v___y_4874_);
v___x_4876_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_4877_ = lean_string_append(v___x_4875_, v___x_4876_);
v___x_4878_ = lean_string_append(v___x_4792_, v___x_4877_);
lean_dec_ref(v___x_4877_);
v___y_4780_ = v___x_4878_;
goto v___jp_4779_;
}
}
}
else
{
lean_object* v___x_4890_; lean_object* v___x_4891_; 
lean_dec(v_val_4841_);
lean_dec(v_val_4840_);
v___x_4890_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_4891_ = lean_string_append(v___x_4792_, v___x_4890_);
v___y_4780_ = v___x_4891_;
goto v___jp_4779_;
}
}
}
v___jp_4779_:
{
lean_object* v___x_4782_; 
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 1, v_a_4772_);
lean_ctor_set(v___x_4777_, 0, v___y_4780_);
v___x_4782_ = v___x_4777_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___y_4780_);
lean_ctor_set(v_reuseFailAlloc_4784_, 1, v_a_4772_);
v___x_4782_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
v_a_4771_ = v_tail_4775_;
v_a_4772_ = v___x_4782_;
goto _start;
}
}
v___jp_4793_:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
v___x_4796_ = lean_string_append(v___y_4794_, v___y_4795_);
lean_dec_ref(v___y_4795_);
v___x_4797_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4798_ = lean_string_append(v___x_4796_, v___x_4797_);
v___x_4799_ = lean_string_append(v___x_4792_, v___x_4798_);
lean_dec_ref(v___x_4798_);
v___y_4780_ = v___x_4799_;
goto v___jp_4779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object* v_cls_4893_, lean_object* v_msg_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_){
_start:
{
lean_object* v_ref_4900_; lean_object* v___x_4901_; lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4947_; 
v_ref_4900_ = lean_ctor_get(v___y_4897_, 2);
v___x_4901_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
v_a_4902_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4904_ = v___x_4901_;
v_isShared_4905_ = v_isSharedCheck_4947_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4901_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4947_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4906_; lean_object* v_traceState_4907_; lean_object* v_env_4908_; lean_object* v_nextMacroScope_4909_; lean_object* v_ngen_4910_; lean_object* v_auxDeclNGen_4911_; lean_object* v_cache_4912_; lean_object* v_recordedDeps_4913_; lean_object* v_messages_4914_; lean_object* v_infoState_4915_; lean_object* v_snapshotTasks_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4946_; 
v___x_4906_ = lean_st_ref_take(v___y_4898_);
v_traceState_4907_ = lean_ctor_get(v___x_4906_, 4);
v_env_4908_ = lean_ctor_get(v___x_4906_, 0);
v_nextMacroScope_4909_ = lean_ctor_get(v___x_4906_, 1);
v_ngen_4910_ = lean_ctor_get(v___x_4906_, 2);
v_auxDeclNGen_4911_ = lean_ctor_get(v___x_4906_, 3);
v_cache_4912_ = lean_ctor_get(v___x_4906_, 5);
v_recordedDeps_4913_ = lean_ctor_get(v___x_4906_, 6);
v_messages_4914_ = lean_ctor_get(v___x_4906_, 7);
v_infoState_4915_ = lean_ctor_get(v___x_4906_, 8);
v_snapshotTasks_4916_ = lean_ctor_get(v___x_4906_, 9);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4918_ = v___x_4906_;
v_isShared_4919_ = v_isSharedCheck_4946_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_snapshotTasks_4916_);
lean_inc(v_infoState_4915_);
lean_inc(v_messages_4914_);
lean_inc(v_recordedDeps_4913_);
lean_inc(v_cache_4912_);
lean_inc(v_traceState_4907_);
lean_inc(v_auxDeclNGen_4911_);
lean_inc(v_ngen_4910_);
lean_inc(v_nextMacroScope_4909_);
lean_inc(v_env_4908_);
lean_dec(v___x_4906_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4946_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
uint64_t v_tid_4920_; lean_object* v_traces_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4945_; 
v_tid_4920_ = lean_ctor_get_uint64(v_traceState_4907_, sizeof(void*)*1);
v_traces_4921_ = lean_ctor_get(v_traceState_4907_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v_traceState_4907_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4923_ = v_traceState_4907_;
v_isShared_4924_ = v_isSharedCheck_4945_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_traces_4921_);
lean_dec(v_traceState_4907_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4945_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4925_; lean_object* v___x_4926_; double v___x_4927_; uint8_t v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4936_; 
v___x_4925_ = lean_box(0);
v___x_4926_ = lean_box(0);
v___x_4927_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4928_ = 0;
v___x_4929_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4930_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4930_, 0, v_cls_4893_);
lean_ctor_set(v___x_4930_, 1, v___x_4926_);
lean_ctor_set(v___x_4930_, 2, v___x_4929_);
lean_ctor_set_float(v___x_4930_, sizeof(void*)*3, v___x_4927_);
lean_ctor_set_float(v___x_4930_, sizeof(void*)*3 + 8, v___x_4927_);
lean_ctor_set_uint8(v___x_4930_, sizeof(void*)*3 + 16, v___x_4928_);
v___x_4931_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4932_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4932_, 0, v___x_4930_);
lean_ctor_set(v___x_4932_, 1, v_a_4902_);
lean_ctor_set(v___x_4932_, 2, v___x_4931_);
lean_inc(v_ref_4900_);
v___x_4933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4933_, 0, v_ref_4900_);
lean_ctor_set(v___x_4933_, 1, v___x_4932_);
v___x_4934_ = l_Lean_PersistentArray_push___redArg(v_traces_4921_, v___x_4933_);
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 0, v___x_4934_);
v___x_4936_ = v___x_4923_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v___x_4934_);
lean_ctor_set_uint64(v_reuseFailAlloc_4944_, sizeof(void*)*1, v_tid_4920_);
v___x_4936_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
lean_object* v___x_4938_; 
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 4, v___x_4936_);
v___x_4938_ = v___x_4918_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v_env_4908_);
lean_ctor_set(v_reuseFailAlloc_4943_, 1, v_nextMacroScope_4909_);
lean_ctor_set(v_reuseFailAlloc_4943_, 2, v_ngen_4910_);
lean_ctor_set(v_reuseFailAlloc_4943_, 3, v_auxDeclNGen_4911_);
lean_ctor_set(v_reuseFailAlloc_4943_, 4, v___x_4936_);
lean_ctor_set(v_reuseFailAlloc_4943_, 5, v_cache_4912_);
lean_ctor_set(v_reuseFailAlloc_4943_, 6, v_recordedDeps_4913_);
lean_ctor_set(v_reuseFailAlloc_4943_, 7, v_messages_4914_);
lean_ctor_set(v_reuseFailAlloc_4943_, 8, v_infoState_4915_);
lean_ctor_set(v_reuseFailAlloc_4943_, 9, v_snapshotTasks_4916_);
v___x_4938_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
lean_object* v___x_4939_; lean_object* v___x_4941_; 
v___x_4939_ = lean_st_ref_put(v___y_4898_, v___x_4938_);
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 0, v___x_4925_);
v___x_4941_ = v___x_4904_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v___x_4925_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg___boxed(lean_object* v_cls_4948_, lean_object* v_msg_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
lean_object* v_res_4955_; 
v_res_4955_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4948_, v_msg_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_);
lean_dec(v___y_4953_);
lean_dec_ref(v___y_4952_);
lean_dec(v___y_4951_);
lean_dec_ref(v___y_4950_);
return v_res_4955_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1(void){
_start:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4957_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__0));
v___x_4958_ = l_Lean_stringToMessageData(v___x_4957_);
return v___x_4958_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1(void){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4960_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__0));
v___x_4961_ = l_Lean_stringToMessageData(v___x_4960_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega(lean_object* v_p_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, uint8_t v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_){
_start:
{
lean_object* v___y_4974_; lean_object* v___y_4975_; lean_object* v___y_4976_; uint8_t v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; lean_object* v___y_4982_; lean_object* v_toCold_4988_; lean_object* v_options_4989_; uint8_t v_hasTrace_4990_; 
v_toCold_4988_ = lean_ctor_get(v_a_4970_, 0);
v_options_4989_ = lean_ctor_get(v_toCold_4988_, 2);
v_hasTrace_4990_ = lean_ctor_get_uint8(v_options_4989_, sizeof(void*)*1);
if (v_hasTrace_4990_ == 0)
{
v___y_4974_ = v_a_4963_;
v___y_4975_ = v_a_4964_;
v___y_4976_ = v_a_4965_;
v___y_4977_ = v_a_4966_;
v___y_4978_ = v_a_4967_;
v___y_4979_ = v_a_4968_;
v___y_4980_ = v_a_4969_;
v___y_4981_ = v_a_4970_;
v___y_4982_ = v_a_4971_;
goto v___jp_4973_;
}
else
{
lean_object* v_inheritedTraceOptions_4991_; lean_object* v_cls_4992_; lean_object* v___x_4993_; uint8_t v___x_4994_; 
v_inheritedTraceOptions_4991_ = lean_ctor_get(v_toCold_4988_, 11);
v_cls_4992_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4993_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_4994_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4991_, v_options_4989_, v___x_4993_);
if (v___x_4994_ == 0)
{
v___y_4974_ = v_a_4963_;
v___y_4975_ = v_a_4964_;
v___y_4976_ = v_a_4965_;
v___y_4977_ = v_a_4966_;
v___y_4978_ = v_a_4967_;
v___y_4979_ = v_a_4968_;
v___y_4980_ = v_a_4969_;
v___y_4981_ = v_a_4970_;
v___y_4982_ = v_a_4971_;
goto v___jp_4973_;
}
else
{
lean_object* v_constraints_4995_; uint8_t v_possible_4996_; lean_object* v___x_4997_; lean_object* v___y_4999_; 
v_constraints_4995_ = lean_ctor_get(v_p_4962_, 2);
v_possible_4996_ = lean_ctor_get_uint8(v_p_4962_, sizeof(void*)*7);
v___x_4997_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1);
if (v_possible_4996_ == 0)
{
lean_object* v___x_5012_; 
v___x_5012_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
v___y_4999_ = v___x_5012_;
goto v___jp_4998_;
}
else
{
uint8_t v___x_5013_; 
v___x_5013_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_4962_);
if (v___x_5013_ == 0)
{
lean_object* v_buckets_5014_; lean_object* v___x_5015_; lean_object* v___y_5017_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; uint8_t v___x_5024_; 
v_buckets_5014_ = lean_ctor_get(v_constraints_4995_, 1);
v___x_5015_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5021_ = lean_box(0);
v___x_5022_ = lean_array_get_size(v_buckets_5014_);
v___x_5023_ = lean_unsigned_to_nat(0u);
v___x_5024_ = lean_nat_dec_lt(v___x_5023_, v___x_5022_);
if (v___x_5024_ == 0)
{
v___y_5017_ = v___x_5021_;
goto v___jp_5016_;
}
else
{
size_t v___x_5025_; size_t v___x_5026_; lean_object* v___x_5027_; 
v___x_5025_ = lean_usize_of_nat(v___x_5022_);
v___x_5026_ = ((size_t)0ULL);
v___x_5027_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5014_, v___x_5025_, v___x_5026_, v___x_5021_);
v___y_5017_ = v___x_5027_;
goto v___jp_5016_;
}
v___jp_5016_:
{
lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
v___x_5018_ = lean_box(0);
v___x_5019_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5017_, v___x_5018_);
v___x_5020_ = l_String_intercalate(v___x_5015_, v___x_5019_);
v___y_4999_ = v___x_5020_;
goto v___jp_4998_;
}
}
else
{
lean_object* v___x_5028_; 
v___x_5028_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_4999_ = v___x_5028_;
goto v___jp_4998_;
}
}
v___jp_4998_:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_5000_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5000_, 0, v___y_4999_);
v___x_5001_ = l_Lean_MessageData_ofFormat(v___x_5000_);
v___x_5002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5002_, 0, v___x_4997_);
lean_ctor_set(v___x_5002_, 1, v___x_5001_);
v___x_5003_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4992_, v___x_5002_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_dec_ref_known(v___x_5003_, 1);
v___y_4974_ = v_a_4963_;
v___y_4975_ = v_a_4964_;
v___y_4976_ = v_a_4965_;
v___y_4977_ = v_a_4966_;
v___y_4978_ = v_a_4967_;
v___y_4979_ = v_a_4968_;
v___y_4980_ = v_a_4969_;
v___y_4981_ = v_a_4970_;
v___y_4982_ = v_a_4971_;
goto v___jp_4973_;
}
else
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5011_; 
lean_dec_ref(v_p_4962_);
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5006_ = v___x_5003_;
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_5003_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5009_; 
if (v_isShared_5007_ == 0)
{
v___x_5009_ = v___x_5006_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_a_5004_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
}
}
}
}
v___jp_4973_:
{
uint8_t v_possible_4983_; 
v_possible_4983_ = lean_ctor_get_uint8(v_p_4962_, sizeof(void*)*7);
if (v_possible_4983_ == 0)
{
lean_object* v___x_4984_; 
v___x_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4984_, 0, v_p_4962_);
return v___x_4984_;
}
else
{
lean_object* v___x_4985_; 
v___x_4985_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_4962_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v_a_4986_; lean_object* v___x_4987_; 
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_a_4986_);
lean_dec_ref_known(v___x_4985_, 1);
v___x_4987_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_a_4986_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_);
return v___x_4987_;
}
else
{
return v___x_4985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination(lean_object* v_p_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, uint8_t v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_){
_start:
{
lean_object* v___y_5041_; lean_object* v___y_5042_; lean_object* v___y_5043_; uint8_t v___y_5044_; lean_object* v___y_5045_; lean_object* v___y_5046_; lean_object* v___y_5047_; lean_object* v___y_5048_; lean_object* v___y_5049_; uint8_t v_possible_5053_; 
v_possible_5053_ = lean_ctor_get_uint8(v_p_5029_, sizeof(void*)*7);
if (v_possible_5053_ == 0)
{
lean_object* v___x_5054_; 
v___x_5054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5054_, 0, v_p_5029_);
return v___x_5054_;
}
else
{
lean_object* v_constraints_5055_; uint8_t v___x_5056_; 
v_constraints_5055_ = lean_ctor_get(v_p_5029_, 2);
v___x_5056_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_5029_);
if (v___x_5056_ == 0)
{
lean_object* v_toCold_5057_; lean_object* v_options_5058_; uint8_t v_hasTrace_5059_; 
v_toCold_5057_ = lean_ctor_get(v_a_5037_, 0);
v_options_5058_ = lean_ctor_get(v_toCold_5057_, 2);
v_hasTrace_5059_ = lean_ctor_get_uint8(v_options_5058_, sizeof(void*)*1);
if (v_hasTrace_5059_ == 0)
{
v___y_5041_ = v_a_5030_;
v___y_5042_ = v_a_5031_;
v___y_5043_ = v_a_5032_;
v___y_5044_ = v_a_5033_;
v___y_5045_ = v_a_5034_;
v___y_5046_ = v_a_5035_;
v___y_5047_ = v_a_5036_;
v___y_5048_ = v_a_5037_;
v___y_5049_ = v_a_5038_;
goto v___jp_5040_;
}
else
{
lean_object* v_inheritedTraceOptions_5060_; lean_object* v_cls_5061_; lean_object* v___x_5062_; uint8_t v___x_5063_; 
v_inheritedTraceOptions_5060_ = lean_ctor_get(v_toCold_5057_, 11);
v_cls_5061_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_5062_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_5063_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5060_, v_options_5058_, v___x_5062_);
if (v___x_5063_ == 0)
{
v___y_5041_ = v_a_5030_;
v___y_5042_ = v_a_5031_;
v___y_5043_ = v_a_5032_;
v___y_5044_ = v_a_5033_;
v___y_5045_ = v_a_5034_;
v___y_5046_ = v_a_5035_;
v___y_5047_ = v_a_5036_;
v___y_5048_ = v_a_5037_;
v___y_5049_ = v_a_5038_;
goto v___jp_5040_;
}
else
{
lean_object* v___x_5064_; lean_object* v___y_5066_; 
v___x_5064_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1);
if (v___x_5056_ == 0)
{
lean_object* v_buckets_5079_; lean_object* v___x_5080_; lean_object* v___y_5082_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; uint8_t v___x_5089_; 
v_buckets_5079_ = lean_ctor_get(v_constraints_5055_, 1);
v___x_5080_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5086_ = lean_box(0);
v___x_5087_ = lean_array_get_size(v_buckets_5079_);
v___x_5088_ = lean_unsigned_to_nat(0u);
v___x_5089_ = lean_nat_dec_lt(v___x_5088_, v___x_5087_);
if (v___x_5089_ == 0)
{
v___y_5082_ = v___x_5086_;
goto v___jp_5081_;
}
else
{
size_t v___x_5090_; size_t v___x_5091_; lean_object* v___x_5092_; 
v___x_5090_ = lean_usize_of_nat(v___x_5087_);
v___x_5091_ = ((size_t)0ULL);
v___x_5092_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5079_, v___x_5090_, v___x_5091_, v___x_5086_);
v___y_5082_ = v___x_5092_;
goto v___jp_5081_;
}
v___jp_5081_:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5083_ = lean_box(0);
v___x_5084_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5082_, v___x_5083_);
v___x_5085_ = l_String_intercalate(v___x_5080_, v___x_5084_);
v___y_5066_ = v___x_5085_;
goto v___jp_5065_;
}
}
else
{
lean_object* v___x_5093_; 
v___x_5093_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_5066_ = v___x_5093_;
goto v___jp_5065_;
}
v___jp_5065_:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5067_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5067_, 0, v___y_5066_);
v___x_5068_ = l_Lean_MessageData_ofFormat(v___x_5067_);
v___x_5069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5064_);
lean_ctor_set(v___x_5069_, 1, v___x_5068_);
v___x_5070_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5061_, v___x_5069_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
if (lean_obj_tag(v___x_5070_) == 0)
{
lean_dec_ref_known(v___x_5070_, 1);
v___y_5041_ = v_a_5030_;
v___y_5042_ = v_a_5031_;
v___y_5043_ = v_a_5032_;
v___y_5044_ = v_a_5033_;
v___y_5045_ = v_a_5034_;
v___y_5046_ = v_a_5035_;
v___y_5047_ = v_a_5036_;
v___y_5048_ = v_a_5037_;
v___y_5049_ = v_a_5038_;
goto v___jp_5040_;
}
else
{
lean_object* v_a_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5078_; 
lean_dec_ref(v_p_5029_);
v_a_5071_ = lean_ctor_get(v___x_5070_, 0);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5070_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5073_ = v___x_5070_;
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_a_5071_);
lean_dec(v___x_5070_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5076_; 
if (v_isShared_5074_ == 0)
{
v___x_5076_ = v___x_5073_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5071_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5094_; 
v___x_5094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5094_, 0, v_p_5029_);
return v___x_5094_;
}
}
v___jp_5040_:
{
lean_object* v___x_5050_; 
v___x_5050_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_5029_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_);
if (lean_obj_tag(v___x_5050_) == 0)
{
lean_object* v_a_5051_; lean_object* v___x_5052_; 
v_a_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc(v_a_5051_);
lean_dec_ref_known(v___x_5050_, 1);
v___x_5052_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_a_5051_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_);
return v___x_5052_;
}
else
{
return v___x_5050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___boxed(lean_object* v_p_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_){
_start:
{
uint8_t v_a_boxed_5106_; lean_object* v_res_5107_; 
v_a_boxed_5106_ = lean_unbox(v_a_5099_);
v_res_5107_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_p_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_boxed_5106_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
lean_dec(v_a_5104_);
lean_dec_ref(v_a_5103_);
lean_dec(v_a_5102_);
lean_dec_ref(v_a_5101_);
lean_dec(v_a_5100_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec(v_a_5096_);
return v_res_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___boxed(lean_object* v_p_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_){
_start:
{
uint8_t v_a_boxed_5119_; lean_object* v_res_5120_; 
v_a_boxed_5119_ = lean_unbox(v_a_5112_);
v_res_5120_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_p_5108_, v_a_5109_, v_a_5110_, v_a_5111_, v_a_boxed_5119_, v_a_5113_, v_a_5114_, v_a_5115_, v_a_5116_, v_a_5117_);
lean_dec(v_a_5117_);
lean_dec_ref(v_a_5116_);
lean_dec(v_a_5115_);
lean_dec_ref(v_a_5114_);
lean_dec(v_a_5113_);
lean_dec_ref(v_a_5111_);
lean_dec(v_a_5110_);
lean_dec(v_a_5109_);
return v_res_5120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(lean_object* v_cls_5121_, lean_object* v_msg_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, uint8_t v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_){
_start:
{
lean_object* v___x_5133_; 
v___x_5133_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5121_, v_msg_5122_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
return v___x_5133_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___boxed(lean_object* v_cls_5134_, lean_object* v_msg_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_){
_start:
{
uint8_t v___y_16400__boxed_5146_; lean_object* v_res_5147_; 
v___y_16400__boxed_5146_ = lean_unbox(v___y_5139_);
v_res_5147_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(v_cls_5134_, v_msg_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_16400__boxed_5146_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_);
lean_dec(v___y_5144_);
lean_dec_ref(v___y_5143_);
lean_dec(v___y_5142_);
lean_dec_ref(v___y_5141_);
lean_dec(v___y_5140_);
lean_dec_ref(v___y_5138_);
lean_dec(v___y_5137_);
lean_dec(v___y_5136_);
return v_res_5147_;
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
