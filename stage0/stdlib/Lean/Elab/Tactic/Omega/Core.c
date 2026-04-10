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
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* l_Int_repr___boxed(lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
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
lean_dec_ref(v_t_286_);
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
lean_dec_ref(v_t_286_);
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
lean_dec_ref(v_t_286_);
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
lean_dec_ref(v_t_286_);
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
lean_dec_ref(v_t_286_);
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
lean_dec_ref(v___x_421_);
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
lean_object* v_startInclusive_470_; lean_object* v_endExclusive_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v_startInclusive_470_ = lean_ctor_get(v_s_444_, 1);
v_endExclusive_471_ = lean_ctor_get(v_s_444_, 2);
v___x_472_ = lean_nat_sub(v_endExclusive_471_, v_startInclusive_470_);
v___x_473_ = lean_nat_dec_eq(v_pos_466_, v___x_472_);
lean_dec(v___x_472_);
if (v___x_473_ == 0)
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
lean_object* v_needle_492_; lean_object* v_table_493_; lean_object* v_stackPos_494_; lean_object* v_needlePos_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_554_; 
v_needle_492_ = lean_ctor_get(v_a_446_, 0);
v_table_493_ = lean_ctor_get(v_a_446_, 1);
v_stackPos_494_ = lean_ctor_get(v_a_446_, 2);
v_needlePos_495_ = lean_ctor_get(v_a_446_, 3);
v_isSharedCheck_554_ = !lean_is_exclusive(v_a_446_);
if (v_isSharedCheck_554_ == 0)
{
v___x_497_ = v_a_446_;
v_isShared_498_ = v_isSharedCheck_554_;
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
v_isShared_498_ = v_isSharedCheck_554_;
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
uint8_t v___x_510_; 
lean_dec(v___x_506_);
lean_del_object(v___x_497_);
lean_dec(v_needlePos_495_);
lean_dec(v_stackPos_494_);
lean_dec_ref(v_table_493_);
lean_dec_ref(v_needle_492_);
v___x_510_ = lean_nat_dec_lt(v_basePos_505_, v___x_508_);
if (v___x_510_ == 0)
{
lean_dec(v___x_508_);
lean_dec(v_basePos_505_);
lean_dec_ref(v_s_444_);
return v_b_447_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = l_String_Slice_pos_x21(v_s_444_, v_basePos_505_);
lean_dec(v_basePos_505_);
v___x_512_ = lean_box(3);
v_it_449_ = v___x_512_;
v_startPos_450_ = v___x_511_;
v_endPos_451_ = v___x_508_;
goto v___jp_448_;
}
}
else
{
lean_object* v___x_513_; uint8_t v_stackByte_514_; lean_object* v___x_515_; uint8_t v_patByte_516_; uint8_t v___x_517_; 
lean_dec(v___x_508_);
v___x_513_ = lean_nat_add(v_startInclusive_503_, v_stackPos_494_);
v_stackByte_514_ = lean_string_get_byte_fast(v_str_502_, v___x_513_);
v___x_515_ = lean_nat_add(v_startInclusive_500_, v_needlePos_495_);
v_patByte_516_ = lean_string_get_byte_fast(v_str_499_, v___x_515_);
v___x_517_ = lean_uint8_dec_eq(v_stackByte_514_, v_patByte_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; uint8_t v___x_519_; 
lean_dec(v___x_506_);
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_nat_dec_eq(v_needlePos_495_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_newNeedlePos_522_; uint8_t v___x_523_; 
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_nat_sub(v_needlePos_495_, v___x_520_);
lean_dec(v_needlePos_495_);
v_newNeedlePos_522_ = lean_array_fget_borrowed(v_table_493_, v___x_521_);
lean_dec(v___x_521_);
v___x_523_ = lean_nat_dec_eq(v_newNeedlePos_522_, v___x_518_);
if (v___x_523_ == 0)
{
lean_object* v_oldBasePos_524_; lean_object* v___x_525_; lean_object* v_newBasePos_526_; lean_object* v___x_528_; 
lean_inc(v_newNeedlePos_522_);
v_oldBasePos_524_ = l_String_Slice_pos_x21(v_s_444_, v_basePos_505_);
lean_dec(v_basePos_505_);
v___x_525_ = lean_nat_sub(v_stackPos_494_, v_newNeedlePos_522_);
v_newBasePos_526_ = l_String_Slice_pos_x21(v_s_444_, v___x_525_);
lean_dec(v___x_525_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 3, v_newNeedlePos_522_);
v___x_528_ = v___x_497_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_needle_492_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_table_493_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_stackPos_494_);
lean_ctor_set(v_reuseFailAlloc_529_, 3, v_newNeedlePos_522_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v_it_449_ = v___x_528_;
v_startPos_450_ = v_oldBasePos_524_;
v_endPos_451_ = v_newBasePos_526_;
goto v___jp_448_;
}
}
else
{
lean_object* v_basePos_530_; lean_object* v_nextStackPos_531_; lean_object* v___x_533_; 
v_basePos_530_ = l_String_Slice_pos_x21(v_s_444_, v_basePos_505_);
lean_dec(v_basePos_505_);
v_nextStackPos_531_ = l_String_Slice_posGE___redArg(v_s_444_, v_stackPos_494_);
lean_inc(v_nextStackPos_531_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 3, v___x_518_);
lean_ctor_set(v___x_497_, 2, v_nextStackPos_531_);
v___x_533_ = v___x_497_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_needle_492_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_table_493_);
lean_ctor_set(v_reuseFailAlloc_534_, 2, v_nextStackPos_531_);
lean_ctor_set(v_reuseFailAlloc_534_, 3, v___x_518_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
v_it_449_ = v___x_533_;
v_startPos_450_ = v_basePos_530_;
v_endPos_451_ = v_nextStackPos_531_;
goto v___jp_448_;
}
}
}
else
{
lean_object* v_basePos_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_nextStackPos_538_; lean_object* v___x_540_; 
lean_dec(v_basePos_505_);
lean_dec(v_needlePos_495_);
v_basePos_535_ = l_String_Slice_pos_x21(v_s_444_, v_stackPos_494_);
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = lean_nat_add(v_stackPos_494_, v___x_536_);
lean_dec(v_stackPos_494_);
v_nextStackPos_538_ = l_String_Slice_posGE___redArg(v_s_444_, v___x_537_);
lean_inc(v_nextStackPos_538_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 3, v___x_518_);
lean_ctor_set(v___x_497_, 2, v_nextStackPos_538_);
v___x_540_ = v___x_497_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_needle_492_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_table_493_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_nextStackPos_538_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v___x_518_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
v_it_449_ = v___x_540_;
v_startPos_450_ = v_basePos_535_;
v_endPos_451_ = v_nextStackPos_538_;
goto v___jp_448_;
}
}
}
else
{
lean_object* v___x_542_; lean_object* v_nextStackPos_543_; lean_object* v_nextNeedlePos_544_; uint8_t v___x_545_; 
lean_dec(v_basePos_505_);
v___x_542_ = lean_unsigned_to_nat(1u);
v_nextStackPos_543_ = lean_nat_add(v_stackPos_494_, v___x_542_);
lean_dec(v_stackPos_494_);
v_nextNeedlePos_544_ = lean_nat_add(v_needlePos_495_, v___x_542_);
lean_dec(v_needlePos_495_);
v___x_545_ = lean_nat_dec_eq(v_nextNeedlePos_544_, v___x_506_);
lean_dec(v___x_506_);
if (v___x_545_ == 0)
{
lean_object* v___x_547_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 3, v_nextNeedlePos_544_);
lean_ctor_set(v___x_497_, 2, v_nextStackPos_543_);
v___x_547_ = v___x_497_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_needle_492_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_table_493_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v_nextStackPos_543_);
lean_ctor_set(v_reuseFailAlloc_549_, 3, v_nextNeedlePos_544_);
v___x_547_ = v_reuseFailAlloc_549_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
v_a_446_ = v___x_547_;
goto _start;
}
}
else
{
lean_object* v___x_550_; lean_object* v___x_552_; 
lean_dec(v_nextNeedlePos_544_);
v___x_550_ = lean_unsigned_to_nat(0u);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 3, v___x_550_);
lean_ctor_set(v___x_497_, 2, v_nextStackPos_543_);
v___x_552_ = v___x_497_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_needle_492_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_table_493_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_nextStackPos_543_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
v_it_460_ = v___x_552_;
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
v___x_456_ = lean_string_utf8_extract(v_str_453_, v_startInclusive_454_, v_endExclusive_455_);
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
v___x_463_ = lean_string_utf8_extract(v_replacement_445_, v___x_461_, v___x_462_);
v___x_464_ = lean_string_append(v_b_447_, v___x_463_);
lean_dec_ref(v___x_463_);
v_a_446_ = v_it_460_;
v_b_447_ = v___x_464_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg___boxed(lean_object* v_s_555_, lean_object* v_replacement_556_, lean_object* v_a_557_, lean_object* v_b_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_555_, v_replacement_556_, v_a_557_, v_b_558_);
lean_dec_ref(v_replacement_556_);
return v_res_559_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_563_ = lean_string_utf8_byte_size(v___x_562_);
return v___x_563_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2);
v___x_566_ = lean_nat_dec_eq(v___x_565_, v___x_564_);
return v___x_566_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
lean_ctor_set(v___x_570_, 2, v___x_567_);
return v___x_570_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4);
v___x_572_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__5);
v___x_575_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4);
v___x_576_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_574_);
lean_ctor_set(v___x_576_, 2, v___x_573_);
lean_ctor_set(v___x_576_, 3, v___x_573_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(lean_object* v_s_579_, lean_object* v_replacement_580_){
_start:
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_582_ = lean_uint8_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__6);
v___x_584_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_579_, v_replacement_580_, v___x_583_, v___x_581_);
return v___x_584_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__7));
v___x_586_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_579_, v_replacement_580_, v___x_585_, v___x_581_);
return v___x_586_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___boxed(lean_object* v_s_587_, lean_object* v_replacement_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v_s_587_, v_replacement_588_);
lean_dec_ref(v_replacement_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(lean_object* v_s_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_593_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__0));
v___x_594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__1));
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_string_utf8_byte_size(v_s_592_);
v___x_597_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_597_, 0, v_s_592_);
lean_ctor_set(v___x_597_, 1, v___x_595_);
lean_ctor_set(v___x_597_, 2, v___x_596_);
v___x_598_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v___x_597_, v___x_594_);
v___x_599_ = lean_string_append(v___x_593_, v___x_598_);
lean_dec_ref(v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0(lean_object* v_s_600_, lean_object* v_pattern_601_, lean_object* v_replacement_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v_s_600_, v_replacement_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___boxed(lean_object* v_s_604_, lean_object* v_pattern_605_, lean_object* v_replacement_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0(v_s_604_, v_pattern_605_, v_replacement_606_);
lean_dec_ref(v_replacement_606_);
lean_dec_ref(v_pattern_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0(lean_object* v_s_608_, lean_object* v_replacement_609_, lean_object* v_inst_610_, lean_object* v_R_611_, lean_object* v_a_612_, lean_object* v_b_613_, lean_object* v_c_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_608_, v_replacement_609_, v_a_612_, v_b_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___boxed(lean_object* v_s_616_, lean_object* v_replacement_617_, lean_object* v_inst_618_, lean_object* v_R_619_, lean_object* v_a_620_, lean_object* v_b_621_, lean_object* v_c_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0(v_s_616_, v_replacement_617_, v_inst_618_, v_R_619_, v_a_620_, v_b_621_, v_c_622_);
lean_dec_ref(v_replacement_617_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
if (lean_obj_tag(v_x_626_) == 0)
{
return v_x_625_;
}
else
{
lean_object* v_head_627_; lean_object* v_tail_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_head_627_ = lean_ctor_get(v_x_626_, 0);
v_tail_628_ = lean_ctor_get(v_x_626_, 1);
v___x_629_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_630_ = lean_string_append(v_x_625_, v___x_629_);
v___x_631_ = l_Int_repr(v_head_627_);
v___x_632_ = lean_string_append(v___x_630_, v___x_631_);
lean_dec_ref(v___x_631_);
v_x_625_ = v___x_632_;
v_x_626_ = v_tail_628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___boxed(lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v_x_634_, v_x_635_);
lean_dec(v_x_635_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(lean_object* v_x_640_){
_start:
{
if (lean_obj_tag(v_x_640_) == 0)
{
lean_object* v___x_641_; 
v___x_641_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__0));
return v___x_641_;
}
else
{
lean_object* v_tail_642_; 
v_tail_642_ = lean_ctor_get(v_x_640_, 1);
if (lean_obj_tag(v_tail_642_) == 0)
{
lean_object* v_head_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_head_643_ = lean_ctor_get(v_x_640_, 0);
v___x_644_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v___x_645_ = l_Int_repr(v_head_643_);
v___x_646_ = lean_string_append(v___x_644_, v___x_645_);
lean_dec_ref(v___x_645_);
v___x_647_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_648_ = lean_string_append(v___x_646_, v___x_647_);
return v___x_648_;
}
else
{
lean_object* v_head_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint32_t v___x_654_; lean_object* v___x_655_; 
v_head_649_ = lean_ctor_get(v_x_640_, 0);
v___x_650_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v___x_651_ = l_Int_repr(v_head_649_);
v___x_652_ = lean_string_append(v___x_650_, v___x_651_);
lean_dec_ref(v___x_651_);
v___x_653_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v___x_652_, v_tail_642_);
v___x_654_ = 93;
v___x_655_ = lean_string_push(v___x_653_, v___x_654_);
return v___x_655_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___boxed(lean_object* v_x_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_656_);
lean_dec(v_x_656_);
return v_res_657_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
if (lean_obj_tag(v_x_659_) == 0)
{
uint8_t v___x_660_; 
v___x_660_ = 1;
return v___x_660_;
}
else
{
uint8_t v___x_661_; 
v___x_661_ = 0;
return v___x_661_;
}
}
else
{
if (lean_obj_tag(v_x_659_) == 0)
{
uint8_t v___x_662_; 
v___x_662_ = 0;
return v___x_662_;
}
else
{
lean_object* v_head_663_; lean_object* v_tail_664_; lean_object* v_head_665_; lean_object* v_tail_666_; uint8_t v___x_667_; 
v_head_663_ = lean_ctor_get(v_x_658_, 0);
v_tail_664_ = lean_ctor_get(v_x_658_, 1);
v_head_665_ = lean_ctor_get(v_x_659_, 0);
v_tail_666_ = lean_ctor_get(v_x_659_, 1);
v___x_667_ = lean_int_dec_eq(v_head_663_, v_head_665_);
if (v___x_667_ == 0)
{
return v___x_667_;
}
else
{
v_x_658_ = v_tail_664_;
v_x_659_ = v_tail_666_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1___boxed(lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_669_, v_x_670_);
lean_dec(v_x_670_);
lean_dec(v_x_669_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString(lean_object* v_s_690_, lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
switch(lean_obj_tag(v_x_692_))
{
case 0:
{
lean_object* v_i_693_; lean_object* v_lowerBound_694_; lean_object* v_upperBound_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___y_700_; lean_object* v___y_707_; lean_object* v___y_708_; 
v_i_693_ = lean_ctor_get(v_x_692_, 2);
lean_inc(v_i_693_);
lean_dec_ref(v_x_692_);
v_lowerBound_694_ = lean_ctor_get(v_s_690_, 0);
lean_inc(v_lowerBound_694_);
v_upperBound_695_ = lean_ctor_get(v_s_690_, 1);
lean_inc(v_upperBound_695_);
lean_dec_ref(v_s_690_);
v___x_696_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_691_);
lean_dec(v_x_691_);
v___x_697_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_698_ = lean_string_append(v___x_696_, v___x_697_);
if (lean_obj_tag(v_lowerBound_694_) == 0)
{
if (lean_obj_tag(v_upperBound_695_) == 0)
{
lean_object* v___x_712_; 
v___x_712_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_700_ = v___x_712_;
goto v___jp_699_;
}
else
{
lean_object* v_val_713_; lean_object* v___x_714_; lean_object* v___y_716_; lean_object* v_intZero_720_; uint8_t v_isNeg_721_; 
v_val_713_ = lean_ctor_get(v_upperBound_695_, 0);
lean_inc(v_val_713_);
lean_dec_ref(v_upperBound_695_);
v___x_714_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_720_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_721_ = lean_int_dec_lt(v_val_713_, v_intZero_720_);
if (v_isNeg_721_ == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; 
v_a_722_ = lean_nat_abs(v_val_713_);
lean_dec(v_val_713_);
v___x_723_ = l_Nat_reprFast(v_a_722_);
v___y_716_ = v___x_723_;
goto v___jp_715_;
}
else
{
lean_object* v_abs_724_; lean_object* v_one_725_; lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_abs_724_ = lean_nat_abs(v_val_713_);
lean_dec(v_val_713_);
v_one_725_ = lean_unsigned_to_nat(1u);
v_a_726_ = lean_nat_sub(v_abs_724_, v_one_725_);
lean_dec(v_abs_724_);
v___x_727_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_728_ = lean_nat_add(v_a_726_, v_one_725_);
lean_dec(v_a_726_);
v___x_729_ = l_Nat_reprFast(v___x_728_);
v___x_730_ = lean_string_append(v___x_727_, v___x_729_);
lean_dec_ref(v___x_729_);
v___y_716_ = v___x_730_;
goto v___jp_715_;
}
v___jp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_string_append(v___x_714_, v___y_716_);
lean_dec_ref(v___y_716_);
v___x_718_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_719_ = lean_string_append(v___x_717_, v___x_718_);
v___y_700_ = v___x_719_;
goto v___jp_699_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_695_) == 0)
{
lean_object* v_val_731_; lean_object* v___x_732_; lean_object* v___y_734_; lean_object* v_intZero_738_; uint8_t v_isNeg_739_; 
v_val_731_ = lean_ctor_get(v_lowerBound_694_, 0);
lean_inc(v_val_731_);
lean_dec_ref(v_lowerBound_694_);
v___x_732_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_738_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_739_ = lean_int_dec_lt(v_val_731_, v_intZero_738_);
if (v_isNeg_739_ == 0)
{
lean_object* v_a_740_; lean_object* v___x_741_; 
v_a_740_ = lean_nat_abs(v_val_731_);
lean_dec(v_val_731_);
v___x_741_ = l_Nat_reprFast(v_a_740_);
v___y_734_ = v___x_741_;
goto v___jp_733_;
}
else
{
lean_object* v_abs_742_; lean_object* v_one_743_; lean_object* v_a_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_abs_742_ = lean_nat_abs(v_val_731_);
lean_dec(v_val_731_);
v_one_743_ = lean_unsigned_to_nat(1u);
v_a_744_ = lean_nat_sub(v_abs_742_, v_one_743_);
lean_dec(v_abs_742_);
v___x_745_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_746_ = lean_nat_add(v_a_744_, v_one_743_);
lean_dec(v_a_744_);
v___x_747_ = l_Nat_reprFast(v___x_746_);
v___x_748_ = lean_string_append(v___x_745_, v___x_747_);
lean_dec_ref(v___x_747_);
v___y_734_ = v___x_748_;
goto v___jp_733_;
}
v___jp_733_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_string_append(v___x_732_, v___y_734_);
lean_dec_ref(v___y_734_);
v___x_736_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_737_ = lean_string_append(v___x_735_, v___x_736_);
v___y_700_ = v___x_737_;
goto v___jp_699_;
}
}
else
{
lean_object* v_val_749_; lean_object* v_val_750_; uint8_t v___x_751_; 
v_val_749_ = lean_ctor_get(v_lowerBound_694_, 0);
lean_inc(v_val_749_);
lean_dec_ref(v_lowerBound_694_);
v_val_750_ = lean_ctor_get(v_upperBound_695_, 0);
lean_inc(v_val_750_);
lean_dec_ref(v_upperBound_695_);
v___x_751_ = lean_int_dec_lt(v_val_750_, v_val_749_);
if (v___x_751_ == 0)
{
uint8_t v___x_752_; 
v___x_752_ = lean_int_dec_eq(v_val_749_, v_val_750_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___y_755_; lean_object* v_intZero_770_; uint8_t v_isNeg_771_; 
v___x_753_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_770_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_771_ = lean_int_dec_lt(v_val_749_, v_intZero_770_);
if (v_isNeg_771_ == 0)
{
lean_object* v_a_772_; lean_object* v___x_773_; 
v_a_772_ = lean_nat_abs(v_val_749_);
lean_dec(v_val_749_);
v___x_773_ = l_Nat_reprFast(v_a_772_);
v___y_755_ = v___x_773_;
goto v___jp_754_;
}
else
{
lean_object* v_abs_774_; lean_object* v_one_775_; lean_object* v_a_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_abs_774_ = lean_nat_abs(v_val_749_);
lean_dec(v_val_749_);
v_one_775_ = lean_unsigned_to_nat(1u);
v_a_776_ = lean_nat_sub(v_abs_774_, v_one_775_);
lean_dec(v_abs_774_);
v___x_777_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_778_ = lean_nat_add(v_a_776_, v_one_775_);
lean_dec(v_a_776_);
v___x_779_ = l_Nat_reprFast(v___x_778_);
v___x_780_ = lean_string_append(v___x_777_, v___x_779_);
lean_dec_ref(v___x_779_);
v___y_755_ = v___x_780_;
goto v___jp_754_;
}
v___jp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_intZero_759_; uint8_t v_isNeg_760_; 
v___x_756_ = lean_string_append(v___x_753_, v___y_755_);
lean_dec_ref(v___y_755_);
v___x_757_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_758_ = lean_string_append(v___x_756_, v___x_757_);
v_intZero_759_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_760_ = lean_int_dec_lt(v_val_750_, v_intZero_759_);
if (v_isNeg_760_ == 0)
{
lean_object* v_a_761_; lean_object* v___x_762_; 
v_a_761_ = lean_nat_abs(v_val_750_);
lean_dec(v_val_750_);
v___x_762_ = l_Nat_reprFast(v_a_761_);
v___y_707_ = v___x_758_;
v___y_708_ = v___x_762_;
goto v___jp_706_;
}
else
{
lean_object* v_abs_763_; lean_object* v_one_764_; lean_object* v_a_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_abs_763_ = lean_nat_abs(v_val_750_);
lean_dec(v_val_750_);
v_one_764_ = lean_unsigned_to_nat(1u);
v_a_765_ = lean_nat_sub(v_abs_763_, v_one_764_);
lean_dec(v_abs_763_);
v___x_766_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_767_ = lean_nat_add(v_a_765_, v_one_764_);
lean_dec(v_a_765_);
v___x_768_ = l_Nat_reprFast(v___x_767_);
v___x_769_ = lean_string_append(v___x_766_, v___x_768_);
lean_dec_ref(v___x_768_);
v___y_707_ = v___x_758_;
v___y_708_ = v___x_769_;
goto v___jp_706_;
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___y_783_; lean_object* v_intZero_787_; uint8_t v_isNeg_788_; 
lean_dec(v_val_750_);
v___x_781_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_787_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_788_ = lean_int_dec_lt(v_val_749_, v_intZero_787_);
if (v_isNeg_788_ == 0)
{
lean_object* v_a_789_; lean_object* v___x_790_; 
v_a_789_ = lean_nat_abs(v_val_749_);
lean_dec(v_val_749_);
v___x_790_ = l_Nat_reprFast(v_a_789_);
v___y_783_ = v___x_790_;
goto v___jp_782_;
}
else
{
lean_object* v_abs_791_; lean_object* v_one_792_; lean_object* v_a_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_abs_791_ = lean_nat_abs(v_val_749_);
lean_dec(v_val_749_);
v_one_792_ = lean_unsigned_to_nat(1u);
v_a_793_ = lean_nat_sub(v_abs_791_, v_one_792_);
lean_dec(v_abs_791_);
v___x_794_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_795_ = lean_nat_add(v_a_793_, v_one_792_);
lean_dec(v_a_793_);
v___x_796_ = l_Nat_reprFast(v___x_795_);
v___x_797_ = lean_string_append(v___x_794_, v___x_796_);
lean_dec_ref(v___x_796_);
v___y_783_ = v___x_797_;
goto v___jp_782_;
}
v___jp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_784_ = lean_string_append(v___x_781_, v___y_783_);
lean_dec_ref(v___y_783_);
v___x_785_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_786_ = lean_string_append(v___x_784_, v___x_785_);
v___y_700_ = v___x_786_;
goto v___jp_699_;
}
}
}
else
{
lean_object* v___x_798_; 
lean_dec(v_val_750_);
lean_dec(v_val_749_);
v___x_798_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_700_ = v___x_798_;
goto v___jp_699_;
}
}
}
v___jp_699_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_701_ = lean_string_append(v___x_698_, v___y_700_);
lean_dec_ref(v___y_700_);
v___x_702_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__1));
v___x_703_ = lean_string_append(v___x_701_, v___x_702_);
v___x_704_ = l_Nat_reprFast(v_i_693_);
v___x_705_ = lean_string_append(v___x_703_, v___x_704_);
lean_dec_ref(v___x_704_);
return v___x_705_;
}
v___jp_706_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_709_ = lean_string_append(v___y_707_, v___y_708_);
lean_dec_ref(v___y_708_);
v___x_710_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_711_ = lean_string_append(v___x_709_, v___x_710_);
v___y_700_ = v___x_711_;
goto v___jp_699_;
}
}
case 1:
{
lean_object* v_s_799_; lean_object* v_c_800_; lean_object* v_j_801_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; uint8_t v___y_859_; uint8_t v___x_922_; 
v_s_799_ = lean_ctor_get(v_x_692_, 0);
lean_inc_ref(v_s_799_);
v_c_800_ = lean_ctor_get(v_x_692_, 1);
lean_inc(v_c_800_);
v_j_801_ = lean_ctor_get(v_x_692_, 2);
lean_inc_ref(v_j_801_);
lean_dec_ref(v_x_692_);
v___x_922_ = l_Lean_Omega_instBEqConstraint_beq(v_s_690_, v_s_799_);
if (v___x_922_ == 0)
{
v___y_859_ = v___x_922_;
goto v___jp_858_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_691_, v_c_800_);
v___y_859_ = v___x_923_;
goto v___jp_858_;
}
v___jp_802_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_805_ = lean_string_append(v___y_803_, v___y_804_);
lean_dec_ref(v___y_804_);
v___x_806_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9));
v___x_807_ = lean_string_append(v___x_805_, v___x_806_);
v___x_808_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_799_, v_c_800_, v_j_801_);
v___x_809_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_808_);
v___x_810_ = lean_string_append(v___x_807_, v___x_809_);
lean_dec_ref(v___x_809_);
return v___x_810_;
}
v___jp_811_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_inc_ref(v___y_813_);
v___x_815_ = lean_string_append(v___y_813_, v___y_814_);
lean_dec_ref(v___y_814_);
v___x_816_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_817_ = lean_string_append(v___x_815_, v___x_816_);
v___y_803_ = v___y_812_;
v___y_804_ = v___x_817_;
goto v___jp_802_;
}
v___jp_818_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_inc_ref(v___y_819_);
v___x_822_ = lean_string_append(v___y_819_, v___y_821_);
lean_dec_ref(v___y_821_);
v___x_823_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_824_ = lean_string_append(v___x_822_, v___x_823_);
v___y_803_ = v___y_820_;
v___y_804_ = v___x_824_;
goto v___jp_802_;
}
v___jp_825_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_string_append(v___y_827_, v___y_828_);
lean_dec_ref(v___y_828_);
v___x_830_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_831_ = lean_string_append(v___x_829_, v___x_830_);
v___y_803_ = v___y_826_;
v___y_804_ = v___x_831_;
goto v___jp_802_;
}
v___jp_832_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v_intZero_840_; uint8_t v_isNeg_841_; 
lean_inc_ref(v___y_834_);
v___x_837_ = lean_string_append(v___y_834_, v___y_836_);
lean_dec_ref(v___y_836_);
v___x_838_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_839_ = lean_string_append(v___x_837_, v___x_838_);
v_intZero_840_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_841_ = lean_int_dec_lt(v___y_835_, v_intZero_840_);
if (v_isNeg_841_ == 0)
{
lean_object* v_a_842_; lean_object* v___x_843_; 
v_a_842_ = lean_nat_abs(v___y_835_);
lean_dec(v___y_835_);
v___x_843_ = l_Nat_reprFast(v_a_842_);
v___y_826_ = v___y_833_;
v___y_827_ = v___x_839_;
v___y_828_ = v___x_843_;
goto v___jp_825_;
}
else
{
lean_object* v_abs_844_; lean_object* v_one_845_; lean_object* v_a_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_abs_844_ = lean_nat_abs(v___y_835_);
lean_dec(v___y_835_);
v_one_845_ = lean_unsigned_to_nat(1u);
v_a_846_ = lean_nat_sub(v_abs_844_, v_one_845_);
lean_dec(v_abs_844_);
v___x_847_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_848_ = lean_nat_add(v_a_846_, v_one_845_);
lean_dec(v_a_846_);
v___x_849_ = l_Nat_reprFast(v___x_848_);
v___x_850_ = lean_string_append(v___x_847_, v___x_849_);
lean_dec_ref(v___x_849_);
v___y_826_ = v___y_833_;
v___y_827_ = v___x_839_;
v___y_828_ = v___x_850_;
goto v___jp_825_;
}
}
v___jp_851_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_inc_ref(v___y_853_);
v___x_855_ = lean_string_append(v___y_853_, v___y_854_);
lean_dec_ref(v___y_854_);
v___x_856_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_857_ = lean_string_append(v___x_855_, v___x_856_);
v___y_803_ = v___y_852_;
v___y_804_ = v___x_857_;
goto v___jp_802_;
}
v___jp_858_:
{
if (v___y_859_ == 0)
{
lean_object* v_lowerBound_860_; lean_object* v_upperBound_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_lowerBound_860_ = lean_ctor_get(v_s_690_, 0);
lean_inc(v_lowerBound_860_);
v_upperBound_861_ = lean_ctor_get(v_s_690_, 1);
lean_inc(v_upperBound_861_);
lean_dec_ref(v_s_690_);
v___x_862_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_691_);
lean_dec(v_x_691_);
v___x_863_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_864_ = lean_string_append(v___x_862_, v___x_863_);
if (lean_obj_tag(v_lowerBound_860_) == 0)
{
if (lean_obj_tag(v_upperBound_861_) == 0)
{
lean_object* v___x_865_; 
v___x_865_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_803_ = v___x_864_;
v___y_804_ = v___x_865_;
goto v___jp_802_;
}
else
{
lean_object* v_val_866_; lean_object* v___x_867_; lean_object* v_intZero_868_; uint8_t v_isNeg_869_; 
v_val_866_ = lean_ctor_get(v_upperBound_861_, 0);
lean_inc(v_val_866_);
lean_dec_ref(v_upperBound_861_);
v___x_867_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_868_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_869_ = lean_int_dec_lt(v_val_866_, v_intZero_868_);
if (v_isNeg_869_ == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; 
v_a_870_ = lean_nat_abs(v_val_866_);
lean_dec(v_val_866_);
v___x_871_ = l_Nat_reprFast(v_a_870_);
v___y_812_ = v___x_864_;
v___y_813_ = v___x_867_;
v___y_814_ = v___x_871_;
goto v___jp_811_;
}
else
{
lean_object* v_abs_872_; lean_object* v_one_873_; lean_object* v_a_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_abs_872_ = lean_nat_abs(v_val_866_);
lean_dec(v_val_866_);
v_one_873_ = lean_unsigned_to_nat(1u);
v_a_874_ = lean_nat_sub(v_abs_872_, v_one_873_);
lean_dec(v_abs_872_);
v___x_875_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_876_ = lean_nat_add(v_a_874_, v_one_873_);
lean_dec(v_a_874_);
v___x_877_ = l_Nat_reprFast(v___x_876_);
v___x_878_ = lean_string_append(v___x_875_, v___x_877_);
lean_dec_ref(v___x_877_);
v___y_812_ = v___x_864_;
v___y_813_ = v___x_867_;
v___y_814_ = v___x_878_;
goto v___jp_811_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_861_) == 0)
{
lean_object* v_val_879_; lean_object* v___x_880_; lean_object* v_intZero_881_; uint8_t v_isNeg_882_; 
v_val_879_ = lean_ctor_get(v_lowerBound_860_, 0);
lean_inc(v_val_879_);
lean_dec_ref(v_lowerBound_860_);
v___x_880_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_881_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_882_ = lean_int_dec_lt(v_val_879_, v_intZero_881_);
if (v_isNeg_882_ == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; 
v_a_883_ = lean_nat_abs(v_val_879_);
lean_dec(v_val_879_);
v___x_884_ = l_Nat_reprFast(v_a_883_);
v___y_819_ = v___x_880_;
v___y_820_ = v___x_864_;
v___y_821_ = v___x_884_;
goto v___jp_818_;
}
else
{
lean_object* v_abs_885_; lean_object* v_one_886_; lean_object* v_a_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_abs_885_ = lean_nat_abs(v_val_879_);
lean_dec(v_val_879_);
v_one_886_ = lean_unsigned_to_nat(1u);
v_a_887_ = lean_nat_sub(v_abs_885_, v_one_886_);
lean_dec(v_abs_885_);
v___x_888_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_889_ = lean_nat_add(v_a_887_, v_one_886_);
lean_dec(v_a_887_);
v___x_890_ = l_Nat_reprFast(v___x_889_);
v___x_891_ = lean_string_append(v___x_888_, v___x_890_);
lean_dec_ref(v___x_890_);
v___y_819_ = v___x_880_;
v___y_820_ = v___x_864_;
v___y_821_ = v___x_891_;
goto v___jp_818_;
}
}
else
{
lean_object* v_val_892_; lean_object* v_val_893_; uint8_t v___x_894_; 
v_val_892_ = lean_ctor_get(v_lowerBound_860_, 0);
lean_inc(v_val_892_);
lean_dec_ref(v_lowerBound_860_);
v_val_893_ = lean_ctor_get(v_upperBound_861_, 0);
lean_inc(v_val_893_);
lean_dec_ref(v_upperBound_861_);
v___x_894_ = lean_int_dec_lt(v_val_893_, v_val_892_);
if (v___x_894_ == 0)
{
uint8_t v___x_895_; 
v___x_895_ = lean_int_dec_eq(v_val_892_, v_val_893_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v_intZero_897_; uint8_t v_isNeg_898_; 
v___x_896_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_897_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_898_ = lean_int_dec_lt(v_val_892_, v_intZero_897_);
if (v_isNeg_898_ == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; 
v_a_899_ = lean_nat_abs(v_val_892_);
lean_dec(v_val_892_);
v___x_900_ = l_Nat_reprFast(v_a_899_);
v___y_833_ = v___x_864_;
v___y_834_ = v___x_896_;
v___y_835_ = v_val_893_;
v___y_836_ = v___x_900_;
goto v___jp_832_;
}
else
{
lean_object* v_abs_901_; lean_object* v_one_902_; lean_object* v_a_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_abs_901_ = lean_nat_abs(v_val_892_);
lean_dec(v_val_892_);
v_one_902_ = lean_unsigned_to_nat(1u);
v_a_903_ = lean_nat_sub(v_abs_901_, v_one_902_);
lean_dec(v_abs_901_);
v___x_904_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_905_ = lean_nat_add(v_a_903_, v_one_902_);
lean_dec(v_a_903_);
v___x_906_ = l_Nat_reprFast(v___x_905_);
v___x_907_ = lean_string_append(v___x_904_, v___x_906_);
lean_dec_ref(v___x_906_);
v___y_833_ = v___x_864_;
v___y_834_ = v___x_896_;
v___y_835_ = v_val_893_;
v___y_836_ = v___x_907_;
goto v___jp_832_;
}
}
else
{
lean_object* v___x_908_; lean_object* v_intZero_909_; uint8_t v_isNeg_910_; 
lean_dec(v_val_893_);
v___x_908_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_909_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_910_ = lean_int_dec_lt(v_val_892_, v_intZero_909_);
if (v_isNeg_910_ == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; 
v_a_911_ = lean_nat_abs(v_val_892_);
lean_dec(v_val_892_);
v___x_912_ = l_Nat_reprFast(v_a_911_);
v___y_852_ = v___x_864_;
v___y_853_ = v___x_908_;
v___y_854_ = v___x_912_;
goto v___jp_851_;
}
else
{
lean_object* v_abs_913_; lean_object* v_one_914_; lean_object* v_a_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_abs_913_ = lean_nat_abs(v_val_892_);
lean_dec(v_val_892_);
v_one_914_ = lean_unsigned_to_nat(1u);
v_a_915_ = lean_nat_sub(v_abs_913_, v_one_914_);
lean_dec(v_abs_913_);
v___x_916_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_917_ = lean_nat_add(v_a_915_, v_one_914_);
lean_dec(v_a_915_);
v___x_918_ = l_Nat_reprFast(v___x_917_);
v___x_919_ = lean_string_append(v___x_916_, v___x_918_);
lean_dec_ref(v___x_918_);
v___y_852_ = v___x_864_;
v___y_853_ = v___x_908_;
v___y_854_ = v___x_919_;
goto v___jp_851_;
}
}
}
else
{
lean_object* v___x_920_; 
lean_dec(v_val_893_);
lean_dec(v_val_892_);
v___x_920_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_803_ = v___x_864_;
v___y_804_ = v___x_920_;
goto v___jp_802_;
}
}
}
}
else
{
lean_dec(v_x_691_);
lean_dec_ref(v_s_690_);
v_s_690_ = v_s_799_;
v_x_691_ = v_c_800_;
v_x_692_ = v_j_801_;
goto _start;
}
}
}
case 2:
{
lean_object* v_s_924_; lean_object* v_t_925_; lean_object* v_j_926_; lean_object* v_k_927_; lean_object* v_lowerBound_928_; lean_object* v_upperBound_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___y_934_; lean_object* v___y_947_; lean_object* v___y_948_; 
v_s_924_ = lean_ctor_get(v_x_692_, 0);
lean_inc_ref(v_s_924_);
v_t_925_ = lean_ctor_get(v_x_692_, 1);
lean_inc_ref(v_t_925_);
v_j_926_ = lean_ctor_get(v_x_692_, 3);
lean_inc_ref(v_j_926_);
v_k_927_ = lean_ctor_get(v_x_692_, 4);
lean_inc_ref(v_k_927_);
lean_dec_ref(v_x_692_);
v_lowerBound_928_ = lean_ctor_get(v_s_690_, 0);
lean_inc(v_lowerBound_928_);
v_upperBound_929_ = lean_ctor_get(v_s_690_, 1);
lean_inc(v_upperBound_929_);
lean_dec_ref(v_s_690_);
v___x_930_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_691_);
v___x_931_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
if (lean_obj_tag(v_lowerBound_928_) == 0)
{
if (lean_obj_tag(v_upperBound_929_) == 0)
{
lean_object* v___x_952_; 
v___x_952_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_934_ = v___x_952_;
goto v___jp_933_;
}
else
{
lean_object* v_val_953_; lean_object* v___x_954_; lean_object* v___y_956_; lean_object* v_intZero_960_; uint8_t v_isNeg_961_; 
v_val_953_ = lean_ctor_get(v_upperBound_929_, 0);
lean_inc(v_val_953_);
lean_dec_ref(v_upperBound_929_);
v___x_954_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_960_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_961_ = lean_int_dec_lt(v_val_953_, v_intZero_960_);
if (v_isNeg_961_ == 0)
{
lean_object* v_a_962_; lean_object* v___x_963_; 
v_a_962_ = lean_nat_abs(v_val_953_);
lean_dec(v_val_953_);
v___x_963_ = l_Nat_reprFast(v_a_962_);
v___y_956_ = v___x_963_;
goto v___jp_955_;
}
else
{
lean_object* v_abs_964_; lean_object* v_one_965_; lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_abs_964_ = lean_nat_abs(v_val_953_);
lean_dec(v_val_953_);
v_one_965_ = lean_unsigned_to_nat(1u);
v_a_966_ = lean_nat_sub(v_abs_964_, v_one_965_);
lean_dec(v_abs_964_);
v___x_967_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_968_ = lean_nat_add(v_a_966_, v_one_965_);
lean_dec(v_a_966_);
v___x_969_ = l_Nat_reprFast(v___x_968_);
v___x_970_ = lean_string_append(v___x_967_, v___x_969_);
lean_dec_ref(v___x_969_);
v___y_956_ = v___x_970_;
goto v___jp_955_;
}
v___jp_955_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = lean_string_append(v___x_954_, v___y_956_);
lean_dec_ref(v___y_956_);
v___x_958_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_959_ = lean_string_append(v___x_957_, v___x_958_);
v___y_934_ = v___x_959_;
goto v___jp_933_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_929_) == 0)
{
lean_object* v_val_971_; lean_object* v___x_972_; lean_object* v___y_974_; lean_object* v_intZero_978_; uint8_t v_isNeg_979_; 
v_val_971_ = lean_ctor_get(v_lowerBound_928_, 0);
lean_inc(v_val_971_);
lean_dec_ref(v_lowerBound_928_);
v___x_972_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_978_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_979_ = lean_int_dec_lt(v_val_971_, v_intZero_978_);
if (v_isNeg_979_ == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; 
v_a_980_ = lean_nat_abs(v_val_971_);
lean_dec(v_val_971_);
v___x_981_ = l_Nat_reprFast(v_a_980_);
v___y_974_ = v___x_981_;
goto v___jp_973_;
}
else
{
lean_object* v_abs_982_; lean_object* v_one_983_; lean_object* v_a_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_abs_982_ = lean_nat_abs(v_val_971_);
lean_dec(v_val_971_);
v_one_983_ = lean_unsigned_to_nat(1u);
v_a_984_ = lean_nat_sub(v_abs_982_, v_one_983_);
lean_dec(v_abs_982_);
v___x_985_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_986_ = lean_nat_add(v_a_984_, v_one_983_);
lean_dec(v_a_984_);
v___x_987_ = l_Nat_reprFast(v___x_986_);
v___x_988_ = lean_string_append(v___x_985_, v___x_987_);
lean_dec_ref(v___x_987_);
v___y_974_ = v___x_988_;
goto v___jp_973_;
}
v___jp_973_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_string_append(v___x_972_, v___y_974_);
lean_dec_ref(v___y_974_);
v___x_976_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_977_ = lean_string_append(v___x_975_, v___x_976_);
v___y_934_ = v___x_977_;
goto v___jp_933_;
}
}
else
{
lean_object* v_val_989_; lean_object* v_val_990_; uint8_t v___x_991_; 
v_val_989_ = lean_ctor_get(v_lowerBound_928_, 0);
lean_inc(v_val_989_);
lean_dec_ref(v_lowerBound_928_);
v_val_990_ = lean_ctor_get(v_upperBound_929_, 0);
lean_inc(v_val_990_);
lean_dec_ref(v_upperBound_929_);
v___x_991_ = lean_int_dec_lt(v_val_990_, v_val_989_);
if (v___x_991_ == 0)
{
uint8_t v___x_992_; 
v___x_992_ = lean_int_dec_eq(v_val_989_, v_val_990_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___y_995_; lean_object* v_intZero_1010_; uint8_t v_isNeg_1011_; 
v___x_993_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1010_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1011_ = lean_int_dec_lt(v_val_989_, v_intZero_1010_);
if (v_isNeg_1011_ == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; 
v_a_1012_ = lean_nat_abs(v_val_989_);
lean_dec(v_val_989_);
v___x_1013_ = l_Nat_reprFast(v_a_1012_);
v___y_995_ = v___x_1013_;
goto v___jp_994_;
}
else
{
lean_object* v_abs_1014_; lean_object* v_one_1015_; lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_abs_1014_ = lean_nat_abs(v_val_989_);
lean_dec(v_val_989_);
v_one_1015_ = lean_unsigned_to_nat(1u);
v_a_1016_ = lean_nat_sub(v_abs_1014_, v_one_1015_);
lean_dec(v_abs_1014_);
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1018_ = lean_nat_add(v_a_1016_, v_one_1015_);
lean_dec(v_a_1016_);
v___x_1019_ = l_Nat_reprFast(v___x_1018_);
v___x_1020_ = lean_string_append(v___x_1017_, v___x_1019_);
lean_dec_ref(v___x_1019_);
v___y_995_ = v___x_1020_;
goto v___jp_994_;
}
v___jp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v_intZero_999_; uint8_t v_isNeg_1000_; 
v___x_996_ = lean_string_append(v___x_993_, v___y_995_);
lean_dec_ref(v___y_995_);
v___x_997_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_998_ = lean_string_append(v___x_996_, v___x_997_);
v_intZero_999_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1000_ = lean_int_dec_lt(v_val_990_, v_intZero_999_);
if (v_isNeg_1000_ == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_nat_abs(v_val_990_);
lean_dec(v_val_990_);
v___x_1002_ = l_Nat_reprFast(v_a_1001_);
v___y_947_ = v___x_998_;
v___y_948_ = v___x_1002_;
goto v___jp_946_;
}
else
{
lean_object* v_abs_1003_; lean_object* v_one_1004_; lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_abs_1003_ = lean_nat_abs(v_val_990_);
lean_dec(v_val_990_);
v_one_1004_ = lean_unsigned_to_nat(1u);
v_a_1005_ = lean_nat_sub(v_abs_1003_, v_one_1004_);
lean_dec(v_abs_1003_);
v___x_1006_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1007_ = lean_nat_add(v_a_1005_, v_one_1004_);
lean_dec(v_a_1005_);
v___x_1008_ = l_Nat_reprFast(v___x_1007_);
v___x_1009_ = lean_string_append(v___x_1006_, v___x_1008_);
lean_dec_ref(v___x_1008_);
v___y_947_ = v___x_998_;
v___y_948_ = v___x_1009_;
goto v___jp_946_;
}
}
}
else
{
lean_object* v___x_1021_; lean_object* v___y_1023_; lean_object* v_intZero_1027_; uint8_t v_isNeg_1028_; 
lean_dec(v_val_990_);
v___x_1021_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1027_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1028_ = lean_int_dec_lt(v_val_989_, v_intZero_1027_);
if (v_isNeg_1028_ == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1030_; 
v_a_1029_ = lean_nat_abs(v_val_989_);
lean_dec(v_val_989_);
v___x_1030_ = l_Nat_reprFast(v_a_1029_);
v___y_1023_ = v___x_1030_;
goto v___jp_1022_;
}
else
{
lean_object* v_abs_1031_; lean_object* v_one_1032_; lean_object* v_a_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_abs_1031_ = lean_nat_abs(v_val_989_);
lean_dec(v_val_989_);
v_one_1032_ = lean_unsigned_to_nat(1u);
v_a_1033_ = lean_nat_sub(v_abs_1031_, v_one_1032_);
lean_dec(v_abs_1031_);
v___x_1034_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1035_ = lean_nat_add(v_a_1033_, v_one_1032_);
lean_dec(v_a_1033_);
v___x_1036_ = l_Nat_reprFast(v___x_1035_);
v___x_1037_ = lean_string_append(v___x_1034_, v___x_1036_);
lean_dec_ref(v___x_1036_);
v___y_1023_ = v___x_1037_;
goto v___jp_1022_;
}
v___jp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = lean_string_append(v___x_1021_, v___y_1023_);
lean_dec_ref(v___y_1023_);
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1026_ = lean_string_append(v___x_1024_, v___x_1025_);
v___y_934_ = v___x_1026_;
goto v___jp_933_;
}
}
}
else
{
lean_object* v___x_1038_; 
lean_dec(v_val_990_);
lean_dec(v_val_989_);
v___x_1038_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_934_ = v___x_1038_;
goto v___jp_933_;
}
}
}
v___jp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_935_ = lean_string_append(v___x_932_, v___y_934_);
lean_dec_ref(v___y_934_);
v___x_936_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__10));
v___x_937_ = lean_string_append(v___x_935_, v___x_936_);
lean_inc(v_x_691_);
v___x_938_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_924_, v_x_691_, v_j_926_);
v___x_939_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_938_);
v___x_940_ = lean_string_append(v___x_937_, v___x_939_);
lean_dec_ref(v___x_939_);
v___x_941_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_942_ = lean_string_append(v___x_940_, v___x_941_);
v___x_943_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_925_, v_x_691_, v_k_927_);
v___x_944_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_943_);
v___x_945_ = lean_string_append(v___x_942_, v___x_944_);
lean_dec_ref(v___x_944_);
return v___x_945_;
}
v___jp_946_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_string_append(v___y_947_, v___y_948_);
lean_dec_ref(v___y_948_);
v___x_950_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_951_ = lean_string_append(v___x_949_, v___x_950_);
v___y_934_ = v___x_951_;
goto v___jp_933_;
}
}
case 3:
{
lean_object* v_s_1039_; lean_object* v_t_1040_; lean_object* v_x_1041_; lean_object* v_y_1042_; lean_object* v_a_1043_; lean_object* v_j_1044_; lean_object* v_b_1045_; lean_object* v_k_1046_; lean_object* v_lowerBound_1047_; lean_object* v_upperBound_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___y_1053_; lean_object* v___y_1074_; lean_object* v___y_1075_; 
v_s_1039_ = lean_ctor_get(v_x_692_, 0);
lean_inc_ref(v_s_1039_);
v_t_1040_ = lean_ctor_get(v_x_692_, 1);
lean_inc_ref(v_t_1040_);
v_x_1041_ = lean_ctor_get(v_x_692_, 2);
lean_inc(v_x_1041_);
v_y_1042_ = lean_ctor_get(v_x_692_, 3);
lean_inc(v_y_1042_);
v_a_1043_ = lean_ctor_get(v_x_692_, 4);
lean_inc(v_a_1043_);
v_j_1044_ = lean_ctor_get(v_x_692_, 5);
lean_inc_ref(v_j_1044_);
v_b_1045_ = lean_ctor_get(v_x_692_, 6);
lean_inc(v_b_1045_);
v_k_1046_ = lean_ctor_get(v_x_692_, 7);
lean_inc_ref(v_k_1046_);
lean_dec_ref(v_x_692_);
v_lowerBound_1047_ = lean_ctor_get(v_s_690_, 0);
lean_inc(v_lowerBound_1047_);
v_upperBound_1048_ = lean_ctor_get(v_s_690_, 1);
lean_inc(v_upperBound_1048_);
lean_dec_ref(v_s_690_);
v___x_1049_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_691_);
lean_dec(v_x_691_);
v___x_1050_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1051_ = lean_string_append(v___x_1049_, v___x_1050_);
if (lean_obj_tag(v_lowerBound_1047_) == 0)
{
if (lean_obj_tag(v_upperBound_1048_) == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1053_ = v___x_1079_;
goto v___jp_1052_;
}
else
{
lean_object* v_val_1080_; lean_object* v___x_1081_; lean_object* v___y_1083_; lean_object* v_intZero_1087_; uint8_t v_isNeg_1088_; 
v_val_1080_ = lean_ctor_get(v_upperBound_1048_, 0);
lean_inc(v_val_1080_);
lean_dec_ref(v_upperBound_1048_);
v___x_1081_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1087_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1088_ = lean_int_dec_lt(v_val_1080_, v_intZero_1087_);
if (v_isNeg_1088_ == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; 
v_a_1089_ = lean_nat_abs(v_val_1080_);
lean_dec(v_val_1080_);
v___x_1090_ = l_Nat_reprFast(v_a_1089_);
v___y_1083_ = v___x_1090_;
goto v___jp_1082_;
}
else
{
lean_object* v_abs_1091_; lean_object* v_one_1092_; lean_object* v_a_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_abs_1091_ = lean_nat_abs(v_val_1080_);
lean_dec(v_val_1080_);
v_one_1092_ = lean_unsigned_to_nat(1u);
v_a_1093_ = lean_nat_sub(v_abs_1091_, v_one_1092_);
lean_dec(v_abs_1091_);
v___x_1094_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1095_ = lean_nat_add(v_a_1093_, v_one_1092_);
lean_dec(v_a_1093_);
v___x_1096_ = l_Nat_reprFast(v___x_1095_);
v___x_1097_ = lean_string_append(v___x_1094_, v___x_1096_);
lean_dec_ref(v___x_1096_);
v___y_1083_ = v___x_1097_;
goto v___jp_1082_;
}
v___jp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = lean_string_append(v___x_1081_, v___y_1083_);
lean_dec_ref(v___y_1083_);
v___x_1085_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1086_ = lean_string_append(v___x_1084_, v___x_1085_);
v___y_1053_ = v___x_1086_;
goto v___jp_1052_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1048_) == 0)
{
lean_object* v_val_1098_; lean_object* v___x_1099_; lean_object* v___y_1101_; lean_object* v_intZero_1105_; uint8_t v_isNeg_1106_; 
v_val_1098_ = lean_ctor_get(v_lowerBound_1047_, 0);
lean_inc(v_val_1098_);
lean_dec_ref(v_lowerBound_1047_);
v___x_1099_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1105_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1106_ = lean_int_dec_lt(v_val_1098_, v_intZero_1105_);
if (v_isNeg_1106_ == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1108_; 
v_a_1107_ = lean_nat_abs(v_val_1098_);
lean_dec(v_val_1098_);
v___x_1108_ = l_Nat_reprFast(v_a_1107_);
v___y_1101_ = v___x_1108_;
goto v___jp_1100_;
}
else
{
lean_object* v_abs_1109_; lean_object* v_one_1110_; lean_object* v_a_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_abs_1109_ = lean_nat_abs(v_val_1098_);
lean_dec(v_val_1098_);
v_one_1110_ = lean_unsigned_to_nat(1u);
v_a_1111_ = lean_nat_sub(v_abs_1109_, v_one_1110_);
lean_dec(v_abs_1109_);
v___x_1112_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1113_ = lean_nat_add(v_a_1111_, v_one_1110_);
lean_dec(v_a_1111_);
v___x_1114_ = l_Nat_reprFast(v___x_1113_);
v___x_1115_ = lean_string_append(v___x_1112_, v___x_1114_);
lean_dec_ref(v___x_1114_);
v___y_1101_ = v___x_1115_;
goto v___jp_1100_;
}
v___jp_1100_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = lean_string_append(v___x_1099_, v___y_1101_);
lean_dec_ref(v___y_1101_);
v___x_1103_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1104_ = lean_string_append(v___x_1102_, v___x_1103_);
v___y_1053_ = v___x_1104_;
goto v___jp_1052_;
}
}
else
{
lean_object* v_val_1116_; lean_object* v_val_1117_; uint8_t v___x_1118_; 
v_val_1116_ = lean_ctor_get(v_lowerBound_1047_, 0);
lean_inc(v_val_1116_);
lean_dec_ref(v_lowerBound_1047_);
v_val_1117_ = lean_ctor_get(v_upperBound_1048_, 0);
lean_inc(v_val_1117_);
lean_dec_ref(v_upperBound_1048_);
v___x_1118_ = lean_int_dec_lt(v_val_1117_, v_val_1116_);
if (v___x_1118_ == 0)
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_int_dec_eq(v_val_1116_, v_val_1117_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___y_1122_; lean_object* v_intZero_1137_; uint8_t v_isNeg_1138_; 
v___x_1120_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1137_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1138_ = lean_int_dec_lt(v_val_1116_, v_intZero_1137_);
if (v_isNeg_1138_ == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1140_; 
v_a_1139_ = lean_nat_abs(v_val_1116_);
lean_dec(v_val_1116_);
v___x_1140_ = l_Nat_reprFast(v_a_1139_);
v___y_1122_ = v___x_1140_;
goto v___jp_1121_;
}
else
{
lean_object* v_abs_1141_; lean_object* v_one_1142_; lean_object* v_a_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_abs_1141_ = lean_nat_abs(v_val_1116_);
lean_dec(v_val_1116_);
v_one_1142_ = lean_unsigned_to_nat(1u);
v_a_1143_ = lean_nat_sub(v_abs_1141_, v_one_1142_);
lean_dec(v_abs_1141_);
v___x_1144_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1145_ = lean_nat_add(v_a_1143_, v_one_1142_);
lean_dec(v_a_1143_);
v___x_1146_ = l_Nat_reprFast(v___x_1145_);
v___x_1147_ = lean_string_append(v___x_1144_, v___x_1146_);
lean_dec_ref(v___x_1146_);
v___y_1122_ = v___x_1147_;
goto v___jp_1121_;
}
v___jp_1121_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v_intZero_1126_; uint8_t v_isNeg_1127_; 
v___x_1123_ = lean_string_append(v___x_1120_, v___y_1122_);
lean_dec_ref(v___y_1122_);
v___x_1124_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1125_ = lean_string_append(v___x_1123_, v___x_1124_);
v_intZero_1126_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1127_ = lean_int_dec_lt(v_val_1117_, v_intZero_1126_);
if (v_isNeg_1127_ == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1129_; 
v_a_1128_ = lean_nat_abs(v_val_1117_);
lean_dec(v_val_1117_);
v___x_1129_ = l_Nat_reprFast(v_a_1128_);
v___y_1074_ = v___x_1125_;
v___y_1075_ = v___x_1129_;
goto v___jp_1073_;
}
else
{
lean_object* v_abs_1130_; lean_object* v_one_1131_; lean_object* v_a_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v_abs_1130_ = lean_nat_abs(v_val_1117_);
lean_dec(v_val_1117_);
v_one_1131_ = lean_unsigned_to_nat(1u);
v_a_1132_ = lean_nat_sub(v_abs_1130_, v_one_1131_);
lean_dec(v_abs_1130_);
v___x_1133_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1134_ = lean_nat_add(v_a_1132_, v_one_1131_);
lean_dec(v_a_1132_);
v___x_1135_ = l_Nat_reprFast(v___x_1134_);
v___x_1136_ = lean_string_append(v___x_1133_, v___x_1135_);
lean_dec_ref(v___x_1135_);
v___y_1074_ = v___x_1125_;
v___y_1075_ = v___x_1136_;
goto v___jp_1073_;
}
}
}
else
{
lean_object* v___x_1148_; lean_object* v___y_1150_; lean_object* v_intZero_1154_; uint8_t v_isNeg_1155_; 
lean_dec(v_val_1117_);
v___x_1148_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1154_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1155_ = lean_int_dec_lt(v_val_1116_, v_intZero_1154_);
if (v_isNeg_1155_ == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1157_; 
v_a_1156_ = lean_nat_abs(v_val_1116_);
lean_dec(v_val_1116_);
v___x_1157_ = l_Nat_reprFast(v_a_1156_);
v___y_1150_ = v___x_1157_;
goto v___jp_1149_;
}
else
{
lean_object* v_abs_1158_; lean_object* v_one_1159_; lean_object* v_a_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_abs_1158_ = lean_nat_abs(v_val_1116_);
lean_dec(v_val_1116_);
v_one_1159_ = lean_unsigned_to_nat(1u);
v_a_1160_ = lean_nat_sub(v_abs_1158_, v_one_1159_);
lean_dec(v_abs_1158_);
v___x_1161_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1162_ = lean_nat_add(v_a_1160_, v_one_1159_);
lean_dec(v_a_1160_);
v___x_1163_ = l_Nat_reprFast(v___x_1162_);
v___x_1164_ = lean_string_append(v___x_1161_, v___x_1163_);
lean_dec_ref(v___x_1163_);
v___y_1150_ = v___x_1164_;
goto v___jp_1149_;
}
v___jp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = lean_string_append(v___x_1148_, v___y_1150_);
lean_dec_ref(v___y_1150_);
v___x_1152_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1153_ = lean_string_append(v___x_1151_, v___x_1152_);
v___y_1053_ = v___x_1153_;
goto v___jp_1052_;
}
}
}
else
{
lean_object* v___x_1165_; 
lean_dec(v_val_1117_);
lean_dec(v_val_1116_);
v___x_1165_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1053_ = v___x_1165_;
goto v___jp_1052_;
}
}
}
v___jp_1052_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1054_ = lean_string_append(v___x_1051_, v___y_1053_);
lean_dec_ref(v___y_1053_);
v___x_1055_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__11));
v___x_1056_ = lean_string_append(v___x_1054_, v___x_1055_);
v___x_1057_ = l_Int_repr(v_a_1043_);
lean_dec(v_a_1043_);
v___x_1058_ = lean_string_append(v___x_1056_, v___x_1057_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__12));
v___x_1060_ = lean_string_append(v___x_1058_, v___x_1059_);
v___x_1061_ = l_Int_repr(v_b_1045_);
lean_dec(v_b_1045_);
v___x_1062_ = lean_string_append(v___x_1060_, v___x_1061_);
lean_dec_ref(v___x_1061_);
v___x_1063_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__13));
v___x_1064_ = lean_string_append(v___x_1062_, v___x_1063_);
v___x_1065_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_1039_, v_x_1041_, v_j_1044_);
v___x_1066_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1065_);
v___x_1067_ = lean_string_append(v___x_1064_, v___x_1066_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_1069_ = lean_string_append(v___x_1067_, v___x_1068_);
v___x_1070_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_1040_, v_y_1042_, v_k_1046_);
v___x_1071_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1070_);
v___x_1072_ = lean_string_append(v___x_1069_, v___x_1071_);
lean_dec_ref(v___x_1071_);
return v___x_1072_;
}
v___jp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = lean_string_append(v___y_1074_, v___y_1075_);
lean_dec_ref(v___y_1075_);
v___x_1077_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1078_ = lean_string_append(v___x_1076_, v___x_1077_);
v___y_1053_ = v___x_1078_;
goto v___jp_1052_;
}
}
default: 
{
lean_object* v_m_1166_; lean_object* v_r_1167_; lean_object* v_i_1168_; lean_object* v_x_1169_; lean_object* v_j_1170_; lean_object* v_lowerBound_1171_; lean_object* v_upperBound_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___y_1177_; lean_object* v___y_1194_; lean_object* v___y_1195_; 
v_m_1166_ = lean_ctor_get(v_x_692_, 0);
lean_inc(v_m_1166_);
v_r_1167_ = lean_ctor_get(v_x_692_, 1);
lean_inc(v_r_1167_);
v_i_1168_ = lean_ctor_get(v_x_692_, 2);
lean_inc(v_i_1168_);
v_x_1169_ = lean_ctor_get(v_x_692_, 3);
lean_inc(v_x_1169_);
v_j_1170_ = lean_ctor_get(v_x_692_, 4);
lean_inc_ref(v_j_1170_);
lean_dec_ref(v_x_692_);
v_lowerBound_1171_ = lean_ctor_get(v_s_690_, 0);
lean_inc(v_lowerBound_1171_);
v_upperBound_1172_ = lean_ctor_get(v_s_690_, 1);
lean_inc(v_upperBound_1172_);
lean_dec_ref(v_s_690_);
v___x_1173_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_691_);
lean_dec(v_x_691_);
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1175_ = lean_string_append(v___x_1173_, v___x_1174_);
if (lean_obj_tag(v_lowerBound_1171_) == 0)
{
if (lean_obj_tag(v_upperBound_1172_) == 0)
{
lean_object* v___x_1199_; 
v___x_1199_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1177_ = v___x_1199_;
goto v___jp_1176_;
}
else
{
lean_object* v_val_1200_; lean_object* v___x_1201_; lean_object* v___y_1203_; lean_object* v_intZero_1207_; uint8_t v_isNeg_1208_; 
v_val_1200_ = lean_ctor_get(v_upperBound_1172_, 0);
lean_inc(v_val_1200_);
lean_dec_ref(v_upperBound_1172_);
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1207_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1208_ = lean_int_dec_lt(v_val_1200_, v_intZero_1207_);
if (v_isNeg_1208_ == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1210_; 
v_a_1209_ = lean_nat_abs(v_val_1200_);
lean_dec(v_val_1200_);
v___x_1210_ = l_Nat_reprFast(v_a_1209_);
v___y_1203_ = v___x_1210_;
goto v___jp_1202_;
}
else
{
lean_object* v_abs_1211_; lean_object* v_one_1212_; lean_object* v_a_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_abs_1211_ = lean_nat_abs(v_val_1200_);
lean_dec(v_val_1200_);
v_one_1212_ = lean_unsigned_to_nat(1u);
v_a_1213_ = lean_nat_sub(v_abs_1211_, v_one_1212_);
lean_dec(v_abs_1211_);
v___x_1214_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1215_ = lean_nat_add(v_a_1213_, v_one_1212_);
lean_dec(v_a_1213_);
v___x_1216_ = l_Nat_reprFast(v___x_1215_);
v___x_1217_ = lean_string_append(v___x_1214_, v___x_1216_);
lean_dec_ref(v___x_1216_);
v___y_1203_ = v___x_1217_;
goto v___jp_1202_;
}
v___jp_1202_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = lean_string_append(v___x_1201_, v___y_1203_);
lean_dec_ref(v___y_1203_);
v___x_1205_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1206_ = lean_string_append(v___x_1204_, v___x_1205_);
v___y_1177_ = v___x_1206_;
goto v___jp_1176_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1172_) == 0)
{
lean_object* v_val_1218_; lean_object* v___x_1219_; lean_object* v___y_1221_; lean_object* v_intZero_1225_; uint8_t v_isNeg_1226_; 
v_val_1218_ = lean_ctor_get(v_lowerBound_1171_, 0);
lean_inc(v_val_1218_);
lean_dec_ref(v_lowerBound_1171_);
v___x_1219_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1225_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1226_ = lean_int_dec_lt(v_val_1218_, v_intZero_1225_);
if (v_isNeg_1226_ == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1228_; 
v_a_1227_ = lean_nat_abs(v_val_1218_);
lean_dec(v_val_1218_);
v___x_1228_ = l_Nat_reprFast(v_a_1227_);
v___y_1221_ = v___x_1228_;
goto v___jp_1220_;
}
else
{
lean_object* v_abs_1229_; lean_object* v_one_1230_; lean_object* v_a_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_abs_1229_ = lean_nat_abs(v_val_1218_);
lean_dec(v_val_1218_);
v_one_1230_ = lean_unsigned_to_nat(1u);
v_a_1231_ = lean_nat_sub(v_abs_1229_, v_one_1230_);
lean_dec(v_abs_1229_);
v___x_1232_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1233_ = lean_nat_add(v_a_1231_, v_one_1230_);
lean_dec(v_a_1231_);
v___x_1234_ = l_Nat_reprFast(v___x_1233_);
v___x_1235_ = lean_string_append(v___x_1232_, v___x_1234_);
lean_dec_ref(v___x_1234_);
v___y_1221_ = v___x_1235_;
goto v___jp_1220_;
}
v___jp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_string_append(v___x_1219_, v___y_1221_);
lean_dec_ref(v___y_1221_);
v___x_1223_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1224_ = lean_string_append(v___x_1222_, v___x_1223_);
v___y_1177_ = v___x_1224_;
goto v___jp_1176_;
}
}
else
{
lean_object* v_val_1236_; lean_object* v_val_1237_; uint8_t v___x_1238_; 
v_val_1236_ = lean_ctor_get(v_lowerBound_1171_, 0);
lean_inc(v_val_1236_);
lean_dec_ref(v_lowerBound_1171_);
v_val_1237_ = lean_ctor_get(v_upperBound_1172_, 0);
lean_inc(v_val_1237_);
lean_dec_ref(v_upperBound_1172_);
v___x_1238_ = lean_int_dec_lt(v_val_1237_, v_val_1236_);
if (v___x_1238_ == 0)
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_int_dec_eq(v_val_1236_, v_val_1237_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___y_1242_; lean_object* v_intZero_1257_; uint8_t v_isNeg_1258_; 
v___x_1240_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1257_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1258_ = lean_int_dec_lt(v_val_1236_, v_intZero_1257_);
if (v_isNeg_1258_ == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; 
v_a_1259_ = lean_nat_abs(v_val_1236_);
lean_dec(v_val_1236_);
v___x_1260_ = l_Nat_reprFast(v_a_1259_);
v___y_1242_ = v___x_1260_;
goto v___jp_1241_;
}
else
{
lean_object* v_abs_1261_; lean_object* v_one_1262_; lean_object* v_a_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_abs_1261_ = lean_nat_abs(v_val_1236_);
lean_dec(v_val_1236_);
v_one_1262_ = lean_unsigned_to_nat(1u);
v_a_1263_ = lean_nat_sub(v_abs_1261_, v_one_1262_);
lean_dec(v_abs_1261_);
v___x_1264_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1265_ = lean_nat_add(v_a_1263_, v_one_1262_);
lean_dec(v_a_1263_);
v___x_1266_ = l_Nat_reprFast(v___x_1265_);
v___x_1267_ = lean_string_append(v___x_1264_, v___x_1266_);
lean_dec_ref(v___x_1266_);
v___y_1242_ = v___x_1267_;
goto v___jp_1241_;
}
v___jp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v_intZero_1246_; uint8_t v_isNeg_1247_; 
v___x_1243_ = lean_string_append(v___x_1240_, v___y_1242_);
lean_dec_ref(v___y_1242_);
v___x_1244_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1245_ = lean_string_append(v___x_1243_, v___x_1244_);
v_intZero_1246_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1247_ = lean_int_dec_lt(v_val_1237_, v_intZero_1246_);
if (v_isNeg_1247_ == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1249_; 
v_a_1248_ = lean_nat_abs(v_val_1237_);
lean_dec(v_val_1237_);
v___x_1249_ = l_Nat_reprFast(v_a_1248_);
v___y_1194_ = v___x_1245_;
v___y_1195_ = v___x_1249_;
goto v___jp_1193_;
}
else
{
lean_object* v_abs_1250_; lean_object* v_one_1251_; lean_object* v_a_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_abs_1250_ = lean_nat_abs(v_val_1237_);
lean_dec(v_val_1237_);
v_one_1251_ = lean_unsigned_to_nat(1u);
v_a_1252_ = lean_nat_sub(v_abs_1250_, v_one_1251_);
lean_dec(v_abs_1250_);
v___x_1253_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1254_ = lean_nat_add(v_a_1252_, v_one_1251_);
lean_dec(v_a_1252_);
v___x_1255_ = l_Nat_reprFast(v___x_1254_);
v___x_1256_ = lean_string_append(v___x_1253_, v___x_1255_);
lean_dec_ref(v___x_1255_);
v___y_1194_ = v___x_1245_;
v___y_1195_ = v___x_1256_;
goto v___jp_1193_;
}
}
}
else
{
lean_object* v___x_1268_; lean_object* v___y_1270_; lean_object* v_intZero_1274_; uint8_t v_isNeg_1275_; 
lean_dec(v_val_1237_);
v___x_1268_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1274_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1275_ = lean_int_dec_lt(v_val_1236_, v_intZero_1274_);
if (v_isNeg_1275_ == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1277_; 
v_a_1276_ = lean_nat_abs(v_val_1236_);
lean_dec(v_val_1236_);
v___x_1277_ = l_Nat_reprFast(v_a_1276_);
v___y_1270_ = v___x_1277_;
goto v___jp_1269_;
}
else
{
lean_object* v_abs_1278_; lean_object* v_one_1279_; lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_abs_1278_ = lean_nat_abs(v_val_1236_);
lean_dec(v_val_1236_);
v_one_1279_ = lean_unsigned_to_nat(1u);
v_a_1280_ = lean_nat_sub(v_abs_1278_, v_one_1279_);
lean_dec(v_abs_1278_);
v___x_1281_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1282_ = lean_nat_add(v_a_1280_, v_one_1279_);
lean_dec(v_a_1280_);
v___x_1283_ = l_Nat_reprFast(v___x_1282_);
v___x_1284_ = lean_string_append(v___x_1281_, v___x_1283_);
lean_dec_ref(v___x_1283_);
v___y_1270_ = v___x_1284_;
goto v___jp_1269_;
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_string_append(v___x_1268_, v___y_1270_);
lean_dec_ref(v___y_1270_);
v___x_1272_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1273_ = lean_string_append(v___x_1271_, v___x_1272_);
v___y_1177_ = v___x_1273_;
goto v___jp_1176_;
}
}
}
else
{
lean_object* v___x_1285_; 
lean_dec(v_val_1237_);
lean_dec(v_val_1236_);
v___x_1285_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1177_ = v___x_1285_;
goto v___jp_1176_;
}
}
}
v___jp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1178_ = lean_string_append(v___x_1175_, v___y_1177_);
lean_dec_ref(v___y_1177_);
v___x_1179_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__14));
v___x_1180_ = lean_string_append(v___x_1178_, v___x_1179_);
v___x_1181_ = l_Nat_reprFast(v_m_1166_);
v___x_1182_ = lean_string_append(v___x_1180_, v___x_1181_);
lean_dec_ref(v___x_1181_);
v___x_1183_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__15));
v___x_1184_ = lean_string_append(v___x_1182_, v___x_1183_);
v___x_1185_ = l_Nat_reprFast(v_i_1168_);
v___x_1186_ = lean_string_append(v___x_1184_, v___x_1185_);
lean_dec_ref(v___x_1185_);
v___x_1187_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__16));
v___x_1188_ = lean_string_append(v___x_1186_, v___x_1187_);
v___x_1189_ = l_Lean_Omega_Constraint_exact(v_r_1167_);
v___x_1190_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v___x_1189_, v_x_1169_, v_j_1170_);
v___x_1191_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1190_);
v___x_1192_ = lean_string_append(v___x_1188_, v___x_1191_);
lean_dec_ref(v___x_1191_);
return v___x_1192_;
}
v___jp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_string_append(v___y_1194_, v___y_1195_);
lean_dec_ref(v___y_1195_);
v___x_1197_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1198_ = lean_string_append(v___x_1196_, v___x_1197_);
v___y_1177_ = v___x_1198_;
goto v___jp_1176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_instToString(lean_object* v_s_1286_, lean_object* v_x_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Justification_toString), 3, 2);
lean_closure_set(v___x_1288_, 0, v_s_1286_);
lean_closure_set(v___x_1288_, 1, v_x_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(lean_object* v_nilFn_1289_, lean_object* v_consFn_1290_, lean_object* v_x_1291_){
_start:
{
if (lean_obj_tag(v_x_1291_) == 0)
{
lean_dec_ref(v_consFn_1290_);
lean_inc_ref(v_nilFn_1289_);
return v_nilFn_1289_;
}
else
{
lean_object* v_head_1292_; lean_object* v_tail_1293_; lean_object* v___y_1295_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v_head_1292_ = lean_ctor_get(v_x_1291_, 0);
v_tail_1293_ = lean_ctor_get(v_x_1291_, 1);
v___x_1298_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1299_ = lean_int_dec_le(v___x_1298_, v_head_1292_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1300_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1301_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1302_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1303_ = lean_int_neg(v_head_1292_);
v___x_1304_ = l_Int_toNat(v___x_1303_);
lean_dec(v___x_1303_);
v___x_1305_ = l_Lean_instToExprInt_mkNat(v___x_1304_);
v___x_1306_ = l_Lean_mkApp3(v___x_1300_, v___x_1301_, v___x_1302_, v___x_1305_);
v___y_1295_ = v___x_1306_;
goto v___jp_1294_;
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = l_Int_toNat(v_head_1292_);
v___x_1308_ = l_Lean_instToExprInt_mkNat(v___x_1307_);
v___y_1295_ = v___x_1308_;
goto v___jp_1294_;
}
v___jp_1294_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_inc_ref(v_consFn_1290_);
v___x_1296_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1289_, v_consFn_1290_, v_tail_1293_);
v___x_1297_ = l_Lean_mkAppB(v_consFn_1290_, v___y_1295_, v___x_1296_);
return v___x_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0___boxed(lean_object* v_nilFn_1309_, lean_object* v_consFn_1310_, lean_object* v_x_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1309_, v_consFn_1310_, v_x_1311_);
lean_dec(v_x_1311_);
lean_dec_ref(v_nilFn_1309_);
return v_res_1312_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = lean_box(0);
v___x_1319_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1));
v___x_1320_ = l_Lean_Expr_const___override(v___x_1319_, v___x_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof(lean_object* v_s_1321_, lean_object* v_x_1322_, lean_object* v_v_1323_, lean_object* v_prf_1324_){
_start:
{
lean_object* v___x_1325_; lean_object* v___y_1327_; lean_object* v_lowerBound_1332_; lean_object* v_upperBound_1333_; lean_object* v___x_1334_; lean_object* v_type_1335_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1343_; 
v___x_1325_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2);
v_lowerBound_1332_ = lean_ctor_get(v_s_1321_, 0);
v_upperBound_1333_ = lean_ctor_get(v_s_1321_, 1);
v___x_1334_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1335_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1332_) == 0)
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1343_ = v___x_1359_;
goto v___jp_1342_;
}
else
{
lean_object* v_val_1360_; lean_object* v___x_1361_; lean_object* v___y_1363_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_val_1360_ = lean_ctor_get(v_lowerBound_1332_, 0);
v___x_1361_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1365_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1366_ = lean_int_dec_le(v___x_1365_, v_val_1360_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1367_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1368_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1369_ = lean_int_neg(v_val_1360_);
v___x_1370_ = l_Int_toNat(v___x_1369_);
lean_dec(v___x_1369_);
v___x_1371_ = l_Lean_instToExprInt_mkNat(v___x_1370_);
v___x_1372_ = l_Lean_mkApp3(v___x_1367_, v_type_1335_, v___x_1368_, v___x_1371_);
v___y_1363_ = v___x_1372_;
goto v___jp_1362_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = l_Int_toNat(v_val_1360_);
v___x_1374_ = l_Lean_instToExprInt_mkNat(v___x_1373_);
v___y_1363_ = v___x_1374_;
goto v___jp_1362_;
}
v___jp_1362_:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_mkAppB(v___x_1361_, v_type_1335_, v___y_1363_);
v___y_1343_ = v___x_1364_;
goto v___jp_1342_;
}
}
v___jp_1326_:
{
lean_object* v_nil_1328_; lean_object* v_cons_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_nil_1328_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1329_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1330_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1328_, v_cons_1329_, v_x_1322_);
v___x_1331_ = l_Lean_mkApp4(v___x_1325_, v___y_1327_, v___x_1330_, v_v_1323_, v_prf_1324_);
return v___x_1331_;
}
v___jp_1336_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_inc_ref(v___y_1338_);
v___x_1340_ = l_Lean_mkAppB(v___y_1338_, v_type_1335_, v___y_1339_);
v___x_1341_ = l_Lean_Expr_app___override(v___y_1337_, v___x_1340_);
v___y_1327_ = v___x_1341_;
goto v___jp_1326_;
}
v___jp_1342_:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_Expr_app___override(v___x_1334_, v___y_1343_);
if (lean_obj_tag(v_upperBound_1333_) == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1346_ = l_Lean_Expr_app___override(v___x_1344_, v___x_1345_);
v___y_1327_ = v___x_1346_;
goto v___jp_1326_;
}
else
{
lean_object* v_val_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v_val_1347_ = lean_ctor_get(v_upperBound_1333_, 0);
v___x_1348_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1349_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1350_ = lean_int_dec_le(v___x_1349_, v_val_1347_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1351_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1352_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1353_ = lean_int_neg(v_val_1347_);
v___x_1354_ = l_Int_toNat(v___x_1353_);
lean_dec(v___x_1353_);
v___x_1355_ = l_Lean_instToExprInt_mkNat(v___x_1354_);
v___x_1356_ = l_Lean_mkApp3(v___x_1351_, v_type_1335_, v___x_1352_, v___x_1355_);
v___y_1337_ = v___x_1344_;
v___y_1338_ = v___x_1348_;
v___y_1339_ = v___x_1356_;
goto v___jp_1336_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = l_Int_toNat(v_val_1347_);
v___x_1358_ = l_Lean_instToExprInt_mkNat(v___x_1357_);
v___y_1337_ = v___x_1344_;
v___y_1338_ = v___x_1348_;
v___y_1339_ = v___x_1358_;
goto v___jp_1336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___boxed(lean_object* v_s_1375_, lean_object* v_x_1376_, lean_object* v_v_1377_, lean_object* v_prf_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1375_, v_x_1376_, v_v_1377_, v_prf_1378_);
lean_dec(v_x_1376_);
lean_dec_ref(v_s_1375_);
return v_res_1379_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1));
v___x_1388_ = l_Lean_Expr_const___override(v___x_1387_, v___x_1386_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof(lean_object* v_s_1389_, lean_object* v_t_1390_, lean_object* v_x_1391_, lean_object* v_v_1392_, lean_object* v_ps_1393_, lean_object* v_pt_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1446_; lean_object* v_lowerBound_1464_; lean_object* v_upperBound_1465_; lean_object* v___x_1466_; lean_object* v_type_1467_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1475_; 
v___x_1395_ = lean_box(0);
v___x_1396_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2);
v_lowerBound_1464_ = lean_ctor_get(v_s_1389_, 0);
v_upperBound_1465_ = lean_ctor_get(v_s_1389_, 1);
v___x_1466_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1467_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1464_) == 0)
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1475_ = v___x_1491_;
goto v___jp_1474_;
}
else
{
lean_object* v_val_1492_; lean_object* v___x_1493_; lean_object* v___y_1495_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v_val_1492_ = lean_ctor_get(v_lowerBound_1464_, 0);
v___x_1493_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1497_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1498_ = lean_int_dec_le(v___x_1497_, v_val_1492_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1499_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1500_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1501_ = lean_int_neg(v_val_1492_);
v___x_1502_ = l_Int_toNat(v___x_1501_);
lean_dec(v___x_1501_);
v___x_1503_ = l_Lean_instToExprInt_mkNat(v___x_1502_);
v___x_1504_ = l_Lean_mkApp3(v___x_1499_, v_type_1467_, v___x_1500_, v___x_1503_);
v___y_1495_ = v___x_1504_;
goto v___jp_1494_;
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = l_Int_toNat(v_val_1492_);
v___x_1506_ = l_Lean_instToExprInt_mkNat(v___x_1505_);
v___y_1495_ = v___x_1506_;
goto v___jp_1494_;
}
v___jp_1494_:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_mkAppB(v___x_1493_, v_type_1467_, v___y_1495_);
v___y_1475_ = v___x_1496_;
goto v___jp_1474_;
}
}
v___jp_1397_:
{
lean_object* v_nil_1400_; lean_object* v_cons_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_nil_1400_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1401_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1402_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1400_, v_cons_1401_, v_x_1391_);
v___x_1403_ = l_Lean_mkApp6(v___x_1396_, v___y_1398_, v___y_1399_, v___x_1402_, v_v_1392_, v_ps_1393_, v_pt_1394_);
return v___x_1403_;
}
v___jp_1404_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_inc_ref(v___y_1406_);
v___x_1410_ = l_Lean_mkAppB(v___y_1406_, v___y_1405_, v___y_1409_);
v___x_1411_ = l_Lean_Expr_app___override(v___y_1407_, v___x_1410_);
v___y_1398_ = v___y_1408_;
v___y_1399_ = v___x_1411_;
goto v___jp_1397_;
}
v___jp_1412_:
{
lean_object* v_upperBound_1418_; lean_object* v___x_1419_; 
v_upperBound_1418_ = lean_ctor_get(v_t_1390_, 1);
lean_inc_ref(v___y_1413_);
v___x_1419_ = l_Lean_Expr_app___override(v___y_1413_, v___y_1417_);
if (lean_obj_tag(v_upperBound_1418_) == 0)
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1421_ = l_Lean_Expr_app___override(v___x_1420_, v___y_1414_);
v___x_1422_ = l_Lean_Expr_app___override(v___x_1419_, v___x_1421_);
v___y_1398_ = v___y_1416_;
v___y_1399_ = v___x_1422_;
goto v___jp_1397_;
}
else
{
lean_object* v_val_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v_val_1423_ = lean_ctor_get(v_upperBound_1418_, 0);
v___x_1424_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1425_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1426_ = lean_int_dec_le(v___x_1425_, v_val_1423_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1427_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1428_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1415_);
v___x_1429_ = l_Lean_Name_mkStr2(v___y_1415_, v___x_1428_);
v___x_1430_ = l_Lean_Expr_const___override(v___x_1429_, v___x_1395_);
v___x_1431_ = lean_int_neg(v_val_1423_);
v___x_1432_ = l_Int_toNat(v___x_1431_);
lean_dec(v___x_1431_);
v___x_1433_ = l_Lean_instToExprInt_mkNat(v___x_1432_);
lean_inc_ref(v___y_1414_);
v___x_1434_ = l_Lean_mkApp3(v___x_1427_, v___y_1414_, v___x_1430_, v___x_1433_);
v___y_1405_ = v___y_1414_;
v___y_1406_ = v___x_1424_;
v___y_1407_ = v___x_1419_;
v___y_1408_ = v___y_1416_;
v___y_1409_ = v___x_1434_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = l_Int_toNat(v_val_1423_);
v___x_1436_ = l_Lean_instToExprInt_mkNat(v___x_1435_);
v___y_1405_ = v___y_1414_;
v___y_1406_ = v___x_1424_;
v___y_1407_ = v___x_1419_;
v___y_1408_ = v___y_1416_;
v___y_1409_ = v___x_1436_;
goto v___jp_1404_;
}
}
}
v___jp_1437_:
{
lean_object* v___x_1444_; 
lean_inc_ref(v___y_1439_);
lean_inc_ref(v___y_1441_);
v___x_1444_ = l_Lean_mkAppB(v___y_1441_, v___y_1439_, v___y_1443_);
v___y_1413_ = v___y_1438_;
v___y_1414_ = v___y_1439_;
v___y_1415_ = v___y_1440_;
v___y_1416_ = v___y_1442_;
v___y_1417_ = v___x_1444_;
goto v___jp_1412_;
}
v___jp_1445_:
{
lean_object* v_lowerBound_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v_type_1450_; 
v_lowerBound_1447_ = lean_ctor_get(v_t_1390_, 0);
v___x_1448_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1449_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1450_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1447_) == 0)
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1413_ = v___x_1448_;
v___y_1414_ = v_type_1450_;
v___y_1415_ = v___x_1449_;
v___y_1416_ = v___y_1446_;
v___y_1417_ = v___x_1451_;
goto v___jp_1412_;
}
else
{
lean_object* v_val_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v_val_1452_ = lean_ctor_get(v_lowerBound_1447_, 0);
v___x_1453_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1454_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1455_ = lean_int_dec_le(v___x_1454_, v_val_1452_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1456_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1457_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1458_ = lean_int_neg(v_val_1452_);
v___x_1459_ = l_Int_toNat(v___x_1458_);
lean_dec(v___x_1458_);
v___x_1460_ = l_Lean_instToExprInt_mkNat(v___x_1459_);
v___x_1461_ = l_Lean_mkApp3(v___x_1456_, v_type_1450_, v___x_1457_, v___x_1460_);
v___y_1438_ = v___x_1448_;
v___y_1439_ = v_type_1450_;
v___y_1440_ = v___x_1449_;
v___y_1441_ = v___x_1453_;
v___y_1442_ = v___y_1446_;
v___y_1443_ = v___x_1461_;
goto v___jp_1437_;
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = l_Int_toNat(v_val_1452_);
v___x_1463_ = l_Lean_instToExprInt_mkNat(v___x_1462_);
v___y_1438_ = v___x_1448_;
v___y_1439_ = v_type_1450_;
v___y_1440_ = v___x_1449_;
v___y_1441_ = v___x_1453_;
v___y_1442_ = v___y_1446_;
v___y_1443_ = v___x_1463_;
goto v___jp_1437_;
}
}
}
v___jp_1468_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_inc_ref(v___y_1469_);
v___x_1472_ = l_Lean_mkAppB(v___y_1469_, v_type_1467_, v___y_1471_);
v___x_1473_ = l_Lean_Expr_app___override(v___y_1470_, v___x_1472_);
v___y_1446_ = v___x_1473_;
goto v___jp_1445_;
}
v___jp_1474_:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Expr_app___override(v___x_1466_, v___y_1475_);
if (lean_obj_tag(v_upperBound_1465_) == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1478_ = l_Lean_Expr_app___override(v___x_1476_, v___x_1477_);
v___y_1446_ = v___x_1478_;
goto v___jp_1445_;
}
else
{
lean_object* v_val_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v_val_1479_ = lean_ctor_get(v_upperBound_1465_, 0);
v___x_1480_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1481_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1482_ = lean_int_dec_le(v___x_1481_, v_val_1479_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1483_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1484_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1485_ = lean_int_neg(v_val_1479_);
v___x_1486_ = l_Int_toNat(v___x_1485_);
lean_dec(v___x_1485_);
v___x_1487_ = l_Lean_instToExprInt_mkNat(v___x_1486_);
v___x_1488_ = l_Lean_mkApp3(v___x_1483_, v_type_1467_, v___x_1484_, v___x_1487_);
v___y_1469_ = v___x_1480_;
v___y_1470_ = v___x_1476_;
v___y_1471_ = v___x_1488_;
goto v___jp_1468_;
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = l_Int_toNat(v_val_1479_);
v___x_1490_ = l_Lean_instToExprInt_mkNat(v___x_1489_);
v___y_1469_ = v___x_1480_;
v___y_1470_ = v___x_1476_;
v___y_1471_ = v___x_1490_;
goto v___jp_1468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___boxed(lean_object* v_s_1507_, lean_object* v_t_1508_, lean_object* v_x_1509_, lean_object* v_v_1510_, lean_object* v_ps_1511_, lean_object* v_pt_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1507_, v_t_1508_, v_x_1509_, v_v_1510_, v_ps_1511_, v_pt_1512_);
lean_dec(v_x_1509_);
lean_dec_ref(v_t_1508_);
lean_dec_ref(v_s_1507_);
return v_res_1513_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = lean_box(0);
v___x_1520_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1));
v___x_1521_ = l_Lean_Expr_const___override(v___x_1520_, v___x_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof(lean_object* v_s_1522_, lean_object* v_t_1523_, lean_object* v_a_1524_, lean_object* v_x_1525_, lean_object* v_b_1526_, lean_object* v_y_1527_, lean_object* v_v_1528_, lean_object* v_px_1529_, lean_object* v_py_1530_){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1617_; lean_object* v_lowerBound_1635_; lean_object* v_upperBound_1636_; lean_object* v___x_1637_; lean_object* v_type_1638_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1646_; 
v___x_1531_ = lean_box(0);
v___x_1532_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2);
v_lowerBound_1635_ = lean_ctor_get(v_s_1522_, 0);
v_upperBound_1636_ = lean_ctor_get(v_s_1522_, 1);
v___x_1637_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1638_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1635_) == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1646_ = v___x_1662_;
goto v___jp_1645_;
}
else
{
lean_object* v_val_1663_; lean_object* v___x_1664_; lean_object* v___y_1666_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v_val_1663_ = lean_ctor_get(v_lowerBound_1635_, 0);
v___x_1664_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1668_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1669_ = lean_int_dec_le(v___x_1668_, v_val_1663_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1670_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1671_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1672_ = lean_int_neg(v_val_1663_);
v___x_1673_ = l_Int_toNat(v___x_1672_);
lean_dec(v___x_1672_);
v___x_1674_ = l_Lean_instToExprInt_mkNat(v___x_1673_);
v___x_1675_ = l_Lean_mkApp3(v___x_1670_, v_type_1638_, v___x_1671_, v___x_1674_);
v___y_1666_ = v___x_1675_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = l_Int_toNat(v_val_1663_);
v___x_1677_ = l_Lean_instToExprInt_mkNat(v___x_1676_);
v___y_1666_ = v___x_1677_;
goto v___jp_1665_;
}
v___jp_1665_:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_mkAppB(v___x_1664_, v_type_1638_, v___y_1666_);
v___y_1646_ = v___x_1667_;
goto v___jp_1645_;
}
}
v___jp_1533_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v___y_1537_, v___y_1535_, v_y_1527_);
v___x_1542_ = l_Lean_mkApp9(v___x_1532_, v___y_1539_, v___y_1538_, v___y_1534_, v___y_1536_, v___y_1540_, v___x_1541_, v_v_1528_, v_px_1529_, v_py_1530_);
return v___x_1542_;
}
v___jp_1543_:
{
lean_object* v_type_1547_; lean_object* v_nil_1548_; lean_object* v_cons_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_type_1547_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_nil_1548_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1549_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1550_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1548_, v_cons_1549_, v_x_1525_);
v___x_1551_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1552_ = lean_int_dec_le(v___x_1551_, v_b_1526_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1553_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1554_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1555_ = lean_int_neg(v_b_1526_);
v___x_1556_ = l_Int_toNat(v___x_1555_);
lean_dec(v___x_1555_);
v___x_1557_ = l_Lean_instToExprInt_mkNat(v___x_1556_);
v___x_1558_ = l_Lean_mkApp3(v___x_1553_, v_type_1547_, v___x_1554_, v___x_1557_);
v___y_1534_ = v___y_1546_;
v___y_1535_ = v_cons_1549_;
v___y_1536_ = v___x_1550_;
v___y_1537_ = v_nil_1548_;
v___y_1538_ = v___y_1545_;
v___y_1539_ = v___y_1544_;
v___y_1540_ = v___x_1558_;
goto v___jp_1533_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = l_Int_toNat(v_b_1526_);
v___x_1560_ = l_Lean_instToExprInt_mkNat(v___x_1559_);
v___y_1534_ = v___y_1546_;
v___y_1535_ = v_cons_1549_;
v___y_1536_ = v___x_1550_;
v___y_1537_ = v_nil_1548_;
v___y_1538_ = v___y_1545_;
v___y_1539_ = v___y_1544_;
v___y_1540_ = v___x_1560_;
goto v___jp_1533_;
}
}
v___jp_1561_:
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1565_ = lean_int_dec_le(v___x_1564_, v_a_1524_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1566_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1567_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1568_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1569_ = lean_int_neg(v_a_1524_);
v___x_1570_ = l_Int_toNat(v___x_1569_);
lean_dec(v___x_1569_);
v___x_1571_ = l_Lean_instToExprInt_mkNat(v___x_1570_);
v___x_1572_ = l_Lean_mkApp3(v___x_1566_, v___x_1567_, v___x_1568_, v___x_1571_);
v___y_1544_ = v___y_1562_;
v___y_1545_ = v___y_1563_;
v___y_1546_ = v___x_1572_;
goto v___jp_1543_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = l_Int_toNat(v_a_1524_);
v___x_1574_ = l_Lean_instToExprInt_mkNat(v___x_1573_);
v___y_1544_ = v___y_1562_;
v___y_1545_ = v___y_1563_;
v___y_1546_ = v___x_1574_;
goto v___jp_1543_;
}
}
v___jp_1575_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_inc_ref(v___y_1578_);
v___x_1581_ = l_Lean_mkAppB(v___y_1578_, v___y_1576_, v___y_1580_);
v___x_1582_ = l_Lean_Expr_app___override(v___y_1579_, v___x_1581_);
v___y_1562_ = v___y_1577_;
v___y_1563_ = v___x_1582_;
goto v___jp_1561_;
}
v___jp_1583_:
{
lean_object* v_upperBound_1589_; lean_object* v___x_1590_; 
v_upperBound_1589_ = lean_ctor_get(v_t_1523_, 1);
lean_inc_ref(v___y_1584_);
v___x_1590_ = l_Lean_Expr_app___override(v___y_1584_, v___y_1588_);
if (lean_obj_tag(v_upperBound_1589_) == 0)
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1592_ = l_Lean_Expr_app___override(v___x_1591_, v___y_1586_);
v___x_1593_ = l_Lean_Expr_app___override(v___x_1590_, v___x_1592_);
v___y_1562_ = v___y_1587_;
v___y_1563_ = v___x_1593_;
goto v___jp_1561_;
}
else
{
lean_object* v_val_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_val_1594_ = lean_ctor_get(v_upperBound_1589_, 0);
v___x_1595_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1596_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1597_ = lean_int_dec_le(v___x_1596_, v_val_1594_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1598_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1599_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1585_);
v___x_1600_ = l_Lean_Name_mkStr2(v___y_1585_, v___x_1599_);
v___x_1601_ = l_Lean_Expr_const___override(v___x_1600_, v___x_1531_);
v___x_1602_ = lean_int_neg(v_val_1594_);
v___x_1603_ = l_Int_toNat(v___x_1602_);
lean_dec(v___x_1602_);
v___x_1604_ = l_Lean_instToExprInt_mkNat(v___x_1603_);
lean_inc_ref(v___y_1586_);
v___x_1605_ = l_Lean_mkApp3(v___x_1598_, v___y_1586_, v___x_1601_, v___x_1604_);
v___y_1576_ = v___y_1586_;
v___y_1577_ = v___y_1587_;
v___y_1578_ = v___x_1595_;
v___y_1579_ = v___x_1590_;
v___y_1580_ = v___x_1605_;
goto v___jp_1575_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = l_Int_toNat(v_val_1594_);
v___x_1607_ = l_Lean_instToExprInt_mkNat(v___x_1606_);
v___y_1576_ = v___y_1586_;
v___y_1577_ = v___y_1587_;
v___y_1578_ = v___x_1595_;
v___y_1579_ = v___x_1590_;
v___y_1580_ = v___x_1607_;
goto v___jp_1575_;
}
}
}
v___jp_1608_:
{
lean_object* v___x_1615_; 
lean_inc_ref(v___y_1612_);
lean_inc_ref(v___y_1611_);
v___x_1615_ = l_Lean_mkAppB(v___y_1611_, v___y_1612_, v___y_1614_);
v___y_1584_ = v___y_1609_;
v___y_1585_ = v___y_1610_;
v___y_1586_ = v___y_1612_;
v___y_1587_ = v___y_1613_;
v___y_1588_ = v___x_1615_;
goto v___jp_1583_;
}
v___jp_1616_:
{
lean_object* v_lowerBound_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v_type_1621_; 
v_lowerBound_1618_ = lean_ctor_get(v_t_1523_, 0);
v___x_1619_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1620_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1621_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1618_) == 0)
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1584_ = v___x_1619_;
v___y_1585_ = v___x_1620_;
v___y_1586_ = v_type_1621_;
v___y_1587_ = v___y_1617_;
v___y_1588_ = v___x_1622_;
goto v___jp_1583_;
}
else
{
lean_object* v_val_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v_val_1623_ = lean_ctor_get(v_lowerBound_1618_, 0);
v___x_1624_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1625_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1626_ = lean_int_dec_le(v___x_1625_, v_val_1623_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1627_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1628_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1629_ = lean_int_neg(v_val_1623_);
v___x_1630_ = l_Int_toNat(v___x_1629_);
lean_dec(v___x_1629_);
v___x_1631_ = l_Lean_instToExprInt_mkNat(v___x_1630_);
v___x_1632_ = l_Lean_mkApp3(v___x_1627_, v_type_1621_, v___x_1628_, v___x_1631_);
v___y_1609_ = v___x_1619_;
v___y_1610_ = v___x_1620_;
v___y_1611_ = v___x_1624_;
v___y_1612_ = v_type_1621_;
v___y_1613_ = v___y_1617_;
v___y_1614_ = v___x_1632_;
goto v___jp_1608_;
}
else
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = l_Int_toNat(v_val_1623_);
v___x_1634_ = l_Lean_instToExprInt_mkNat(v___x_1633_);
v___y_1609_ = v___x_1619_;
v___y_1610_ = v___x_1620_;
v___y_1611_ = v___x_1624_;
v___y_1612_ = v_type_1621_;
v___y_1613_ = v___y_1617_;
v___y_1614_ = v___x_1634_;
goto v___jp_1608_;
}
}
}
v___jp_1639_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_inc_ref(v___y_1641_);
v___x_1643_ = l_Lean_mkAppB(v___y_1641_, v_type_1638_, v___y_1642_);
v___x_1644_ = l_Lean_Expr_app___override(v___y_1640_, v___x_1643_);
v___y_1617_ = v___x_1644_;
goto v___jp_1616_;
}
v___jp_1645_:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Expr_app___override(v___x_1637_, v___y_1646_);
if (lean_obj_tag(v_upperBound_1636_) == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1649_ = l_Lean_Expr_app___override(v___x_1647_, v___x_1648_);
v___y_1617_ = v___x_1649_;
goto v___jp_1616_;
}
else
{
lean_object* v_val_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v_val_1650_ = lean_ctor_get(v_upperBound_1636_, 0);
v___x_1651_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1652_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1653_ = lean_int_dec_le(v___x_1652_, v_val_1650_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1654_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1655_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1656_ = lean_int_neg(v_val_1650_);
v___x_1657_ = l_Int_toNat(v___x_1656_);
lean_dec(v___x_1656_);
v___x_1658_ = l_Lean_instToExprInt_mkNat(v___x_1657_);
v___x_1659_ = l_Lean_mkApp3(v___x_1654_, v_type_1638_, v___x_1655_, v___x_1658_);
v___y_1640_ = v___x_1647_;
v___y_1641_ = v___x_1651_;
v___y_1642_ = v___x_1659_;
goto v___jp_1639_;
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = l_Int_toNat(v_val_1650_);
v___x_1661_ = l_Lean_instToExprInt_mkNat(v___x_1660_);
v___y_1640_ = v___x_1647_;
v___y_1641_ = v___x_1651_;
v___y_1642_ = v___x_1661_;
goto v___jp_1639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___boxed(lean_object* v_s_1678_, lean_object* v_t_1679_, lean_object* v_a_1680_, lean_object* v_x_1681_, lean_object* v_b_1682_, lean_object* v_y_1683_, lean_object* v_v_1684_, lean_object* v_px_1685_, lean_object* v_py_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1678_, v_t_1679_, v_a_1680_, v_x_1681_, v_b_1682_, v_y_1683_, v_v_1684_, v_px_1685_, v_py_1686_);
lean_dec(v_y_1683_);
lean_dec(v_b_1682_);
lean_dec(v_x_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_t_1679_);
lean_dec_ref(v_s_1678_);
return v_res_1687_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_1694_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2));
v___x_1695_ = l_Lean_Expr_const___override(v___x_1694_, v___x_1693_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = lean_box(0);
v___x_1700_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5));
v___x_1701_ = l_Lean_Expr_const___override(v___x_1700_, v___x_1699_);
return v___x_1701_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = lean_box(0);
v___x_1706_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8));
v___x_1707_ = l_Lean_Expr_const___override(v___x_1706_, v___x_1705_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = lean_box(0);
v___x_1716_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12));
v___x_1717_ = l_Lean_Expr_const___override(v___x_1716_, v___x_1715_);
return v___x_1717_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_box(0);
v___x_1725_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15));
v___x_1726_ = l_Lean_Expr_const___override(v___x_1725_, v___x_1724_);
return v___x_1726_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = lean_box(0);
v___x_1733_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18));
v___x_1734_ = l_Lean_Expr_const___override(v___x_1733_, v___x_1732_);
return v___x_1734_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = lean_box(0);
v___x_1741_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21));
v___x_1742_ = l_Lean_Expr_const___override(v___x_1741_, v___x_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof(lean_object* v_m_1743_, lean_object* v_r_1744_, lean_object* v_i_1745_, lean_object* v_x_1746_, lean_object* v_v_1747_, lean_object* v_w_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_m_1754_; lean_object* v___y_1756_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_m_1754_ = l_Lean_mkNatLit(v_m_1743_);
v___x_1784_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1785_ = lean_int_dec_le(v___x_1784_, v_r_1744_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1786_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1787_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1788_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1789_ = lean_int_neg(v_r_1744_);
v___x_1790_ = l_Int_toNat(v___x_1789_);
lean_dec(v___x_1789_);
v___x_1791_ = l_Lean_instToExprInt_mkNat(v___x_1790_);
v___x_1792_ = l_Lean_mkApp3(v___x_1786_, v___x_1787_, v___x_1788_, v___x_1791_);
v___y_1756_ = v___x_1792_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = l_Int_toNat(v_r_1744_);
v___x_1794_ = l_Lean_instToExprInt_mkNat(v___x_1793_);
v___y_1756_ = v___x_1794_;
goto v___jp_1755_;
}
v___jp_1755_:
{
lean_object* v_i_1757_; lean_object* v_nil_1758_; lean_object* v_cons_1759_; lean_object* v_x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v_i_1757_ = l_Lean_mkNatLit(v_i_1745_);
v_nil_1758_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1759_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v_x_1760_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1758_, v_cons_1759_, v_x_1746_);
v___x_1761_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3);
v___x_1762_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6);
v___x_1763_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9);
v___x_1764_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13);
lean_inc_ref(v_x_1760_);
v___x_1765_ = l_Lean_Expr_app___override(v___x_1764_, v_x_1760_);
lean_inc_ref(v_i_1757_);
v___x_1766_ = l_Lean_mkApp4(v___x_1761_, v___x_1762_, v___x_1763_, v___x_1765_, v_i_1757_);
v___x_1767_ = l_Lean_Meta_mkDecideProof(v___x_1766_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16);
lean_inc_ref(v_i_1757_);
lean_inc_ref_n(v_v_1747_, 2);
v___x_1770_ = l_Lean_mkAppB(v___x_1769_, v_v_1747_, v_i_1757_);
v___x_1771_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc_ref(v_x_1760_);
lean_inc_ref(v_m_1754_);
v___x_1772_ = l_Lean_mkApp3(v___x_1771_, v_m_1754_, v_x_1760_, v_v_1747_);
v___x_1773_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v___x_1770_, v___x_1772_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1783_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1783_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1783_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1778_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22);
v___x_1779_ = l_Lean_mkApp8(v___x_1778_, v_m_1754_, v___y_1756_, v_i_1757_, v_x_1760_, v_v_1747_, v_a_1768_, v_a_1774_, v_w_1748_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1779_);
v___x_1781_ = v___x_1776_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_dec(v_a_1768_);
lean_dec_ref(v_x_1760_);
lean_dec_ref(v_i_1757_);
lean_dec_ref(v___y_1756_);
lean_dec_ref(v_m_1754_);
lean_dec_ref(v_w_1748_);
lean_dec_ref(v_v_1747_);
return v___x_1773_;
}
}
else
{
lean_dec_ref(v_x_1760_);
lean_dec_ref(v_i_1757_);
lean_dec_ref(v___y_1756_);
lean_dec_ref(v_m_1754_);
lean_dec_ref(v_w_1748_);
lean_dec_ref(v_v_1747_);
return v___x_1767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___boxed(lean_object* v_m_1795_, lean_object* v_r_1796_, lean_object* v_i_1797_, lean_object* v_x_1798_, lean_object* v_v_1799_, lean_object* v_w_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1795_, v_r_1796_, v_i_1797_, v_x_1798_, v_v_1799_, v_w_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_x_1798_);
lean_dec(v_r_1796_);
return v_res_1806_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0(void){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_instMonadEIO(lean_box(0));
return v___x_1807_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0);
v___x_1809_ = l_StateRefT_x27_instMonad___redArg(v___x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(lean_object* v_c_1814_, lean_object* v_v_1815_, lean_object* v_assumptions_1816_, lean_object* v_x_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, uint8_t v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v___x_1828_; lean_object* v_toApplicative_1829_; lean_object* v_toFunctor_1830_; lean_object* v_toSeq_1831_; lean_object* v_toSeqLeft_1832_; lean_object* v_toSeqRight_1833_; lean_object* v___f_1834_; lean_object* v___f_1835_; lean_object* v___f_1836_; lean_object* v___f_1837_; lean_object* v___x_1838_; lean_object* v___f_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v_toApplicative_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1940_; 
v___x_1828_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1);
v_toApplicative_1829_ = lean_ctor_get(v___x_1828_, 0);
v_toFunctor_1830_ = lean_ctor_get(v_toApplicative_1829_, 0);
v_toSeq_1831_ = lean_ctor_get(v_toApplicative_1829_, 2);
v_toSeqLeft_1832_ = lean_ctor_get(v_toApplicative_1829_, 3);
v_toSeqRight_1833_ = lean_ctor_get(v_toApplicative_1829_, 4);
v___f_1834_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2));
v___f_1835_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1830_, 2);
v___f_1836_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1836_, 0, v_toFunctor_1830_);
v___f_1837_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1837_, 0, v_toFunctor_1830_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___f_1836_);
lean_ctor_set(v___x_1838_, 1, v___f_1837_);
lean_inc(v_toSeqRight_1833_);
v___f_1839_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1839_, 0, v_toSeqRight_1833_);
lean_inc(v_toSeqLeft_1832_);
v___f_1840_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1840_, 0, v_toSeqLeft_1832_);
lean_inc(v_toSeq_1831_);
v___f_1841_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1841_, 0, v_toSeq_1831_);
v___x_1842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1838_);
lean_ctor_set(v___x_1842_, 1, v___f_1834_);
lean_ctor_set(v___x_1842_, 2, v___f_1841_);
lean_ctor_set(v___x_1842_, 3, v___f_1840_);
lean_ctor_set(v___x_1842_, 4, v___f_1839_);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v___f_1835_);
v___x_1844_ = l_StateRefT_x27_instMonad___redArg(v___x_1843_);
v_toApplicative_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v___x_1844_, 1);
lean_dec(v_unused_1941_);
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1940_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_toApplicative_1845_);
lean_dec(v___x_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1940_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_toFunctor_1849_; lean_object* v_toSeq_1850_; lean_object* v_toSeqLeft_1851_; lean_object* v_toSeqRight_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1938_; 
v_toFunctor_1849_ = lean_ctor_get(v_toApplicative_1845_, 0);
v_toSeq_1850_ = lean_ctor_get(v_toApplicative_1845_, 2);
v_toSeqLeft_1851_ = lean_ctor_get(v_toApplicative_1845_, 3);
v_toSeqRight_1852_ = lean_ctor_get(v_toApplicative_1845_, 4);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_toApplicative_1845_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v_toApplicative_1845_, 1);
lean_dec(v_unused_1939_);
v___x_1854_ = v_toApplicative_1845_;
v_isShared_1855_ = v_isSharedCheck_1938_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_toSeqRight_1852_);
lean_inc(v_toSeqLeft_1851_);
lean_inc(v_toSeq_1850_);
lean_inc(v_toFunctor_1849_);
lean_dec(v_toApplicative_1845_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1938_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___f_1856_; lean_object* v___f_1857_; lean_object* v___f_1858_; lean_object* v___f_1859_; lean_object* v___x_1860_; lean_object* v___f_1861_; lean_object* v___f_1862_; lean_object* v___f_1863_; lean_object* v___x_1865_; 
v___f_1856_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4));
v___f_1857_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5));
lean_inc_ref(v_toFunctor_1849_);
v___f_1858_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1858_, 0, v_toFunctor_1849_);
v___f_1859_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1859_, 0, v_toFunctor_1849_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___f_1858_);
lean_ctor_set(v___x_1860_, 1, v___f_1859_);
v___f_1861_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1861_, 0, v_toSeqRight_1852_);
v___f_1862_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1862_, 0, v_toSeqLeft_1851_);
v___f_1863_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1863_, 0, v_toSeq_1850_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 4, v___f_1861_);
lean_ctor_set(v___x_1854_, 3, v___f_1862_);
lean_ctor_set(v___x_1854_, 2, v___f_1863_);
lean_ctor_set(v___x_1854_, 1, v___f_1856_);
lean_ctor_set(v___x_1854_, 0, v___x_1860_);
v___x_1865_ = v___x_1854_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___f_1856_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v___f_1863_);
lean_ctor_set(v_reuseFailAlloc_1937_, 3, v___f_1862_);
lean_ctor_set(v_reuseFailAlloc_1937_, 4, v___f_1861_);
v___x_1865_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1867_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 1, v___f_1857_);
lean_ctor_set(v___x_1847_, 0, v___x_1865_);
v___x_1867_ = v___x_1847_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___f_1857_);
v___x_1867_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1868_ = l_StateRefT_x27_instMonad___redArg(v___x_1867_);
v___x_1869_ = l_ReaderT_instMonad___redArg(v___x_1868_);
v___x_1870_ = l_ReaderT_instMonad___redArg(v___x_1869_);
v___x_1871_ = l_StateRefT_x27_instMonad___redArg(v___x_1870_);
v___x_1872_ = l_StateRefT_x27_instMonad___redArg(v___x_1871_);
switch(lean_obj_tag(v_x_1817_))
{
case 0:
{
lean_object* v_i_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_3965__overap_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec_ref(v_v_1815_);
v_i_1873_ = lean_ctor_get(v_x_1817_, 2);
lean_inc(v_i_1873_);
lean_dec_ref(v_x_1817_);
v___x_1874_ = l_Lean_instInhabitedExpr;
v___x_1875_ = l_instInhabitedOfMonad___redArg(v___x_1872_, v___x_1874_);
v___x_3965__overap_1876_ = lean_array_get(v___x_1875_, v_assumptions_1816_, v_i_1873_);
lean_dec(v_i_1873_);
lean_dec(v___x_1875_);
v___x_1877_ = lean_box(v_a_1821_);
lean_inc(v_a_1826_);
lean_inc_ref(v_a_1825_);
lean_inc(v_a_1824_);
lean_inc_ref(v_a_1823_);
lean_inc(v_a_1822_);
lean_inc_ref(v_a_1820_);
lean_inc(v_a_1819_);
lean_inc(v_a_1818_);
v___x_1878_ = lean_apply_10(v___x_3965__overap_1876_, v_a_1818_, v_a_1819_, v_a_1820_, v___x_1877_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, lean_box(0));
return v___x_1878_;
}
case 1:
{
lean_object* v_s_1879_; lean_object* v_c_1880_; lean_object* v_j_1881_; lean_object* v___x_1882_; 
lean_dec_ref(v___x_1872_);
v_s_1879_ = lean_ctor_get(v_x_1817_, 0);
lean_inc_ref(v_s_1879_);
v_c_1880_ = lean_ctor_get(v_x_1817_, 1);
lean_inc(v_c_1880_);
v_j_1881_ = lean_ctor_get(v_x_1817_, 2);
lean_inc_ref(v_j_1881_);
lean_dec_ref(v_x_1817_);
lean_inc_ref(v_v_1815_);
v___x_1882_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1880_, v_v_1815_, v_assumptions_1816_, v_j_1881_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1891_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1879_, v_c_1880_, v_v_1815_, v_a_1883_);
lean_dec(v_c_1880_);
lean_dec_ref(v_s_1879_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
else
{
lean_dec(v_c_1880_);
lean_dec_ref(v_s_1879_);
lean_dec_ref(v_v_1815_);
return v___x_1882_;
}
}
case 2:
{
lean_object* v_s_1892_; lean_object* v_t_1893_; lean_object* v_j_1894_; lean_object* v_k_1895_; lean_object* v___x_1896_; 
lean_dec_ref(v___x_1872_);
v_s_1892_ = lean_ctor_get(v_x_1817_, 0);
lean_inc_ref(v_s_1892_);
v_t_1893_ = lean_ctor_get(v_x_1817_, 1);
lean_inc_ref(v_t_1893_);
v_j_1894_ = lean_ctor_get(v_x_1817_, 3);
lean_inc_ref(v_j_1894_);
v_k_1895_ = lean_ctor_get(v_x_1817_, 4);
lean_inc_ref(v_k_1895_);
lean_dec_ref(v_x_1817_);
lean_inc_ref(v_v_1815_);
v___x_1896_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1814_, v_v_1815_, v_assumptions_1816_, v_j_1894_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1898_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref(v___x_1896_);
lean_inc_ref(v_v_1815_);
v___x_1898_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1814_, v_v_1815_, v_assumptions_1816_, v_k_1895_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1907_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1907_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1907_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1903_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1892_, v_t_1893_, v_c_1814_, v_v_1815_, v_a_1897_, v_a_1899_);
lean_dec_ref(v_t_1893_);
lean_dec_ref(v_s_1892_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1903_);
v___x_1905_ = v___x_1901_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
else
{
lean_dec(v_a_1897_);
lean_dec_ref(v_t_1893_);
lean_dec_ref(v_s_1892_);
lean_dec_ref(v_v_1815_);
return v___x_1898_;
}
}
else
{
lean_dec_ref(v_k_1895_);
lean_dec_ref(v_t_1893_);
lean_dec_ref(v_s_1892_);
lean_dec_ref(v_v_1815_);
return v___x_1896_;
}
}
case 3:
{
lean_object* v_s_1908_; lean_object* v_t_1909_; lean_object* v_x_1910_; lean_object* v_y_1911_; lean_object* v_a_1912_; lean_object* v_j_1913_; lean_object* v_b_1914_; lean_object* v_k_1915_; lean_object* v___x_1916_; 
lean_dec_ref(v___x_1872_);
v_s_1908_ = lean_ctor_get(v_x_1817_, 0);
lean_inc_ref(v_s_1908_);
v_t_1909_ = lean_ctor_get(v_x_1817_, 1);
lean_inc_ref(v_t_1909_);
v_x_1910_ = lean_ctor_get(v_x_1817_, 2);
lean_inc(v_x_1910_);
v_y_1911_ = lean_ctor_get(v_x_1817_, 3);
lean_inc(v_y_1911_);
v_a_1912_ = lean_ctor_get(v_x_1817_, 4);
lean_inc(v_a_1912_);
v_j_1913_ = lean_ctor_get(v_x_1817_, 5);
lean_inc_ref(v_j_1913_);
v_b_1914_ = lean_ctor_get(v_x_1817_, 6);
lean_inc(v_b_1914_);
v_k_1915_ = lean_ctor_get(v_x_1817_, 7);
lean_inc_ref(v_k_1915_);
lean_dec_ref(v_x_1817_);
lean_inc_ref(v_v_1815_);
v___x_1916_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1910_, v_v_1815_, v_assumptions_1816_, v_j_1913_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref(v___x_1916_);
lean_inc_ref(v_v_1815_);
v___x_1918_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_y_1911_, v_v_1815_, v_assumptions_1816_, v_k_1915_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1927_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1927_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1927_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1908_, v_t_1909_, v_a_1912_, v_x_1910_, v_b_1914_, v_y_1911_, v_v_1815_, v_a_1917_, v_a_1919_);
lean_dec(v_y_1911_);
lean_dec(v_b_1914_);
lean_dec(v_x_1910_);
lean_dec(v_a_1912_);
lean_dec_ref(v_t_1909_);
lean_dec_ref(v_s_1908_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1923_);
v___x_1925_ = v___x_1921_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
else
{
lean_dec(v_a_1917_);
lean_dec(v_b_1914_);
lean_dec(v_a_1912_);
lean_dec(v_y_1911_);
lean_dec(v_x_1910_);
lean_dec_ref(v_t_1909_);
lean_dec_ref(v_s_1908_);
lean_dec_ref(v_v_1815_);
return v___x_1918_;
}
}
else
{
lean_dec_ref(v_k_1915_);
lean_dec(v_b_1914_);
lean_dec(v_a_1912_);
lean_dec(v_y_1911_);
lean_dec(v_x_1910_);
lean_dec_ref(v_t_1909_);
lean_dec_ref(v_s_1908_);
lean_dec_ref(v_v_1815_);
return v___x_1916_;
}
}
default: 
{
lean_object* v_m_1928_; lean_object* v_r_1929_; lean_object* v_i_1930_; lean_object* v_x_1931_; lean_object* v_j_1932_; lean_object* v___x_1933_; 
lean_dec_ref(v___x_1872_);
v_m_1928_ = lean_ctor_get(v_x_1817_, 0);
lean_inc(v_m_1928_);
v_r_1929_ = lean_ctor_get(v_x_1817_, 1);
lean_inc(v_r_1929_);
v_i_1930_ = lean_ctor_get(v_x_1817_, 2);
lean_inc(v_i_1930_);
v_x_1931_ = lean_ctor_get(v_x_1817_, 3);
lean_inc(v_x_1931_);
v_j_1932_ = lean_ctor_get(v_x_1817_, 4);
lean_inc_ref(v_j_1932_);
lean_dec_ref(v_x_1817_);
lean_inc_ref(v_v_1815_);
v___x_1933_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1931_, v_v_1815_, v_assumptions_1816_, v_j_1932_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1935_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref(v___x_1933_);
v___x_1935_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1928_, v_r_1929_, v_i_1930_, v_x_1931_, v_v_1815_, v_a_1934_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_x_1931_);
lean_dec(v_r_1929_);
return v___x_1935_;
}
else
{
lean_dec(v_x_1931_);
lean_dec(v_i_1930_);
lean_dec(v_r_1929_);
lean_dec(v_m_1928_);
lean_dec_ref(v_v_1815_);
return v___x_1933_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___boxed(lean_object* v_c_1942_, lean_object* v_v_1943_, lean_object* v_assumptions_1944_, lean_object* v_x_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
uint8_t v_a_boxed_1956_; lean_object* v_res_1957_; 
v_a_boxed_1956_ = lean_unbox(v_a_1949_);
v_res_1957_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1942_, v_v_1943_, v_assumptions_1944_, v_x_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_boxed_1956_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec_ref(v_assumptions_1944_);
lean_dec(v_c_1942_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof(lean_object* v_s_1958_, lean_object* v_c_1959_, lean_object* v_v_1960_, lean_object* v_assumptions_1961_, lean_object* v_x_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, uint8_t v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1959_, v_v_1960_, v_assumptions_1961_, v_x_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___boxed(lean_object* v_s_1974_, lean_object* v_c_1975_, lean_object* v_v_1976_, lean_object* v_assumptions_1977_, lean_object* v_x_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
uint8_t v_a_boxed_1989_; lean_object* v_res_1990_; 
v_a_boxed_1989_ = lean_unbox(v_a_1982_);
v_res_1990_ = l_Lean_Elab_Tactic_Omega_Justification_proof(v_s_1974_, v_c_1975_, v_v_1976_, v_assumptions_1977_, v_x_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_boxed_1989_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_assumptions_1977_);
lean_dec(v_c_1975_);
lean_dec_ref(v_s_1974_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_instToString___lam__0(lean_object* v_f_1991_){
_start:
{
lean_object* v_coeffs_1992_; lean_object* v_constraint_1993_; lean_object* v_justification_1994_; lean_object* v___x_1995_; 
v_coeffs_1992_ = lean_ctor_get(v_f_1991_, 0);
lean_inc(v_coeffs_1992_);
v_constraint_1993_ = lean_ctor_get(v_f_1991_, 1);
lean_inc_ref(v_constraint_1993_);
v_justification_1994_ = lean_ctor_get(v_f_1991_, 2);
lean_inc_ref(v_justification_1994_);
lean_dec_ref(v_f_1991_);
v___x_1995_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_1993_, v_coeffs_1992_, v_justification_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_tidy(lean_object* v_f_1998_){
_start:
{
lean_object* v_coeffs_1999_; lean_object* v_constraint_2000_; lean_object* v_justification_2001_; lean_object* v___x_2002_; 
v_coeffs_1999_ = lean_ctor_get(v_f_1998_, 0);
v_constraint_2000_ = lean_ctor_get(v_f_1998_, 1);
v_justification_2001_ = lean_ctor_get(v_f_1998_, 2);
lean_inc_ref(v_justification_2001_);
lean_inc(v_coeffs_1999_);
lean_inc_ref(v_constraint_2000_);
v___x_2002_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(v_constraint_2000_, v_coeffs_1999_, v_justification_2001_);
if (lean_obj_tag(v___x_2002_) == 0)
{
return v_f_1998_;
}
else
{
lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2014_; 
v_isSharedCheck_2014_ = !lean_is_exclusive(v_f_1998_);
if (v_isSharedCheck_2014_ == 0)
{
lean_object* v_unused_2015_; lean_object* v_unused_2016_; lean_object* v_unused_2017_; 
v_unused_2015_ = lean_ctor_get(v_f_1998_, 2);
lean_dec(v_unused_2015_);
v_unused_2016_ = lean_ctor_get(v_f_1998_, 1);
lean_dec(v_unused_2016_);
v_unused_2017_ = lean_ctor_get(v_f_1998_, 0);
lean_dec(v_unused_2017_);
v___x_2004_ = v_f_1998_;
v_isShared_2005_ = v_isSharedCheck_2014_;
goto v_resetjp_2003_;
}
else
{
lean_dec(v_f_1998_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2014_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v_val_2006_; lean_object* v_snd_2007_; lean_object* v_fst_2008_; lean_object* v_fst_2009_; lean_object* v_snd_2010_; lean_object* v___x_2012_; 
v_val_2006_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_val_2006_);
lean_dec_ref(v___x_2002_);
v_snd_2007_ = lean_ctor_get(v_val_2006_, 1);
lean_inc(v_snd_2007_);
v_fst_2008_ = lean_ctor_get(v_val_2006_, 0);
lean_inc(v_fst_2008_);
lean_dec(v_val_2006_);
v_fst_2009_ = lean_ctor_get(v_snd_2007_, 0);
lean_inc(v_fst_2009_);
v_snd_2010_ = lean_ctor_get(v_snd_2007_, 1);
lean_inc(v_snd_2010_);
lean_dec(v_snd_2007_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 2, v_snd_2010_);
lean_ctor_set(v___x_2004_, 1, v_fst_2008_);
lean_ctor_set(v___x_2004_, 0, v_fst_2009_);
v___x_2012_ = v___x_2004_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_fst_2009_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_fst_2008_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_snd_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_combo(lean_object* v_a_2018_, lean_object* v_f_2019_, lean_object* v_b_2020_, lean_object* v_g_2021_){
_start:
{
lean_object* v_coeffs_2022_; lean_object* v_constraint_2023_; lean_object* v_justification_2024_; lean_object* v_coeffs_2025_; lean_object* v_constraint_2026_; lean_object* v_justification_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2037_; 
v_coeffs_2022_ = lean_ctor_get(v_f_2019_, 0);
lean_inc(v_coeffs_2022_);
v_constraint_2023_ = lean_ctor_get(v_f_2019_, 1);
lean_inc_ref(v_constraint_2023_);
v_justification_2024_ = lean_ctor_get(v_f_2019_, 2);
lean_inc_ref(v_justification_2024_);
lean_dec_ref(v_f_2019_);
v_coeffs_2025_ = lean_ctor_get(v_g_2021_, 0);
v_constraint_2026_ = lean_ctor_get(v_g_2021_, 1);
v_justification_2027_ = lean_ctor_get(v_g_2021_, 2);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_g_2021_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2029_ = v_g_2021_;
v_isShared_2030_ = v_isSharedCheck_2037_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_justification_2027_);
lean_inc(v_constraint_2026_);
lean_inc(v_coeffs_2025_);
lean_dec(v_g_2021_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2037_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
lean_inc(v_coeffs_2025_);
lean_inc_n(v_b_2020_, 2);
lean_inc(v_coeffs_2022_);
lean_inc_n(v_a_2018_, 2);
v___x_2031_ = l_Lean_Omega_IntList_combo(v_a_2018_, v_coeffs_2022_, v_b_2020_, v_coeffs_2025_);
lean_inc_ref(v_constraint_2026_);
lean_inc_ref(v_constraint_2023_);
v___x_2032_ = l_Lean_Omega_Constraint_combo(v_a_2018_, v_constraint_2023_, v_b_2020_, v_constraint_2026_);
v___x_2033_ = lean_alloc_ctor(3, 8, 0);
lean_ctor_set(v___x_2033_, 0, v_constraint_2023_);
lean_ctor_set(v___x_2033_, 1, v_constraint_2026_);
lean_ctor_set(v___x_2033_, 2, v_coeffs_2022_);
lean_ctor_set(v___x_2033_, 3, v_coeffs_2025_);
lean_ctor_set(v___x_2033_, 4, v_a_2018_);
lean_ctor_set(v___x_2033_, 5, v_justification_2024_);
lean_ctor_set(v___x_2033_, 6, v_b_2020_);
lean_ctor_set(v___x_2033_, 7, v_justification_2027_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 2, v___x_2033_);
lean_ctor_set(v___x_2029_, 1, v___x_2032_);
lean_ctor_set(v___x_2029_, 0, v___x_2031_);
v___x_2035_ = v___x_2029_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__10));
v___x_2064_ = l_Lean_mkAtom(v___x_2063_);
return v___x_2064_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11);
v___x_2066_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2067_ = lean_array_push(v___x_2066_, v___x_2065_);
return v___x_2067_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2068_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12);
v___x_2069_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9));
v___x_2070_ = lean_box(2);
v___x_2071_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v___x_2069_);
lean_ctor_set(v___x_2071_, 2, v___x_2068_);
return v___x_2071_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14(void){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13);
v___x_2073_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2074_ = lean_array_push(v___x_2073_, v___x_2072_);
return v___x_2074_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2075_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14);
v___x_2076_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7));
v___x_2077_ = lean_box(2);
v___x_2078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v___x_2076_);
lean_ctor_set(v___x_2078_, 2, v___x_2075_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15);
v___x_2080_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2081_ = lean_array_push(v___x_2080_, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2082_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16);
v___x_2083_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5));
v___x_2084_ = lean_box(2);
v___x_2085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v___x_2083_);
lean_ctor_set(v___x_2085_, 2, v___x_2082_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17);
v___x_2087_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2088_ = lean_array_push(v___x_2087_, v___x_2086_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2089_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18);
v___x_2090_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2));
v___x_2091_ = lean_box(2);
v___x_2092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v___x_2090_);
lean_ctor_set(v___x_2092_, 2, v___x_2089_);
return v___x_2092_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam(void){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19);
return v___x_2093_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_isEmpty(lean_object* v_p_2094_){
_start:
{
lean_object* v_constraints_2095_; lean_object* v_size_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v_constraints_2095_ = lean_ctor_get(v_p_2094_, 2);
v_size_2096_ = lean_ctor_get(v_constraints_2095_, 0);
v___x_2097_ = lean_unsigned_to_nat(0u);
v___x_2098_ = lean_nat_dec_eq(v_size_2096_, v___x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_isEmpty___boxed(lean_object* v_p_2099_){
_start:
{
uint8_t v_res_2100_; lean_object* v_r_2101_; 
v_res_2100_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2099_);
lean_dec_ref(v_p_2099_);
v_r_2101_ = lean_box(v_res_2100_);
return v_r_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object* v_x_2103_){
_start:
{
lean_object* v_snd_2104_; lean_object* v_constraint_2105_; lean_object* v_fst_2106_; lean_object* v_lowerBound_2107_; lean_object* v_upperBound_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___y_2114_; lean_object* v___y_2115_; 
v_snd_2104_ = lean_ctor_get(v_x_2103_, 1);
v_constraint_2105_ = lean_ctor_get(v_snd_2104_, 1);
lean_inc_ref(v_constraint_2105_);
v_fst_2106_ = lean_ctor_get(v_x_2103_, 0);
lean_inc(v_fst_2106_);
lean_dec_ref(v_x_2103_);
v_lowerBound_2107_ = lean_ctor_get(v_constraint_2105_, 0);
lean_inc(v_lowerBound_2107_);
v_upperBound_2108_ = lean_ctor_get(v_constraint_2105_, 1);
lean_inc(v_upperBound_2108_);
lean_dec_ref(v_constraint_2105_);
v___x_2109_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0___closed__0));
v___x_2110_ = l_List_toString___redArg(v___x_2109_, v_fst_2106_);
v___x_2111_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_2112_ = lean_string_append(v___x_2110_, v___x_2111_);
if (lean_obj_tag(v_lowerBound_2107_) == 0)
{
if (lean_obj_tag(v_upperBound_2108_) == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_2121_ = lean_string_append(v___x_2112_, v___x_2120_);
return v___x_2121_;
}
else
{
lean_object* v_val_2122_; lean_object* v___x_2123_; lean_object* v___y_2125_; lean_object* v_intZero_2130_; uint8_t v_isNeg_2131_; 
v_val_2122_ = lean_ctor_get(v_upperBound_2108_, 0);
lean_inc(v_val_2122_);
lean_dec_ref(v_upperBound_2108_);
v___x_2123_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_2130_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2131_ = lean_int_dec_lt(v_val_2122_, v_intZero_2130_);
if (v_isNeg_2131_ == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; 
v_a_2132_ = lean_nat_abs(v_val_2122_);
lean_dec(v_val_2122_);
v___x_2133_ = l_Nat_reprFast(v_a_2132_);
v___y_2125_ = v___x_2133_;
goto v___jp_2124_;
}
else
{
lean_object* v_abs_2134_; lean_object* v_one_2135_; lean_object* v_a_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v_abs_2134_ = lean_nat_abs(v_val_2122_);
lean_dec(v_val_2122_);
v_one_2135_ = lean_unsigned_to_nat(1u);
v_a_2136_ = lean_nat_sub(v_abs_2134_, v_one_2135_);
lean_dec(v_abs_2134_);
v___x_2137_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2138_ = lean_nat_add(v_a_2136_, v_one_2135_);
lean_dec(v_a_2136_);
v___x_2139_ = l_Nat_reprFast(v___x_2138_);
v___x_2140_ = lean_string_append(v___x_2137_, v___x_2139_);
lean_dec_ref(v___x_2139_);
v___y_2125_ = v___x_2140_;
goto v___jp_2124_;
}
v___jp_2124_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2126_ = lean_string_append(v___x_2123_, v___y_2125_);
lean_dec_ref(v___y_2125_);
v___x_2127_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2128_ = lean_string_append(v___x_2126_, v___x_2127_);
v___x_2129_ = lean_string_append(v___x_2112_, v___x_2128_);
lean_dec_ref(v___x_2128_);
return v___x_2129_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_2108_) == 0)
{
lean_object* v_val_2141_; lean_object* v___x_2142_; lean_object* v___y_2144_; lean_object* v_intZero_2149_; uint8_t v_isNeg_2150_; 
v_val_2141_ = lean_ctor_get(v_lowerBound_2107_, 0);
lean_inc(v_val_2141_);
lean_dec_ref(v_lowerBound_2107_);
v___x_2142_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2149_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2150_ = lean_int_dec_lt(v_val_2141_, v_intZero_2149_);
if (v_isNeg_2150_ == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; 
v_a_2151_ = lean_nat_abs(v_val_2141_);
lean_dec(v_val_2141_);
v___x_2152_ = l_Nat_reprFast(v_a_2151_);
v___y_2144_ = v___x_2152_;
goto v___jp_2143_;
}
else
{
lean_object* v_abs_2153_; lean_object* v_one_2154_; lean_object* v_a_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v_abs_2153_ = lean_nat_abs(v_val_2141_);
lean_dec(v_val_2141_);
v_one_2154_ = lean_unsigned_to_nat(1u);
v_a_2155_ = lean_nat_sub(v_abs_2153_, v_one_2154_);
lean_dec(v_abs_2153_);
v___x_2156_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2157_ = lean_nat_add(v_a_2155_, v_one_2154_);
lean_dec(v_a_2155_);
v___x_2158_ = l_Nat_reprFast(v___x_2157_);
v___x_2159_ = lean_string_append(v___x_2156_, v___x_2158_);
lean_dec_ref(v___x_2158_);
v___y_2144_ = v___x_2159_;
goto v___jp_2143_;
}
v___jp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2145_ = lean_string_append(v___x_2142_, v___y_2144_);
lean_dec_ref(v___y_2144_);
v___x_2146_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_2147_ = lean_string_append(v___x_2145_, v___x_2146_);
v___x_2148_ = lean_string_append(v___x_2112_, v___x_2147_);
lean_dec_ref(v___x_2147_);
return v___x_2148_;
}
}
else
{
lean_object* v_val_2160_; lean_object* v_val_2161_; uint8_t v___x_2162_; 
v_val_2160_ = lean_ctor_get(v_lowerBound_2107_, 0);
lean_inc(v_val_2160_);
lean_dec_ref(v_lowerBound_2107_);
v_val_2161_ = lean_ctor_get(v_upperBound_2108_, 0);
lean_inc(v_val_2161_);
lean_dec_ref(v_upperBound_2108_);
v___x_2162_ = lean_int_dec_lt(v_val_2161_, v_val_2160_);
if (v___x_2162_ == 0)
{
uint8_t v___x_2163_; 
v___x_2163_ = lean_int_dec_eq(v_val_2160_, v_val_2161_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; lean_object* v___y_2166_; lean_object* v_intZero_2181_; uint8_t v_isNeg_2182_; 
v___x_2164_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2181_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2182_ = lean_int_dec_lt(v_val_2160_, v_intZero_2181_);
if (v_isNeg_2182_ == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; 
v_a_2183_ = lean_nat_abs(v_val_2160_);
lean_dec(v_val_2160_);
v___x_2184_ = l_Nat_reprFast(v_a_2183_);
v___y_2166_ = v___x_2184_;
goto v___jp_2165_;
}
else
{
lean_object* v_abs_2185_; lean_object* v_one_2186_; lean_object* v_a_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v_abs_2185_ = lean_nat_abs(v_val_2160_);
lean_dec(v_val_2160_);
v_one_2186_ = lean_unsigned_to_nat(1u);
v_a_2187_ = lean_nat_sub(v_abs_2185_, v_one_2186_);
lean_dec(v_abs_2185_);
v___x_2188_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2189_ = lean_nat_add(v_a_2187_, v_one_2186_);
lean_dec(v_a_2187_);
v___x_2190_ = l_Nat_reprFast(v___x_2189_);
v___x_2191_ = lean_string_append(v___x_2188_, v___x_2190_);
lean_dec_ref(v___x_2190_);
v___y_2166_ = v___x_2191_;
goto v___jp_2165_;
}
v___jp_2165_:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v_intZero_2170_; uint8_t v_isNeg_2171_; 
v___x_2167_ = lean_string_append(v___x_2164_, v___y_2166_);
lean_dec_ref(v___y_2166_);
v___x_2168_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_2169_ = lean_string_append(v___x_2167_, v___x_2168_);
v_intZero_2170_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2171_ = lean_int_dec_lt(v_val_2161_, v_intZero_2170_);
if (v_isNeg_2171_ == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; 
v_a_2172_ = lean_nat_abs(v_val_2161_);
lean_dec(v_val_2161_);
v___x_2173_ = l_Nat_reprFast(v_a_2172_);
v___y_2114_ = v___x_2169_;
v___y_2115_ = v___x_2173_;
goto v___jp_2113_;
}
else
{
lean_object* v_abs_2174_; lean_object* v_one_2175_; lean_object* v_a_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v_abs_2174_ = lean_nat_abs(v_val_2161_);
lean_dec(v_val_2161_);
v_one_2175_ = lean_unsigned_to_nat(1u);
v_a_2176_ = lean_nat_sub(v_abs_2174_, v_one_2175_);
lean_dec(v_abs_2174_);
v___x_2177_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2178_ = lean_nat_add(v_a_2176_, v_one_2175_);
lean_dec(v_a_2176_);
v___x_2179_ = l_Nat_reprFast(v___x_2178_);
v___x_2180_ = lean_string_append(v___x_2177_, v___x_2179_);
lean_dec_ref(v___x_2179_);
v___y_2114_ = v___x_2169_;
v___y_2115_ = v___x_2180_;
goto v___jp_2113_;
}
}
}
else
{
lean_object* v___x_2192_; lean_object* v___y_2194_; lean_object* v_intZero_2199_; uint8_t v_isNeg_2200_; 
lean_dec(v_val_2161_);
v___x_2192_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_2199_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2200_ = lean_int_dec_lt(v_val_2160_, v_intZero_2199_);
if (v_isNeg_2200_ == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2202_; 
v_a_2201_ = lean_nat_abs(v_val_2160_);
lean_dec(v_val_2160_);
v___x_2202_ = l_Nat_reprFast(v_a_2201_);
v___y_2194_ = v___x_2202_;
goto v___jp_2193_;
}
else
{
lean_object* v_abs_2203_; lean_object* v_one_2204_; lean_object* v_a_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v_abs_2203_ = lean_nat_abs(v_val_2160_);
lean_dec(v_val_2160_);
v_one_2204_ = lean_unsigned_to_nat(1u);
v_a_2205_ = lean_nat_sub(v_abs_2203_, v_one_2204_);
lean_dec(v_abs_2203_);
v___x_2206_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2207_ = lean_nat_add(v_a_2205_, v_one_2204_);
lean_dec(v_a_2205_);
v___x_2208_ = l_Nat_reprFast(v___x_2207_);
v___x_2209_ = lean_string_append(v___x_2206_, v___x_2208_);
lean_dec_ref(v___x_2208_);
v___y_2194_ = v___x_2209_;
goto v___jp_2193_;
}
v___jp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2195_ = lean_string_append(v___x_2192_, v___y_2194_);
lean_dec_ref(v___y_2194_);
v___x_2196_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_2197_ = lean_string_append(v___x_2195_, v___x_2196_);
v___x_2198_ = lean_string_append(v___x_2112_, v___x_2197_);
lean_dec_ref(v___x_2197_);
return v___x_2198_;
}
}
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec(v_val_2161_);
lean_dec(v_val_2160_);
v___x_2210_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_2211_ = lean_string_append(v___x_2112_, v___x_2210_);
return v___x_2211_;
}
}
}
v___jp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2116_ = lean_string_append(v___y_2114_, v___y_2115_);
lean_dec_ref(v___y_2115_);
v___x_2117_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2118_ = lean_string_append(v___x_2116_, v___x_2117_);
v___x_2119_ = lean_string_append(v___x_2112_, v___x_2118_);
lean_dec_ref(v___x_2118_);
return v___x_2119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object* v_a_2212_, lean_object* v_b_2213_, lean_object* v_d_2214_){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_a_2212_);
lean_ctor_set(v___x_2215_, 1, v_b_2213_);
v___x_2216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v_d_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2(lean_object* v___x_2217_, lean_object* v___f_2218_, lean_object* v_l_2219_, lean_object* v_acc_2220_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2217_, v___f_2218_, v_acc_2220_, v_l_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3(lean_object* v___f_2243_, lean_object* v___f_2244_, lean_object* v_p_2245_){
_start:
{
uint8_t v_possible_2246_; 
v_possible_2246_ = lean_ctor_get_uint8(v_p_2245_, sizeof(void*)*7);
if (v_possible_2246_ == 0)
{
lean_object* v___x_2247_; 
lean_dec_ref(v_p_2245_);
lean_dec_ref(v___f_2244_);
lean_dec_ref(v___f_2243_);
v___x_2247_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
return v___x_2247_;
}
else
{
lean_object* v_constraints_2248_; uint8_t v___x_2249_; 
v_constraints_2248_ = lean_ctor_get(v_p_2245_, 2);
lean_inc_ref(v_constraints_2248_);
v___x_2249_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2245_);
lean_dec_ref(v_p_2245_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v_buckets_2251_; lean_object* v___x_2252_; lean_object* v___y_2254_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2250_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10));
v_buckets_2251_ = lean_ctor_get(v_constraints_2248_, 1);
lean_inc_ref(v_buckets_2251_);
lean_dec_ref(v_constraints_2248_);
v___x_2252_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_2258_ = lean_box(0);
v___x_2259_ = lean_array_get_size(v_buckets_2251_);
v___x_2260_ = lean_unsigned_to_nat(0u);
v___x_2261_ = lean_nat_dec_lt(v___x_2260_, v___x_2259_);
if (v___x_2261_ == 0)
{
lean_dec_ref(v_buckets_2251_);
lean_dec_ref(v___f_2244_);
v___y_2254_ = v___x_2258_;
goto v___jp_2253_;
}
else
{
lean_object* v___f_2262_; size_t v___x_2263_; size_t v___x_2264_; lean_object* v___x_2265_; 
v___f_2262_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2), 4, 2);
lean_closure_set(v___f_2262_, 0, v___x_2250_);
lean_closure_set(v___f_2262_, 1, v___f_2244_);
v___x_2263_ = lean_usize_of_nat(v___x_2259_);
v___x_2264_ = ((size_t)0ULL);
v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2250_, v___f_2262_, v_buckets_2251_, v___x_2263_, v___x_2264_, v___x_2258_);
v___y_2254_ = v___x_2265_;
goto v___jp_2253_;
}
v___jp_2253_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = l_List_mapTR_loop___redArg(v___f_2243_, v___y_2254_, v___x_2255_);
v___x_2257_ = l_String_intercalate(v___x_2252_, v___x_2256_);
return v___x_2257_;
}
}
else
{
lean_object* v___x_2266_; 
lean_dec_ref(v_constraints_2248_);
lean_dec_ref(v___f_2244_);
lean_dec_ref(v___f_2243_);
v___x_2266_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
return v___x_2266_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_box(0);
v___x_2280_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1));
v___x_2281_ = l_Lean_Expr_const___override(v___x_2280_, v___x_2279_);
return v___x_2281_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = lean_box(0);
v___x_2288_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5));
v___x_2289_ = l_Lean_Expr_const___override(v___x_2288_, v___x_2287_);
return v___x_2289_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = lean_box(0);
v___x_2297_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8));
v___x_2298_ = l_Lean_Expr_const___override(v___x_2297_, v___x_2296_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse(lean_object* v_s_2299_, lean_object* v_x_2300_, lean_object* v_j_2301_, lean_object* v_assumptions_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, uint8_t v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2304_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2315_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc_n(v_a_2314_, 2);
lean_dec_ref(v___x_2313_);
v___x_2315_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_2300_, v_a_2314_, v_assumptions_2302_, v_j_2301_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2317_; lean_object* v_lowerBound_2318_; lean_object* v_upperBound_2319_; lean_object* v_nil_2320_; lean_object* v_cons_2321_; lean_object* v___x_2322_; lean_object* v___y_2324_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___x_2347_; lean_object* v___y_2349_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref(v___x_2315_);
v___x_2317_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_lowerBound_2318_ = lean_ctor_get(v_s_2299_, 0);
v_upperBound_2319_ = lean_ctor_get(v_s_2299_, 1);
v_nil_2320_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2321_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2322_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2320_, v_cons_2321_, v_x_2300_);
v___x_2347_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
if (lean_obj_tag(v_lowerBound_2318_) == 0)
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_2349_ = v___x_2365_;
goto v___jp_2348_;
}
else
{
lean_object* v_val_2366_; lean_object* v___x_2367_; lean_object* v___y_2369_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v_val_2366_ = lean_ctor_get(v_lowerBound_2318_, 0);
v___x_2367_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2371_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2372_ = lean_int_dec_le(v___x_2371_, v_val_2366_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2373_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2374_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2375_ = lean_int_neg(v_val_2366_);
v___x_2376_ = l_Int_toNat(v___x_2375_);
lean_dec(v___x_2375_);
v___x_2377_ = l_Lean_instToExprInt_mkNat(v___x_2376_);
v___x_2378_ = l_Lean_mkApp3(v___x_2373_, v___x_2317_, v___x_2374_, v___x_2377_);
v___y_2369_ = v___x_2378_;
goto v___jp_2368_;
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = l_Int_toNat(v_val_2366_);
v___x_2380_ = l_Lean_instToExprInt_mkNat(v___x_2379_);
v___y_2369_ = v___x_2380_;
goto v___jp_2368_;
}
v___jp_2368_:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_mkAppB(v___x_2367_, v___x_2317_, v___y_2369_);
v___y_2349_ = v___x_2370_;
goto v___jp_2348_;
}
}
v___jp_2323_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2325_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2);
lean_inc_ref(v___y_2324_);
v___x_2326_ = l_Lean_Expr_app___override(v___x_2325_, v___y_2324_);
v___x_2327_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6);
v___x_2328_ = l_Lean_Meta_mkEq(v___x_2326_, v___x_2327_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2330_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = l_Lean_Meta_mkDecideProof(v_a_2329_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2340_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2340_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2340_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2335_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9);
v___x_2336_ = l_Lean_mkApp5(v___x_2335_, v___y_2324_, v_a_2331_, v___x_2322_, v_a_2314_, v_a_2316_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2336_);
v___x_2338_ = v___x_2333_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
lean_dec_ref(v___y_2324_);
lean_dec_ref(v___x_2322_);
lean_dec(v_a_2316_);
lean_dec(v_a_2314_);
return v___x_2330_;
}
}
else
{
lean_dec_ref(v___y_2324_);
lean_dec_ref(v___x_2322_);
lean_dec(v_a_2316_);
lean_dec(v_a_2314_);
return v___x_2328_;
}
}
v___jp_2341_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_inc_ref(v___y_2343_);
v___x_2345_ = l_Lean_mkAppB(v___y_2343_, v___x_2317_, v___y_2344_);
v___x_2346_ = l_Lean_Expr_app___override(v___y_2342_, v___x_2345_);
v___y_2324_ = v___x_2346_;
goto v___jp_2323_;
}
v___jp_2348_:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Expr_app___override(v___x_2347_, v___y_2349_);
if (lean_obj_tag(v_upperBound_2319_) == 0)
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_2352_ = l_Lean_Expr_app___override(v___x_2350_, v___x_2351_);
v___y_2324_ = v___x_2352_;
goto v___jp_2323_;
}
else
{
lean_object* v_val_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
v_val_2353_ = lean_ctor_get(v_upperBound_2319_, 0);
v___x_2354_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2355_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2356_ = lean_int_dec_le(v___x_2355_, v_val_2353_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2357_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2358_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2359_ = lean_int_neg(v_val_2353_);
v___x_2360_ = l_Int_toNat(v___x_2359_);
lean_dec(v___x_2359_);
v___x_2361_ = l_Lean_instToExprInt_mkNat(v___x_2360_);
v___x_2362_ = l_Lean_mkApp3(v___x_2357_, v___x_2317_, v___x_2358_, v___x_2361_);
v___y_2342_ = v___x_2350_;
v___y_2343_ = v___x_2354_;
v___y_2344_ = v___x_2362_;
goto v___jp_2341_;
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = l_Int_toNat(v_val_2353_);
v___x_2364_ = l_Lean_instToExprInt_mkNat(v___x_2363_);
v___y_2342_ = v___x_2350_;
v___y_2343_ = v___x_2354_;
v___y_2344_ = v___x_2364_;
goto v___jp_2341_;
}
}
}
}
else
{
lean_dec(v_a_2314_);
return v___x_2315_;
}
}
else
{
lean_dec_ref(v_j_2301_);
return v___x_2313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed(lean_object* v_s_2381_, lean_object* v_x_2382_, lean_object* v_j_2383_, lean_object* v_assumptions_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
uint8_t v_a_boxed_2395_; lean_object* v_res_2396_; 
v_a_boxed_2395_ = lean_unbox(v_a_2388_);
v_res_2396_ = l_Lean_Elab_Tactic_Omega_Problem_proveFalse(v_s_2381_, v_x_2382_, v_j_2383_, v_assumptions_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_boxed_2395_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_assumptions_2384_);
lean_dec(v_x_2382_);
lean_dec_ref(v_s_2381_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0(lean_object* v_constraint_2397_, lean_object* v_coeffs_2398_, lean_object* v_justification_2399_, lean_object* v_x_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_2397_, v_coeffs_2398_, v_justification_2399_);
return v___x_2401_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(lean_object* v_a_2402_, lean_object* v_x_2403_){
_start:
{
if (lean_obj_tag(v_x_2403_) == 0)
{
uint8_t v___x_2404_; 
v___x_2404_ = 0;
return v___x_2404_;
}
else
{
lean_object* v_key_2405_; lean_object* v_tail_2406_; uint8_t v___x_2407_; 
v_key_2405_ = lean_ctor_get(v_x_2403_, 0);
v_tail_2406_ = lean_ctor_get(v_x_2403_, 2);
v___x_2407_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2405_, v_a_2402_);
if (v___x_2407_ == 0)
{
v_x_2403_ = v_tail_2406_;
goto _start;
}
else
{
return v___x_2407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg___boxed(lean_object* v_a_2409_, lean_object* v_x_2410_){
_start:
{
uint8_t v_res_2411_; lean_object* v_r_2412_; 
v_res_2411_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2409_, v_x_2410_);
lean_dec(v_x_2410_);
lean_dec(v_a_2409_);
v_r_2412_ = lean_box(v_res_2411_);
return v_r_2412_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(uint64_t v_x_2413_, lean_object* v_x_2414_){
_start:
{
if (lean_obj_tag(v_x_2414_) == 0)
{
return v_x_2413_;
}
else
{
lean_object* v_head_2415_; lean_object* v_tail_2416_; lean_object* v_intZero_2417_; uint8_t v_isNeg_2418_; 
v_head_2415_ = lean_ctor_get(v_x_2414_, 0);
v_tail_2416_ = lean_ctor_get(v_x_2414_, 1);
v_intZero_2417_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2418_ = lean_int_dec_lt(v_head_2415_, v_intZero_2417_);
if (v_isNeg_2418_ == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; uint64_t v___x_2422_; uint64_t v___x_2423_; 
v_a_2419_ = lean_nat_abs(v_head_2415_);
v___x_2420_ = lean_unsigned_to_nat(2u);
v___x_2421_ = lean_nat_mul(v___x_2420_, v_a_2419_);
lean_dec(v_a_2419_);
v___x_2422_ = lean_uint64_of_nat(v___x_2421_);
lean_dec(v___x_2421_);
v___x_2423_ = lean_uint64_mix_hash(v_x_2413_, v___x_2422_);
v_x_2413_ = v___x_2423_;
v_x_2414_ = v_tail_2416_;
goto _start;
}
else
{
lean_object* v_abs_2425_; lean_object* v_one_2426_; lean_object* v_a_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; uint64_t v___x_2431_; uint64_t v___x_2432_; 
v_abs_2425_ = lean_nat_abs(v_head_2415_);
v_one_2426_ = lean_unsigned_to_nat(1u);
v_a_2427_ = lean_nat_sub(v_abs_2425_, v_one_2426_);
lean_dec(v_abs_2425_);
v___x_2428_ = lean_unsigned_to_nat(2u);
v___x_2429_ = lean_nat_mul(v___x_2428_, v_a_2427_);
lean_dec(v_a_2427_);
v___x_2430_ = lean_nat_add(v___x_2429_, v_one_2426_);
lean_dec(v___x_2429_);
v___x_2431_ = lean_uint64_of_nat(v___x_2430_);
lean_dec(v___x_2430_);
v___x_2432_ = lean_uint64_mix_hash(v_x_2413_, v___x_2431_);
v_x_2413_ = v___x_2432_;
v_x_2414_ = v_tail_2416_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0___boxed(lean_object* v_x_2434_, lean_object* v_x_2435_){
_start:
{
uint64_t v_x_980__boxed_2436_; uint64_t v_res_2437_; lean_object* v_r_2438_; 
v_x_980__boxed_2436_ = lean_unbox_uint64(v_x_2434_);
lean_dec_ref(v_x_2434_);
v_res_2437_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v_x_980__boxed_2436_, v_x_2435_);
lean_dec(v_x_2435_);
v_r_2438_ = lean_box_uint64(v_res_2437_);
return v_r_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_2439_, lean_object* v_x_2440_){
_start:
{
if (lean_obj_tag(v_x_2440_) == 0)
{
return v_x_2439_;
}
else
{
lean_object* v_key_2441_; lean_object* v_value_2442_; lean_object* v_tail_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2467_; 
v_key_2441_ = lean_ctor_get(v_x_2440_, 0);
v_value_2442_ = lean_ctor_get(v_x_2440_, 1);
v_tail_2443_ = lean_ctor_get(v_x_2440_, 2);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_x_2440_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2445_ = v_x_2440_;
v_isShared_2446_ = v_isSharedCheck_2467_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_tail_2443_);
lean_inc(v_value_2442_);
lean_inc(v_key_2441_);
lean_dec(v_x_2440_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2467_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; uint64_t v___x_2448_; uint64_t v___x_2449_; uint64_t v___x_2450_; uint64_t v___x_2451_; uint64_t v_fold_2452_; uint64_t v___x_2453_; uint64_t v___x_2454_; uint64_t v___x_2455_; size_t v___x_2456_; size_t v___x_2457_; size_t v___x_2458_; size_t v___x_2459_; size_t v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2463_; 
v___x_2447_ = lean_array_get_size(v_x_2439_);
v___x_2448_ = 7ULL;
v___x_2449_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2448_, v_key_2441_);
v___x_2450_ = 32ULL;
v___x_2451_ = lean_uint64_shift_right(v___x_2449_, v___x_2450_);
v_fold_2452_ = lean_uint64_xor(v___x_2449_, v___x_2451_);
v___x_2453_ = 16ULL;
v___x_2454_ = lean_uint64_shift_right(v_fold_2452_, v___x_2453_);
v___x_2455_ = lean_uint64_xor(v_fold_2452_, v___x_2454_);
v___x_2456_ = lean_uint64_to_usize(v___x_2455_);
v___x_2457_ = lean_usize_of_nat(v___x_2447_);
v___x_2458_ = ((size_t)1ULL);
v___x_2459_ = lean_usize_sub(v___x_2457_, v___x_2458_);
v___x_2460_ = lean_usize_land(v___x_2456_, v___x_2459_);
v___x_2461_ = lean_array_uget_borrowed(v_x_2439_, v___x_2460_);
lean_inc(v___x_2461_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 2, v___x_2461_);
v___x_2463_ = v___x_2445_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_key_2441_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_value_2442_);
lean_ctor_set(v_reuseFailAlloc_2466_, 2, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_array_uset(v_x_2439_, v___x_2460_, v___x_2463_);
v_x_2439_ = v___x_2464_;
v_x_2440_ = v_tail_2443_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(lean_object* v_i_2468_, lean_object* v_source_2469_, lean_object* v_target_2470_){
_start:
{
lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2471_ = lean_array_get_size(v_source_2469_);
v___x_2472_ = lean_nat_dec_lt(v_i_2468_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_dec_ref(v_source_2469_);
lean_dec(v_i_2468_);
return v_target_2470_;
}
else
{
lean_object* v_es_2473_; lean_object* v___x_2474_; lean_object* v_source_2475_; lean_object* v_target_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v_es_2473_ = lean_array_fget(v_source_2469_, v_i_2468_);
v___x_2474_ = lean_box(0);
v_source_2475_ = lean_array_fset(v_source_2469_, v_i_2468_, v___x_2474_);
v_target_2476_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_target_2470_, v_es_2473_);
v___x_2477_ = lean_unsigned_to_nat(1u);
v___x_2478_ = lean_nat_add(v_i_2468_, v___x_2477_);
lean_dec(v_i_2468_);
v_i_2468_ = v___x_2478_;
v_source_2469_ = v_source_2475_;
v_target_2470_ = v_target_2476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(lean_object* v_data_2480_){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v_nbuckets_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2481_ = lean_array_get_size(v_data_2480_);
v___x_2482_ = lean_unsigned_to_nat(2u);
v_nbuckets_2483_ = lean_nat_mul(v___x_2481_, v___x_2482_);
v___x_2484_ = lean_unsigned_to_nat(0u);
v___x_2485_ = lean_box(0);
v___x_2486_ = lean_mk_array(v_nbuckets_2483_, v___x_2485_);
v___x_2487_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v___x_2484_, v_data_2480_, v___x_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(lean_object* v_m_2488_, lean_object* v_a_2489_, lean_object* v_b_2490_){
_start:
{
lean_object* v_size_2491_; lean_object* v_buckets_2492_; lean_object* v___x_2493_; uint64_t v___x_2494_; uint64_t v___x_2495_; uint64_t v___x_2496_; uint64_t v___x_2497_; uint64_t v_fold_2498_; uint64_t v___x_2499_; uint64_t v___x_2500_; uint64_t v___x_2501_; size_t v___x_2502_; size_t v___x_2503_; size_t v___x_2504_; size_t v___x_2505_; size_t v___x_2506_; lean_object* v_bkt_2507_; uint8_t v___x_2508_; 
v_size_2491_ = lean_ctor_get(v_m_2488_, 0);
v_buckets_2492_ = lean_ctor_get(v_m_2488_, 1);
v___x_2493_ = lean_array_get_size(v_buckets_2492_);
v___x_2494_ = 7ULL;
v___x_2495_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2494_, v_a_2489_);
v___x_2496_ = 32ULL;
v___x_2497_ = lean_uint64_shift_right(v___x_2495_, v___x_2496_);
v_fold_2498_ = lean_uint64_xor(v___x_2495_, v___x_2497_);
v___x_2499_ = 16ULL;
v___x_2500_ = lean_uint64_shift_right(v_fold_2498_, v___x_2499_);
v___x_2501_ = lean_uint64_xor(v_fold_2498_, v___x_2500_);
v___x_2502_ = lean_uint64_to_usize(v___x_2501_);
v___x_2503_ = lean_usize_of_nat(v___x_2493_);
v___x_2504_ = ((size_t)1ULL);
v___x_2505_ = lean_usize_sub(v___x_2503_, v___x_2504_);
v___x_2506_ = lean_usize_land(v___x_2502_, v___x_2505_);
v_bkt_2507_ = lean_array_uget_borrowed(v_buckets_2492_, v___x_2506_);
v___x_2508_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2489_, v_bkt_2507_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2529_; 
lean_inc_ref(v_buckets_2492_);
lean_inc(v_size_2491_);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_m_2488_);
if (v_isSharedCheck_2529_ == 0)
{
lean_object* v_unused_2530_; lean_object* v_unused_2531_; 
v_unused_2530_ = lean_ctor_get(v_m_2488_, 1);
lean_dec(v_unused_2530_);
v_unused_2531_ = lean_ctor_get(v_m_2488_, 0);
lean_dec(v_unused_2531_);
v___x_2510_ = v_m_2488_;
v_isShared_2511_ = v_isSharedCheck_2529_;
goto v_resetjp_2509_;
}
else
{
lean_dec(v_m_2488_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2529_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2512_; lean_object* v_size_x27_2513_; lean_object* v___x_2514_; lean_object* v_buckets_x27_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v___x_2512_ = lean_unsigned_to_nat(1u);
v_size_x27_2513_ = lean_nat_add(v_size_2491_, v___x_2512_);
lean_dec(v_size_2491_);
lean_inc(v_bkt_2507_);
v___x_2514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2514_, 0, v_a_2489_);
lean_ctor_set(v___x_2514_, 1, v_b_2490_);
lean_ctor_set(v___x_2514_, 2, v_bkt_2507_);
v_buckets_x27_2515_ = lean_array_uset(v_buckets_2492_, v___x_2506_, v___x_2514_);
v___x_2516_ = lean_unsigned_to_nat(4u);
v___x_2517_ = lean_nat_mul(v_size_x27_2513_, v___x_2516_);
v___x_2518_ = lean_unsigned_to_nat(3u);
v___x_2519_ = lean_nat_div(v___x_2517_, v___x_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_array_get_size(v_buckets_x27_2515_);
v___x_2521_ = lean_nat_dec_le(v___x_2519_, v___x_2520_);
lean_dec(v___x_2519_);
if (v___x_2521_ == 0)
{
lean_object* v_val_2522_; lean_object* v___x_2524_; 
v_val_2522_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2515_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 1, v_val_2522_);
lean_ctor_set(v___x_2510_, 0, v_size_x27_2513_);
v___x_2524_ = v___x_2510_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_size_x27_2513_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_val_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
else
{
lean_object* v___x_2527_; 
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 1, v_buckets_x27_2515_);
lean_ctor_set(v___x_2510_, 0, v_size_x27_2513_);
v___x_2527_ = v___x_2510_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_size_x27_2513_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_buckets_x27_2515_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
else
{
lean_dec(v_b_2490_);
lean_dec(v_a_2489_);
return v_m_2488_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(lean_object* v_a_2532_, lean_object* v_b_2533_, lean_object* v_x_2534_){
_start:
{
if (lean_obj_tag(v_x_2534_) == 0)
{
lean_dec(v_b_2533_);
lean_dec(v_a_2532_);
return v_x_2534_;
}
else
{
lean_object* v_key_2535_; lean_object* v_value_2536_; lean_object* v_tail_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2549_; 
v_key_2535_ = lean_ctor_get(v_x_2534_, 0);
v_value_2536_ = lean_ctor_get(v_x_2534_, 1);
v_tail_2537_ = lean_ctor_get(v_x_2534_, 2);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_x_2534_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2539_ = v_x_2534_;
v_isShared_2540_ = v_isSharedCheck_2549_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_tail_2537_);
lean_inc(v_value_2536_);
lean_inc(v_key_2535_);
lean_dec(v_x_2534_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2549_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
uint8_t v___x_2541_; 
v___x_2541_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2535_, v_a_2532_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2544_; 
v___x_2542_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2532_, v_b_2533_, v_tail_2537_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 2, v___x_2542_);
v___x_2544_ = v___x_2539_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_key_2535_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_value_2536_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
else
{
lean_object* v___x_2547_; 
lean_dec(v_value_2536_);
lean_dec(v_key_2535_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 1, v_b_2533_);
lean_ctor_set(v___x_2539_, 0, v_a_2532_);
v___x_2547_ = v___x_2539_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2532_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_b_2533_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_tail_2537_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(lean_object* v_m_2550_, lean_object* v_a_2551_, lean_object* v_b_2552_){
_start:
{
lean_object* v_size_2553_; lean_object* v_buckets_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2598_; 
v_size_2553_ = lean_ctor_get(v_m_2550_, 0);
v_buckets_2554_ = lean_ctor_get(v_m_2550_, 1);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_m_2550_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2556_ = v_m_2550_;
v_isShared_2557_ = v_isSharedCheck_2598_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_buckets_2554_);
lean_inc(v_size_2553_);
lean_dec(v_m_2550_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2598_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; uint64_t v___x_2559_; uint64_t v___x_2560_; uint64_t v___x_2561_; uint64_t v___x_2562_; uint64_t v_fold_2563_; uint64_t v___x_2564_; uint64_t v___x_2565_; uint64_t v___x_2566_; size_t v___x_2567_; size_t v___x_2568_; size_t v___x_2569_; size_t v___x_2570_; size_t v___x_2571_; lean_object* v_bkt_2572_; uint8_t v___x_2573_; 
v___x_2558_ = lean_array_get_size(v_buckets_2554_);
v___x_2559_ = 7ULL;
v___x_2560_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2559_, v_a_2551_);
v___x_2561_ = 32ULL;
v___x_2562_ = lean_uint64_shift_right(v___x_2560_, v___x_2561_);
v_fold_2563_ = lean_uint64_xor(v___x_2560_, v___x_2562_);
v___x_2564_ = 16ULL;
v___x_2565_ = lean_uint64_shift_right(v_fold_2563_, v___x_2564_);
v___x_2566_ = lean_uint64_xor(v_fold_2563_, v___x_2565_);
v___x_2567_ = lean_uint64_to_usize(v___x_2566_);
v___x_2568_ = lean_usize_of_nat(v___x_2558_);
v___x_2569_ = ((size_t)1ULL);
v___x_2570_ = lean_usize_sub(v___x_2568_, v___x_2569_);
v___x_2571_ = lean_usize_land(v___x_2567_, v___x_2570_);
v_bkt_2572_ = lean_array_uget_borrowed(v_buckets_2554_, v___x_2571_);
v___x_2573_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2551_, v_bkt_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v_size_x27_2575_; lean_object* v___x_2576_; lean_object* v_buckets_x27_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2574_ = lean_unsigned_to_nat(1u);
v_size_x27_2575_ = lean_nat_add(v_size_2553_, v___x_2574_);
lean_dec(v_size_2553_);
lean_inc(v_bkt_2572_);
v___x_2576_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2576_, 0, v_a_2551_);
lean_ctor_set(v___x_2576_, 1, v_b_2552_);
lean_ctor_set(v___x_2576_, 2, v_bkt_2572_);
v_buckets_x27_2577_ = lean_array_uset(v_buckets_2554_, v___x_2571_, v___x_2576_);
v___x_2578_ = lean_unsigned_to_nat(4u);
v___x_2579_ = lean_nat_mul(v_size_x27_2575_, v___x_2578_);
v___x_2580_ = lean_unsigned_to_nat(3u);
v___x_2581_ = lean_nat_div(v___x_2579_, v___x_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_array_get_size(v_buckets_x27_2577_);
v___x_2583_ = lean_nat_dec_le(v___x_2581_, v___x_2582_);
lean_dec(v___x_2581_);
if (v___x_2583_ == 0)
{
lean_object* v_val_2584_; lean_object* v___x_2586_; 
v_val_2584_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2577_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 1, v_val_2584_);
lean_ctor_set(v___x_2556_, 0, v_size_x27_2575_);
v___x_2586_ = v___x_2556_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_size_x27_2575_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_val_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
else
{
lean_object* v___x_2589_; 
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 1, v_buckets_x27_2577_);
lean_ctor_set(v___x_2556_, 0, v_size_x27_2575_);
v___x_2589_ = v___x_2556_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_size_x27_2575_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_buckets_x27_2577_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
else
{
lean_object* v___x_2591_; lean_object* v_buckets_x27_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
lean_inc(v_bkt_2572_);
v___x_2591_ = lean_box(0);
v_buckets_x27_2592_ = lean_array_uset(v_buckets_2554_, v___x_2571_, v___x_2591_);
v___x_2593_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2551_, v_b_2552_, v_bkt_2572_);
v___x_2594_ = lean_array_uset(v_buckets_x27_2592_, v___x_2571_, v___x_2593_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 1, v___x_2594_);
v___x_2596_ = v___x_2556_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_size_2553_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(lean_object* v_p_2599_, lean_object* v_x_2600_){
_start:
{
lean_object* v_coeffs_2601_; lean_object* v_constraint_2602_; lean_object* v_justification_2603_; uint8_t v___x_2604_; 
v_coeffs_2601_ = lean_ctor_get(v_x_2600_, 0);
lean_inc(v_coeffs_2601_);
v_constraint_2602_ = lean_ctor_get(v_x_2600_, 1);
lean_inc_ref(v_constraint_2602_);
v_justification_2603_ = lean_ctor_get(v_x_2600_, 2);
v___x_2604_ = l_Lean_Omega_Constraint_isImpossible(v_constraint_2602_);
if (v___x_2604_ == 0)
{
lean_object* v_assumptions_2605_; lean_object* v_numVars_2606_; lean_object* v_constraints_2607_; lean_object* v_equalities_2608_; lean_object* v_eliminations_2609_; uint8_t v_possible_2610_; lean_object* v_proveFalse_x3f_2611_; lean_object* v_explanation_x3f_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2630_; 
v_assumptions_2605_ = lean_ctor_get(v_p_2599_, 0);
v_numVars_2606_ = lean_ctor_get(v_p_2599_, 1);
v_constraints_2607_ = lean_ctor_get(v_p_2599_, 2);
v_equalities_2608_ = lean_ctor_get(v_p_2599_, 3);
v_eliminations_2609_ = lean_ctor_get(v_p_2599_, 4);
v_possible_2610_ = lean_ctor_get_uint8(v_p_2599_, sizeof(void*)*7);
v_proveFalse_x3f_2611_ = lean_ctor_get(v_p_2599_, 5);
v_explanation_x3f_2612_ = lean_ctor_get(v_p_2599_, 6);
v_isSharedCheck_2630_ = !lean_is_exclusive(v_p_2599_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2614_ = v_p_2599_;
v_isShared_2615_ = v_isSharedCheck_2630_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_explanation_x3f_2612_);
lean_inc(v_proveFalse_x3f_2611_);
lean_inc(v_eliminations_2609_);
lean_inc(v_equalities_2608_);
lean_inc(v_constraints_2607_);
lean_inc(v_numVars_2606_);
lean_inc(v_assumptions_2605_);
lean_dec(v_p_2599_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2630_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___y_2617_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2628_ = l_List_lengthTR___redArg(v_coeffs_2601_);
v___x_2629_ = lean_nat_dec_le(v_numVars_2606_, v___x_2628_);
if (v___x_2629_ == 0)
{
lean_dec(v___x_2628_);
v___y_2617_ = v_numVars_2606_;
goto v___jp_2616_;
}
else
{
lean_dec(v_numVars_2606_);
v___y_2617_ = v___x_2628_;
goto v___jp_2616_;
}
v___jp_2616_:
{
lean_object* v___x_2618_; uint8_t v___x_2619_; 
lean_inc(v_coeffs_2601_);
v___x_2618_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_constraints_2607_, v_coeffs_2601_, v_x_2600_);
v___x_2619_ = l_Lean_Omega_Constraint_isExact(v_constraint_2602_);
lean_dec_ref(v_constraint_2602_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2621_; 
lean_dec(v_coeffs_2601_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 2, v___x_2618_);
lean_ctor_set(v___x_2614_, 1, v___y_2617_);
v___x_2621_ = v___x_2614_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_assumptions_2605_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v___y_2617_);
lean_ctor_set(v_reuseFailAlloc_2622_, 2, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2622_, 3, v_equalities_2608_);
lean_ctor_set(v_reuseFailAlloc_2622_, 4, v_eliminations_2609_);
lean_ctor_set(v_reuseFailAlloc_2622_, 5, v_proveFalse_x3f_2611_);
lean_ctor_set(v_reuseFailAlloc_2622_, 6, v_explanation_x3f_2612_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, sizeof(void*)*7, v_possible_2610_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2623_ = lean_box(0);
v___x_2624_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_equalities_2608_, v_coeffs_2601_, v___x_2623_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 3, v___x_2624_);
lean_ctor_set(v___x_2614_, 2, v___x_2618_);
lean_ctor_set(v___x_2614_, 1, v___y_2617_);
v___x_2626_ = v___x_2614_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_assumptions_2605_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v___y_2617_);
lean_ctor_set(v_reuseFailAlloc_2627_, 2, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2627_, 3, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2627_, 4, v_eliminations_2609_);
lean_ctor_set(v_reuseFailAlloc_2627_, 5, v_proveFalse_x3f_2611_);
lean_ctor_set(v_reuseFailAlloc_2627_, 6, v_explanation_x3f_2612_);
lean_ctor_set_uint8(v_reuseFailAlloc_2627_, sizeof(void*)*7, v_possible_2610_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
else
{
lean_object* v_assumptions_2631_; lean_object* v_numVars_2632_; lean_object* v_constraints_2633_; lean_object* v_equalities_2634_; lean_object* v_eliminations_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2647_; 
lean_inc_ref(v_justification_2603_);
lean_dec_ref(v_x_2600_);
v_assumptions_2631_ = lean_ctor_get(v_p_2599_, 0);
v_numVars_2632_ = lean_ctor_get(v_p_2599_, 1);
v_constraints_2633_ = lean_ctor_get(v_p_2599_, 2);
v_equalities_2634_ = lean_ctor_get(v_p_2599_, 3);
v_eliminations_2635_ = lean_ctor_get(v_p_2599_, 4);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_p_2599_);
if (v_isSharedCheck_2647_ == 0)
{
lean_object* v_unused_2648_; lean_object* v_unused_2649_; 
v_unused_2648_ = lean_ctor_get(v_p_2599_, 6);
lean_dec(v_unused_2648_);
v_unused_2649_ = lean_ctor_get(v_p_2599_, 5);
lean_dec(v_unused_2649_);
v___x_2637_ = v_p_2599_;
v_isShared_2638_ = v_isSharedCheck_2647_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_eliminations_2635_);
lean_inc(v_equalities_2634_);
lean_inc(v_constraints_2633_);
lean_inc(v_numVars_2632_);
lean_inc(v_assumptions_2631_);
lean_dec(v_p_2599_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2647_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___f_2639_; uint8_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
lean_inc_ref(v_justification_2603_);
lean_inc(v_coeffs_2601_);
lean_inc_ref(v_constraint_2602_);
v___f_2639_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0), 4, 3);
lean_closure_set(v___f_2639_, 0, v_constraint_2602_);
lean_closure_set(v___f_2639_, 1, v_coeffs_2601_);
lean_closure_set(v___f_2639_, 2, v_justification_2603_);
v___x_2640_ = 0;
lean_inc_ref(v_assumptions_2631_);
v___x_2641_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed), 14, 4);
lean_closure_set(v___x_2641_, 0, v_constraint_2602_);
lean_closure_set(v___x_2641_, 1, v_coeffs_2601_);
lean_closure_set(v___x_2641_, 2, v_justification_2603_);
lean_closure_set(v___x_2641_, 3, v_assumptions_2631_);
v___x_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
v___x_2643_ = lean_mk_thunk(v___f_2639_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 6, v___x_2643_);
lean_ctor_set(v___x_2637_, 5, v___x_2642_);
v___x_2645_ = v___x_2637_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_assumptions_2631_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_numVars_2632_);
lean_ctor_set(v_reuseFailAlloc_2646_, 2, v_constraints_2633_);
lean_ctor_set(v_reuseFailAlloc_2646_, 3, v_equalities_2634_);
lean_ctor_set(v_reuseFailAlloc_2646_, 4, v_eliminations_2635_);
lean_ctor_set(v_reuseFailAlloc_2646_, 5, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2646_, 6, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_ctor_set_uint8(v___x_2645_, sizeof(void*)*7, v___x_2640_);
return v___x_2645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0(lean_object* v_00_u03b2_2650_, lean_object* v_m_2651_, lean_object* v_a_2652_, lean_object* v_b_2653_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_m_2651_, v_a_2652_, v_b_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1(lean_object* v_00_u03b2_2655_, lean_object* v_m_2656_, lean_object* v_a_2657_, lean_object* v_b_2658_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_m_2656_, v_a_2657_, v_b_2658_);
return v___x_2659_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_object* v_00_u03b2_2660_, lean_object* v_a_2661_, lean_object* v_x_2662_){
_start:
{
uint8_t v___x_2663_; 
v___x_2663_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2661_, v_x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2664_, lean_object* v_a_2665_, lean_object* v_x_2666_){
_start:
{
uint8_t v_res_2667_; lean_object* v_r_2668_; 
v_res_2667_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(v_00_u03b2_2664_, v_a_2665_, v_x_2666_);
lean_dec(v_x_2666_);
lean_dec(v_a_2665_);
v_r_2668_ = lean_box(v_res_2667_);
return v_r_2668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2(lean_object* v_00_u03b2_2669_, lean_object* v_data_2670_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_data_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3(lean_object* v_00_u03b2_2672_, lean_object* v_a_2673_, lean_object* v_b_2674_, lean_object* v_x_2675_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2673_, v_b_2674_, v_x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2677_, lean_object* v_i_2678_, lean_object* v_source_2679_, lean_object* v_target_2680_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v_i_2678_, v_source_2679_, v_target_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2682_, lean_object* v_x_2683_, lean_object* v_x_2684_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_x_2683_, v_x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(lean_object* v_a_2686_, lean_object* v_x_2687_){
_start:
{
if (lean_obj_tag(v_x_2687_) == 0)
{
lean_object* v___x_2688_; 
v___x_2688_ = lean_box(0);
return v___x_2688_;
}
else
{
lean_object* v_key_2689_; lean_object* v_value_2690_; lean_object* v_tail_2691_; uint8_t v___x_2692_; 
v_key_2689_ = lean_ctor_get(v_x_2687_, 0);
v_value_2690_ = lean_ctor_get(v_x_2687_, 1);
v_tail_2691_ = lean_ctor_get(v_x_2687_, 2);
v___x_2692_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2689_, v_a_2686_);
if (v___x_2692_ == 0)
{
v_x_2687_ = v_tail_2691_;
goto _start;
}
else
{
lean_object* v___x_2694_; 
lean_inc(v_value_2690_);
v___x_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2694_, 0, v_value_2690_);
return v___x_2694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg___boxed(lean_object* v_a_2695_, lean_object* v_x_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2695_, v_x_2696_);
lean_dec(v_x_2696_);
lean_dec(v_a_2695_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(lean_object* v_m_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v_buckets_2700_; lean_object* v___x_2701_; uint64_t v___x_2702_; uint64_t v___x_2703_; uint64_t v___x_2704_; uint64_t v___x_2705_; uint64_t v_fold_2706_; uint64_t v___x_2707_; uint64_t v___x_2708_; uint64_t v___x_2709_; size_t v___x_2710_; size_t v___x_2711_; size_t v___x_2712_; size_t v___x_2713_; size_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v_buckets_2700_ = lean_ctor_get(v_m_2698_, 1);
v___x_2701_ = lean_array_get_size(v_buckets_2700_);
v___x_2702_ = 7ULL;
v___x_2703_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2702_, v_a_2699_);
v___x_2704_ = 32ULL;
v___x_2705_ = lean_uint64_shift_right(v___x_2703_, v___x_2704_);
v_fold_2706_ = lean_uint64_xor(v___x_2703_, v___x_2705_);
v___x_2707_ = 16ULL;
v___x_2708_ = lean_uint64_shift_right(v_fold_2706_, v___x_2707_);
v___x_2709_ = lean_uint64_xor(v_fold_2706_, v___x_2708_);
v___x_2710_ = lean_uint64_to_usize(v___x_2709_);
v___x_2711_ = lean_usize_of_nat(v___x_2701_);
v___x_2712_ = ((size_t)1ULL);
v___x_2713_ = lean_usize_sub(v___x_2711_, v___x_2712_);
v___x_2714_ = lean_usize_land(v___x_2710_, v___x_2713_);
v___x_2715_ = lean_array_uget_borrowed(v_buckets_2700_, v___x_2714_);
v___x_2716_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2699_, v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg___boxed(lean_object* v_m_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2717_, v_a_2718_);
lean_dec(v_a_2718_);
lean_dec_ref(v_m_2717_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addConstraint(lean_object* v_p_2720_, lean_object* v_x_2721_){
_start:
{
uint8_t v_possible_2722_; 
v_possible_2722_ = lean_ctor_get_uint8(v_p_2720_, sizeof(void*)*7);
if (v_possible_2722_ == 0)
{
lean_dec_ref(v_x_2721_);
return v_p_2720_;
}
else
{
lean_object* v_coeffs_2723_; lean_object* v_constraint_2724_; lean_object* v_justification_2725_; lean_object* v_constraints_2726_; lean_object* v___x_2727_; 
v_coeffs_2723_ = lean_ctor_get(v_x_2721_, 0);
v_constraint_2724_ = lean_ctor_get(v_x_2721_, 1);
v_justification_2725_ = lean_ctor_get(v_x_2721_, 2);
v_constraints_2726_ = lean_ctor_get(v_p_2720_, 2);
v___x_2727_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2726_, v_coeffs_2723_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_lowerBound_2728_; 
v_lowerBound_2728_ = lean_ctor_get(v_constraint_2724_, 0);
if (lean_obj_tag(v_lowerBound_2728_) == 0)
{
lean_object* v_upperBound_2729_; 
v_upperBound_2729_ = lean_ctor_get(v_constraint_2724_, 1);
if (lean_obj_tag(v_upperBound_2729_) == 0)
{
lean_dec_ref(v_x_2721_);
return v_p_2720_;
}
else
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2720_, v_x_2721_);
return v___x_2730_;
}
}
else
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2720_, v_x_2721_);
return v___x_2731_;
}
}
else
{
lean_object* v_val_2732_; lean_object* v_coeffs_2733_; lean_object* v_constraint_2734_; lean_object* v_justification_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2750_; 
v_val_2732_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_val_2732_);
lean_dec_ref(v___x_2727_);
v_coeffs_2733_ = lean_ctor_get(v_val_2732_, 0);
v_constraint_2734_ = lean_ctor_get(v_val_2732_, 1);
v_justification_2735_ = lean_ctor_get(v_val_2732_, 2);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_val_2732_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2737_ = v_val_2732_;
v_isShared_2738_ = v_isSharedCheck_2750_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_justification_2735_);
lean_inc(v_constraint_2734_);
lean_inc(v_coeffs_2733_);
lean_dec(v_val_2732_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2750_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc(v_coeffs_2723_);
v___x_2740_ = l_instDecidableEqList___redArg(v___x_2739_, v_coeffs_2723_, v_coeffs_2733_);
if (v___x_2740_ == 0)
{
lean_del_object(v___x_2737_);
lean_dec_ref(v_justification_2735_);
lean_dec_ref(v_constraint_2734_);
lean_dec_ref(v_x_2721_);
return v_p_2720_;
}
else
{
lean_object* v_r_2741_; uint8_t v___x_2742_; 
lean_inc_ref_n(v_constraint_2734_, 2);
lean_inc_ref(v_constraint_2724_);
v_r_2741_ = l_Lean_Omega_Constraint_combine(v_constraint_2724_, v_constraint_2734_);
lean_inc_ref(v_r_2741_);
v___x_2742_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2741_, v_constraint_2734_);
if (v___x_2742_ == 0)
{
uint8_t v___x_2743_; 
lean_inc_ref(v_constraint_2724_);
lean_inc_ref(v_r_2741_);
v___x_2743_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2741_, v_constraint_2724_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2746_; 
lean_inc_ref(v_justification_2725_);
lean_inc_ref(v_constraint_2724_);
lean_inc_n(v_coeffs_2723_, 2);
lean_dec_ref(v_x_2721_);
v___x_2744_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_2744_, 0, v_constraint_2724_);
lean_ctor_set(v___x_2744_, 1, v_constraint_2734_);
lean_ctor_set(v___x_2744_, 2, v_coeffs_2723_);
lean_ctor_set(v___x_2744_, 3, v_justification_2725_);
lean_ctor_set(v___x_2744_, 4, v_justification_2735_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 2, v___x_2744_);
lean_ctor_set(v___x_2737_, 1, v_r_2741_);
lean_ctor_set(v___x_2737_, 0, v_coeffs_2723_);
v___x_2746_ = v___x_2737_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_coeffs_2723_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_r_2741_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v___x_2744_);
v___x_2746_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2720_, v___x_2746_);
return v___x_2747_;
}
}
else
{
lean_object* v___x_2749_; 
lean_dec_ref(v_r_2741_);
lean_del_object(v___x_2737_);
lean_dec_ref(v_justification_2735_);
lean_dec_ref(v_constraint_2734_);
v___x_2749_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2720_, v_x_2721_);
return v___x_2749_;
}
}
else
{
lean_dec_ref(v_r_2741_);
lean_del_object(v___x_2737_);
lean_dec_ref(v_justification_2735_);
lean_dec_ref(v_constraint_2734_);
lean_dec_ref(v_x_2721_);
return v_p_2720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(lean_object* v_00_u03b2_2751_, lean_object* v_m_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2752_, v_a_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___boxed(lean_object* v_00_u03b2_2755_, lean_object* v_m_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(v_00_u03b2_2755_, v_m_2756_, v_a_2757_);
lean_dec(v_a_2757_);
lean_dec_ref(v_m_2756_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(lean_object* v_00_u03b2_2759_, lean_object* v_a_2760_, lean_object* v_x_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2760_, v_x_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2763_, lean_object* v_a_2764_, lean_object* v_x_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(v_00_u03b2_2763_, v_a_2764_, v_x_2765_);
lean_dec(v_x_2765_);
lean_dec(v_a_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(lean_object* v_x_2767_, lean_object* v_x_2768_){
_start:
{
if (lean_obj_tag(v_x_2768_) == 0)
{
return v_x_2767_;
}
else
{
if (lean_obj_tag(v_x_2767_) == 0)
{
lean_object* v_key_2769_; lean_object* v_tail_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_key_2769_ = lean_ctor_get(v_x_2768_, 0);
lean_inc_n(v_key_2769_, 2);
v_tail_2770_ = lean_ctor_get(v_x_2768_, 2);
lean_inc(v_tail_2770_);
lean_dec_ref(v_x_2768_);
v___x_2771_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2769_);
v___x_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2772_, 0, v_key_2769_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
v___x_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
v_x_2767_ = v___x_2773_;
v_x_2768_ = v_tail_2770_;
goto _start;
}
else
{
lean_object* v_val_2775_; lean_object* v_key_2776_; lean_object* v_tail_2777_; lean_object* v_fst_2778_; lean_object* v_snd_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2807_; 
v_val_2775_ = lean_ctor_get(v_x_2767_, 0);
lean_inc(v_val_2775_);
v_key_2776_ = lean_ctor_get(v_x_2768_, 0);
lean_inc(v_key_2776_);
v_tail_2777_ = lean_ctor_get(v_x_2768_, 2);
lean_inc(v_tail_2777_);
lean_dec_ref(v_x_2768_);
v_fst_2778_ = lean_ctor_get(v_val_2775_, 0);
v_snd_2779_ = lean_ctor_get(v_val_2775_, 1);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_val_2775_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2781_ = v_val_2775_;
v_isShared_2782_ = v_isSharedCheck_2807_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_snd_2779_);
lean_inc(v_fst_2778_);
lean_dec(v_val_2775_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2807_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2783_ = lean_unsigned_to_nat(2u);
v___x_2784_ = lean_nat_dec_le(v___x_2783_, v_snd_2779_);
if (v___x_2784_ == 0)
{
lean_del_object(v___x_2781_);
lean_dec(v_snd_2779_);
lean_dec(v_fst_2778_);
lean_dec(v_key_2776_);
v_x_2768_ = v_tail_2777_;
goto _start;
}
else
{
lean_object* v_m_x27_2786_; uint8_t v___y_2788_; uint8_t v___x_2802_; 
lean_inc(v_key_2776_);
v_m_x27_2786_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2776_);
v___x_2802_ = lean_nat_dec_lt(v_m_x27_2786_, v_snd_2779_);
if (v___x_2802_ == 0)
{
uint8_t v___x_2803_; 
v___x_2803_ = lean_nat_dec_eq(v_m_x27_2786_, v_snd_2779_);
lean_dec(v_snd_2779_);
if (v___x_2803_ == 0)
{
lean_dec(v_fst_2778_);
v___y_2788_ = v___x_2803_;
goto v___jp_2787_;
}
else
{
lean_object* v___x_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
lean_inc(v_key_2776_);
v___x_2804_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_key_2776_);
v___x_2805_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_fst_2778_);
v___x_2806_ = lean_nat_dec_lt(v___x_2804_, v___x_2805_);
lean_dec(v___x_2805_);
lean_dec(v___x_2804_);
v___y_2788_ = v___x_2806_;
goto v___jp_2787_;
}
}
else
{
lean_dec(v_snd_2779_);
lean_dec(v_fst_2778_);
v___y_2788_ = v___x_2802_;
goto v___jp_2787_;
}
v___jp_2787_:
{
if (v___y_2788_ == 0)
{
lean_dec(v_m_x27_2786_);
lean_del_object(v___x_2781_);
lean_dec(v_key_2776_);
v_x_2768_ = v_tail_2777_;
goto _start;
}
else
{
lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2800_; 
v_isSharedCheck_2800_ = !lean_is_exclusive(v_x_2767_);
if (v_isSharedCheck_2800_ == 0)
{
lean_object* v_unused_2801_; 
v_unused_2801_ = lean_ctor_get(v_x_2767_, 0);
lean_dec(v_unused_2801_);
v___x_2791_ = v_x_2767_;
v_isShared_2792_ = v_isSharedCheck_2800_;
goto v_resetjp_2790_;
}
else
{
lean_dec(v_x_2767_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2800_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 1, v_m_x27_2786_);
lean_ctor_set(v___x_2781_, 0, v_key_2776_);
v___x_2794_ = v___x_2781_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_key_2776_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_m_x27_2786_);
v___x_2794_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2796_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2794_);
v___x_2796_ = v___x_2791_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
v_x_2767_ = v___x_2796_;
v_x_2768_ = v_tail_2777_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(lean_object* v_as_2808_, size_t v_i_2809_, size_t v_stop_2810_, lean_object* v_b_2811_){
_start:
{
uint8_t v___x_2812_; 
v___x_2812_ = lean_usize_dec_eq(v_i_2809_, v_stop_2810_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; size_t v___x_2815_; size_t v___x_2816_; 
v___x_2813_ = lean_array_uget_borrowed(v_as_2808_, v_i_2809_);
lean_inc(v___x_2813_);
v___x_2814_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(v_b_2811_, v___x_2813_);
v___x_2815_ = ((size_t)1ULL);
v___x_2816_ = lean_usize_add(v_i_2809_, v___x_2815_);
v_i_2809_ = v___x_2816_;
v_b_2811_ = v___x_2814_;
goto _start;
}
else
{
return v_b_2811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1___boxed(lean_object* v_as_2818_, lean_object* v_i_2819_, lean_object* v_stop_2820_, lean_object* v_b_2821_){
_start:
{
size_t v_i_boxed_2822_; size_t v_stop_boxed_2823_; lean_object* v_res_2824_; 
v_i_boxed_2822_ = lean_unbox_usize(v_i_2819_);
lean_dec(v_i_2819_);
v_stop_boxed_2823_ = lean_unbox_usize(v_stop_2820_);
lean_dec(v_stop_2820_);
v_res_2824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_as_2818_, v_i_boxed_2822_, v_stop_boxed_2823_, v_b_2821_);
lean_dec_ref(v_as_2818_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality(lean_object* v_p_2825_){
_start:
{
lean_object* v_equalities_2826_; lean_object* v_buckets_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v_equalities_2826_ = lean_ctor_get(v_p_2825_, 3);
v_buckets_2827_ = lean_ctor_get(v_equalities_2826_, 1);
v___x_2828_ = lean_box(0);
v___x_2829_ = lean_unsigned_to_nat(0u);
v___x_2830_ = lean_array_get_size(v_buckets_2827_);
v___x_2831_ = lean_nat_dec_lt(v___x_2829_, v___x_2830_);
if (v___x_2831_ == 0)
{
return v___x_2828_;
}
else
{
uint8_t v___x_2832_; 
v___x_2832_ = lean_nat_dec_le(v___x_2830_, v___x_2830_);
if (v___x_2832_ == 0)
{
if (v___x_2831_ == 0)
{
return v___x_2828_;
}
else
{
size_t v___x_2833_; size_t v___x_2834_; lean_object* v___x_2835_; 
v___x_2833_ = ((size_t)0ULL);
v___x_2834_ = lean_usize_of_nat(v___x_2830_);
v___x_2835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2827_, v___x_2833_, v___x_2834_, v___x_2828_);
return v___x_2835_;
}
}
else
{
size_t v___x_2836_; size_t v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = ((size_t)0ULL);
v___x_2837_ = lean_usize_of_nat(v___x_2830_);
v___x_2838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2827_, v___x_2836_, v___x_2837_, v___x_2828_);
return v___x_2838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality___boxed(lean_object* v_p_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_2839_);
lean_dec_ref(v_p_2839_);
return v_res_2840_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = lean_unsigned_to_nat(1u);
v___x_2842_ = lean_nat_to_int(v___x_2841_);
return v___x_2842_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2844_ = lean_int_neg(v___x_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(lean_object* v_as_2845_, size_t v_i_2846_, size_t v_stop_2847_, lean_object* v_b_2848_){
_start:
{
uint8_t v___x_2849_; 
v___x_2849_ = lean_usize_dec_eq(v_i_2846_, v_stop_2847_);
if (v___x_2849_ == 0)
{
size_t v___x_2850_; size_t v___x_2851_; lean_object* v___x_2852_; lean_object* v_snd_2853_; lean_object* v_fst_2854_; lean_object* v_fst_2855_; lean_object* v_snd_2856_; lean_object* v_coeffs_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; uint8_t v___x_2860_; 
v___x_2850_ = ((size_t)1ULL);
v___x_2851_ = lean_usize_sub(v_i_2846_, v___x_2850_);
v___x_2852_ = lean_array_uget_borrowed(v_as_2845_, v___x_2851_);
v_snd_2853_ = lean_ctor_get(v___x_2852_, 1);
v_fst_2854_ = lean_ctor_get(v___x_2852_, 0);
v_fst_2855_ = lean_ctor_get(v_snd_2853_, 0);
v_snd_2856_ = lean_ctor_get(v_snd_2853_, 1);
v_coeffs_2857_ = lean_ctor_get(v_b_2848_, 0);
lean_inc(v_fst_2855_);
v___x_2858_ = l_Lean_Omega_IntList_get(v_coeffs_2857_, v_fst_2855_);
v___x_2859_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2860_ = lean_int_dec_eq(v___x_2858_, v___x_2859_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2861_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2862_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2863_ = lean_int_mul(v___x_2862_, v_snd_2856_);
v___x_2864_ = lean_int_mul(v___x_2863_, v___x_2858_);
lean_dec(v___x_2858_);
lean_dec(v___x_2863_);
lean_inc(v_fst_2854_);
v___x_2865_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v___x_2864_, v_fst_2854_, v___x_2861_, v_b_2848_);
v_i_2846_ = v___x_2851_;
v_b_2848_ = v___x_2865_;
goto _start;
}
else
{
lean_dec(v___x_2858_);
v_i_2846_ = v___x_2851_;
goto _start;
}
}
else
{
return v_b_2848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___boxed(lean_object* v_as_2868_, lean_object* v_i_2869_, lean_object* v_stop_2870_, lean_object* v_b_2871_){
_start:
{
size_t v_i_boxed_2872_; size_t v_stop_boxed_2873_; lean_object* v_res_2874_; 
v_i_boxed_2872_ = lean_unbox_usize(v_i_2869_);
lean_dec(v_i_2869_);
v_stop_boxed_2873_ = lean_unbox_usize(v_stop_2870_);
lean_dec(v_stop_2870_);
v_res_2874_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v_as_2868_, v_i_boxed_2872_, v_stop_boxed_2873_, v_b_2871_);
lean_dec_ref(v_as_2868_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(lean_object* v_init_2875_, lean_object* v_l_2876_){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2877_ = lean_array_mk(v_l_2876_);
v___x_2878_ = lean_array_get_size(v___x_2877_);
v___x_2879_ = lean_unsigned_to_nat(0u);
v___x_2880_ = lean_nat_dec_lt(v___x_2879_, v___x_2878_);
if (v___x_2880_ == 0)
{
lean_dec_ref(v___x_2877_);
return v_init_2875_;
}
else
{
size_t v___x_2881_; size_t v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = lean_usize_of_nat(v___x_2878_);
v___x_2882_ = ((size_t)0ULL);
v___x_2883_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v___x_2877_, v___x_2881_, v___x_2882_, v_init_2875_);
lean_dec_ref(v___x_2877_);
return v___x_2883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(lean_object* v_p_2884_, lean_object* v_f_2885_){
_start:
{
lean_object* v_eliminations_2886_; lean_object* v___x_2887_; 
v_eliminations_2886_ = lean_ctor_get(v_p_2884_, 4);
lean_inc(v_eliminations_2886_);
lean_dec_ref(v_p_2884_);
v___x_2887_ = l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(v_f_2885_, v_eliminations_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__0(lean_object* v_x_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
return v___x_2889_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1(lean_object* v_x_2890_){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; uint8_t v___x_2893_; 
v___x_2891_ = lean_nat_abs(v_x_2890_);
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = lean_nat_dec_eq(v___x_2891_, v___x_2892_);
lean_dec(v___x_2891_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1___boxed(lean_object* v_x_2894_){
_start:
{
uint8_t v_res_2895_; lean_object* v_r_2896_; 
v_res_2895_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1(v_x_2894_);
lean_dec(v_x_2894_);
v_r_2896_ = lean_box(v_res_2895_);
return v_r_2896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(lean_object* v___y_2897_, lean_object* v_sign_2898_, lean_object* v_val_2899_, lean_object* v_x_2900_, lean_object* v_x_2901_){
_start:
{
if (lean_obj_tag(v_x_2901_) == 0)
{
lean_dec_ref(v_val_2899_);
lean_dec(v___y_2897_);
return v_x_2900_;
}
else
{
lean_object* v_key_2902_; lean_object* v_value_2903_; lean_object* v_tail_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v_key_2902_ = lean_ctor_get(v_x_2901_, 0);
lean_inc(v_key_2902_);
v_value_2903_ = lean_ctor_get(v_x_2901_, 1);
lean_inc(v_value_2903_);
v_tail_2904_ = lean_ctor_get(v_x_2901_, 2);
lean_inc(v_tail_2904_);
lean_dec_ref(v_x_2901_);
lean_inc(v___y_2897_);
v___x_2905_ = l_Lean_Omega_IntList_get(v_key_2902_, v___y_2897_);
lean_dec(v_key_2902_);
v___x_2906_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2907_ = lean_int_dec_eq(v___x_2905_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v_k_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2908_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2909_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2910_ = lean_int_mul(v___x_2909_, v_sign_2898_);
v_k_2911_ = lean_int_mul(v___x_2910_, v___x_2905_);
lean_dec(v___x_2905_);
lean_dec(v___x_2910_);
lean_inc_ref(v_val_2899_);
v___x_2912_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_k_2911_, v_val_2899_, v___x_2908_, v_value_2903_);
v___x_2913_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_2912_);
v___x_2914_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2900_, v___x_2913_);
v_x_2900_ = v___x_2914_;
v_x_2901_ = v_tail_2904_;
goto _start;
}
else
{
lean_object* v___x_2916_; 
lean_dec(v___x_2905_);
v___x_2916_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2900_, v_value_2903_);
v_x_2900_ = v___x_2916_;
v_x_2901_ = v_tail_2904_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0___boxed(lean_object* v___y_2918_, lean_object* v_sign_2919_, lean_object* v_val_2920_, lean_object* v_x_2921_, lean_object* v_x_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2918_, v_sign_2919_, v_val_2920_, v_x_2921_, v_x_2922_);
lean_dec(v_sign_2919_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object* v___y_2924_, lean_object* v_sign_2925_, lean_object* v_val_2926_, lean_object* v_as_2927_, size_t v_i_2928_, size_t v_stop_2929_, lean_object* v_b_2930_){
_start:
{
uint8_t v___x_2931_; 
v___x_2931_ = lean_usize_dec_eq(v_i_2928_, v_stop_2929_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2933_; size_t v___x_2934_; size_t v___x_2935_; 
v___x_2932_ = lean_array_uget_borrowed(v_as_2927_, v_i_2928_);
lean_inc(v___x_2932_);
lean_inc_ref(v_val_2926_);
lean_inc(v___y_2924_);
v___x_2933_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2924_, v_sign_2925_, v_val_2926_, v_b_2930_, v___x_2932_);
v___x_2934_ = ((size_t)1ULL);
v___x_2935_ = lean_usize_add(v_i_2928_, v___x_2934_);
v_i_2928_ = v___x_2935_;
v_b_2930_ = v___x_2933_;
goto _start;
}
else
{
lean_dec_ref(v_val_2926_);
lean_dec(v___y_2924_);
return v_b_2930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1___boxed(lean_object* v___y_2937_, lean_object* v_sign_2938_, lean_object* v_val_2939_, lean_object* v_as_2940_, lean_object* v_i_2941_, lean_object* v_stop_2942_, lean_object* v_b_2943_){
_start:
{
size_t v_i_boxed_2944_; size_t v_stop_boxed_2945_; lean_object* v_res_2946_; 
v_i_boxed_2944_ = lean_unbox_usize(v_i_2941_);
lean_dec(v_i_2941_);
v_stop_boxed_2945_ = lean_unbox_usize(v_stop_2942_);
lean_dec(v_stop_2942_);
v_res_2946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2937_, v_sign_2938_, v_val_2939_, v_as_2940_, v_i_boxed_2944_, v_stop_boxed_2945_, v_b_2943_);
lean_dec_ref(v_as_2940_);
lean_dec(v_sign_2938_);
return v_res_2946_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_box(0);
v___x_2949_ = lean_unsigned_to_nat(16u);
v___x_2950_ = lean_mk_array(v___x_2949_, v___x_2948_);
return v___x_2950_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1);
v___x_2952_ = lean_unsigned_to_nat(0u);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
lean_ctor_set(v___x_2953_, 1, v___x_2951_);
return v___x_2953_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3(void){
_start:
{
lean_object* v___f_2954_; lean_object* v___x_2955_; 
v___f_2954_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0));
v___x_2955_ = lean_mk_thunk(v___f_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(lean_object* v_p_2957_, lean_object* v_c_2958_){
_start:
{
lean_object* v___y_2960_; lean_object* v___f_3007_; lean_object* v___x_3008_; 
v___f_3007_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__4));
lean_inc(v_c_2958_);
v___x_3008_ = l_List_findIdx_x3f___redArg(v___f_3007_, v_c_2958_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_unsigned_to_nat(0u);
v___y_2960_ = v___x_3009_;
goto v___jp_2959_;
}
else
{
lean_object* v_val_3010_; 
v_val_3010_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_val_3010_);
lean_dec_ref(v___x_3008_);
v___y_2960_ = v_val_3010_;
goto v___jp_2959_;
}
v___jp_2959_:
{
lean_object* v_assumptions_2961_; lean_object* v_constraints_2962_; lean_object* v_eliminations_2963_; lean_object* v___x_2964_; 
v_assumptions_2961_ = lean_ctor_get(v_p_2957_, 0);
v_constraints_2962_ = lean_ctor_get(v_p_2957_, 2);
lean_inc_ref(v_constraints_2962_);
v_eliminations_2963_ = lean_ctor_get(v_p_2957_, 4);
v___x_2964_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2962_, v_c_2958_);
if (lean_obj_tag(v___x_2964_) == 1)
{
lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2999_; 
lean_inc(v_eliminations_2963_);
lean_inc_ref(v_assumptions_2961_);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_p_2957_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; lean_object* v_unused_3001_; lean_object* v_unused_3002_; lean_object* v_unused_3003_; lean_object* v_unused_3004_; lean_object* v_unused_3005_; lean_object* v_unused_3006_; 
v_unused_3000_ = lean_ctor_get(v_p_2957_, 6);
lean_dec(v_unused_3000_);
v_unused_3001_ = lean_ctor_get(v_p_2957_, 5);
lean_dec(v_unused_3001_);
v_unused_3002_ = lean_ctor_get(v_p_2957_, 4);
lean_dec(v_unused_3002_);
v_unused_3003_ = lean_ctor_get(v_p_2957_, 3);
lean_dec(v_unused_3003_);
v_unused_3004_ = lean_ctor_get(v_p_2957_, 2);
lean_dec(v_unused_3004_);
v_unused_3005_ = lean_ctor_get(v_p_2957_, 1);
lean_dec(v_unused_3005_);
v_unused_3006_ = lean_ctor_get(v_p_2957_, 0);
lean_dec(v_unused_3006_);
v___x_2966_ = v_p_2957_;
v_isShared_2967_ = v_isSharedCheck_2999_;
goto v_resetjp_2965_;
}
else
{
lean_dec(v_p_2957_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2999_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v_val_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v_buckets_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2997_; 
v_val_2968_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_val_2968_);
lean_dec_ref(v___x_2964_);
v___x_2969_ = lean_unsigned_to_nat(0u);
v___x_2970_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v_buckets_2971_ = lean_ctor_get(v_constraints_2962_, 1);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_constraints_2962_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; 
v_unused_2998_ = lean_ctor_get(v_constraints_2962_, 0);
lean_dec(v_unused_2998_);
v___x_2973_ = v_constraints_2962_;
v_isShared_2974_ = v_isSharedCheck_2997_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_buckets_2971_);
lean_dec(v_constraints_2962_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2997_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2975_; lean_object* v_sign_2976_; lean_object* v___x_2978_; 
lean_inc_n(v___y_2960_, 2);
v___x_2975_ = l_Lean_Omega_IntList_get(v_c_2958_, v___y_2960_);
lean_dec(v_c_2958_);
v_sign_2976_ = l_Int_sign(v___x_2975_);
lean_dec(v___x_2975_);
lean_inc(v_sign_2976_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 1, v_sign_2976_);
lean_ctor_set(v___x_2973_, 0, v___y_2960_);
v___x_2978_ = v___x_2973_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___y_2960_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_sign_2976_);
v___x_2978_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v_init_2985_; 
lean_inc(v_val_2968_);
v___x_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2979_, 0, v_val_2968_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
v___x_2980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
lean_ctor_set(v___x_2980_, 1, v_eliminations_2963_);
v___x_2981_ = 1;
v___x_2982_ = lean_box(0);
v___x_2983_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 6, v___x_2983_);
lean_ctor_set(v___x_2966_, 5, v___x_2982_);
lean_ctor_set(v___x_2966_, 4, v___x_2980_);
lean_ctor_set(v___x_2966_, 3, v___x_2970_);
lean_ctor_set(v___x_2966_, 2, v___x_2970_);
lean_ctor_set(v___x_2966_, 1, v___x_2969_);
v_init_2985_ = v___x_2966_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_assumptions_2961_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2995_, 2, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2995_, 3, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2995_, 4, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_2995_, 5, v___x_2982_);
lean_ctor_set(v_reuseFailAlloc_2995_, 6, v___x_2983_);
v_init_2985_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2986_; uint8_t v___x_2987_; 
lean_ctor_set_uint8(v_init_2985_, sizeof(void*)*7, v___x_2981_);
v___x_2986_ = lean_array_get_size(v_buckets_2971_);
v___x_2987_ = lean_nat_dec_lt(v___x_2969_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_dec(v_sign_2976_);
lean_dec_ref(v_buckets_2971_);
lean_dec(v_val_2968_);
lean_dec(v___y_2960_);
return v_init_2985_;
}
else
{
uint8_t v___x_2988_; 
v___x_2988_ = lean_nat_dec_le(v___x_2986_, v___x_2986_);
if (v___x_2988_ == 0)
{
if (v___x_2987_ == 0)
{
lean_dec(v_sign_2976_);
lean_dec_ref(v_buckets_2971_);
lean_dec(v_val_2968_);
lean_dec(v___y_2960_);
return v_init_2985_;
}
else
{
size_t v___x_2989_; size_t v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = ((size_t)0ULL);
v___x_2990_ = lean_usize_of_nat(v___x_2986_);
v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2960_, v_sign_2976_, v_val_2968_, v_buckets_2971_, v___x_2989_, v___x_2990_, v_init_2985_);
lean_dec_ref(v_buckets_2971_);
lean_dec(v_sign_2976_);
return v___x_2991_;
}
}
else
{
size_t v___x_2992_; size_t v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = ((size_t)0ULL);
v___x_2993_ = lean_usize_of_nat(v___x_2986_);
v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2960_, v_sign_2976_, v_val_2968_, v_buckets_2971_, v___x_2992_, v___x_2993_, v_init_2985_);
lean_dec_ref(v_buckets_2971_);
lean_dec(v_sign_2976_);
return v___x_2994_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2964_);
lean_dec_ref(v_constraints_2962_);
lean_dec(v___y_2960_);
lean_dec(v_c_2958_);
return v_p_2957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(lean_object* v_msgData_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v___x_3017_; lean_object* v_env_3018_; lean_object* v___x_3019_; lean_object* v_mctx_3020_; lean_object* v_lctx_3021_; lean_object* v_options_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3017_ = lean_st_ref_get(v___y_3015_);
v_env_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc_ref(v_env_3018_);
lean_dec(v___x_3017_);
v___x_3019_ = lean_st_ref_get(v___y_3013_);
v_mctx_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc_ref(v_mctx_3020_);
lean_dec(v___x_3019_);
v_lctx_3021_ = lean_ctor_get(v___y_3012_, 2);
v_options_3022_ = lean_ctor_get(v___y_3014_, 2);
lean_inc_ref(v_options_3022_);
lean_inc_ref(v_lctx_3021_);
v___x_3023_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3023_, 0, v_env_3018_);
lean_ctor_set(v___x_3023_, 1, v_mctx_3020_);
lean_ctor_set(v___x_3023_, 2, v_lctx_3021_);
lean_ctor_set(v___x_3023_, 3, v_options_3022_);
v___x_3024_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
lean_ctor_set(v___x_3024_, 1, v_msgData_3011_);
v___x_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0___boxed(lean_object* v_msgData_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msgData_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(lean_object* v_msg_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_ref_3039_; lean_object* v___x_3040_; lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3049_; 
v_ref_3039_ = lean_ctor_get(v___y_3036_, 5);
v___x_3040_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3045_; lean_object* v___x_3047_; 
lean_inc(v_ref_3039_);
v___x_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3045_, 0, v_ref_3039_);
lean_ctor_set(v___x_3045_, 1, v_a_3041_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set_tag(v___x_3043_, 1);
lean_ctor_set(v___x_3043_, 0, v___x_3045_);
v___x_3047_ = v___x_3043_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg___boxed(lean_object* v_msg_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
return v_res_3056_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0));
v___x_3059_ = l_Lean_stringToMessageData(v___x_3058_);
return v___x_3059_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2));
v___x_3062_ = l_Lean_stringToMessageData(v___x_3061_);
return v___x_3062_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4));
v___x_3065_ = l_Lean_stringToMessageData(v___x_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(lean_object* v_p_3066_, lean_object* v_c_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, uint8_t v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v_constraints_3078_; lean_object* v___x_3079_; 
v_constraints_3078_ = lean_ctor_get(v_p_3066_, 2);
v___x_3079_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_3078_, v_c_3067_);
if (lean_obj_tag(v___x_3079_) == 1)
{
lean_object* v_val_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3179_; 
v_val_3080_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3082_ = v___x_3079_;
v_isShared_3083_ = v_isSharedCheck_3179_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_val_3080_);
lean_dec(v___x_3079_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3179_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v_constraint_3084_; lean_object* v_lowerBound_3085_; 
v_constraint_3084_ = lean_ctor_get(v_val_3080_, 1);
v_lowerBound_3085_ = lean_ctor_get(v_constraint_3084_, 0);
lean_inc(v_lowerBound_3085_);
if (lean_obj_tag(v_lowerBound_3085_) == 1)
{
lean_object* v_upperBound_3086_; 
lean_del_object(v___x_3082_);
v_upperBound_3086_ = lean_ctor_get(v_constraint_3084_, 1);
lean_inc(v_upperBound_3086_);
if (lean_obj_tag(v_upperBound_3086_) == 1)
{
lean_object* v_coeffs_3087_; lean_object* v_justification_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3166_; 
v_coeffs_3087_ = lean_ctor_get(v_val_3080_, 0);
v_justification_3088_ = lean_ctor_get(v_val_3080_, 2);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_val_3080_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; 
v_unused_3167_ = lean_ctor_get(v_val_3080_, 1);
lean_dec(v_unused_3167_);
v___x_3090_ = v_val_3080_;
v_isShared_3091_ = v_isSharedCheck_3166_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_justification_3088_);
lean_inc(v_coeffs_3087_);
lean_dec(v_val_3080_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3166_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v_val_3092_; lean_object* v_val_3093_; lean_object* v___x_3094_; 
v_val_3092_ = lean_ctor_get(v_lowerBound_3085_, 0);
lean_inc(v_val_3092_);
lean_dec_ref(v_lowerBound_3085_);
v_val_3093_ = lean_ctor_get(v_upperBound_3086_, 0);
lean_inc(v_val_3093_);
lean_dec_ref(v_upperBound_3086_);
v___x_3094_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3069_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v_m_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v_nil_3101_; lean_object* v_cons_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_a_3095_);
lean_dec_ref(v___x_3094_);
lean_inc(v_c_3067_);
v___x_3096_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_c_3067_);
v___x_3097_ = lean_unsigned_to_nat(1u);
v_m_3098_ = lean_nat_add(v___x_3096_, v___x_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc(v_m_3098_);
v___x_3100_ = l_Lean_mkNatLit(v_m_3098_);
v_nil_3101_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3102_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3103_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3101_, v_cons_3102_, v_c_3067_);
lean_dec(v_c_3067_);
v___x_3104_ = l_Lean_mkApp3(v___x_3099_, v___x_3100_, v___x_3103_, v_a_3095_);
v___x_3105_ = l_Lean_Elab_Tactic_Omega_lookup(v___x_3104_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3149_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3108_ = v___x_3105_;
v_isShared_3109_ = v_isSharedCheck_3149_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3105_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3149_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v_fst_3110_; lean_object* v_snd_3111_; uint8_t v___x_3124_; 
v_fst_3110_ = lean_ctor_get(v_a_3106_, 0);
lean_inc(v_fst_3110_);
v_snd_3111_ = lean_ctor_get(v_a_3106_, 1);
lean_inc(v_snd_3111_);
lean_dec(v_a_3106_);
v___x_3124_ = lean_int_dec_eq(v_val_3093_, v_val_3092_);
lean_dec(v_val_3093_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec(v_snd_3111_);
lean_dec(v_fst_3110_);
lean_del_object(v___x_3108_);
lean_dec(v_m_3098_);
lean_dec(v_val_3092_);
lean_del_object(v___x_3090_);
lean_dec_ref(v_justification_3088_);
lean_dec(v_coeffs_3087_);
lean_dec_ref(v_p_3066_);
v___x_3125_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1);
v___x_3126_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3125_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
return v___x_3126_;
}
else
{
if (lean_obj_tag(v_snd_3111_) == 0)
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_fst_3110_);
lean_del_object(v___x_3108_);
lean_dec(v_m_3098_);
lean_dec(v_val_3092_);
lean_del_object(v___x_3090_);
lean_dec_ref(v_justification_3088_);
lean_dec(v_coeffs_3087_);
lean_dec_ref(v_p_3066_);
v___x_3127_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3);
v___x_3128_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3127_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
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
lean_object* v_val_3137_; uint8_t v___x_3138_; 
v_val_3137_ = lean_ctor_get(v_snd_3111_, 0);
lean_inc(v_val_3137_);
lean_dec_ref(v_snd_3111_);
v___x_3138_ = l_List_isEmpty___redArg(v_val_3137_);
lean_dec(v_val_3137_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec(v_fst_3110_);
lean_del_object(v___x_3108_);
lean_dec(v_m_3098_);
lean_dec(v_val_3092_);
lean_del_object(v___x_3090_);
lean_dec_ref(v_justification_3088_);
lean_dec(v_coeffs_3087_);
lean_dec_ref(v_p_3066_);
v___x_3139_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5);
v___x_3140_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3139_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3140_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3140_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
else
{
goto v___jp_3112_;
}
}
}
v___jp_3112_:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
lean_inc(v_coeffs_3087_);
lean_inc_n(v_m_3098_, 2);
v___x_3113_ = l_Lean_Omega_bmod__coeffs(v_m_3098_, v_fst_3110_, v_coeffs_3087_);
v___x_3114_ = l_Int_bmod(v_val_3092_, v_m_3098_);
v___x_3115_ = l_Lean_Omega_Constraint_exact(v___x_3114_);
v___x_3116_ = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(v___x_3116_, 0, v_m_3098_);
lean_ctor_set(v___x_3116_, 1, v_val_3092_);
lean_ctor_set(v___x_3116_, 2, v_fst_3110_);
lean_ctor_set(v___x_3116_, 3, v_coeffs_3087_);
lean_ctor_set(v___x_3116_, 4, v_justification_3088_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 2, v___x_3116_);
lean_ctor_set(v___x_3090_, 1, v___x_3115_);
lean_ctor_set(v___x_3090_, 0, v___x_3113_);
v___x_3118_ = v___x_3090_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3113_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3123_, 2, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3119_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_3066_, v___x_3118_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 0, v___x_3119_);
v___x_3121_ = v___x_3108_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3119_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v_m_3098_);
lean_dec(v_val_3093_);
lean_dec(v_val_3092_);
lean_del_object(v___x_3090_);
lean_dec_ref(v_justification_3088_);
lean_dec(v_coeffs_3087_);
lean_dec_ref(v_p_3066_);
v_a_3150_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3105_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3105_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec(v_val_3093_);
lean_dec(v_val_3092_);
lean_del_object(v___x_3090_);
lean_dec_ref(v_justification_3088_);
lean_dec(v_coeffs_3087_);
lean_dec(v_c_3067_);
lean_dec_ref(v_p_3066_);
v_a_3158_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3094_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3094_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
}
else
{
lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec(v_upperBound_3086_);
lean_dec(v_val_3080_);
lean_dec(v_c_3067_);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_lowerBound_3085_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v_lowerBound_3085_, 0);
lean_dec(v_unused_3175_);
v___x_3169_ = v_lowerBound_3085_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_dec(v_lowerBound_3085_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
lean_ctor_set_tag(v___x_3169_, 0);
lean_ctor_set(v___x_3169_, 0, v_p_3066_);
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_p_3066_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
else
{
lean_object* v___x_3177_; 
lean_dec(v_lowerBound_3085_);
lean_dec(v_val_3080_);
lean_dec(v_c_3067_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set_tag(v___x_3082_, 0);
lean_ctor_set(v___x_3082_, 0, v_p_3066_);
v___x_3177_ = v___x_3082_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_p_3066_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
else
{
lean_object* v___x_3180_; 
lean_dec(v___x_3079_);
lean_dec(v_c_3067_);
v___x_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3180_, 0, v_p_3066_);
return v___x_3180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___boxed(lean_object* v_p_3181_, lean_object* v_c_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_){
_start:
{
uint8_t v_a_boxed_3193_; lean_object* v_res_3194_; 
v_a_boxed_3193_ = lean_unbox(v_a_3186_);
v_res_3194_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3181_, v_c_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_boxed_3193_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_3188_);
lean_dec(v_a_3187_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec(v_a_3183_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_object* v_00_u03b1_3195_, lean_object* v_msg_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, uint8_t v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3196_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___boxed(lean_object* v_00_u03b1_3208_, lean_object* v_msg_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
uint8_t v___y_14890__boxed_3220_; lean_object* v_res_3221_; 
v___y_14890__boxed_3220_ = lean_unbox(v___y_3213_);
v_res_3221_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(v_00_u03b1_3208_, v_msg_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_14890__boxed_3220_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec(v___y_3210_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality(lean_object* v_p_3222_, lean_object* v_c_3223_, lean_object* v_m_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, uint8_t v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_){
_start:
{
lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3235_ = lean_unsigned_to_nat(1u);
v___x_3236_ = lean_nat_dec_eq(v_m_3224_, v___x_3235_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3222_, v_c_3223_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_);
return v___x_3237_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_3222_, v_c_3223_);
v___x_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
return v___x_3239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality___boxed(lean_object* v_p_3240_, lean_object* v_c_3241_, lean_object* v_m_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
uint8_t v_a_boxed_3253_; lean_object* v_res_3254_; 
v_a_boxed_3253_ = lean_unbox(v_a_3246_);
v_res_3254_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3240_, v_c_3241_, v_m_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_boxed_3253_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_);
lean_dec(v_a_3251_);
lean_dec_ref(v_a_3250_);
lean_dec(v_a_3249_);
lean_dec_ref(v_a_3248_);
lean_dec(v_a_3247_);
lean_dec_ref(v_a_3245_);
lean_dec(v_a_3244_);
lean_dec(v_a_3243_);
lean_dec(v_m_3242_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(lean_object* v_p_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, uint8_t v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
uint8_t v_possible_3266_; 
v_possible_3266_ = lean_ctor_get_uint8(v_p_3255_, sizeof(void*)*7);
if (v_possible_3266_ == 0)
{
lean_object* v___x_3267_; 
v___x_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3267_, 0, v_p_3255_);
return v___x_3267_;
}
else
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_3255_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v___x_3269_; 
v___x_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3269_, 0, v_p_3255_);
return v___x_3269_;
}
else
{
lean_object* v_val_3270_; lean_object* v_fst_3271_; lean_object* v_snd_3272_; lean_object* v___x_3273_; 
v_val_3270_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_val_3270_);
lean_dec_ref(v___x_3268_);
v_fst_3271_ = lean_ctor_get(v_val_3270_, 0);
lean_inc(v_fst_3271_);
v_snd_3272_ = lean_ctor_get(v_val_3270_, 1);
lean_inc(v_snd_3272_);
lean_dec(v_val_3270_);
v___x_3273_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3255_, v_fst_3271_, v_snd_3272_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
lean_dec(v_snd_3272_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref(v___x_3273_);
v_p_3255_ = v_a_3274_;
goto _start;
}
else
{
return v___x_3273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities___boxed(lean_object* v_p_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
uint8_t v_a_boxed_3287_; lean_object* v_res_3288_; 
v_a_boxed_3287_ = lean_unbox(v_a_3280_);
v_res_3288_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_boxed_3287_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
lean_dec(v_a_3285_);
lean_dec_ref(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_a_3282_);
lean_dec(v_a_3281_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec(v_a_3277_);
return v_res_3288_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3295_ = lean_box(0);
v___x_3296_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1));
v___x_3297_ = l_Lean_Expr_const___override(v___x_3296_, v___x_3295_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object* v_c_3298_, lean_object* v_x_3299_, lean_object* v_p_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, uint8_t v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3302_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref(v___x_3311_);
v___x_3313_ = lean_box(v_a_3304_);
lean_inc(v_a_3309_);
lean_inc_ref(v_a_3308_);
lean_inc(v_a_3307_);
lean_inc_ref(v_a_3306_);
lean_inc(v_a_3305_);
lean_inc_ref(v_a_3303_);
lean_inc(v_a_3302_);
lean_inc(v_a_3301_);
v___x_3314_ = lean_apply_10(v_p_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v___x_3313_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, lean_box(0));
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3340_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3317_ = v___x_3314_;
v_isShared_3318_ = v_isSharedCheck_3340_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3314_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3340_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3319_; lean_object* v___y_3321_; lean_object* v___x_3329_; uint8_t v___x_3330_; 
v___x_3319_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2);
v___x_3329_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3330_ = lean_int_dec_le(v___x_3329_, v_c_3298_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3331_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3332_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3333_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3334_ = lean_int_neg(v_c_3298_);
v___x_3335_ = l_Int_toNat(v___x_3334_);
lean_dec(v___x_3334_);
v___x_3336_ = l_Lean_instToExprInt_mkNat(v___x_3335_);
v___x_3337_ = l_Lean_mkApp3(v___x_3331_, v___x_3332_, v___x_3333_, v___x_3336_);
v___y_3321_ = v___x_3337_;
goto v___jp_3320_;
}
else
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = l_Int_toNat(v_c_3298_);
v___x_3339_ = l_Lean_instToExprInt_mkNat(v___x_3338_);
v___y_3321_ = v___x_3339_;
goto v___jp_3320_;
}
v___jp_3320_:
{
lean_object* v_nil_3322_; lean_object* v_cons_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3327_; 
v_nil_3322_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3323_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3324_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3322_, v_cons_3323_, v_x_3299_);
v___x_3325_ = l_Lean_mkApp4(v___x_3319_, v___y_3321_, v___x_3324_, v_a_3312_, v_a_3315_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 0, v___x_3325_);
v___x_3327_ = v___x_3317_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
else
{
lean_dec(v_a_3312_);
return v___x_3314_;
}
}
else
{
lean_dec_ref(v_p_3300_);
return v___x_3311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object* v_c_3341_, lean_object* v_x_3342_, lean_object* v_p_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_){
_start:
{
uint8_t v_a_boxed_3354_; lean_object* v_res_3355_; 
v_a_boxed_3354_ = lean_unbox(v_a_3347_);
v_res_3355_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(v_c_3341_, v_x_3342_, v_p_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_boxed_3354_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3346_);
lean_dec(v_a_3345_);
lean_dec(v_a_3344_);
lean_dec(v_x_3342_);
lean_dec(v_c_3341_);
return v_res_3355_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2(void){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3362_ = lean_box(0);
v___x_3363_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1));
v___x_3364_ = l_Lean_Expr_const___override(v___x_3363_, v___x_3362_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(lean_object* v_c_3365_, lean_object* v_x_3366_, lean_object* v_p_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, uint8_t v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3369_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref(v___x_3378_);
v___x_3380_ = lean_box(v_a_3371_);
lean_inc(v_a_3376_);
lean_inc_ref(v_a_3375_);
lean_inc(v_a_3374_);
lean_inc_ref(v_a_3373_);
lean_inc(v_a_3372_);
lean_inc_ref(v_a_3370_);
lean_inc(v_a_3369_);
lean_inc(v_a_3368_);
v___x_3381_ = lean_apply_10(v_p_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v___x_3380_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, lean_box(0));
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3407_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3384_ = v___x_3381_;
v_isShared_3385_ = v_isSharedCheck_3407_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3407_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v___y_3388_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v___x_3386_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2);
v___x_3396_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3397_ = lean_int_dec_le(v___x_3396_, v_c_3365_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3398_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3399_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3400_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3401_ = lean_int_neg(v_c_3365_);
v___x_3402_ = l_Int_toNat(v___x_3401_);
lean_dec(v___x_3401_);
v___x_3403_ = l_Lean_instToExprInt_mkNat(v___x_3402_);
v___x_3404_ = l_Lean_mkApp3(v___x_3398_, v___x_3399_, v___x_3400_, v___x_3403_);
v___y_3388_ = v___x_3404_;
goto v___jp_3387_;
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3405_ = l_Int_toNat(v_c_3365_);
v___x_3406_ = l_Lean_instToExprInt_mkNat(v___x_3405_);
v___y_3388_ = v___x_3406_;
goto v___jp_3387_;
}
v___jp_3387_:
{
lean_object* v_nil_3389_; lean_object* v_cons_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3394_; 
v_nil_3389_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3390_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3391_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3389_, v_cons_3390_, v_x_3366_);
v___x_3392_ = l_Lean_mkApp4(v___x_3386_, v___y_3388_, v___x_3391_, v_a_3379_, v_a_3382_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3392_);
v___x_3394_ = v___x_3384_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
else
{
lean_dec(v_a_3379_);
return v___x_3381_;
}
}
else
{
lean_dec_ref(v_p_3367_);
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed(lean_object* v_c_3408_, lean_object* v_x_3409_, lean_object* v_p_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_){
_start:
{
uint8_t v_a_boxed_3421_; lean_object* v_res_3422_; 
v_a_boxed_3421_ = lean_unbox(v_a_3414_);
v_res_3422_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(v_c_3408_, v_x_3409_, v_p_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_boxed_3421_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_);
lean_dec(v_a_3419_);
lean_dec_ref(v_a_3418_);
lean_dec(v_a_3417_);
lean_dec_ref(v_a_3416_);
lean_dec(v_a_3415_);
lean_dec_ref(v_a_3413_);
lean_dec(v_a_3412_);
lean_dec(v_a_3411_);
lean_dec(v_x_3409_);
lean_dec(v_c_3408_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(lean_object* v_prf_x3f_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, uint8_t v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
if (lean_obj_tag(v_prf_x3f_3423_) == 0)
{
lean_object* v___x_3434_; uint8_t v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3434_ = lean_box(0);
v___x_3435_ = 0;
v___x_3436_ = lean_box(0);
v___x_3437_ = l_Lean_Meta_mkFreshExprMVar(v___x_3434_, v___x_3435_, v___x_3436_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; uint8_t v___x_3439_; lean_object* v___x_3440_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref(v___x_3437_);
v___x_3439_ = 0;
v___x_3440_ = l_Lean_Meta_mkSorry(v_a_3438_, v___x_3439_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
return v___x_3440_;
}
else
{
return v___x_3437_;
}
}
else
{
lean_object* v_val_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v_val_3441_ = lean_ctor_get(v_prf_x3f_3423_, 0);
lean_inc(v_val_3441_);
lean_dec_ref(v_prf_x3f_3423_);
v___x_3442_ = lean_box(v___y_3427_);
lean_inc(v___y_3432_);
lean_inc_ref(v___y_3431_);
lean_inc(v___y_3430_);
lean_inc_ref(v___y_3429_);
lean_inc(v___y_3428_);
lean_inc_ref(v___y_3426_);
lean_inc(v___y_3425_);
lean_inc(v___y_3424_);
v___x_3443_ = lean_apply_10(v_val_3441_, v___y_3424_, v___y_3425_, v___y_3426_, v___x_3442_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, lean_box(0));
return v___x_3443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed(lean_object* v_prf_x3f_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
uint8_t v___y_833__boxed_3455_; lean_object* v_res_3456_; 
v___y_833__boxed_3455_ = lean_unbox(v___y_3448_);
v_res_3456_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(v_prf_x3f_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_833__boxed_3455_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec(v___y_3445_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality(lean_object* v_p_3457_, lean_object* v_const_3458_, lean_object* v_coeffs_3459_, lean_object* v_prf_x3f_3460_){
_start:
{
lean_object* v_assumptions_3461_; lean_object* v_numVars_3462_; lean_object* v_constraints_3463_; lean_object* v_equalities_3464_; lean_object* v_eliminations_3465_; uint8_t v_possible_3466_; lean_object* v_proveFalse_x3f_3467_; lean_object* v_explanation_x3f_3468_; lean_object* v_prf_3469_; lean_object* v_i_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v_p_x27_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v_f_3479_; lean_object* v_f_3480_; lean_object* v_f_3481_; lean_object* v___x_3482_; 
v_assumptions_3461_ = lean_ctor_get(v_p_3457_, 0);
v_numVars_3462_ = lean_ctor_get(v_p_3457_, 1);
v_constraints_3463_ = lean_ctor_get(v_p_3457_, 2);
v_equalities_3464_ = lean_ctor_get(v_p_3457_, 3);
v_eliminations_3465_ = lean_ctor_get(v_p_3457_, 4);
v_possible_3466_ = lean_ctor_get_uint8(v_p_3457_, sizeof(void*)*7);
v_proveFalse_x3f_3467_ = lean_ctor_get(v_p_3457_, 5);
v_explanation_x3f_3468_ = lean_ctor_get(v_p_3457_, 6);
v_prf_3469_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3469_, 0, v_prf_x3f_3460_);
v_i_3470_ = lean_array_get_size(v_assumptions_3461_);
lean_inc_n(v_coeffs_3459_, 2);
lean_inc(v_const_3458_);
v___x_3471_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed), 13, 3);
lean_closure_set(v___x_3471_, 0, v_const_3458_);
lean_closure_set(v___x_3471_, 1, v_coeffs_3459_);
lean_closure_set(v___x_3471_, 2, v_prf_3469_);
lean_inc_ref(v_assumptions_3461_);
v___x_3472_ = lean_array_push(v_assumptions_3461_, v___x_3471_);
lean_inc_ref(v_explanation_x3f_3468_);
lean_inc(v_proveFalse_x3f_3467_);
lean_inc(v_eliminations_3465_);
lean_inc_ref(v_equalities_3464_);
lean_inc_ref(v_constraints_3463_);
lean_inc(v_numVars_3462_);
v_p_x27_3473_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3473_, 0, v___x_3472_);
lean_ctor_set(v_p_x27_3473_, 1, v_numVars_3462_);
lean_ctor_set(v_p_x27_3473_, 2, v_constraints_3463_);
lean_ctor_set(v_p_x27_3473_, 3, v_equalities_3464_);
lean_ctor_set(v_p_x27_3473_, 4, v_eliminations_3465_);
lean_ctor_set(v_p_x27_3473_, 5, v_proveFalse_x3f_3467_);
lean_ctor_set(v_p_x27_3473_, 6, v_explanation_x3f_3468_);
lean_ctor_set_uint8(v_p_x27_3473_, sizeof(void*)*7, v_possible_3466_);
v___x_3474_ = lean_int_neg(v_const_3458_);
lean_dec(v_const_3458_);
v___x_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
v___x_3476_ = lean_box(0);
v___x_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3475_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
lean_inc_ref(v___x_3477_);
v___x_3478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
lean_ctor_set(v___x_3478_, 1, v_coeffs_3459_);
lean_ctor_set(v___x_3478_, 2, v_i_3470_);
v_f_3479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3479_, 0, v_coeffs_3459_);
lean_ctor_set(v_f_3479_, 1, v___x_3477_);
lean_ctor_set(v_f_3479_, 2, v___x_3478_);
v_f_3480_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3457_, v_f_3479_);
v_f_3481_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3480_);
v___x_3482_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3473_, v_f_3481_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality(lean_object* v_p_3483_, lean_object* v_const_3484_, lean_object* v_coeffs_3485_, lean_object* v_prf_x3f_3486_){
_start:
{
lean_object* v_assumptions_3487_; lean_object* v_numVars_3488_; lean_object* v_constraints_3489_; lean_object* v_equalities_3490_; lean_object* v_eliminations_3491_; uint8_t v_possible_3492_; lean_object* v_proveFalse_x3f_3493_; lean_object* v_explanation_x3f_3494_; lean_object* v_prf_3495_; lean_object* v_i_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v_p_x27_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v_f_3504_; lean_object* v_f_3505_; lean_object* v_f_3506_; lean_object* v___x_3507_; 
v_assumptions_3487_ = lean_ctor_get(v_p_3483_, 0);
v_numVars_3488_ = lean_ctor_get(v_p_3483_, 1);
v_constraints_3489_ = lean_ctor_get(v_p_3483_, 2);
v_equalities_3490_ = lean_ctor_get(v_p_3483_, 3);
v_eliminations_3491_ = lean_ctor_get(v_p_3483_, 4);
v_possible_3492_ = lean_ctor_get_uint8(v_p_3483_, sizeof(void*)*7);
v_proveFalse_x3f_3493_ = lean_ctor_get(v_p_3483_, 5);
v_explanation_x3f_3494_ = lean_ctor_get(v_p_3483_, 6);
v_prf_3495_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3495_, 0, v_prf_x3f_3486_);
v_i_3496_ = lean_array_get_size(v_assumptions_3487_);
lean_inc_n(v_coeffs_3485_, 2);
lean_inc(v_const_3484_);
v___x_3497_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed), 13, 3);
lean_closure_set(v___x_3497_, 0, v_const_3484_);
lean_closure_set(v___x_3497_, 1, v_coeffs_3485_);
lean_closure_set(v___x_3497_, 2, v_prf_3495_);
lean_inc_ref(v_assumptions_3487_);
v___x_3498_ = lean_array_push(v_assumptions_3487_, v___x_3497_);
lean_inc_ref(v_explanation_x3f_3494_);
lean_inc(v_proveFalse_x3f_3493_);
lean_inc(v_eliminations_3491_);
lean_inc_ref(v_equalities_3490_);
lean_inc_ref(v_constraints_3489_);
lean_inc(v_numVars_3488_);
v_p_x27_3499_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3499_, 0, v___x_3498_);
lean_ctor_set(v_p_x27_3499_, 1, v_numVars_3488_);
lean_ctor_set(v_p_x27_3499_, 2, v_constraints_3489_);
lean_ctor_set(v_p_x27_3499_, 3, v_equalities_3490_);
lean_ctor_set(v_p_x27_3499_, 4, v_eliminations_3491_);
lean_ctor_set(v_p_x27_3499_, 5, v_proveFalse_x3f_3493_);
lean_ctor_set(v_p_x27_3499_, 6, v_explanation_x3f_3494_);
lean_ctor_set_uint8(v_p_x27_3499_, sizeof(void*)*7, v_possible_3492_);
v___x_3500_ = lean_int_neg(v_const_3484_);
lean_dec(v_const_3484_);
v___x_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
lean_inc_ref(v___x_3501_);
v___x_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
lean_inc_ref(v___x_3502_);
v___x_3503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
lean_ctor_set(v___x_3503_, 1, v_coeffs_3485_);
lean_ctor_set(v___x_3503_, 2, v_i_3496_);
v_f_3504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3504_, 0, v_coeffs_3485_);
lean_ctor_set(v_f_3504_, 1, v___x_3502_);
lean_ctor_set(v_f_3504_, 2, v___x_3503_);
v_f_3505_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3483_, v_f_3504_);
v_f_3506_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3505_);
v___x_3507_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3499_, v_f_3506_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(lean_object* v_x_3508_, lean_object* v_x_3509_){
_start:
{
if (lean_obj_tag(v_x_3509_) == 0)
{
return v_x_3508_;
}
else
{
lean_object* v_head_3510_; lean_object* v_snd_3511_; lean_object* v_tail_3512_; lean_object* v_fst_3513_; lean_object* v_fst_3514_; lean_object* v_snd_3515_; lean_object* v___x_3516_; 
v_head_3510_ = lean_ctor_get(v_x_3509_, 0);
lean_inc(v_head_3510_);
v_snd_3511_ = lean_ctor_get(v_head_3510_, 1);
lean_inc(v_snd_3511_);
v_tail_3512_ = lean_ctor_get(v_x_3509_, 1);
lean_inc(v_tail_3512_);
lean_dec_ref(v_x_3509_);
v_fst_3513_ = lean_ctor_get(v_head_3510_, 0);
lean_inc(v_fst_3513_);
lean_dec(v_head_3510_);
v_fst_3514_ = lean_ctor_get(v_snd_3511_, 0);
lean_inc(v_fst_3514_);
v_snd_3515_ = lean_ctor_get(v_snd_3511_, 1);
lean_inc(v_snd_3515_);
lean_dec(v_snd_3511_);
v___x_3516_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality(v_x_3508_, v_fst_3513_, v_fst_3514_, v_snd_3515_);
v_x_3508_ = v___x_3516_;
v_x_3509_ = v_tail_3512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequalities(lean_object* v_p_3518_, lean_object* v_ineqs_3519_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(v_p_3518_, v_ineqs_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(lean_object* v_x_3521_, lean_object* v_x_3522_){
_start:
{
if (lean_obj_tag(v_x_3522_) == 0)
{
return v_x_3521_;
}
else
{
lean_object* v_head_3523_; lean_object* v_snd_3524_; lean_object* v_tail_3525_; lean_object* v_fst_3526_; lean_object* v_fst_3527_; lean_object* v_snd_3528_; lean_object* v___x_3529_; 
v_head_3523_ = lean_ctor_get(v_x_3522_, 0);
lean_inc(v_head_3523_);
v_snd_3524_ = lean_ctor_get(v_head_3523_, 1);
lean_inc(v_snd_3524_);
v_tail_3525_ = lean_ctor_get(v_x_3522_, 1);
lean_inc(v_tail_3525_);
lean_dec_ref(v_x_3522_);
v_fst_3526_ = lean_ctor_get(v_head_3523_, 0);
lean_inc(v_fst_3526_);
lean_dec(v_head_3523_);
v_fst_3527_ = lean_ctor_get(v_snd_3524_, 0);
lean_inc(v_fst_3527_);
v_snd_3528_ = lean_ctor_get(v_snd_3524_, 1);
lean_inc(v_snd_3528_);
lean_dec(v_snd_3524_);
v___x_3529_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality(v_x_3521_, v_fst_3526_, v_fst_3527_, v_snd_3528_);
v_x_3521_ = v___x_3529_;
v_x_3522_ = v_tail_3525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEqualities(lean_object* v_p_3531_, lean_object* v_eqs_3532_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(v_p_3531_, v_eqs_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0(lean_object* v___x_3540_, lean_object* v_x_3541_){
_start:
{
lean_object* v_constraint_3542_; lean_object* v_coeffs_3543_; lean_object* v_lowerBound_3544_; lean_object* v_upperBound_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___y_3550_; lean_object* v___y_3551_; 
v_constraint_3542_ = lean_ctor_get(v_x_3541_, 1);
lean_inc_ref(v_constraint_3542_);
v_coeffs_3543_ = lean_ctor_get(v_x_3541_, 0);
lean_inc(v_coeffs_3543_);
lean_dec_ref(v_x_3541_);
v_lowerBound_3544_ = lean_ctor_get(v_constraint_3542_, 0);
lean_inc(v_lowerBound_3544_);
v_upperBound_3545_ = lean_ctor_get(v_constraint_3542_, 1);
lean_inc(v_upperBound_3545_);
lean_dec_ref(v_constraint_3542_);
v___x_3546_ = l_List_toString___redArg(v___x_3540_, v_coeffs_3543_);
v___x_3547_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3548_ = lean_string_append(v___x_3546_, v___x_3547_);
if (lean_obj_tag(v_lowerBound_3544_) == 0)
{
if (lean_obj_tag(v_upperBound_3545_) == 0)
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3556_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3557_ = lean_string_append(v___x_3548_, v___x_3556_);
return v___x_3557_;
}
else
{
lean_object* v_val_3558_; lean_object* v___x_3559_; lean_object* v___y_3561_; lean_object* v_intZero_3566_; uint8_t v_isNeg_3567_; 
v_val_3558_ = lean_ctor_get(v_upperBound_3545_, 0);
lean_inc(v_val_3558_);
lean_dec_ref(v_upperBound_3545_);
v___x_3559_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3566_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3567_ = lean_int_dec_lt(v_val_3558_, v_intZero_3566_);
if (v_isNeg_3567_ == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3569_; 
v_a_3568_ = lean_nat_abs(v_val_3558_);
lean_dec(v_val_3558_);
v___x_3569_ = l_Nat_reprFast(v_a_3568_);
v___y_3561_ = v___x_3569_;
goto v___jp_3560_;
}
else
{
lean_object* v_abs_3570_; lean_object* v_one_3571_; lean_object* v_a_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v_abs_3570_ = lean_nat_abs(v_val_3558_);
lean_dec(v_val_3558_);
v_one_3571_ = lean_unsigned_to_nat(1u);
v_a_3572_ = lean_nat_sub(v_abs_3570_, v_one_3571_);
lean_dec(v_abs_3570_);
v___x_3573_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3574_ = lean_nat_add(v_a_3572_, v_one_3571_);
lean_dec(v_a_3572_);
v___x_3575_ = l_Nat_reprFast(v___x_3574_);
v___x_3576_ = lean_string_append(v___x_3573_, v___x_3575_);
lean_dec_ref(v___x_3575_);
v___y_3561_ = v___x_3576_;
goto v___jp_3560_;
}
v___jp_3560_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3562_ = lean_string_append(v___x_3559_, v___y_3561_);
lean_dec_ref(v___y_3561_);
v___x_3563_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3564_ = lean_string_append(v___x_3562_, v___x_3563_);
v___x_3565_ = lean_string_append(v___x_3548_, v___x_3564_);
lean_dec_ref(v___x_3564_);
return v___x_3565_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3545_) == 0)
{
lean_object* v_val_3577_; lean_object* v___x_3578_; lean_object* v___y_3580_; lean_object* v_intZero_3585_; uint8_t v_isNeg_3586_; 
v_val_3577_ = lean_ctor_get(v_lowerBound_3544_, 0);
lean_inc(v_val_3577_);
lean_dec_ref(v_lowerBound_3544_);
v___x_3578_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3585_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3586_ = lean_int_dec_lt(v_val_3577_, v_intZero_3585_);
if (v_isNeg_3586_ == 0)
{
lean_object* v_a_3587_; lean_object* v___x_3588_; 
v_a_3587_ = lean_nat_abs(v_val_3577_);
lean_dec(v_val_3577_);
v___x_3588_ = l_Nat_reprFast(v_a_3587_);
v___y_3580_ = v___x_3588_;
goto v___jp_3579_;
}
else
{
lean_object* v_abs_3589_; lean_object* v_one_3590_; lean_object* v_a_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_abs_3589_ = lean_nat_abs(v_val_3577_);
lean_dec(v_val_3577_);
v_one_3590_ = lean_unsigned_to_nat(1u);
v_a_3591_ = lean_nat_sub(v_abs_3589_, v_one_3590_);
lean_dec(v_abs_3589_);
v___x_3592_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3593_ = lean_nat_add(v_a_3591_, v_one_3590_);
lean_dec(v_a_3591_);
v___x_3594_ = l_Nat_reprFast(v___x_3593_);
v___x_3595_ = lean_string_append(v___x_3592_, v___x_3594_);
lean_dec_ref(v___x_3594_);
v___y_3580_ = v___x_3595_;
goto v___jp_3579_;
}
v___jp_3579_:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3581_ = lean_string_append(v___x_3578_, v___y_3580_);
lean_dec_ref(v___y_3580_);
v___x_3582_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3583_ = lean_string_append(v___x_3581_, v___x_3582_);
v___x_3584_ = lean_string_append(v___x_3548_, v___x_3583_);
lean_dec_ref(v___x_3583_);
return v___x_3584_;
}
}
else
{
lean_object* v_val_3596_; lean_object* v_val_3597_; uint8_t v___x_3598_; 
v_val_3596_ = lean_ctor_get(v_lowerBound_3544_, 0);
lean_inc(v_val_3596_);
lean_dec_ref(v_lowerBound_3544_);
v_val_3597_ = lean_ctor_get(v_upperBound_3545_, 0);
lean_inc(v_val_3597_);
lean_dec_ref(v_upperBound_3545_);
v___x_3598_ = lean_int_dec_lt(v_val_3597_, v_val_3596_);
if (v___x_3598_ == 0)
{
uint8_t v___x_3599_; 
v___x_3599_ = lean_int_dec_eq(v_val_3596_, v_val_3597_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; lean_object* v___y_3602_; lean_object* v_intZero_3617_; uint8_t v_isNeg_3618_; 
v___x_3600_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3617_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3618_ = lean_int_dec_lt(v_val_3596_, v_intZero_3617_);
if (v_isNeg_3618_ == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3620_; 
v_a_3619_ = lean_nat_abs(v_val_3596_);
lean_dec(v_val_3596_);
v___x_3620_ = l_Nat_reprFast(v_a_3619_);
v___y_3602_ = v___x_3620_;
goto v___jp_3601_;
}
else
{
lean_object* v_abs_3621_; lean_object* v_one_3622_; lean_object* v_a_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v_abs_3621_ = lean_nat_abs(v_val_3596_);
lean_dec(v_val_3596_);
v_one_3622_ = lean_unsigned_to_nat(1u);
v_a_3623_ = lean_nat_sub(v_abs_3621_, v_one_3622_);
lean_dec(v_abs_3621_);
v___x_3624_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3625_ = lean_nat_add(v_a_3623_, v_one_3622_);
lean_dec(v_a_3623_);
v___x_3626_ = l_Nat_reprFast(v___x_3625_);
v___x_3627_ = lean_string_append(v___x_3624_, v___x_3626_);
lean_dec_ref(v___x_3626_);
v___y_3602_ = v___x_3627_;
goto v___jp_3601_;
}
v___jp_3601_:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v_intZero_3606_; uint8_t v_isNeg_3607_; 
v___x_3603_ = lean_string_append(v___x_3600_, v___y_3602_);
lean_dec_ref(v___y_3602_);
v___x_3604_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3605_ = lean_string_append(v___x_3603_, v___x_3604_);
v_intZero_3606_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3607_ = lean_int_dec_lt(v_val_3597_, v_intZero_3606_);
if (v_isNeg_3607_ == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3609_; 
v_a_3608_ = lean_nat_abs(v_val_3597_);
lean_dec(v_val_3597_);
v___x_3609_ = l_Nat_reprFast(v_a_3608_);
v___y_3550_ = v___x_3605_;
v___y_3551_ = v___x_3609_;
goto v___jp_3549_;
}
else
{
lean_object* v_abs_3610_; lean_object* v_one_3611_; lean_object* v_a_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v_abs_3610_ = lean_nat_abs(v_val_3597_);
lean_dec(v_val_3597_);
v_one_3611_ = lean_unsigned_to_nat(1u);
v_a_3612_ = lean_nat_sub(v_abs_3610_, v_one_3611_);
lean_dec(v_abs_3610_);
v___x_3613_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3614_ = lean_nat_add(v_a_3612_, v_one_3611_);
lean_dec(v_a_3612_);
v___x_3615_ = l_Nat_reprFast(v___x_3614_);
v___x_3616_ = lean_string_append(v___x_3613_, v___x_3615_);
lean_dec_ref(v___x_3615_);
v___y_3550_ = v___x_3605_;
v___y_3551_ = v___x_3616_;
goto v___jp_3549_;
}
}
}
else
{
lean_object* v___x_3628_; lean_object* v___y_3630_; lean_object* v_intZero_3635_; uint8_t v_isNeg_3636_; 
lean_dec(v_val_3597_);
v___x_3628_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3635_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3636_ = lean_int_dec_lt(v_val_3596_, v_intZero_3635_);
if (v_isNeg_3636_ == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3638_; 
v_a_3637_ = lean_nat_abs(v_val_3596_);
lean_dec(v_val_3596_);
v___x_3638_ = l_Nat_reprFast(v_a_3637_);
v___y_3630_ = v___x_3638_;
goto v___jp_3629_;
}
else
{
lean_object* v_abs_3639_; lean_object* v_one_3640_; lean_object* v_a_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v_abs_3639_ = lean_nat_abs(v_val_3596_);
lean_dec(v_val_3596_);
v_one_3640_ = lean_unsigned_to_nat(1u);
v_a_3641_ = lean_nat_sub(v_abs_3639_, v_one_3640_);
lean_dec(v_abs_3639_);
v___x_3642_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3643_ = lean_nat_add(v_a_3641_, v_one_3640_);
lean_dec(v_a_3641_);
v___x_3644_ = l_Nat_reprFast(v___x_3643_);
v___x_3645_ = lean_string_append(v___x_3642_, v___x_3644_);
lean_dec_ref(v___x_3644_);
v___y_3630_ = v___x_3645_;
goto v___jp_3629_;
}
v___jp_3629_:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3631_ = lean_string_append(v___x_3628_, v___y_3630_);
lean_dec_ref(v___y_3630_);
v___x_3632_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3633_ = lean_string_append(v___x_3631_, v___x_3632_);
v___x_3634_ = lean_string_append(v___x_3548_, v___x_3633_);
lean_dec_ref(v___x_3633_);
return v___x_3634_;
}
}
}
else
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
lean_dec(v_val_3597_);
lean_dec(v_val_3596_);
v___x_3646_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3647_ = lean_string_append(v___x_3548_, v___x_3646_);
return v___x_3647_;
}
}
}
v___jp_3549_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3552_ = lean_string_append(v___y_3550_, v___y_3551_);
lean_dec_ref(v___y_3551_);
v___x_3553_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3554_ = lean_string_append(v___x_3552_, v___x_3553_);
v___x_3555_ = lean_string_append(v___x_3548_, v___x_3554_);
lean_dec_ref(v___x_3554_);
return v___x_3555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1(lean_object* v___x_3648_, lean_object* v_x_3649_){
_start:
{
lean_object* v_fst_3650_; lean_object* v_constraint_3651_; lean_object* v_coeffs_3652_; lean_object* v_lowerBound_3653_; lean_object* v_upperBound_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___y_3659_; lean_object* v___y_3660_; 
v_fst_3650_ = lean_ctor_get(v_x_3649_, 0);
lean_inc(v_fst_3650_);
lean_dec_ref(v_x_3649_);
v_constraint_3651_ = lean_ctor_get(v_fst_3650_, 1);
lean_inc_ref(v_constraint_3651_);
v_coeffs_3652_ = lean_ctor_get(v_fst_3650_, 0);
lean_inc(v_coeffs_3652_);
lean_dec(v_fst_3650_);
v_lowerBound_3653_ = lean_ctor_get(v_constraint_3651_, 0);
lean_inc(v_lowerBound_3653_);
v_upperBound_3654_ = lean_ctor_get(v_constraint_3651_, 1);
lean_inc(v_upperBound_3654_);
lean_dec_ref(v_constraint_3651_);
v___x_3655_ = l_List_toString___redArg(v___x_3648_, v_coeffs_3652_);
v___x_3656_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3657_ = lean_string_append(v___x_3655_, v___x_3656_);
if (lean_obj_tag(v_lowerBound_3653_) == 0)
{
if (lean_obj_tag(v_upperBound_3654_) == 0)
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3666_ = lean_string_append(v___x_3657_, v___x_3665_);
return v___x_3666_;
}
else
{
lean_object* v_val_3667_; lean_object* v___x_3668_; lean_object* v___y_3670_; lean_object* v_intZero_3675_; uint8_t v_isNeg_3676_; 
v_val_3667_ = lean_ctor_get(v_upperBound_3654_, 0);
lean_inc(v_val_3667_);
lean_dec_ref(v_upperBound_3654_);
v___x_3668_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3675_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3676_ = lean_int_dec_lt(v_val_3667_, v_intZero_3675_);
if (v_isNeg_3676_ == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3678_; 
v_a_3677_ = lean_nat_abs(v_val_3667_);
lean_dec(v_val_3667_);
v___x_3678_ = l_Nat_reprFast(v_a_3677_);
v___y_3670_ = v___x_3678_;
goto v___jp_3669_;
}
else
{
lean_object* v_abs_3679_; lean_object* v_one_3680_; lean_object* v_a_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v_abs_3679_ = lean_nat_abs(v_val_3667_);
lean_dec(v_val_3667_);
v_one_3680_ = lean_unsigned_to_nat(1u);
v_a_3681_ = lean_nat_sub(v_abs_3679_, v_one_3680_);
lean_dec(v_abs_3679_);
v___x_3682_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3683_ = lean_nat_add(v_a_3681_, v_one_3680_);
lean_dec(v_a_3681_);
v___x_3684_ = l_Nat_reprFast(v___x_3683_);
v___x_3685_ = lean_string_append(v___x_3682_, v___x_3684_);
lean_dec_ref(v___x_3684_);
v___y_3670_ = v___x_3685_;
goto v___jp_3669_;
}
v___jp_3669_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3671_ = lean_string_append(v___x_3668_, v___y_3670_);
lean_dec_ref(v___y_3670_);
v___x_3672_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3673_ = lean_string_append(v___x_3671_, v___x_3672_);
v___x_3674_ = lean_string_append(v___x_3657_, v___x_3673_);
lean_dec_ref(v___x_3673_);
return v___x_3674_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3654_) == 0)
{
lean_object* v_val_3686_; lean_object* v___x_3687_; lean_object* v___y_3689_; lean_object* v_intZero_3694_; uint8_t v_isNeg_3695_; 
v_val_3686_ = lean_ctor_get(v_lowerBound_3653_, 0);
lean_inc(v_val_3686_);
lean_dec_ref(v_lowerBound_3653_);
v___x_3687_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3694_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3695_ = lean_int_dec_lt(v_val_3686_, v_intZero_3694_);
if (v_isNeg_3695_ == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3697_; 
v_a_3696_ = lean_nat_abs(v_val_3686_);
lean_dec(v_val_3686_);
v___x_3697_ = l_Nat_reprFast(v_a_3696_);
v___y_3689_ = v___x_3697_;
goto v___jp_3688_;
}
else
{
lean_object* v_abs_3698_; lean_object* v_one_3699_; lean_object* v_a_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v_abs_3698_ = lean_nat_abs(v_val_3686_);
lean_dec(v_val_3686_);
v_one_3699_ = lean_unsigned_to_nat(1u);
v_a_3700_ = lean_nat_sub(v_abs_3698_, v_one_3699_);
lean_dec(v_abs_3698_);
v___x_3701_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3702_ = lean_nat_add(v_a_3700_, v_one_3699_);
lean_dec(v_a_3700_);
v___x_3703_ = l_Nat_reprFast(v___x_3702_);
v___x_3704_ = lean_string_append(v___x_3701_, v___x_3703_);
lean_dec_ref(v___x_3703_);
v___y_3689_ = v___x_3704_;
goto v___jp_3688_;
}
v___jp_3688_:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3690_ = lean_string_append(v___x_3687_, v___y_3689_);
lean_dec_ref(v___y_3689_);
v___x_3691_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3692_ = lean_string_append(v___x_3690_, v___x_3691_);
v___x_3693_ = lean_string_append(v___x_3657_, v___x_3692_);
lean_dec_ref(v___x_3692_);
return v___x_3693_;
}
}
else
{
lean_object* v_val_3705_; lean_object* v_val_3706_; uint8_t v___x_3707_; 
v_val_3705_ = lean_ctor_get(v_lowerBound_3653_, 0);
lean_inc(v_val_3705_);
lean_dec_ref(v_lowerBound_3653_);
v_val_3706_ = lean_ctor_get(v_upperBound_3654_, 0);
lean_inc(v_val_3706_);
lean_dec_ref(v_upperBound_3654_);
v___x_3707_ = lean_int_dec_lt(v_val_3706_, v_val_3705_);
if (v___x_3707_ == 0)
{
uint8_t v___x_3708_; 
v___x_3708_ = lean_int_dec_eq(v_val_3705_, v_val_3706_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; lean_object* v___y_3711_; lean_object* v_intZero_3726_; uint8_t v_isNeg_3727_; 
v___x_3709_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3726_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3727_ = lean_int_dec_lt(v_val_3705_, v_intZero_3726_);
if (v_isNeg_3727_ == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; 
v_a_3728_ = lean_nat_abs(v_val_3705_);
lean_dec(v_val_3705_);
v___x_3729_ = l_Nat_reprFast(v_a_3728_);
v___y_3711_ = v___x_3729_;
goto v___jp_3710_;
}
else
{
lean_object* v_abs_3730_; lean_object* v_one_3731_; lean_object* v_a_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v_abs_3730_ = lean_nat_abs(v_val_3705_);
lean_dec(v_val_3705_);
v_one_3731_ = lean_unsigned_to_nat(1u);
v_a_3732_ = lean_nat_sub(v_abs_3730_, v_one_3731_);
lean_dec(v_abs_3730_);
v___x_3733_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3734_ = lean_nat_add(v_a_3732_, v_one_3731_);
lean_dec(v_a_3732_);
v___x_3735_ = l_Nat_reprFast(v___x_3734_);
v___x_3736_ = lean_string_append(v___x_3733_, v___x_3735_);
lean_dec_ref(v___x_3735_);
v___y_3711_ = v___x_3736_;
goto v___jp_3710_;
}
v___jp_3710_:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v_intZero_3715_; uint8_t v_isNeg_3716_; 
v___x_3712_ = lean_string_append(v___x_3709_, v___y_3711_);
lean_dec_ref(v___y_3711_);
v___x_3713_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3714_ = lean_string_append(v___x_3712_, v___x_3713_);
v_intZero_3715_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3716_ = lean_int_dec_lt(v_val_3706_, v_intZero_3715_);
if (v_isNeg_3716_ == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3718_; 
v_a_3717_ = lean_nat_abs(v_val_3706_);
lean_dec(v_val_3706_);
v___x_3718_ = l_Nat_reprFast(v_a_3717_);
v___y_3659_ = v___x_3714_;
v___y_3660_ = v___x_3718_;
goto v___jp_3658_;
}
else
{
lean_object* v_abs_3719_; lean_object* v_one_3720_; lean_object* v_a_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v_abs_3719_ = lean_nat_abs(v_val_3706_);
lean_dec(v_val_3706_);
v_one_3720_ = lean_unsigned_to_nat(1u);
v_a_3721_ = lean_nat_sub(v_abs_3719_, v_one_3720_);
lean_dec(v_abs_3719_);
v___x_3722_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3723_ = lean_nat_add(v_a_3721_, v_one_3720_);
lean_dec(v_a_3721_);
v___x_3724_ = l_Nat_reprFast(v___x_3723_);
v___x_3725_ = lean_string_append(v___x_3722_, v___x_3724_);
lean_dec_ref(v___x_3724_);
v___y_3659_ = v___x_3714_;
v___y_3660_ = v___x_3725_;
goto v___jp_3658_;
}
}
}
else
{
lean_object* v___x_3737_; lean_object* v___y_3739_; lean_object* v_intZero_3744_; uint8_t v_isNeg_3745_; 
lean_dec(v_val_3706_);
v___x_3737_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3744_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3745_ = lean_int_dec_lt(v_val_3705_, v_intZero_3744_);
if (v_isNeg_3745_ == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3747_; 
v_a_3746_ = lean_nat_abs(v_val_3705_);
lean_dec(v_val_3705_);
v___x_3747_ = l_Nat_reprFast(v_a_3746_);
v___y_3739_ = v___x_3747_;
goto v___jp_3738_;
}
else
{
lean_object* v_abs_3748_; lean_object* v_one_3749_; lean_object* v_a_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v_abs_3748_ = lean_nat_abs(v_val_3705_);
lean_dec(v_val_3705_);
v_one_3749_ = lean_unsigned_to_nat(1u);
v_a_3750_ = lean_nat_sub(v_abs_3748_, v_one_3749_);
lean_dec(v_abs_3748_);
v___x_3751_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3752_ = lean_nat_add(v_a_3750_, v_one_3749_);
lean_dec(v_a_3750_);
v___x_3753_ = l_Nat_reprFast(v___x_3752_);
v___x_3754_ = lean_string_append(v___x_3751_, v___x_3753_);
lean_dec_ref(v___x_3753_);
v___y_3739_ = v___x_3754_;
goto v___jp_3738_;
}
v___jp_3738_:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3740_ = lean_string_append(v___x_3737_, v___y_3739_);
lean_dec_ref(v___y_3739_);
v___x_3741_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3742_ = lean_string_append(v___x_3740_, v___x_3741_);
v___x_3743_ = lean_string_append(v___x_3657_, v___x_3742_);
lean_dec_ref(v___x_3742_);
return v___x_3743_;
}
}
}
else
{
lean_object* v___x_3755_; lean_object* v___x_3756_; 
lean_dec(v_val_3706_);
lean_dec(v_val_3705_);
v___x_3755_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3756_ = lean_string_append(v___x_3657_, v___x_3755_);
return v___x_3756_;
}
}
}
v___jp_3658_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3661_ = lean_string_append(v___y_3659_, v___y_3660_);
lean_dec_ref(v___y_3660_);
v___x_3662_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3663_ = lean_string_append(v___x_3661_, v___x_3662_);
v___x_3664_ = lean_string_append(v___x_3657_, v___x_3663_);
lean_dec_ref(v___x_3663_);
return v___x_3664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2(lean_object* v___f_3761_, lean_object* v___f_3762_, lean_object* v___f_3763_, lean_object* v_d_3764_){
_start:
{
lean_object* v_var_3765_; lean_object* v_irrelevant_3766_; lean_object* v_lowerBounds_3767_; lean_object* v_upperBounds_3768_; lean_object* v___x_3769_; lean_object* v_irrelevant_3770_; lean_object* v_lowerBounds_3771_; lean_object* v_upperBounds_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v_var_3765_ = lean_ctor_get(v_d_3764_, 0);
lean_inc(v_var_3765_);
v_irrelevant_3766_ = lean_ctor_get(v_d_3764_, 1);
lean_inc(v_irrelevant_3766_);
v_lowerBounds_3767_ = lean_ctor_get(v_d_3764_, 2);
lean_inc(v_lowerBounds_3767_);
v_upperBounds_3768_ = lean_ctor_get(v_d_3764_, 3);
lean_inc(v_upperBounds_3768_);
lean_dec_ref(v_d_3764_);
v___x_3769_ = lean_box(0);
v_irrelevant_3770_ = l_List_mapTR_loop___redArg(v___f_3761_, v_irrelevant_3766_, v___x_3769_);
lean_inc_ref(v___f_3762_);
v_lowerBounds_3771_ = l_List_mapTR_loop___redArg(v___f_3762_, v_lowerBounds_3767_, v___x_3769_);
v_upperBounds_3772_ = l_List_mapTR_loop___redArg(v___f_3762_, v_upperBounds_3768_, v___x_3769_);
v___x_3773_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0));
v___x_3774_ = l_Nat_reprFast(v_var_3765_);
v___x_3775_ = lean_string_append(v___x_3773_, v___x_3774_);
lean_dec_ref(v___x_3774_);
v___x_3776_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_3777_ = lean_string_append(v___x_3775_, v___x_3776_);
v___x_3778_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1));
lean_inc_ref_n(v___f_3763_, 2);
v___x_3779_ = l_List_toString___redArg(v___f_3763_, v_irrelevant_3770_);
v___x_3780_ = lean_string_append(v___x_3778_, v___x_3779_);
lean_dec_ref(v___x_3779_);
v___x_3781_ = lean_string_append(v___x_3780_, v___x_3776_);
v___x_3782_ = lean_string_append(v___x_3777_, v___x_3781_);
lean_dec_ref(v___x_3781_);
v___x_3783_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2));
v___x_3784_ = l_List_toString___redArg(v___f_3763_, v_lowerBounds_3771_);
v___x_3785_ = lean_string_append(v___x_3783_, v___x_3784_);
lean_dec_ref(v___x_3784_);
v___x_3786_ = lean_string_append(v___x_3785_, v___x_3776_);
v___x_3787_ = lean_string_append(v___x_3782_, v___x_3786_);
lean_dec_ref(v___x_3786_);
v___x_3788_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3));
v___x_3789_ = l_List_toString___redArg(v___f_3763_, v_upperBounds_3772_);
v___x_3790_ = lean_string_append(v___x_3788_, v___x_3789_);
lean_dec_ref(v___x_3789_);
v___x_3791_ = lean_string_append(v___x_3787_, v___x_3790_);
lean_dec_ref(v___x_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(lean_object* v_d_3802_){
_start:
{
lean_object* v_lowerBounds_3803_; lean_object* v_upperBounds_3804_; uint8_t v___x_3805_; 
v_lowerBounds_3803_ = lean_ctor_get(v_d_3802_, 2);
v_upperBounds_3804_ = lean_ctor_get(v_d_3802_, 3);
v___x_3805_ = l_List_isEmpty___redArg(v_lowerBounds_3803_);
if (v___x_3805_ == 0)
{
return v___x_3805_;
}
else
{
uint8_t v___x_3806_; 
v___x_3806_ = l_List_isEmpty___redArg(v_upperBounds_3804_);
return v___x_3806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty___boxed(lean_object* v_d_3807_){
_start:
{
uint8_t v_res_3808_; lean_object* v_r_3809_; 
v_res_3808_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v_d_3807_);
lean_dec_ref(v_d_3807_);
v_r_3809_ = lean_box(v_res_3808_);
return v_r_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(lean_object* v_d_3810_){
_start:
{
lean_object* v_lowerBounds_3811_; lean_object* v_upperBounds_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v_lowerBounds_3811_ = lean_ctor_get(v_d_3810_, 2);
v_upperBounds_3812_ = lean_ctor_get(v_d_3810_, 3);
v___x_3813_ = l_List_lengthTR___redArg(v_lowerBounds_3811_);
v___x_3814_ = l_List_lengthTR___redArg(v_upperBounds_3812_);
v___x_3815_ = lean_nat_mul(v___x_3813_, v___x_3814_);
lean_dec(v___x_3814_);
lean_dec(v___x_3813_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size___boxed(lean_object* v_d_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_d_3816_);
lean_dec_ref(v_d_3816_);
return v_res_3817_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(lean_object* v_d_3818_){
_start:
{
uint8_t v_lowerExact_3819_; 
v_lowerExact_3819_ = lean_ctor_get_uint8(v_d_3818_, sizeof(void*)*4);
if (v_lowerExact_3819_ == 0)
{
uint8_t v_upperExact_3820_; 
v_upperExact_3820_ = lean_ctor_get_uint8(v_d_3818_, sizeof(void*)*4 + 1);
return v_upperExact_3820_;
}
else
{
return v_lowerExact_3819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact___boxed(lean_object* v_d_3821_){
_start:
{
uint8_t v_res_3822_; lean_object* v_r_3823_; 
v_res_3822_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_d_3821_);
lean_dec_ref(v_d_3821_);
v_r_3823_ = lean_box(v_res_3822_);
return v_r_3823_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(lean_object* v_x_3824_, lean_object* v_x_3825_){
_start:
{
if (lean_obj_tag(v_x_3825_) == 0)
{
return v_x_3824_;
}
else
{
lean_object* v_head_3826_; lean_object* v_tail_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v_head_3826_ = lean_ctor_get(v_x_3825_, 0);
v_tail_3827_ = lean_ctor_get(v_x_3825_, 1);
v___x_3828_ = lean_box(0);
v___x_3829_ = 1;
lean_inc(v_head_3826_);
v___x_3830_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3830_, 0, v_head_3826_);
lean_ctor_set(v___x_3830_, 1, v___x_3828_);
lean_ctor_set(v___x_3830_, 2, v___x_3828_);
lean_ctor_set(v___x_3830_, 3, v___x_3828_);
lean_ctor_set_uint8(v___x_3830_, sizeof(void*)*4, v___x_3829_);
lean_ctor_set_uint8(v___x_3830_, sizeof(void*)*4 + 1, v___x_3829_);
v___x_3831_ = lean_array_push(v_x_3824_, v___x_3830_);
v_x_3824_ = v___x_3831_;
v_x_3825_ = v_tail_3827_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2___boxed(lean_object* v_x_3833_, lean_object* v_x_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v_x_3833_, v_x_3834_);
lean_dec(v_x_3834_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object* v___x_3836_, lean_object* v_b_3837_, lean_object* v___x_3838_, lean_object* v_____r_3839_, lean_object* v_d_x27_3840_){
_start:
{
lean_object* v_upperBound_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3868_; 
v_upperBound_3841_ = lean_ctor_get(v___x_3836_, 1);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3868_ == 0)
{
lean_object* v_unused_3869_; 
v_unused_3869_ = lean_ctor_get(v___x_3836_, 0);
lean_dec(v_unused_3869_);
v___x_3843_ = v___x_3836_;
v_isShared_3844_ = v_isSharedCheck_3868_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_upperBound_3841_);
lean_dec(v___x_3836_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3868_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
if (lean_obj_tag(v_upperBound_3841_) == 0)
{
lean_del_object(v___x_3843_);
lean_dec(v___x_3838_);
lean_dec_ref(v_b_3837_);
return v_d_x27_3840_;
}
else
{
lean_object* v_var_3845_; lean_object* v_irrelevant_3846_; lean_object* v_lowerBounds_3847_; lean_object* v_upperBounds_3848_; uint8_t v_lowerExact_3849_; uint8_t v_upperExact_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3867_; 
lean_dec_ref(v_upperBound_3841_);
v_var_3845_ = lean_ctor_get(v_d_x27_3840_, 0);
v_irrelevant_3846_ = lean_ctor_get(v_d_x27_3840_, 1);
v_lowerBounds_3847_ = lean_ctor_get(v_d_x27_3840_, 2);
v_upperBounds_3848_ = lean_ctor_get(v_d_x27_3840_, 3);
v_lowerExact_3849_ = lean_ctor_get_uint8(v_d_x27_3840_, sizeof(void*)*4);
v_upperExact_3850_ = lean_ctor_get_uint8(v_d_x27_3840_, sizeof(void*)*4 + 1);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_d_x27_3840_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3852_ = v_d_x27_3840_;
v_isShared_3853_ = v_isSharedCheck_3867_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_upperBounds_3848_);
lean_inc(v_lowerBounds_3847_);
lean_inc(v_irrelevant_3846_);
lean_inc(v_var_3845_);
lean_dec(v_d_x27_3840_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3867_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
lean_inc(v___x_3838_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 1, v___x_3838_);
lean_ctor_set(v___x_3843_, 0, v_b_3837_);
v___x_3855_ = v___x_3843_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_b_3837_);
lean_ctor_set(v_reuseFailAlloc_3866_, 1, v___x_3838_);
v___x_3855_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3856_; 
v___x_3856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3855_);
lean_ctor_set(v___x_3856_, 1, v_upperBounds_3848_);
if (v_upperExact_3850_ == 0)
{
lean_object* v___x_3858_; 
lean_dec(v___x_3838_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 3, v___x_3856_);
v___x_3858_ = v___x_3852_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_var_3845_);
lean_ctor_set(v_reuseFailAlloc_3859_, 1, v_irrelevant_3846_);
lean_ctor_set(v_reuseFailAlloc_3859_, 2, v_lowerBounds_3847_);
lean_ctor_set(v_reuseFailAlloc_3859_, 3, v___x_3856_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, sizeof(void*)*4, v_lowerExact_3849_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, sizeof(void*)*4 + 1, v_upperExact_3850_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
else
{
lean_object* v___x_3860_; lean_object* v___x_3861_; uint8_t v___x_3862_; lean_object* v___x_3864_; 
v___x_3860_ = lean_nat_abs(v___x_3838_);
lean_dec(v___x_3838_);
v___x_3861_ = lean_unsigned_to_nat(1u);
v___x_3862_ = lean_nat_dec_eq(v___x_3860_, v___x_3861_);
lean_dec(v___x_3860_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 3, v___x_3856_);
v___x_3864_ = v___x_3852_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_var_3845_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_irrelevant_3846_);
lean_ctor_set(v_reuseFailAlloc_3865_, 2, v_lowerBounds_3847_);
lean_ctor_set(v_reuseFailAlloc_3865_, 3, v___x_3856_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, sizeof(void*)*4, v_lowerExact_3849_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
lean_ctor_set_uint8(v___x_3864_, sizeof(void*)*4 + 1, v___x_3862_);
return v___x_3864_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(lean_object* v_upperBound_3870_, lean_object* v_coeffs_3871_, lean_object* v_constraint_3872_, lean_object* v_b_3873_, lean_object* v_a_3874_, lean_object* v_b_3875_){
_start:
{
lean_object* v_a_3877_; uint8_t v___x_3881_; 
v___x_3881_ = lean_nat_dec_lt(v_a_3874_, v_upperBound_3870_);
if (v___x_3881_ == 0)
{
lean_dec(v_a_3874_);
lean_dec_ref(v_b_3873_);
lean_dec_ref(v_constraint_3872_);
return v_b_3875_;
}
else
{
lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3882_ = lean_array_get_size(v_b_3875_);
v___x_3883_ = lean_nat_dec_lt(v_a_3874_, v___x_3882_);
if (v___x_3883_ == 0)
{
v_a_3877_ = v_b_3875_;
goto v___jp_3876_;
}
else
{
lean_object* v___x_3884_; lean_object* v_v_3885_; lean_object* v___x_3886_; lean_object* v_xs_x27_3887_; lean_object* v___y_3889_; lean_object* v___x_3891_; uint8_t v___x_3892_; 
lean_inc(v_a_3874_);
v___x_3884_ = l_Lean_Omega_IntList_get(v_coeffs_3871_, v_a_3874_);
v_v_3885_ = lean_array_fget(v_b_3875_, v_a_3874_);
v___x_3886_ = lean_box(0);
v_xs_x27_3887_ = lean_array_fset(v_b_3875_, v_a_3874_, v___x_3886_);
v___x_3891_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3892_ = lean_int_dec_eq(v___x_3884_, v___x_3891_);
if (v___x_3892_ == 0)
{
lean_object* v___x_3893_; lean_object* v_lowerBound_3894_; 
lean_inc_ref(v_constraint_3872_);
lean_inc(v___x_3884_);
v___x_3893_ = l_Lean_Omega_Constraint_scale(v___x_3884_, v_constraint_3872_);
v_lowerBound_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_lowerBound_3894_);
if (lean_obj_tag(v_lowerBound_3894_) == 0)
{
lean_object* v___x_3895_; 
lean_inc_ref(v_b_3873_);
v___x_3895_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3893_, v_b_3873_, v___x_3884_, v___x_3886_, v_v_3885_);
v___y_3889_ = v___x_3895_;
goto v___jp_3888_;
}
else
{
lean_object* v_var_3896_; lean_object* v_irrelevant_3897_; lean_object* v_lowerBounds_3898_; lean_object* v_upperBounds_3899_; uint8_t v_lowerExact_3900_; uint8_t v_upperExact_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3916_; 
lean_dec_ref(v_lowerBound_3894_);
v_var_3896_ = lean_ctor_get(v_v_3885_, 0);
v_irrelevant_3897_ = lean_ctor_get(v_v_3885_, 1);
v_lowerBounds_3898_ = lean_ctor_get(v_v_3885_, 2);
v_upperBounds_3899_ = lean_ctor_get(v_v_3885_, 3);
v_lowerExact_3900_ = lean_ctor_get_uint8(v_v_3885_, sizeof(void*)*4);
v_upperExact_3901_ = lean_ctor_get_uint8(v_v_3885_, sizeof(void*)*4 + 1);
v_isSharedCheck_3916_ = !lean_is_exclusive(v_v_3885_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3903_ = v_v_3885_;
v_isShared_3904_ = v_isSharedCheck_3916_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_upperBounds_3899_);
lean_inc(v_lowerBounds_3898_);
lean_inc(v_irrelevant_3897_);
lean_inc(v_var_3896_);
lean_dec(v_v_3885_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3916_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; uint8_t v___y_3908_; 
lean_inc(v___x_3884_);
lean_inc_ref(v_b_3873_);
v___x_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3905_, 0, v_b_3873_);
lean_ctor_set(v___x_3905_, 1, v___x_3884_);
v___x_3906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
lean_ctor_set(v___x_3906_, 1, v_lowerBounds_3898_);
if (v_lowerExact_3900_ == 0)
{
v___y_3908_ = v_lowerExact_3900_;
goto v___jp_3907_;
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3914_; uint8_t v___x_3915_; 
v___x_3913_ = lean_nat_abs(v___x_3884_);
v___x_3914_ = lean_unsigned_to_nat(1u);
v___x_3915_ = lean_nat_dec_eq(v___x_3913_, v___x_3914_);
lean_dec(v___x_3913_);
v___y_3908_ = v___x_3915_;
goto v___jp_3907_;
}
v___jp_3907_:
{
lean_object* v___x_3910_; 
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 2, v___x_3906_);
v___x_3910_ = v___x_3903_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_var_3896_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v_irrelevant_3897_);
lean_ctor_set(v_reuseFailAlloc_3912_, 2, v___x_3906_);
lean_ctor_set(v_reuseFailAlloc_3912_, 3, v_upperBounds_3899_);
lean_ctor_set_uint8(v_reuseFailAlloc_3912_, sizeof(void*)*4 + 1, v_upperExact_3901_);
v___x_3910_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
lean_object* v___x_3911_; 
lean_ctor_set_uint8(v___x_3910_, sizeof(void*)*4, v___y_3908_);
lean_inc_ref(v_b_3873_);
v___x_3911_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3893_, v_b_3873_, v___x_3884_, v___x_3886_, v___x_3910_);
v___y_3889_ = v___x_3911_;
goto v___jp_3888_;
}
}
}
}
}
else
{
lean_object* v_var_3917_; lean_object* v_irrelevant_3918_; lean_object* v_lowerBounds_3919_; lean_object* v_upperBounds_3920_; uint8_t v_lowerExact_3921_; uint8_t v_upperExact_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3930_; 
lean_dec(v___x_3884_);
v_var_3917_ = lean_ctor_get(v_v_3885_, 0);
v_irrelevant_3918_ = lean_ctor_get(v_v_3885_, 1);
v_lowerBounds_3919_ = lean_ctor_get(v_v_3885_, 2);
v_upperBounds_3920_ = lean_ctor_get(v_v_3885_, 3);
v_lowerExact_3921_ = lean_ctor_get_uint8(v_v_3885_, sizeof(void*)*4);
v_upperExact_3922_ = lean_ctor_get_uint8(v_v_3885_, sizeof(void*)*4 + 1);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_v_3885_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3924_ = v_v_3885_;
v_isShared_3925_ = v_isSharedCheck_3930_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_upperBounds_3920_);
lean_inc(v_lowerBounds_3919_);
lean_inc(v_irrelevant_3918_);
lean_inc(v_var_3917_);
lean_dec(v_v_3885_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3930_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3926_; lean_object* v___x_3928_; 
lean_inc_ref(v_b_3873_);
v___x_3926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3926_, 0, v_b_3873_);
lean_ctor_set(v___x_3926_, 1, v_irrelevant_3918_);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 1, v___x_3926_);
v___x_3928_ = v___x_3924_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_var_3917_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3929_, 2, v_lowerBounds_3919_);
lean_ctor_set(v_reuseFailAlloc_3929_, 3, v_upperBounds_3920_);
lean_ctor_set_uint8(v_reuseFailAlloc_3929_, sizeof(void*)*4, v_lowerExact_3921_);
lean_ctor_set_uint8(v_reuseFailAlloc_3929_, sizeof(void*)*4 + 1, v_upperExact_3922_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
v___y_3889_ = v___x_3928_;
goto v___jp_3888_;
}
}
}
v___jp_3888_:
{
lean_object* v___x_3890_; 
v___x_3890_ = lean_array_fset(v_xs_x27_3887_, v_a_3874_, v___y_3889_);
v_a_3877_ = v___x_3890_;
goto v___jp_3876_;
}
}
}
v___jp_3876_:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = lean_unsigned_to_nat(1u);
v___x_3879_ = lean_nat_add(v_a_3874_, v___x_3878_);
lean_dec(v_a_3874_);
v_a_3874_ = v___x_3879_;
v_b_3875_ = v_a_3877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___boxed(lean_object* v_upperBound_3931_, lean_object* v_coeffs_3932_, lean_object* v_constraint_3933_, lean_object* v_b_3934_, lean_object* v_a_3935_, lean_object* v_b_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3931_, v_coeffs_3932_, v_constraint_3933_, v_b_3934_, v_a_3935_, v_b_3936_);
lean_dec(v_coeffs_3932_);
lean_dec(v_upperBound_3931_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(lean_object* v_n_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_){
_start:
{
if (lean_obj_tag(v_a_3939_) == 0)
{
lean_object* v___x_3941_; 
v___x_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3941_, 0, v_a_3940_);
return v___x_3941_;
}
else
{
lean_object* v_value_3942_; lean_object* v_tail_3943_; lean_object* v_coeffs_3944_; lean_object* v_constraint_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v_value_3942_ = lean_ctor_get(v_a_3939_, 1);
lean_inc(v_value_3942_);
v_tail_3943_ = lean_ctor_get(v_a_3939_, 2);
lean_inc(v_tail_3943_);
lean_dec_ref(v_a_3939_);
v_coeffs_3944_ = lean_ctor_get(v_value_3942_, 0);
lean_inc(v_coeffs_3944_);
v_constraint_3945_ = lean_ctor_get(v_value_3942_, 1);
lean_inc_ref(v_constraint_3945_);
v___x_3946_ = lean_unsigned_to_nat(0u);
v___x_3947_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_n_3938_, v_coeffs_3944_, v_constraint_3945_, v_value_3942_, v___x_3946_, v_a_3940_);
lean_dec(v_coeffs_3944_);
v_a_3939_ = v_tail_3943_;
v_a_3940_ = v___x_3947_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1___boxed(lean_object* v_n_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3949_, v_a_3950_, v_a_3951_);
lean_dec(v_n_3949_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(lean_object* v_n_3953_, lean_object* v_as_3954_, size_t v_sz_3955_, size_t v_i_3956_, lean_object* v_b_3957_){
_start:
{
uint8_t v___x_3958_; 
v___x_3958_ = lean_usize_dec_lt(v_i_3956_, v_sz_3955_);
if (v___x_3958_ == 0)
{
return v_b_3957_;
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3960_; 
v_a_3959_ = lean_array_uget_borrowed(v_as_3954_, v_i_3956_);
lean_inc(v_a_3959_);
v___x_3960_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3953_, v_a_3959_, v_b_3957_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref(v___x_3960_);
return v_a_3961_;
}
else
{
lean_object* v_a_3962_; size_t v___x_3963_; size_t v___x_3964_; 
v_a_3962_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3962_);
lean_dec_ref(v___x_3960_);
v___x_3963_ = ((size_t)1ULL);
v___x_3964_ = lean_usize_add(v_i_3956_, v___x_3963_);
v_i_3956_ = v___x_3964_;
v_b_3957_ = v_a_3962_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3___boxed(lean_object* v_n_3966_, lean_object* v_as_3967_, lean_object* v_sz_3968_, lean_object* v_i_3969_, lean_object* v_b_3970_){
_start:
{
size_t v_sz_boxed_3971_; size_t v_i_boxed_3972_; lean_object* v_res_3973_; 
v_sz_boxed_3971_ = lean_unbox_usize(v_sz_3968_);
lean_dec(v_sz_3968_);
v_i_boxed_3972_ = lean_unbox_usize(v_i_3969_);
lean_dec(v_i_3969_);
v_res_3973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_n_3966_, v_as_3967_, v_sz_boxed_3971_, v_i_boxed_3972_, v_b_3970_);
lean_dec_ref(v_as_3967_);
lean_dec(v_n_3966_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(lean_object* v_p_3976_){
_start:
{
lean_object* v_constraints_3977_; lean_object* v_numVars_3978_; lean_object* v_buckets_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v_data_3982_; size_t v_sz_3983_; size_t v___x_3984_; lean_object* v___x_3985_; 
v_constraints_3977_ = lean_ctor_get(v_p_3976_, 2);
lean_inc_ref(v_constraints_3977_);
v_numVars_3978_ = lean_ctor_get(v_p_3976_, 1);
lean_inc_n(v_numVars_3978_, 2);
lean_dec_ref(v_p_3976_);
v_buckets_3979_ = lean_ctor_get(v_constraints_3977_, 1);
lean_inc_ref(v_buckets_3979_);
lean_dec_ref(v_constraints_3977_);
v___x_3980_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_3981_ = l_List_range(v_numVars_3978_);
v_data_3982_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v___x_3980_, v___x_3981_);
lean_dec(v___x_3981_);
v_sz_3983_ = lean_array_size(v_buckets_3979_);
v___x_3984_ = ((size_t)0ULL);
v___x_3985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_numVars_3978_, v_buckets_3979_, v_sz_3983_, v___x_3984_, v_data_3982_);
lean_dec_ref(v_buckets_3979_);
lean_dec(v_numVars_3978_);
return v___x_3985_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(lean_object* v_upperBound_3986_, lean_object* v_coeffs_3987_, lean_object* v_constraint_3988_, lean_object* v_b_3989_, lean_object* v_inst_3990_, lean_object* v_R_3991_, lean_object* v_a_3992_, lean_object* v_b_3993_, lean_object* v_c_3994_){
_start:
{
lean_object* v___x_3995_; 
v___x_3995_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3986_, v_coeffs_3987_, v_constraint_3988_, v_b_3989_, v_a_3992_, v_b_3993_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___boxed(lean_object* v_upperBound_3996_, lean_object* v_coeffs_3997_, lean_object* v_constraint_3998_, lean_object* v_b_3999_, lean_object* v_inst_4000_, lean_object* v_R_4001_, lean_object* v_a_4002_, lean_object* v_b_4003_, lean_object* v_c_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(v_upperBound_3996_, v_coeffs_3997_, v_constraint_3998_, v_b_3999_, v_inst_4000_, v_R_4001_, v_a_4002_, v_b_4003_, v_c_4004_);
lean_dec(v_coeffs_3997_);
lean_dec(v_upperBound_3996_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(lean_object* v_cls_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v_options_4015_; uint8_t v_hasTrace_4016_; 
v_options_4015_ = lean_ctor_get(v___y_4012_, 2);
v_hasTrace_4016_ = lean_ctor_get_uint8(v_options_4015_, sizeof(void*)*1);
if (v_hasTrace_4016_ == 0)
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
lean_dec(v_cls_4009_);
v___x_4017_ = lean_box(v_hasTrace_4016_);
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
return v___x_4018_;
}
else
{
lean_object* v_inheritedTraceOptions_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; uint8_t v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v_inheritedTraceOptions_4019_ = lean_ctor_get(v___y_4012_, 13);
v___x_4020_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4021_ = l_Lean_Name_append(v___x_4020_, v_cls_4009_);
v___x_4022_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4019_, v_options_4015_, v___x_4021_);
lean_dec(v___x_4021_);
v___x_4023_ = lean_box(v___x_4022_);
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
return v___x_4024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___boxed(lean_object* v_cls_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(lean_object* v___x_4032_, lean_object* v_fst_4033_, lean_object* v_snd_4034_, lean_object* v_fst_4035_, lean_object* v_____r_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4032_);
v___x_4043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4043_, 0, v_fst_4033_);
lean_ctor_set(v___x_4043_, 1, v_snd_4034_);
v___x_4044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4044_, 0, v_fst_4035_);
lean_ctor_set(v___x_4044_, 1, v___x_4043_);
v___x_4045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4042_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0___boxed(lean_object* v___x_4048_, lean_object* v_fst_4049_, lean_object* v_snd_4050_, lean_object* v_fst_4051_, lean_object* v_____r_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4048_, v_fst_4049_, v_snd_4050_, v_fst_4051_, v_____r_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
return v_res_4058_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4059_; double v___x_4060_; 
v___x_4059_ = lean_unsigned_to_nat(0u);
v___x_4060_ = lean_float_of_nat(v___x_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(lean_object* v_cls_4063_, lean_object* v_msg_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v_ref_4070_; lean_object* v___x_4071_; lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4116_; 
v_ref_4070_ = lean_ctor_get(v___y_4067_, 5);
v___x_4071_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4074_ = v___x_4071_;
v_isShared_4075_ = v_isSharedCheck_4116_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v___x_4071_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4116_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4076_; lean_object* v_traceState_4077_; lean_object* v_env_4078_; lean_object* v_nextMacroScope_4079_; lean_object* v_ngen_4080_; lean_object* v_auxDeclNGen_4081_; lean_object* v_cache_4082_; lean_object* v_messages_4083_; lean_object* v_infoState_4084_; lean_object* v_snapshotTasks_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4115_; 
v___x_4076_ = lean_st_ref_take(v___y_4068_);
v_traceState_4077_ = lean_ctor_get(v___x_4076_, 4);
v_env_4078_ = lean_ctor_get(v___x_4076_, 0);
v_nextMacroScope_4079_ = lean_ctor_get(v___x_4076_, 1);
v_ngen_4080_ = lean_ctor_get(v___x_4076_, 2);
v_auxDeclNGen_4081_ = lean_ctor_get(v___x_4076_, 3);
v_cache_4082_ = lean_ctor_get(v___x_4076_, 5);
v_messages_4083_ = lean_ctor_get(v___x_4076_, 6);
v_infoState_4084_ = lean_ctor_get(v___x_4076_, 7);
v_snapshotTasks_4085_ = lean_ctor_get(v___x_4076_, 8);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4087_ = v___x_4076_;
v_isShared_4088_ = v_isSharedCheck_4115_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_snapshotTasks_4085_);
lean_inc(v_infoState_4084_);
lean_inc(v_messages_4083_);
lean_inc(v_cache_4082_);
lean_inc(v_traceState_4077_);
lean_inc(v_auxDeclNGen_4081_);
lean_inc(v_ngen_4080_);
lean_inc(v_nextMacroScope_4079_);
lean_inc(v_env_4078_);
lean_dec(v___x_4076_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4115_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
uint64_t v_tid_4089_; lean_object* v_traces_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4114_; 
v_tid_4089_ = lean_ctor_get_uint64(v_traceState_4077_, sizeof(void*)*1);
v_traces_4090_ = lean_ctor_get(v_traceState_4077_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v_traceState_4077_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4092_ = v_traceState_4077_;
v_isShared_4093_ = v_isSharedCheck_4114_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_traces_4090_);
lean_dec(v_traceState_4077_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4114_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4094_; double v___x_4095_; uint8_t v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4104_; 
v___x_4094_ = lean_box(0);
v___x_4095_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4096_ = 0;
v___x_4097_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4098_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4098_, 0, v_cls_4063_);
lean_ctor_set(v___x_4098_, 1, v___x_4094_);
lean_ctor_set(v___x_4098_, 2, v___x_4097_);
lean_ctor_set_float(v___x_4098_, sizeof(void*)*3, v___x_4095_);
lean_ctor_set_float(v___x_4098_, sizeof(void*)*3 + 8, v___x_4095_);
lean_ctor_set_uint8(v___x_4098_, sizeof(void*)*3 + 16, v___x_4096_);
v___x_4099_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4100_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4098_);
lean_ctor_set(v___x_4100_, 1, v_a_4072_);
lean_ctor_set(v___x_4100_, 2, v___x_4099_);
lean_inc(v_ref_4070_);
v___x_4101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4101_, 0, v_ref_4070_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = l_Lean_PersistentArray_push___redArg(v_traces_4090_, v___x_4101_);
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 0, v___x_4102_);
v___x_4104_ = v___x_4092_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4102_);
lean_ctor_set_uint64(v_reuseFailAlloc_4113_, sizeof(void*)*1, v_tid_4089_);
v___x_4104_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_object* v___x_4106_; 
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 4, v___x_4104_);
v___x_4106_ = v___x_4087_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_env_4078_);
lean_ctor_set(v_reuseFailAlloc_4112_, 1, v_nextMacroScope_4079_);
lean_ctor_set(v_reuseFailAlloc_4112_, 2, v_ngen_4080_);
lean_ctor_set(v_reuseFailAlloc_4112_, 3, v_auxDeclNGen_4081_);
lean_ctor_set(v_reuseFailAlloc_4112_, 4, v___x_4104_);
lean_ctor_set(v_reuseFailAlloc_4112_, 5, v_cache_4082_);
lean_ctor_set(v_reuseFailAlloc_4112_, 6, v_messages_4083_);
lean_ctor_set(v_reuseFailAlloc_4112_, 7, v_infoState_4084_);
lean_ctor_set(v_reuseFailAlloc_4112_, 8, v_snapshotTasks_4085_);
v___x_4106_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4110_; 
v___x_4107_ = lean_st_ref_set(v___y_4068_, v___x_4106_);
v___x_4108_ = lean_box(0);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 0, v___x_4108_);
v___x_4110_ = v___x_4074_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4108_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___boxed(lean_object* v_cls_4117_, lean_object* v_msg_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4117_, v_msg_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
return v_res_4124_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v_cls_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v_cls_4125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4126_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4127_ = l_Lean_Name_append(v___x_4126_, v_cls_4125_);
return v___x_4127_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4129_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__1));
v___x_4130_ = l_Lean_stringToMessageData(v___x_4129_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(lean_object* v_upperBound_4131_, lean_object* v___y_4132_, lean_object* v_a_4133_, lean_object* v_b_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v_a_4141_; lean_object* v___y_4146_; uint8_t v___x_4165_; 
v___x_4165_ = lean_nat_dec_lt(v_a_4133_, v_upperBound_4131_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; 
lean_dec(v_a_4133_);
v___x_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4166_, 0, v_b_4134_);
return v___x_4166_;
}
else
{
lean_object* v_snd_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4237_; 
v_snd_4167_ = lean_ctor_get(v_b_4134_, 1);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_b_4134_);
if (v_isSharedCheck_4237_ == 0)
{
lean_object* v_unused_4238_; 
v_unused_4238_ = lean_ctor_get(v_b_4134_, 0);
lean_dec(v_unused_4238_);
v___x_4169_ = v_b_4134_;
v_isShared_4170_ = v_isSharedCheck_4237_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_snd_4167_);
lean_dec(v_b_4134_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4237_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v_snd_4171_; lean_object* v_fst_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4236_; 
v_snd_4171_ = lean_ctor_get(v_snd_4167_, 1);
v_fst_4172_ = lean_ctor_get(v_snd_4167_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v_snd_4167_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4174_ = v_snd_4167_;
v_isShared_4175_ = v_isSharedCheck_4236_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_snd_4171_);
lean_inc(v_fst_4172_);
lean_dec(v_snd_4167_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4236_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v_fst_4176_; lean_object* v_snd_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4235_; 
v_fst_4176_ = lean_ctor_get(v_snd_4171_, 0);
v_snd_4177_ = lean_ctor_get(v_snd_4171_, 1);
v_isSharedCheck_4235_ = !lean_is_exclusive(v_snd_4171_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4179_ = v_snd_4171_;
v_isShared_4180_ = v_isSharedCheck_4235_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_snd_4177_);
lean_inc(v_fst_4176_);
lean_dec(v_snd_4171_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4235_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v_bestIdx_4181_; lean_object* v___x_4182_; lean_object* v_cls_4193_; lean_object* v___x_4194_; uint8_t v___x_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; uint8_t v___y_4229_; uint8_t v___y_4232_; 
v_bestIdx_4181_ = lean_unsigned_to_nat(0u);
v___x_4182_ = lean_box(0);
v_cls_4193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4194_ = lean_array_fget_borrowed(v___y_4132_, v_a_4133_);
v___x_4198_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4194_);
v___x_4199_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4194_);
v___x_4200_ = lean_nat_dec_eq(v___x_4199_, v_bestIdx_4181_);
if (v___x_4200_ == 0)
{
uint8_t v___x_4234_; 
v___x_4234_ = lean_unbox(v_snd_4177_);
if (v___x_4234_ == 0)
{
v___y_4232_ = v___x_4198_;
goto v___jp_4231_;
}
else
{
if (v___x_4200_ == 0)
{
v___y_4232_ = v___x_4200_;
goto v___jp_4231_;
}
else
{
v___y_4232_ = v___x_4198_;
goto v___jp_4231_;
}
}
}
else
{
v___y_4232_ = v___x_4200_;
goto v___jp_4231_;
}
v___jp_4183_:
{
lean_object* v___x_4185_; 
if (v_isShared_4180_ == 0)
{
v___x_4185_ = v___x_4179_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_fst_4176_);
lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_snd_4177_);
v___x_4185_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
lean_object* v___x_4187_; 
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 1, v___x_4185_);
v___x_4187_ = v___x_4174_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_fst_4172_);
lean_ctor_set(v_reuseFailAlloc_4191_, 1, v___x_4185_);
v___x_4187_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
lean_object* v___x_4189_; 
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 1, v___x_4187_);
lean_ctor_set(v___x_4169_, 0, v___x_4182_);
v___x_4189_ = v___x_4169_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___x_4182_);
lean_ctor_set(v_reuseFailAlloc_4190_, 1, v___x_4187_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
v_a_4141_ = v___x_4189_;
goto v___jp_4140_;
}
}
}
}
v___jp_4195_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4196_ = lean_box(0);
lean_inc(v___x_4194_);
v___x_4197_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4194_, v_fst_4176_, v_snd_4177_, v_fst_4172_, v___x_4196_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
v___y_4146_ = v___x_4197_;
goto v___jp_4145_;
}
v___jp_4201_:
{
if (v___x_4200_ == 0)
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_dec(v_snd_4177_);
lean_dec(v_fst_4176_);
lean_dec(v_fst_4172_);
v___x_4202_ = lean_box(v___x_4198_);
v___x_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4199_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
lean_inc(v_a_4133_);
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v_a_4133_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4182_);
lean_ctor_set(v___x_4205_, 1, v___x_4204_);
v_a_4141_ = v___x_4205_;
goto v___jp_4140_;
}
else
{
lean_object* v_options_4206_; uint8_t v_hasTrace_4207_; 
lean_dec(v___x_4199_);
v_options_4206_ = lean_ctor_get(v___y_4137_, 2);
v_hasTrace_4207_ = lean_ctor_get_uint8(v_options_4206_, sizeof(void*)*1);
if (v_hasTrace_4207_ == 0)
{
goto v___jp_4195_;
}
else
{
lean_object* v_inheritedTraceOptions_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; 
v_inheritedTraceOptions_4208_ = lean_ctor_get(v___y_4137_, 13);
v___x_4209_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_4210_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4208_, v_options_4206_, v___x_4209_);
if (v___x_4210_ == 0)
{
goto v___jp_4195_;
}
else
{
lean_object* v_var_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v_var_4211_ = lean_ctor_get(v___x_4194_, 0);
v___x_4212_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4211_);
v___x_4213_ = l_Nat_reprFast(v_var_4211_);
v___x_4214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
v___x_4215_ = l_Lean_MessageData_ofFormat(v___x_4214_);
v___x_4216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4212_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
v___x_4217_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4193_, v___x_4216_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4219_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4218_);
lean_dec_ref(v___x_4217_);
lean_inc(v___x_4194_);
v___x_4219_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4194_, v_fst_4176_, v_snd_4177_, v_fst_4172_, v_a_4218_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
v___y_4146_ = v___x_4219_;
goto v___jp_4145_;
}
else
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4227_; 
lean_dec(v_snd_4177_);
lean_dec(v_fst_4176_);
lean_dec(v_fst_4172_);
lean_dec(v_a_4133_);
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
lean_dec(v___x_4199_);
goto v___jp_4183_;
}
else
{
uint8_t v___x_4230_; 
v___x_4230_ = lean_nat_dec_lt(v___x_4199_, v_fst_4176_);
if (v___x_4230_ == 0)
{
lean_dec(v___x_4199_);
goto v___jp_4183_;
}
else
{
lean_del_object(v___x_4179_);
lean_del_object(v___x_4174_);
lean_del_object(v___x_4169_);
goto v___jp_4201_;
}
}
}
v___jp_4231_:
{
if (v___y_4232_ == 0)
{
uint8_t v___x_4233_; 
v___x_4233_ = lean_unbox(v_snd_4177_);
if (v___x_4233_ == 0)
{
if (v___x_4198_ == 0)
{
v___y_4229_ = v___x_4165_;
goto v___jp_4228_;
}
else
{
lean_dec(v___x_4199_);
goto v___jp_4183_;
}
}
else
{
v___y_4229_ = v___x_4198_;
goto v___jp_4228_;
}
}
else
{
lean_del_object(v___x_4179_);
lean_del_object(v___x_4174_);
lean_del_object(v___x_4169_);
goto v___jp_4201_;
}
}
}
}
}
}
v___jp_4140_:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4142_ = lean_unsigned_to_nat(1u);
v___x_4143_ = lean_nat_add(v_a_4133_, v___x_4142_);
lean_dec(v_a_4133_);
v_a_4133_ = v___x_4143_;
v_b_4134_ = v_a_4141_;
goto _start;
}
v___jp_4145_:
{
if (lean_obj_tag(v___y_4146_) == 0)
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4156_; 
v_a_4147_ = lean_ctor_get(v___y_4146_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___y_4146_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4149_ = v___y_4146_;
v_isShared_4150_ = v_isSharedCheck_4156_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___y_4146_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4156_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
if (lean_obj_tag(v_a_4147_) == 0)
{
lean_object* v_a_4151_; lean_object* v___x_4153_; 
lean_dec(v_a_4133_);
v_a_4151_ = lean_ctor_get(v_a_4147_, 0);
lean_inc(v_a_4151_);
lean_dec_ref(v_a_4147_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 0, v_a_4151_);
v___x_4153_ = v___x_4149_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4151_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
else
{
lean_object* v_a_4155_; 
lean_del_object(v___x_4149_);
v_a_4155_ = lean_ctor_get(v_a_4147_, 0);
lean_inc(v_a_4155_);
lean_dec_ref(v_a_4147_);
v_a_4141_ = v_a_4155_;
goto v___jp_4140_;
}
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_dec(v_a_4133_);
v_a_4157_ = lean_ctor_get(v___y_4146_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___y_4146_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___y_4146_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___y_4146_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
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
lean_object* v___x_4369_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v_bestIdx_4375_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4504_; lean_object* v___x_4528_; lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___x_4369_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default));
v_bestIdx_4375_ = lean_unsigned_to_nat(0u);
v___x_4528_ = lean_array_get_size(v_data_4363_);
v___x_4529_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_4530_ = lean_nat_dec_lt(v_bestIdx_4375_, v___x_4528_);
if (v___x_4530_ == 0)
{
v___y_4504_ = v___x_4529_;
goto v___jp_4503_;
}
else
{
uint8_t v___x_4531_; 
v___x_4531_ = lean_nat_dec_le(v___x_4528_, v___x_4528_);
if (v___x_4531_ == 0)
{
if (v___x_4530_ == 0)
{
v___y_4504_ = v___x_4529_;
goto v___jp_4503_;
}
else
{
size_t v___x_4532_; size_t v___x_4533_; lean_object* v___x_4534_; 
v___x_4532_ = ((size_t)0ULL);
v___x_4533_ = lean_usize_of_nat(v___x_4528_);
v___x_4534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4363_, v___x_4532_, v___x_4533_, v___x_4529_);
v___y_4504_ = v___x_4534_;
goto v___jp_4503_;
}
}
else
{
size_t v___x_4535_; size_t v___x_4536_; lean_object* v___x_4537_; 
v___x_4535_ = ((size_t)0ULL);
v___x_4536_ = lean_usize_of_nat(v___x_4528_);
v___x_4537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4363_, v___x_4535_, v___x_4536_, v___x_4529_);
v___y_4504_ = v___x_4537_;
goto v___jp_4503_;
}
}
v___jp_4370_:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = lean_array_get(v___x_4369_, v___y_4372_, v___y_4371_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4372_);
v___x_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4373_);
return v___x_4374_;
}
v___jp_4376_:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; uint8_t v___x_4386_; 
v___x_4384_ = lean_array_get_borrowed(v___x_4369_, v___y_4379_, v_bestIdx_4375_);
v___x_4385_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4384_);
v___x_4386_ = lean_nat_dec_eq(v___x_4385_, v_bestIdx_4375_);
if (v___x_4386_ == 0)
{
lean_object* v___x_4387_; lean_object* v___x_4388_; uint8_t v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4387_ = lean_unsigned_to_nat(1u);
v___x_4388_ = lean_array_get_size(v___y_4379_);
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
v___x_4395_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v___x_4388_, v___y_4379_, v___x_4387_, v___x_4394_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4451_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4398_ = v___x_4395_;
v_isShared_4399_ = v_isSharedCheck_4451_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4395_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4451_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v_fst_4400_; 
v_fst_4400_ = lean_ctor_get(v_a_4396_, 0);
if (lean_obj_tag(v_fst_4400_) == 0)
{
lean_object* v_snd_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4445_; 
lean_del_object(v___x_4398_);
v_snd_4401_ = lean_ctor_get(v_a_4396_, 1);
v_isSharedCheck_4445_ = !lean_is_exclusive(v_a_4396_);
if (v_isSharedCheck_4445_ == 0)
{
lean_object* v_unused_4446_; 
v_unused_4446_ = lean_ctor_get(v_a_4396_, 0);
lean_dec(v_unused_4446_);
v___x_4403_ = v_a_4396_;
v_isShared_4404_ = v_isSharedCheck_4445_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_snd_4401_);
lean_dec(v_a_4396_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4445_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4405_; 
lean_inc_ref(v___y_4377_);
lean_inc(v___y_4383_);
lean_inc_ref(v___y_4382_);
lean_inc(v___y_4381_);
lean_inc_ref(v___y_4380_);
v___x_4405_ = lean_apply_5(v___y_4377_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, lean_box(0));
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; uint8_t v___x_4407_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref(v___x_4405_);
v___x_4407_ = lean_unbox(v_a_4406_);
lean_dec(v_a_4406_);
if (v___x_4407_ == 0)
{
lean_object* v_fst_4408_; 
lean_del_object(v___x_4403_);
lean_dec(v___y_4378_);
v_fst_4408_ = lean_ctor_get(v_snd_4401_, 0);
lean_inc(v_fst_4408_);
lean_dec(v_snd_4401_);
v___y_4371_ = v_fst_4408_;
v___y_4372_ = v___y_4379_;
goto v___jp_4370_;
}
else
{
lean_object* v_fst_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4435_; 
v_fst_4409_ = lean_ctor_get(v_snd_4401_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v_snd_4401_);
if (v_isSharedCheck_4435_ == 0)
{
lean_object* v_unused_4436_; 
v_unused_4436_ = lean_ctor_get(v_snd_4401_, 1);
lean_dec(v_unused_4436_);
v___x_4411_ = v_snd_4401_;
v_isShared_4412_ = v_isSharedCheck_4435_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_fst_4409_);
lean_dec(v_snd_4401_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4435_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4413_; lean_object* v_var_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4420_; 
v___x_4413_ = lean_array_get_borrowed(v___x_4369_, v___y_4379_, v_fst_4409_);
v_var_4414_ = lean_ctor_get(v___x_4413_, 0);
v___x_4415_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4414_);
v___x_4416_ = l_Nat_reprFast(v_var_4414_);
v___x_4417_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4416_);
v___x_4418_ = l_Lean_MessageData_ofFormat(v___x_4417_);
if (v_isShared_4412_ == 0)
{
lean_ctor_set_tag(v___x_4411_, 7);
lean_ctor_set(v___x_4411_, 1, v___x_4418_);
lean_ctor_set(v___x_4411_, 0, v___x_4415_);
v___x_4420_ = v___x_4411_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4415_);
lean_ctor_set(v_reuseFailAlloc_4434_, 1, v___x_4418_);
v___x_4420_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
lean_object* v___x_4421_; lean_object* v___x_4423_; 
v___x_4421_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
if (v_isShared_4404_ == 0)
{
lean_ctor_set_tag(v___x_4403_, 7);
lean_ctor_set(v___x_4403_, 1, v___x_4421_);
lean_ctor_set(v___x_4403_, 0, v___x_4420_);
v___x_4423_ = v___x_4403_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4420_);
lean_ctor_set(v_reuseFailAlloc_4433_, 1, v___x_4421_);
v___x_4423_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
lean_object* v___x_4424_; 
v___x_4424_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4378_, v___x_4423_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_dec_ref(v___x_4424_);
v___y_4371_ = v_fst_4409_;
v___y_4372_ = v___y_4379_;
goto v___jp_4370_;
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_dec(v_fst_4409_);
lean_dec_ref(v___y_4379_);
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4424_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4424_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
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
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_del_object(v___x_4403_);
lean_dec(v_snd_4401_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
v_a_4437_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4405_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4405_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
}
else
{
lean_object* v_val_4447_; lean_object* v___x_4449_; 
lean_inc_ref(v_fst_4400_);
lean_dec(v_a_4396_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
v_val_4447_ = lean_ctor_get(v_fst_4400_, 0);
lean_inc(v_val_4447_);
lean_dec_ref(v_fst_4400_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 0, v_val_4447_);
v___x_4449_ = v___x_4398_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_val_4447_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
v_a_4452_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4395_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4395_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
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
lean_object* v___x_4460_; 
lean_inc(v___x_4384_);
lean_dec(v___x_4385_);
lean_dec_ref(v___y_4379_);
lean_inc_ref(v___y_4377_);
lean_inc(v___y_4383_);
lean_inc_ref(v___y_4382_);
lean_inc(v___y_4381_);
lean_inc_ref(v___y_4380_);
v___x_4460_ = lean_apply_5(v___y_4377_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, lean_box(0));
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4494_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4463_ = v___x_4460_;
v_isShared_4464_ = v_isSharedCheck_4494_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4460_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4494_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
uint8_t v___x_4465_; 
v___x_4465_ = lean_unbox(v_a_4461_);
lean_dec(v_a_4461_);
if (v___x_4465_ == 0)
{
lean_object* v___x_4467_; 
lean_dec(v___y_4378_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4384_);
v___x_4467_ = v___x_4463_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4384_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
else
{
lean_object* v_var_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
lean_del_object(v___x_4463_);
v_var_4469_ = lean_ctor_get(v___x_4384_, 0);
v___x_4470_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4469_);
v___x_4471_ = l_Nat_reprFast(v_var_4469_);
v___x_4472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4471_);
v___x_4473_ = l_Lean_MessageData_ofFormat(v___x_4472_);
v___x_4474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4474_, 0, v___x_4470_);
lean_ctor_set(v___x_4474_, 1, v___x_4473_);
v___x_4475_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
v___x_4476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4474_);
lean_ctor_set(v___x_4476_, 1, v___x_4475_);
v___x_4477_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4378_, v___x_4476_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4484_ == 0)
{
lean_object* v_unused_4485_; 
v_unused_4485_ = lean_ctor_get(v___x_4477_, 0);
lean_dec(v_unused_4485_);
v___x_4479_ = v___x_4477_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_dec(v___x_4477_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 0, v___x_4384_);
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4384_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
lean_dec(v___x_4384_);
v_a_4486_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4477_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4477_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
lean_dec(v___x_4384_);
lean_dec(v___y_4378_);
v_a_4495_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4460_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4460_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
}
v___jp_4503_:
{
lean_object* v_cls_4505_; lean_object* v___f_4506_; lean_object* v___x_4507_; lean_object* v_a_4508_; uint8_t v___x_4509_; 
v_cls_4505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___f_4506_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2));
v___x_4507_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4505_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_a_4508_);
lean_dec_ref(v___x_4507_);
v___x_4509_ = lean_unbox(v_a_4508_);
lean_dec(v_a_4508_);
if (v___x_4509_ == 0)
{
v___y_4377_ = v___f_4506_;
v___y_4378_ = v_cls_4505_;
v___y_4379_ = v___y_4504_;
v___y_4380_ = v_a_4364_;
v___y_4381_ = v_a_4365_;
v___y_4382_ = v_a_4366_;
v___y_4383_ = v_a_4367_;
goto v___jp_4376_;
}
else
{
lean_object* v___x_4510_; size_t v_sz_4511_; size_t v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4510_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4);
v_sz_4511_ = lean_array_size(v___y_4504_);
v___x_4512_ = ((size_t)0ULL);
lean_inc_ref(v___y_4504_);
v___x_4513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_4511_, v___x_4512_, v___y_4504_);
v___x_4514_ = lean_array_to_list(v___x_4513_);
v___x_4515_ = lean_box(0);
v___x_4516_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v___x_4514_, v___x_4515_);
v___x_4517_ = l_Lean_MessageData_ofList(v___x_4516_);
v___x_4518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4510_);
lean_ctor_set(v___x_4518_, 1, v___x_4517_);
v___x_4519_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4505_, v___x_4518_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_dec_ref(v___x_4519_);
v___y_4377_ = v___f_4506_;
v___y_4378_ = v_cls_4505_;
v___y_4379_ = v___y_4504_;
v___y_4380_ = v_a_4364_;
v___y_4381_ = v_a_4365_;
v___y_4382_ = v_a_4366_;
v___y_4383_ = v_a_4367_;
goto v___jp_4376_;
}
else
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4527_; 
lean_dec_ref(v___y_4504_);
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4522_ = v___x_4519_;
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4519_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4525_; 
if (v_isShared_4523_ == 0)
{
v___x_4525_ = v___x_4522_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4520_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object* v_data_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec_ref(v_data_4538_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object* v_upperBound_4545_, lean_object* v___y_4546_, lean_object* v_inst_4547_, lean_object* v_R_4548_, lean_object* v_a_4549_, lean_object* v_b_4550_, lean_object* v_c_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_){
_start:
{
lean_object* v___x_4557_; 
v___x_4557_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4545_, v___y_4546_, v_a_4549_, v_b_4550_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
return v___x_4557_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object* v_upperBound_4558_, lean_object* v___y_4559_, lean_object* v_inst_4560_, lean_object* v_R_4561_, lean_object* v_a_4562_, lean_object* v_b_4563_, lean_object* v_c_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_upperBound_4558_, v___y_4559_, v_inst_4560_, v_R_4561_, v_a_4562_, v_b_4563_, v_c_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec_ref(v___y_4559_);
lean_dec(v_upperBound_4558_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(lean_object* v_snd_4571_, lean_object* v_fst_4572_, lean_object* v_as_x27_4573_, lean_object* v_b_4574_){
_start:
{
if (lean_obj_tag(v_as_x27_4573_) == 0)
{
lean_object* v___x_4576_; 
lean_dec_ref(v_fst_4572_);
v___x_4576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4576_, 0, v_b_4574_);
return v___x_4576_;
}
else
{
lean_object* v_head_4577_; lean_object* v_tail_4578_; lean_object* v_fst_4579_; lean_object* v_snd_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v_head_4577_ = lean_ctor_get(v_as_x27_4573_, 0);
lean_inc(v_head_4577_);
v_tail_4578_ = lean_ctor_get(v_as_x27_4573_, 1);
lean_inc(v_tail_4578_);
lean_dec_ref(v_as_x27_4573_);
v_fst_4579_ = lean_ctor_get(v_head_4577_, 0);
lean_inc(v_fst_4579_);
v_snd_4580_ = lean_ctor_get(v_head_4577_, 1);
lean_inc(v_snd_4580_);
lean_dec(v_head_4577_);
v___x_4581_ = lean_int_neg(v_snd_4571_);
lean_inc_ref(v_fst_4572_);
v___x_4582_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_snd_4580_, v_fst_4572_, v___x_4581_, v_fst_4579_);
v___x_4583_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_4582_);
v___x_4584_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_b_4574_, v___x_4583_);
v_as_x27_4573_ = v_tail_4578_;
v_b_4574_ = v___x_4584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg___boxed(lean_object* v_snd_4586_, lean_object* v_fst_4587_, lean_object* v_as_x27_4588_, lean_object* v_b_4589_, lean_object* v___y_4590_){
_start:
{
lean_object* v_res_4591_; 
v_res_4591_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4586_, v_fst_4587_, v_as_x27_4588_, v_b_4589_);
lean_dec(v_snd_4586_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(lean_object* v_upperBounds_4592_, lean_object* v_as_x27_4593_, lean_object* v_b_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
if (lean_obj_tag(v_as_x27_4593_) == 0)
{
lean_object* v___x_4600_; 
lean_dec(v_upperBounds_4592_);
v___x_4600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4600_, 0, v_b_4594_);
return v___x_4600_;
}
else
{
lean_object* v_head_4601_; lean_object* v_tail_4602_; lean_object* v_fst_4603_; lean_object* v_snd_4604_; lean_object* v___x_4605_; lean_object* v_a_4606_; 
v_head_4601_ = lean_ctor_get(v_as_x27_4593_, 0);
lean_inc(v_head_4601_);
v_tail_4602_ = lean_ctor_get(v_as_x27_4593_, 1);
lean_inc(v_tail_4602_);
lean_dec_ref(v_as_x27_4593_);
v_fst_4603_ = lean_ctor_get(v_head_4601_, 0);
lean_inc(v_fst_4603_);
v_snd_4604_ = lean_ctor_get(v_head_4601_, 1);
lean_inc(v_snd_4604_);
lean_dec(v_head_4601_);
lean_inc(v_upperBounds_4592_);
v___x_4605_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4604_, v_fst_4603_, v_upperBounds_4592_, v_b_4594_);
lean_dec(v_snd_4604_);
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
lean_inc(v_a_4606_);
lean_dec_ref(v___x_4605_);
v_as_x27_4593_ = v_tail_4602_;
v_b_4594_ = v_a_4606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg___boxed(lean_object* v_upperBounds_4608_, lean_object* v_as_x27_4609_, lean_object* v_b_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v_res_4616_; 
v_res_4616_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4608_, v_as_x27_4609_, v_b_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
return v_res_4616_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(lean_object* v_as_x27_4617_, lean_object* v_b_4618_){
_start:
{
if (lean_obj_tag(v_as_x27_4617_) == 0)
{
lean_object* v___x_4620_; 
v___x_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4620_, 0, v_b_4618_);
return v___x_4620_;
}
else
{
lean_object* v_head_4621_; lean_object* v_tail_4622_; lean_object* v___x_4623_; 
v_head_4621_ = lean_ctor_get(v_as_x27_4617_, 0);
lean_inc(v_head_4621_);
v_tail_4622_ = lean_ctor_get(v_as_x27_4617_, 1);
lean_inc(v_tail_4622_);
lean_dec_ref(v_as_x27_4617_);
v___x_4623_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_b_4618_, v_head_4621_);
v_as_x27_4617_ = v_tail_4622_;
v_b_4618_ = v___x_4623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg___boxed(lean_object* v_as_x27_4625_, lean_object* v_b_4626_, lean_object* v___y_4627_){
_start:
{
lean_object* v_res_4628_; 
v_res_4628_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4625_, v_b_4626_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(lean_object* v_p_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v_data_4635_; lean_object* v___x_4636_; 
lean_inc_ref(v_p_4629_);
v_data_4635_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(v_p_4629_);
v___x_4636_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4635_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_);
lean_dec_ref(v_data_4635_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v_irrelevant_4638_; lean_object* v_lowerBounds_4639_; lean_object* v_upperBounds_4640_; lean_object* v_assumptions_4641_; lean_object* v_eliminations_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4657_; 
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
lean_inc(v_a_4637_);
lean_dec_ref(v___x_4636_);
v_irrelevant_4638_ = lean_ctor_get(v_a_4637_, 1);
lean_inc(v_irrelevant_4638_);
v_lowerBounds_4639_ = lean_ctor_get(v_a_4637_, 2);
lean_inc(v_lowerBounds_4639_);
v_upperBounds_4640_ = lean_ctor_get(v_a_4637_, 3);
lean_inc(v_upperBounds_4640_);
lean_dec(v_a_4637_);
v_assumptions_4641_ = lean_ctor_get(v_p_4629_, 0);
v_eliminations_4642_ = lean_ctor_get(v_p_4629_, 4);
v_isSharedCheck_4657_ = !lean_is_exclusive(v_p_4629_);
if (v_isSharedCheck_4657_ == 0)
{
lean_object* v_unused_4658_; lean_object* v_unused_4659_; lean_object* v_unused_4660_; lean_object* v_unused_4661_; lean_object* v_unused_4662_; 
v_unused_4658_ = lean_ctor_get(v_p_4629_, 6);
lean_dec(v_unused_4658_);
v_unused_4659_ = lean_ctor_get(v_p_4629_, 5);
lean_dec(v_unused_4659_);
v_unused_4660_ = lean_ctor_get(v_p_4629_, 3);
lean_dec(v_unused_4660_);
v_unused_4661_ = lean_ctor_get(v_p_4629_, 2);
lean_dec(v_unused_4661_);
v_unused_4662_ = lean_ctor_get(v_p_4629_, 1);
lean_dec(v_unused_4662_);
v___x_4644_ = v_p_4629_;
v_isShared_4645_ = v_isSharedCheck_4657_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_eliminations_4642_);
lean_inc(v_assumptions_4641_);
lean_dec(v_p_4629_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4657_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; uint8_t v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4652_; 
v___x_4646_ = lean_unsigned_to_nat(0u);
v___x_4647_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v___x_4648_ = 1;
v___x_4649_ = lean_box(0);
v___x_4650_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 6, v___x_4650_);
lean_ctor_set(v___x_4644_, 5, v___x_4649_);
lean_ctor_set(v___x_4644_, 3, v___x_4647_);
lean_ctor_set(v___x_4644_, 2, v___x_4647_);
lean_ctor_set(v___x_4644_, 1, v___x_4646_);
v___x_4652_ = v___x_4644_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_assumptions_4641_);
lean_ctor_set(v_reuseFailAlloc_4656_, 1, v___x_4646_);
lean_ctor_set(v_reuseFailAlloc_4656_, 2, v___x_4647_);
lean_ctor_set(v_reuseFailAlloc_4656_, 3, v___x_4647_);
lean_ctor_set(v_reuseFailAlloc_4656_, 4, v_eliminations_4642_);
lean_ctor_set(v_reuseFailAlloc_4656_, 5, v___x_4649_);
lean_ctor_set(v_reuseFailAlloc_4656_, 6, v___x_4650_);
v___x_4652_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
lean_object* v___x_4653_; lean_object* v_a_4654_; lean_object* v___x_4655_; 
lean_ctor_set_uint8(v___x_4652_, sizeof(void*)*7, v___x_4648_);
v___x_4653_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_irrelevant_4638_, v___x_4652_);
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
lean_inc(v_a_4654_);
lean_dec_ref(v___x_4653_);
v___x_4655_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4640_, v_lowerBounds_4639_, v_a_4654_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_);
return v___x_4655_;
}
}
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
lean_dec_ref(v_p_4629_);
v_a_4663_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___x_4636_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4636_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin___boxed(lean_object* v_p_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_){
_start:
{
lean_object* v_res_4677_; 
v_res_4677_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_4671_, v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_);
lean_dec(v_a_4675_);
lean_dec_ref(v_a_4674_);
lean_dec(v_a_4673_);
lean_dec_ref(v_a_4672_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(lean_object* v_snd_4678_, lean_object* v_fst_4679_, lean_object* v_as_4680_, lean_object* v_as_x27_4681_, lean_object* v_b_4682_, lean_object* v_a_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_){
_start:
{
lean_object* v___x_4689_; 
v___x_4689_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4678_, v_fst_4679_, v_as_x27_4681_, v_b_4682_);
return v___x_4689_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___boxed(lean_object* v_snd_4690_, lean_object* v_fst_4691_, lean_object* v_as_4692_, lean_object* v_as_x27_4693_, lean_object* v_b_4694_, lean_object* v_a_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(v_snd_4690_, v_fst_4691_, v_as_4692_, v_as_x27_4693_, v_b_4694_, v_a_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v_as_4692_);
lean_dec(v_snd_4690_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(lean_object* v_as_4702_, lean_object* v_as_x27_4703_, lean_object* v_b_4704_, lean_object* v_a_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v___x_4711_; 
v___x_4711_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4703_, v_b_4704_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___boxed(lean_object* v_as_4712_, lean_object* v_as_x27_4713_, lean_object* v_b_4714_, lean_object* v_a_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(v_as_4712_, v_as_x27_4713_, v_b_4714_, v_a_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v_as_4712_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(lean_object* v_upperBounds_4722_, lean_object* v_as_4723_, lean_object* v_as_x27_4724_, lean_object* v_b_4725_, lean_object* v_a_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_){
_start:
{
lean_object* v___x_4732_; 
v___x_4732_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4722_, v_as_x27_4724_, v_b_4725_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___boxed(lean_object* v_upperBounds_4733_, lean_object* v_as_4734_, lean_object* v_as_x27_4735_, lean_object* v_b_4736_, lean_object* v_a_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(v_upperBounds_4733_, v_as_4734_, v_as_x27_4735_, v_b_4736_, v_a_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
lean_dec(v___y_4741_);
lean_dec_ref(v___y_4740_);
lean_dec(v___y_4739_);
lean_dec_ref(v___y_4738_);
lean_dec(v_as_4734_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object* v_x_4744_, lean_object* v_x_4745_){
_start:
{
if (lean_obj_tag(v_x_4745_) == 0)
{
lean_inc(v_x_4744_);
return v_x_4744_;
}
else
{
lean_object* v_key_4746_; lean_object* v_value_4747_; lean_object* v_tail_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
v_key_4746_ = lean_ctor_get(v_x_4745_, 0);
v_value_4747_ = lean_ctor_get(v_x_4745_, 1);
v_tail_4748_ = lean_ctor_get(v_x_4745_, 2);
v___x_4749_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4744_, v_tail_4748_);
lean_inc(v_value_4747_);
lean_inc(v_key_4746_);
v___x_4750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4750_, 0, v_key_4746_);
lean_ctor_set(v___x_4750_, 1, v_value_4747_);
v___x_4751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4750_);
lean_ctor_set(v___x_4751_, 1, v___x_4749_);
return v___x_4751_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2___boxed(lean_object* v_x_4752_, lean_object* v_x_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4752_, v_x_4753_);
lean_dec(v_x_4753_);
lean_dec(v_x_4752_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object* v_as_4755_, size_t v_i_4756_, size_t v_stop_4757_, lean_object* v_b_4758_){
_start:
{
uint8_t v___x_4759_; 
v___x_4759_ = lean_usize_dec_eq(v_i_4756_, v_stop_4757_);
if (v___x_4759_ == 0)
{
size_t v___x_4760_; size_t v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; 
v___x_4760_ = ((size_t)1ULL);
v___x_4761_ = lean_usize_sub(v_i_4756_, v___x_4760_);
v___x_4762_ = lean_array_uget_borrowed(v_as_4755_, v___x_4761_);
v___x_4763_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_b_4758_, v___x_4762_);
lean_dec(v_b_4758_);
v_i_4756_ = v___x_4761_;
v_b_4758_ = v___x_4763_;
goto _start;
}
else
{
return v_b_4758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object* v_as_4765_, lean_object* v_i_4766_, lean_object* v_stop_4767_, lean_object* v_b_4768_){
_start:
{
size_t v_i_boxed_4769_; size_t v_stop_boxed_4770_; lean_object* v_res_4771_; 
v_i_boxed_4769_ = lean_unbox_usize(v_i_4766_);
lean_dec(v_i_4766_);
v_stop_boxed_4770_ = lean_unbox_usize(v_stop_4767_);
lean_dec(v_stop_4767_);
v_res_4771_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_as_4765_, v_i_boxed_4769_, v_stop_boxed_4770_, v_b_4768_);
lean_dec_ref(v_as_4765_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object* v_a_4772_, lean_object* v_a_4773_){
_start:
{
if (lean_obj_tag(v_a_4772_) == 0)
{
lean_object* v___x_4774_; 
v___x_4774_ = l_List_reverse___redArg(v_a_4773_);
return v___x_4774_;
}
else
{
lean_object* v_head_4775_; lean_object* v_tail_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4893_; 
v_head_4775_ = lean_ctor_get(v_a_4772_, 0);
v_tail_4776_ = lean_ctor_get(v_a_4772_, 1);
v_isSharedCheck_4893_ = !lean_is_exclusive(v_a_4772_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4778_ = v_a_4772_;
v_isShared_4779_ = v_isSharedCheck_4893_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_tail_4776_);
lean_inc(v_head_4775_);
lean_dec(v_a_4772_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4893_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___y_4781_; lean_object* v_snd_4786_; lean_object* v_constraint_4787_; lean_object* v_fst_4788_; lean_object* v_lowerBound_4789_; lean_object* v_upperBound_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___y_4795_; lean_object* v___y_4796_; 
v_snd_4786_ = lean_ctor_get(v_head_4775_, 1);
v_constraint_4787_ = lean_ctor_get(v_snd_4786_, 1);
lean_inc_ref(v_constraint_4787_);
v_fst_4788_ = lean_ctor_get(v_head_4775_, 0);
lean_inc(v_fst_4788_);
lean_dec(v_head_4775_);
v_lowerBound_4789_ = lean_ctor_get(v_constraint_4787_, 0);
lean_inc(v_lowerBound_4789_);
v_upperBound_4790_ = lean_ctor_get(v_constraint_4787_, 1);
lean_inc(v_upperBound_4790_);
lean_dec_ref(v_constraint_4787_);
v___x_4791_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_fst_4788_);
lean_dec(v_fst_4788_);
v___x_4792_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_4793_ = lean_string_append(v___x_4791_, v___x_4792_);
if (lean_obj_tag(v_lowerBound_4789_) == 0)
{
if (lean_obj_tag(v_upperBound_4790_) == 0)
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_4802_ = lean_string_append(v___x_4793_, v___x_4801_);
v___y_4781_ = v___x_4802_;
goto v___jp_4780_;
}
else
{
lean_object* v_val_4803_; lean_object* v___x_4804_; lean_object* v___y_4806_; lean_object* v_intZero_4811_; uint8_t v_isNeg_4812_; 
v_val_4803_ = lean_ctor_get(v_upperBound_4790_, 0);
lean_inc(v_val_4803_);
lean_dec_ref(v_upperBound_4790_);
v___x_4804_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_4811_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4812_ = lean_int_dec_lt(v_val_4803_, v_intZero_4811_);
if (v_isNeg_4812_ == 0)
{
lean_object* v_a_4813_; lean_object* v___x_4814_; 
v_a_4813_ = lean_nat_abs(v_val_4803_);
lean_dec(v_val_4803_);
v___x_4814_ = l_Nat_reprFast(v_a_4813_);
v___y_4806_ = v___x_4814_;
goto v___jp_4805_;
}
else
{
lean_object* v_abs_4815_; lean_object* v_one_4816_; lean_object* v_a_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v_abs_4815_ = lean_nat_abs(v_val_4803_);
lean_dec(v_val_4803_);
v_one_4816_ = lean_unsigned_to_nat(1u);
v_a_4817_ = lean_nat_sub(v_abs_4815_, v_one_4816_);
lean_dec(v_abs_4815_);
v___x_4818_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4819_ = lean_nat_add(v_a_4817_, v_one_4816_);
lean_dec(v_a_4817_);
v___x_4820_ = l_Nat_reprFast(v___x_4819_);
v___x_4821_ = lean_string_append(v___x_4818_, v___x_4820_);
lean_dec_ref(v___x_4820_);
v___y_4806_ = v___x_4821_;
goto v___jp_4805_;
}
v___jp_4805_:
{
lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4807_ = lean_string_append(v___x_4804_, v___y_4806_);
lean_dec_ref(v___y_4806_);
v___x_4808_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4809_ = lean_string_append(v___x_4807_, v___x_4808_);
v___x_4810_ = lean_string_append(v___x_4793_, v___x_4809_);
lean_dec_ref(v___x_4809_);
v___y_4781_ = v___x_4810_;
goto v___jp_4780_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_4790_) == 0)
{
lean_object* v_val_4822_; lean_object* v___x_4823_; lean_object* v___y_4825_; lean_object* v_intZero_4830_; uint8_t v_isNeg_4831_; 
v_val_4822_ = lean_ctor_get(v_lowerBound_4789_, 0);
lean_inc(v_val_4822_);
lean_dec_ref(v_lowerBound_4789_);
v___x_4823_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4830_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4831_ = lean_int_dec_lt(v_val_4822_, v_intZero_4830_);
if (v_isNeg_4831_ == 0)
{
lean_object* v_a_4832_; lean_object* v___x_4833_; 
v_a_4832_ = lean_nat_abs(v_val_4822_);
lean_dec(v_val_4822_);
v___x_4833_ = l_Nat_reprFast(v_a_4832_);
v___y_4825_ = v___x_4833_;
goto v___jp_4824_;
}
else
{
lean_object* v_abs_4834_; lean_object* v_one_4835_; lean_object* v_a_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
v_abs_4834_ = lean_nat_abs(v_val_4822_);
lean_dec(v_val_4822_);
v_one_4835_ = lean_unsigned_to_nat(1u);
v_a_4836_ = lean_nat_sub(v_abs_4834_, v_one_4835_);
lean_dec(v_abs_4834_);
v___x_4837_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4838_ = lean_nat_add(v_a_4836_, v_one_4835_);
lean_dec(v_a_4836_);
v___x_4839_ = l_Nat_reprFast(v___x_4838_);
v___x_4840_ = lean_string_append(v___x_4837_, v___x_4839_);
lean_dec_ref(v___x_4839_);
v___y_4825_ = v___x_4840_;
goto v___jp_4824_;
}
v___jp_4824_:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4826_ = lean_string_append(v___x_4823_, v___y_4825_);
lean_dec_ref(v___y_4825_);
v___x_4827_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_4828_ = lean_string_append(v___x_4826_, v___x_4827_);
v___x_4829_ = lean_string_append(v___x_4793_, v___x_4828_);
lean_dec_ref(v___x_4828_);
v___y_4781_ = v___x_4829_;
goto v___jp_4780_;
}
}
else
{
lean_object* v_val_4841_; lean_object* v_val_4842_; uint8_t v___x_4843_; 
v_val_4841_ = lean_ctor_get(v_lowerBound_4789_, 0);
lean_inc(v_val_4841_);
lean_dec_ref(v_lowerBound_4789_);
v_val_4842_ = lean_ctor_get(v_upperBound_4790_, 0);
lean_inc(v_val_4842_);
lean_dec_ref(v_upperBound_4790_);
v___x_4843_ = lean_int_dec_lt(v_val_4842_, v_val_4841_);
if (v___x_4843_ == 0)
{
uint8_t v___x_4844_; 
v___x_4844_ = lean_int_dec_eq(v_val_4841_, v_val_4842_);
if (v___x_4844_ == 0)
{
lean_object* v___x_4845_; lean_object* v___y_4847_; lean_object* v_intZero_4862_; uint8_t v_isNeg_4863_; 
v___x_4845_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4862_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4863_ = lean_int_dec_lt(v_val_4841_, v_intZero_4862_);
if (v_isNeg_4863_ == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4865_; 
v_a_4864_ = lean_nat_abs(v_val_4841_);
lean_dec(v_val_4841_);
v___x_4865_ = l_Nat_reprFast(v_a_4864_);
v___y_4847_ = v___x_4865_;
goto v___jp_4846_;
}
else
{
lean_object* v_abs_4866_; lean_object* v_one_4867_; lean_object* v_a_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; 
v_abs_4866_ = lean_nat_abs(v_val_4841_);
lean_dec(v_val_4841_);
v_one_4867_ = lean_unsigned_to_nat(1u);
v_a_4868_ = lean_nat_sub(v_abs_4866_, v_one_4867_);
lean_dec(v_abs_4866_);
v___x_4869_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4870_ = lean_nat_add(v_a_4868_, v_one_4867_);
lean_dec(v_a_4868_);
v___x_4871_ = l_Nat_reprFast(v___x_4870_);
v___x_4872_ = lean_string_append(v___x_4869_, v___x_4871_);
lean_dec_ref(v___x_4871_);
v___y_4847_ = v___x_4872_;
goto v___jp_4846_;
}
v___jp_4846_:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v_intZero_4851_; uint8_t v_isNeg_4852_; 
v___x_4848_ = lean_string_append(v___x_4845_, v___y_4847_);
lean_dec_ref(v___y_4847_);
v___x_4849_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_4850_ = lean_string_append(v___x_4848_, v___x_4849_);
v_intZero_4851_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4852_ = lean_int_dec_lt(v_val_4842_, v_intZero_4851_);
if (v_isNeg_4852_ == 0)
{
lean_object* v_a_4853_; lean_object* v___x_4854_; 
v_a_4853_ = lean_nat_abs(v_val_4842_);
lean_dec(v_val_4842_);
v___x_4854_ = l_Nat_reprFast(v_a_4853_);
v___y_4795_ = v___x_4850_;
v___y_4796_ = v___x_4854_;
goto v___jp_4794_;
}
else
{
lean_object* v_abs_4855_; lean_object* v_one_4856_; lean_object* v_a_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v_abs_4855_ = lean_nat_abs(v_val_4842_);
lean_dec(v_val_4842_);
v_one_4856_ = lean_unsigned_to_nat(1u);
v_a_4857_ = lean_nat_sub(v_abs_4855_, v_one_4856_);
lean_dec(v_abs_4855_);
v___x_4858_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4859_ = lean_nat_add(v_a_4857_, v_one_4856_);
lean_dec(v_a_4857_);
v___x_4860_ = l_Nat_reprFast(v___x_4859_);
v___x_4861_ = lean_string_append(v___x_4858_, v___x_4860_);
lean_dec_ref(v___x_4860_);
v___y_4795_ = v___x_4850_;
v___y_4796_ = v___x_4861_;
goto v___jp_4794_;
}
}
}
else
{
lean_object* v___x_4873_; lean_object* v___y_4875_; lean_object* v_intZero_4880_; uint8_t v_isNeg_4881_; 
lean_dec(v_val_4842_);
v___x_4873_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_4880_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4881_ = lean_int_dec_lt(v_val_4841_, v_intZero_4880_);
if (v_isNeg_4881_ == 0)
{
lean_object* v_a_4882_; lean_object* v___x_4883_; 
v_a_4882_ = lean_nat_abs(v_val_4841_);
lean_dec(v_val_4841_);
v___x_4883_ = l_Nat_reprFast(v_a_4882_);
v___y_4875_ = v___x_4883_;
goto v___jp_4874_;
}
else
{
lean_object* v_abs_4884_; lean_object* v_one_4885_; lean_object* v_a_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
v_abs_4884_ = lean_nat_abs(v_val_4841_);
lean_dec(v_val_4841_);
v_one_4885_ = lean_unsigned_to_nat(1u);
v_a_4886_ = lean_nat_sub(v_abs_4884_, v_one_4885_);
lean_dec(v_abs_4884_);
v___x_4887_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4888_ = lean_nat_add(v_a_4886_, v_one_4885_);
lean_dec(v_a_4886_);
v___x_4889_ = l_Nat_reprFast(v___x_4888_);
v___x_4890_ = lean_string_append(v___x_4887_, v___x_4889_);
lean_dec_ref(v___x_4889_);
v___y_4875_ = v___x_4890_;
goto v___jp_4874_;
}
v___jp_4874_:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4876_ = lean_string_append(v___x_4873_, v___y_4875_);
lean_dec_ref(v___y_4875_);
v___x_4877_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_4878_ = lean_string_append(v___x_4876_, v___x_4877_);
v___x_4879_ = lean_string_append(v___x_4793_, v___x_4878_);
lean_dec_ref(v___x_4878_);
v___y_4781_ = v___x_4879_;
goto v___jp_4780_;
}
}
}
else
{
lean_object* v___x_4891_; lean_object* v___x_4892_; 
lean_dec(v_val_4842_);
lean_dec(v_val_4841_);
v___x_4891_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_4892_ = lean_string_append(v___x_4793_, v___x_4891_);
v___y_4781_ = v___x_4892_;
goto v___jp_4780_;
}
}
}
v___jp_4780_:
{
lean_object* v___x_4783_; 
if (v_isShared_4779_ == 0)
{
lean_ctor_set(v___x_4778_, 1, v_a_4773_);
lean_ctor_set(v___x_4778_, 0, v___y_4781_);
v___x_4783_ = v___x_4778_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___y_4781_);
lean_ctor_set(v_reuseFailAlloc_4785_, 1, v_a_4773_);
v___x_4783_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
v_a_4772_ = v_tail_4776_;
v_a_4773_ = v___x_4783_;
goto _start;
}
}
v___jp_4794_:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4797_ = lean_string_append(v___y_4795_, v___y_4796_);
lean_dec_ref(v___y_4796_);
v___x_4798_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4799_ = lean_string_append(v___x_4797_, v___x_4798_);
v___x_4800_ = lean_string_append(v___x_4793_, v___x_4799_);
lean_dec_ref(v___x_4799_);
v___y_4781_ = v___x_4800_;
goto v___jp_4780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object* v_cls_4894_, lean_object* v_msg_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_){
_start:
{
lean_object* v_ref_4901_; lean_object* v___x_4902_; lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4947_; 
v_ref_4901_ = lean_ctor_get(v___y_4898_, 5);
v___x_4902_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_);
v_a_4903_ = lean_ctor_get(v___x_4902_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4905_ = v___x_4902_;
v_isShared_4906_ = v_isSharedCheck_4947_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4902_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4947_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4907_; lean_object* v_traceState_4908_; lean_object* v_env_4909_; lean_object* v_nextMacroScope_4910_; lean_object* v_ngen_4911_; lean_object* v_auxDeclNGen_4912_; lean_object* v_cache_4913_; lean_object* v_messages_4914_; lean_object* v_infoState_4915_; lean_object* v_snapshotTasks_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4946_; 
v___x_4907_ = lean_st_ref_take(v___y_4899_);
v_traceState_4908_ = lean_ctor_get(v___x_4907_, 4);
v_env_4909_ = lean_ctor_get(v___x_4907_, 0);
v_nextMacroScope_4910_ = lean_ctor_get(v___x_4907_, 1);
v_ngen_4911_ = lean_ctor_get(v___x_4907_, 2);
v_auxDeclNGen_4912_ = lean_ctor_get(v___x_4907_, 3);
v_cache_4913_ = lean_ctor_get(v___x_4907_, 5);
v_messages_4914_ = lean_ctor_get(v___x_4907_, 6);
v_infoState_4915_ = lean_ctor_get(v___x_4907_, 7);
v_snapshotTasks_4916_ = lean_ctor_get(v___x_4907_, 8);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4907_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4918_ = v___x_4907_;
v_isShared_4919_ = v_isSharedCheck_4946_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_snapshotTasks_4916_);
lean_inc(v_infoState_4915_);
lean_inc(v_messages_4914_);
lean_inc(v_cache_4913_);
lean_inc(v_traceState_4908_);
lean_inc(v_auxDeclNGen_4912_);
lean_inc(v_ngen_4911_);
lean_inc(v_nextMacroScope_4910_);
lean_inc(v_env_4909_);
lean_dec(v___x_4907_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4946_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
uint64_t v_tid_4920_; lean_object* v_traces_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4945_; 
v_tid_4920_ = lean_ctor_get_uint64(v_traceState_4908_, sizeof(void*)*1);
v_traces_4921_ = lean_ctor_get(v_traceState_4908_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v_traceState_4908_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4923_ = v_traceState_4908_;
v_isShared_4924_ = v_isSharedCheck_4945_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_traces_4921_);
lean_dec(v_traceState_4908_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4945_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4925_; double v___x_4926_; uint8_t v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4935_; 
v___x_4925_ = lean_box(0);
v___x_4926_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4927_ = 0;
v___x_4928_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4929_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4929_, 0, v_cls_4894_);
lean_ctor_set(v___x_4929_, 1, v___x_4925_);
lean_ctor_set(v___x_4929_, 2, v___x_4928_);
lean_ctor_set_float(v___x_4929_, sizeof(void*)*3, v___x_4926_);
lean_ctor_set_float(v___x_4929_, sizeof(void*)*3 + 8, v___x_4926_);
lean_ctor_set_uint8(v___x_4929_, sizeof(void*)*3 + 16, v___x_4927_);
v___x_4930_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4931_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4929_);
lean_ctor_set(v___x_4931_, 1, v_a_4903_);
lean_ctor_set(v___x_4931_, 2, v___x_4930_);
lean_inc(v_ref_4901_);
v___x_4932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4932_, 0, v_ref_4901_);
lean_ctor_set(v___x_4932_, 1, v___x_4931_);
v___x_4933_ = l_Lean_PersistentArray_push___redArg(v_traces_4921_, v___x_4932_);
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 0, v___x_4933_);
v___x_4935_ = v___x_4923_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v___x_4933_);
lean_ctor_set_uint64(v_reuseFailAlloc_4944_, sizeof(void*)*1, v_tid_4920_);
v___x_4935_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4937_; 
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 4, v___x_4935_);
v___x_4937_ = v___x_4918_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v_env_4909_);
lean_ctor_set(v_reuseFailAlloc_4943_, 1, v_nextMacroScope_4910_);
lean_ctor_set(v_reuseFailAlloc_4943_, 2, v_ngen_4911_);
lean_ctor_set(v_reuseFailAlloc_4943_, 3, v_auxDeclNGen_4912_);
lean_ctor_set(v_reuseFailAlloc_4943_, 4, v___x_4935_);
lean_ctor_set(v_reuseFailAlloc_4943_, 5, v_cache_4913_);
lean_ctor_set(v_reuseFailAlloc_4943_, 6, v_messages_4914_);
lean_ctor_set(v_reuseFailAlloc_4943_, 7, v_infoState_4915_);
lean_ctor_set(v_reuseFailAlloc_4943_, 8, v_snapshotTasks_4916_);
v___x_4937_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4941_; 
v___x_4938_ = lean_st_ref_set(v___y_4899_, v___x_4937_);
v___x_4939_ = lean_box(0);
if (v_isShared_4906_ == 0)
{
lean_ctor_set(v___x_4905_, 0, v___x_4939_);
v___x_4941_ = v___x_4905_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v___x_4939_);
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
lean_object* v___y_4974_; lean_object* v___y_4975_; lean_object* v___y_4976_; uint8_t v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; lean_object* v___y_4982_; lean_object* v_options_4988_; uint8_t v_hasTrace_4989_; 
v_options_4988_ = lean_ctor_get(v_a_4970_, 2);
v_hasTrace_4989_ = lean_ctor_get_uint8(v_options_4988_, sizeof(void*)*1);
if (v_hasTrace_4989_ == 0)
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
lean_object* v_inheritedTraceOptions_4990_; lean_object* v_cls_4991_; lean_object* v___x_4992_; uint8_t v___x_4993_; 
v_inheritedTraceOptions_4990_ = lean_ctor_get(v_a_4970_, 13);
v_cls_4991_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4992_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_4993_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4990_, v_options_4988_, v___x_4992_);
if (v___x_4993_ == 0)
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
lean_object* v_constraints_4994_; uint8_t v_possible_4995_; lean_object* v___x_4996_; lean_object* v___y_4998_; 
v_constraints_4994_ = lean_ctor_get(v_p_4962_, 2);
v_possible_4995_ = lean_ctor_get_uint8(v_p_4962_, sizeof(void*)*7);
v___x_4996_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1);
if (v_possible_4995_ == 0)
{
lean_object* v___x_5011_; 
v___x_5011_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
v___y_4998_ = v___x_5011_;
goto v___jp_4997_;
}
else
{
uint8_t v___x_5012_; 
v___x_5012_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_4962_);
if (v___x_5012_ == 0)
{
lean_object* v_buckets_5013_; lean_object* v___x_5014_; lean_object* v___y_5016_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; uint8_t v___x_5023_; 
v_buckets_5013_ = lean_ctor_get(v_constraints_4994_, 1);
v___x_5014_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5020_ = lean_box(0);
v___x_5021_ = lean_array_get_size(v_buckets_5013_);
v___x_5022_ = lean_unsigned_to_nat(0u);
v___x_5023_ = lean_nat_dec_lt(v___x_5022_, v___x_5021_);
if (v___x_5023_ == 0)
{
v___y_5016_ = v___x_5020_;
goto v___jp_5015_;
}
else
{
size_t v___x_5024_; size_t v___x_5025_; lean_object* v___x_5026_; 
v___x_5024_ = lean_usize_of_nat(v___x_5021_);
v___x_5025_ = ((size_t)0ULL);
v___x_5026_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5013_, v___x_5024_, v___x_5025_, v___x_5020_);
v___y_5016_ = v___x_5026_;
goto v___jp_5015_;
}
v___jp_5015_:
{
lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5017_ = lean_box(0);
v___x_5018_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5016_, v___x_5017_);
v___x_5019_ = l_String_intercalate(v___x_5014_, v___x_5018_);
v___y_4998_ = v___x_5019_;
goto v___jp_4997_;
}
}
else
{
lean_object* v___x_5027_; 
v___x_5027_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_4998_ = v___x_5027_;
goto v___jp_4997_;
}
}
v___jp_4997_:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_4999_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4999_, 0, v___y_4998_);
v___x_5000_ = l_Lean_MessageData_ofFormat(v___x_4999_);
v___x_5001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5001_, 0, v___x_4996_);
lean_ctor_set(v___x_5001_, 1, v___x_5000_);
v___x_5002_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4991_, v___x_5001_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
if (lean_obj_tag(v___x_5002_) == 0)
{
lean_dec_ref(v___x_5002_);
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
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5010_; 
lean_dec_ref(v_p_4962_);
v_a_5003_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5010_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5010_ == 0)
{
v___x_5005_ = v___x_5002_;
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_5002_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5008_; 
if (v_isShared_5006_ == 0)
{
v___x_5008_ = v___x_5005_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
return v___x_5008_;
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
lean_dec_ref(v___x_4985_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination(lean_object* v_p_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, uint8_t v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_){
_start:
{
lean_object* v___y_5040_; lean_object* v___y_5041_; lean_object* v___y_5042_; uint8_t v___y_5043_; lean_object* v___y_5044_; lean_object* v___y_5045_; lean_object* v___y_5046_; lean_object* v___y_5047_; lean_object* v___y_5048_; uint8_t v_possible_5052_; 
v_possible_5052_ = lean_ctor_get_uint8(v_p_5028_, sizeof(void*)*7);
if (v_possible_5052_ == 0)
{
lean_object* v___x_5053_; 
v___x_5053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5053_, 0, v_p_5028_);
return v___x_5053_;
}
else
{
lean_object* v_constraints_5054_; uint8_t v___x_5055_; 
v_constraints_5054_ = lean_ctor_get(v_p_5028_, 2);
v___x_5055_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_5028_);
if (v___x_5055_ == 0)
{
lean_object* v_options_5056_; uint8_t v_hasTrace_5057_; 
v_options_5056_ = lean_ctor_get(v_a_5036_, 2);
v_hasTrace_5057_ = lean_ctor_get_uint8(v_options_5056_, sizeof(void*)*1);
if (v_hasTrace_5057_ == 0)
{
v___y_5040_ = v_a_5029_;
v___y_5041_ = v_a_5030_;
v___y_5042_ = v_a_5031_;
v___y_5043_ = v_a_5032_;
v___y_5044_ = v_a_5033_;
v___y_5045_ = v_a_5034_;
v___y_5046_ = v_a_5035_;
v___y_5047_ = v_a_5036_;
v___y_5048_ = v_a_5037_;
goto v___jp_5039_;
}
else
{
lean_object* v_inheritedTraceOptions_5058_; lean_object* v_cls_5059_; lean_object* v___x_5060_; uint8_t v___x_5061_; 
v_inheritedTraceOptions_5058_ = lean_ctor_get(v_a_5036_, 13);
v_cls_5059_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_5060_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_5061_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5058_, v_options_5056_, v___x_5060_);
if (v___x_5061_ == 0)
{
v___y_5040_ = v_a_5029_;
v___y_5041_ = v_a_5030_;
v___y_5042_ = v_a_5031_;
v___y_5043_ = v_a_5032_;
v___y_5044_ = v_a_5033_;
v___y_5045_ = v_a_5034_;
v___y_5046_ = v_a_5035_;
v___y_5047_ = v_a_5036_;
v___y_5048_ = v_a_5037_;
goto v___jp_5039_;
}
else
{
lean_object* v___x_5062_; lean_object* v___y_5064_; 
v___x_5062_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1);
if (v___x_5055_ == 0)
{
lean_object* v_buckets_5077_; lean_object* v___x_5078_; lean_object* v___y_5080_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; uint8_t v___x_5087_; 
v_buckets_5077_ = lean_ctor_get(v_constraints_5054_, 1);
v___x_5078_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5084_ = lean_box(0);
v___x_5085_ = lean_array_get_size(v_buckets_5077_);
v___x_5086_ = lean_unsigned_to_nat(0u);
v___x_5087_ = lean_nat_dec_lt(v___x_5086_, v___x_5085_);
if (v___x_5087_ == 0)
{
v___y_5080_ = v___x_5084_;
goto v___jp_5079_;
}
else
{
size_t v___x_5088_; size_t v___x_5089_; lean_object* v___x_5090_; 
v___x_5088_ = lean_usize_of_nat(v___x_5085_);
v___x_5089_ = ((size_t)0ULL);
v___x_5090_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5077_, v___x_5088_, v___x_5089_, v___x_5084_);
v___y_5080_ = v___x_5090_;
goto v___jp_5079_;
}
v___jp_5079_:
{
lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5081_ = lean_box(0);
v___x_5082_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5080_, v___x_5081_);
v___x_5083_ = l_String_intercalate(v___x_5078_, v___x_5082_);
v___y_5064_ = v___x_5083_;
goto v___jp_5063_;
}
}
else
{
lean_object* v___x_5091_; 
v___x_5091_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_5064_ = v___x_5091_;
goto v___jp_5063_;
}
v___jp_5063_:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5065_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5065_, 0, v___y_5064_);
v___x_5066_ = l_Lean_MessageData_ofFormat(v___x_5065_);
v___x_5067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5062_);
lean_ctor_set(v___x_5067_, 1, v___x_5066_);
v___x_5068_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5059_, v___x_5067_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_);
if (lean_obj_tag(v___x_5068_) == 0)
{
lean_dec_ref(v___x_5068_);
v___y_5040_ = v_a_5029_;
v___y_5041_ = v_a_5030_;
v___y_5042_ = v_a_5031_;
v___y_5043_ = v_a_5032_;
v___y_5044_ = v_a_5033_;
v___y_5045_ = v_a_5034_;
v___y_5046_ = v_a_5035_;
v___y_5047_ = v_a_5036_;
v___y_5048_ = v_a_5037_;
goto v___jp_5039_;
}
else
{
lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5076_; 
lean_dec_ref(v_p_5028_);
v_a_5069_ = lean_ctor_get(v___x_5068_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5068_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5071_ = v___x_5068_;
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_a_5069_);
lean_dec(v___x_5068_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5074_; 
if (v_isShared_5072_ == 0)
{
v___x_5074_ = v___x_5071_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_a_5069_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5092_; 
v___x_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5092_, 0, v_p_5028_);
return v___x_5092_;
}
}
v___jp_5039_:
{
lean_object* v___x_5049_; 
v___x_5049_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_5028_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5051_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
lean_inc(v_a_5050_);
lean_dec_ref(v___x_5049_);
v___x_5051_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_a_5050_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_);
return v___x_5051_;
}
else
{
return v___x_5049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___boxed(lean_object* v_p_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_){
_start:
{
uint8_t v_a_boxed_5104_; lean_object* v_res_5105_; 
v_a_boxed_5104_ = lean_unbox(v_a_5097_);
v_res_5105_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_p_5093_, v_a_5094_, v_a_5095_, v_a_5096_, v_a_boxed_5104_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
lean_dec(v_a_5102_);
lean_dec_ref(v_a_5101_);
lean_dec(v_a_5100_);
lean_dec_ref(v_a_5099_);
lean_dec(v_a_5098_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec(v_a_5094_);
return v_res_5105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___boxed(lean_object* v_p_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_){
_start:
{
uint8_t v_a_boxed_5117_; lean_object* v_res_5118_; 
v_a_boxed_5117_ = lean_unbox(v_a_5110_);
v_res_5118_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_p_5106_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_boxed_5117_, v_a_5111_, v_a_5112_, v_a_5113_, v_a_5114_, v_a_5115_);
lean_dec(v_a_5115_);
lean_dec_ref(v_a_5114_);
lean_dec(v_a_5113_);
lean_dec_ref(v_a_5112_);
lean_dec(v_a_5111_);
lean_dec_ref(v_a_5109_);
lean_dec(v_a_5108_);
lean_dec(v_a_5107_);
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(lean_object* v_cls_5119_, lean_object* v_msg_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, uint8_t v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_){
_start:
{
lean_object* v___x_5131_; 
v___x_5131_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5119_, v_msg_5120_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_);
return v___x_5131_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___boxed(lean_object* v_cls_5132_, lean_object* v_msg_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_){
_start:
{
uint8_t v___y_22338__boxed_5144_; lean_object* v_res_5145_; 
v___y_22338__boxed_5144_ = lean_unbox(v___y_5137_);
v_res_5145_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(v_cls_5132_, v_msg_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_22338__boxed_5144_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_);
lean_dec(v___y_5142_);
lean_dec_ref(v___y_5141_);
lean_dec(v___y_5140_);
lean_dec_ref(v___y_5139_);
lean_dec(v___y_5138_);
lean_dec_ref(v___y_5136_);
lean_dec(v___y_5135_);
lean_dec(v___y_5134_);
return v_res_5145_;
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
