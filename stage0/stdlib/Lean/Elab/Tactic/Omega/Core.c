// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.Core
// Imports: public import Lean.Elab.Tactic.Omega.OmegaM public import Lean.Elab.Tactic.Omega.MinNatAbs import Lean.OrderLevel
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLENat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5_value),LEAN_SCALAR_PTR_LITERAL(211, 47, 64, 46, 87, 101, 57, 105)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Coeffs"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "length"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__7_value),LEAN_SCALAR_PTR_LITERAL(200, 12, 56, 206, 160, 32, 217, 148)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8_value),LEAN_SCALAR_PTR_LITERAL(170, 70, 58, 212, 39, 249, 136, 90)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "get"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__7_value),LEAN_SCALAR_PTR_LITERAL(200, 12, 56, 206, 160, 32, 217, 148)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__10_value),LEAN_SCALAR_PTR_LITERAL(90, 92, 99, 234, 53, 138, 153, 24)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "bmod_div_term"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12_value),LEAN_SCALAR_PTR_LITERAL(146, 160, 30, 167, 226, 78, 110, 197)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bmod_sat"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__4_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__10_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 76, 155, 247, 209, 92, 141, 248)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__14_value),LEAN_SCALAR_PTR_LITERAL(53, 80, 238, 64, 134, 240, 94, 90)}};
static const lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16;
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
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Invalid constraint, expected an equation."};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "When solving hard equality, new atom had been seen before!"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "When solving hard equality, there were unexpected new facts!"};
static const lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__6;
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
lean_inc_ref(v___y_219_);
v___x_221_ = l_Lean_mkAppB(v___y_219_, v_type_216_, v___y_220_);
v___x_222_ = l_Lean_Expr_app___override(v___y_218_, v___x_221_);
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
v___y_218_ = v___x_225_;
v___y_219_ = v___x_229_;
v___y_220_ = v___x_237_;
goto v___jp_217_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = l_Int_toNat(v_val_228_);
v___x_239_ = l_Lean_instToExprInt_mkNat(v___x_238_);
v___y_218_ = v___x_225_;
v___y_219_ = v___x_229_;
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
lean_dec_ref_known(v_x_692_, 3);
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
lean_dec_ref_known(v_upperBound_695_, 1);
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
lean_dec_ref_known(v_lowerBound_694_, 1);
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
lean_dec_ref_known(v_lowerBound_694_, 1);
v_val_750_ = lean_ctor_get(v_upperBound_695_, 0);
lean_inc(v_val_750_);
lean_dec_ref_known(v_upperBound_695_, 1);
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
lean_dec_ref_known(v_x_692_, 3);
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
lean_dec_ref_known(v_upperBound_861_, 1);
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
lean_dec_ref_known(v_lowerBound_860_, 1);
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
lean_dec_ref_known(v_lowerBound_860_, 1);
v_val_893_ = lean_ctor_get(v_upperBound_861_, 0);
lean_inc(v_val_893_);
lean_dec_ref_known(v_upperBound_861_, 1);
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
lean_dec_ref_known(v_x_692_, 5);
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
lean_dec_ref_known(v_upperBound_929_, 1);
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
lean_dec_ref_known(v_lowerBound_928_, 1);
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
lean_dec_ref_known(v_lowerBound_928_, 1);
v_val_990_ = lean_ctor_get(v_upperBound_929_, 0);
lean_inc(v_val_990_);
lean_dec_ref_known(v_upperBound_929_, 1);
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
lean_dec_ref_known(v_x_692_, 8);
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
lean_dec_ref_known(v_upperBound_1048_, 1);
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
lean_dec_ref_known(v_lowerBound_1047_, 1);
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
lean_dec_ref_known(v_lowerBound_1047_, 1);
v_val_1117_ = lean_ctor_get(v_upperBound_1048_, 0);
lean_inc(v_val_1117_);
lean_dec_ref_known(v_upperBound_1048_, 1);
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
lean_dec_ref_known(v_x_692_, 5);
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
lean_dec_ref_known(v_upperBound_1172_, 1);
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
lean_dec_ref_known(v_lowerBound_1171_, 1);
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
lean_dec_ref_known(v_lowerBound_1171_, 1);
v_val_1237_ = lean_ctor_get(v_upperBound_1172_, 0);
lean_inc(v_val_1237_);
lean_dec_ref_known(v_upperBound_1172_, 1);
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
lean_inc_ref(v___y_1337_);
v___x_1340_ = l_Lean_mkAppB(v___y_1337_, v_type_1335_, v___y_1339_);
v___x_1341_ = l_Lean_Expr_app___override(v___y_1338_, v___x_1340_);
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
v___y_1337_ = v___x_1348_;
v___y_1338_ = v___x_1344_;
v___y_1339_ = v___x_1356_;
goto v___jp_1336_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = l_Int_toNat(v_val_1347_);
v___x_1358_ = l_Lean_instToExprInt_mkNat(v___x_1357_);
v___y_1337_ = v___x_1348_;
v___y_1338_ = v___x_1344_;
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
v___x_1410_ = l_Lean_mkAppB(v___y_1406_, v___y_1407_, v___y_1409_);
v___x_1411_ = l_Lean_Expr_app___override(v___y_1408_, v___x_1410_);
v___y_1398_ = v___y_1405_;
v___y_1399_ = v___x_1411_;
goto v___jp_1397_;
}
v___jp_1412_:
{
lean_object* v_upperBound_1418_; lean_object* v___x_1419_; 
v_upperBound_1418_ = lean_ctor_get(v_t_1390_, 1);
lean_inc_ref(v___y_1414_);
v___x_1419_ = l_Lean_Expr_app___override(v___y_1414_, v___y_1417_);
if (lean_obj_tag(v_upperBound_1418_) == 0)
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1421_ = l_Lean_Expr_app___override(v___x_1420_, v___y_1416_);
v___x_1422_ = l_Lean_Expr_app___override(v___x_1419_, v___x_1421_);
v___y_1398_ = v___y_1413_;
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
lean_inc_ref(v___y_1416_);
v___x_1434_ = l_Lean_mkApp3(v___x_1427_, v___y_1416_, v___x_1430_, v___x_1433_);
v___y_1405_ = v___y_1413_;
v___y_1406_ = v___x_1424_;
v___y_1407_ = v___y_1416_;
v___y_1408_ = v___x_1419_;
v___y_1409_ = v___x_1434_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = l_Int_toNat(v_val_1423_);
v___x_1436_ = l_Lean_instToExprInt_mkNat(v___x_1435_);
v___y_1405_ = v___y_1413_;
v___y_1406_ = v___x_1424_;
v___y_1407_ = v___y_1416_;
v___y_1408_ = v___x_1419_;
v___y_1409_ = v___x_1436_;
goto v___jp_1404_;
}
}
}
v___jp_1437_:
{
lean_object* v___x_1444_; 
lean_inc_ref(v___y_1442_);
lean_inc_ref(v___y_1439_);
v___x_1444_ = l_Lean_mkAppB(v___y_1439_, v___y_1442_, v___y_1443_);
v___y_1413_ = v___y_1438_;
v___y_1414_ = v___y_1440_;
v___y_1415_ = v___y_1441_;
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
v___y_1413_ = v___y_1446_;
v___y_1414_ = v___x_1448_;
v___y_1415_ = v___x_1449_;
v___y_1416_ = v_type_1450_;
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
v___y_1438_ = v___y_1446_;
v___y_1439_ = v___x_1453_;
v___y_1440_ = v___x_1448_;
v___y_1441_ = v___x_1449_;
v___y_1442_ = v_type_1450_;
v___y_1443_ = v___x_1461_;
goto v___jp_1437_;
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = l_Int_toNat(v_val_1452_);
v___x_1463_ = l_Lean_instToExprInt_mkNat(v___x_1462_);
v___y_1438_ = v___y_1446_;
v___y_1439_ = v___x_1453_;
v___y_1440_ = v___x_1448_;
v___y_1441_ = v___x_1449_;
v___y_1442_ = v_type_1450_;
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
v___x_1541_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v___y_1539_, v___y_1538_, v_y_1527_);
v___x_1542_ = l_Lean_mkApp9(v___x_1532_, v___y_1537_, v___y_1536_, v___y_1535_, v___y_1534_, v___y_1540_, v___x_1541_, v_v_1528_, v_px_1529_, v_py_1530_);
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
v___y_1534_ = v___x_1550_;
v___y_1535_ = v___y_1546_;
v___y_1536_ = v___y_1544_;
v___y_1537_ = v___y_1545_;
v___y_1538_ = v_cons_1549_;
v___y_1539_ = v_nil_1548_;
v___y_1540_ = v___x_1558_;
goto v___jp_1533_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = l_Int_toNat(v_b_1526_);
v___x_1560_ = l_Lean_instToExprInt_mkNat(v___x_1559_);
v___y_1534_ = v___x_1550_;
v___y_1535_ = v___y_1546_;
v___y_1536_ = v___y_1544_;
v___y_1537_ = v___y_1545_;
v___y_1538_ = v_cons_1549_;
v___y_1539_ = v_nil_1548_;
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
v___y_1544_ = v___y_1563_;
v___y_1545_ = v___y_1562_;
v___y_1546_ = v___x_1572_;
goto v___jp_1543_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = l_Int_toNat(v_a_1524_);
v___x_1574_ = l_Lean_instToExprInt_mkNat(v___x_1573_);
v___y_1544_ = v___y_1563_;
v___y_1545_ = v___y_1562_;
v___y_1546_ = v___x_1574_;
goto v___jp_1543_;
}
}
v___jp_1575_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_inc_ref(v___y_1576_);
v___x_1581_ = l_Lean_mkAppB(v___y_1576_, v___y_1578_, v___y_1580_);
v___x_1582_ = l_Lean_Expr_app___override(v___y_1577_, v___x_1581_);
v___y_1562_ = v___y_1579_;
v___y_1563_ = v___x_1582_;
goto v___jp_1561_;
}
v___jp_1583_:
{
lean_object* v_upperBound_1589_; lean_object* v___x_1590_; 
v_upperBound_1589_ = lean_ctor_get(v_t_1523_, 1);
lean_inc_ref(v___y_1586_);
v___x_1590_ = l_Lean_Expr_app___override(v___y_1586_, v___y_1588_);
if (lean_obj_tag(v_upperBound_1589_) == 0)
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1592_ = l_Lean_Expr_app___override(v___x_1591_, v___y_1585_);
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
lean_inc_ref(v___y_1584_);
v___x_1600_ = l_Lean_Name_mkStr2(v___y_1584_, v___x_1599_);
v___x_1601_ = l_Lean_Expr_const___override(v___x_1600_, v___x_1531_);
v___x_1602_ = lean_int_neg(v_val_1594_);
v___x_1603_ = l_Int_toNat(v___x_1602_);
lean_dec(v___x_1602_);
v___x_1604_ = l_Lean_instToExprInt_mkNat(v___x_1603_);
lean_inc_ref(v___y_1585_);
v___x_1605_ = l_Lean_mkApp3(v___x_1598_, v___y_1585_, v___x_1601_, v___x_1604_);
v___y_1576_ = v___x_1595_;
v___y_1577_ = v___x_1590_;
v___y_1578_ = v___y_1585_;
v___y_1579_ = v___y_1587_;
v___y_1580_ = v___x_1605_;
goto v___jp_1575_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = l_Int_toNat(v_val_1594_);
v___x_1607_ = l_Lean_instToExprInt_mkNat(v___x_1606_);
v___y_1576_ = v___x_1595_;
v___y_1577_ = v___x_1590_;
v___y_1578_ = v___y_1585_;
v___y_1579_ = v___y_1587_;
v___y_1580_ = v___x_1607_;
goto v___jp_1575_;
}
}
}
v___jp_1608_:
{
lean_object* v___x_1615_; 
lean_inc_ref(v___y_1611_);
lean_inc_ref(v___y_1613_);
v___x_1615_ = l_Lean_mkAppB(v___y_1613_, v___y_1611_, v___y_1614_);
v___y_1584_ = v___y_1609_;
v___y_1585_ = v___y_1611_;
v___y_1586_ = v___y_1610_;
v___y_1587_ = v___y_1612_;
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
v___y_1584_ = v___x_1620_;
v___y_1585_ = v_type_1621_;
v___y_1586_ = v___x_1619_;
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
v___y_1609_ = v___x_1620_;
v___y_1610_ = v___x_1619_;
v___y_1611_ = v_type_1621_;
v___y_1612_ = v___y_1617_;
v___y_1613_ = v___x_1624_;
v___y_1614_ = v___x_1632_;
goto v___jp_1608_;
}
else
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = l_Int_toNat(v_val_1623_);
v___x_1634_ = l_Lean_instToExprInt_mkNat(v___x_1633_);
v___y_1609_ = v___x_1620_;
v___y_1610_ = v___x_1619_;
v___y_1611_ = v_type_1621_;
v___y_1612_ = v___y_1617_;
v___y_1613_ = v___x_1624_;
v___y_1614_ = v___x_1634_;
goto v___jp_1608_;
}
}
}
v___jp_1639_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_inc_ref(v___y_1640_);
v___x_1643_ = l_Lean_mkAppB(v___y_1640_, v_type_1638_, v___y_1642_);
v___x_1644_ = l_Lean_Expr_app___override(v___y_1641_, v___x_1643_);
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
v___y_1640_ = v___x_1651_;
v___y_1641_ = v___x_1647_;
v___y_1642_ = v___x_1659_;
goto v___jp_1639_;
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = l_Int_toNat(v_val_1650_);
v___x_1661_ = l_Lean_instToExprInt_mkNat(v___x_1660_);
v___y_1640_ = v___x_1651_;
v___y_1641_ = v___x_1647_;
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
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_unsigned_to_nat(1u);
v___x_1723_ = l_Lean_Level_ofNat(v___x_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof(lean_object* v_m_1724_, lean_object* v_r_1725_, lean_object* v_i_1726_, lean_object* v_x_1727_, lean_object* v_v_1728_, lean_object* v_w_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_m_1735_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v_____do__lift_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1778_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v_m_1735_ = l_Lean_mkNatLit(v_m_1724_);
v___x_1797_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1798_ = lean_int_dec_le(v___x_1797_, v_r_1725_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1799_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1800_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1801_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1802_ = lean_int_neg(v_r_1725_);
v___x_1803_ = l_Int_toNat(v___x_1802_);
lean_dec(v___x_1802_);
v___x_1804_ = l_Lean_instToExprInt_mkNat(v___x_1803_);
v___x_1805_ = l_Lean_mkApp3(v___x_1799_, v___x_1800_, v___x_1801_, v___x_1804_);
v___y_1778_ = v___x_1805_;
goto v___jp_1777_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = l_Int_toNat(v_r_1725_);
v___x_1807_ = l_Lean_instToExprInt_mkNat(v___x_1806_);
v___y_1778_ = v___x_1807_;
goto v___jp_1777_;
}
v___jp_1736_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1746_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2));
lean_inc_n(v___y_1739_, 4);
lean_inc(v_____do__lift_1741_);
v___x_1747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_____do__lift_1741_);
lean_ctor_set(v___x_1747_, 1, v___y_1739_);
v___x_1748_ = l_Lean_Expr_const___override(v___x_1746_, v___x_1747_);
v___x_1749_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__4));
v___x_1750_ = l_Lean_Expr_const___override(v___x_1749_, v___y_1739_);
v___x_1751_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6));
v___x_1752_ = l_Lean_Expr_const___override(v___x_1751_, v___y_1739_);
v___x_1753_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9));
v___x_1754_ = l_Lean_Expr_const___override(v___x_1753_, v___y_1739_);
lean_inc_ref(v___y_1737_);
v___x_1755_ = l_Lean_Expr_app___override(v___x_1754_, v___y_1737_);
lean_inc_ref(v___y_1738_);
v___x_1756_ = l_Lean_mkApp4(v___x_1748_, v___x_1750_, v___x_1752_, v___x_1755_, v___y_1738_);
v___x_1757_ = l_Lean_Meta_mkDecideProof(v___x_1756_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11));
lean_inc_n(v___y_1739_, 2);
v___x_1760_ = l_Lean_Expr_const___override(v___x_1759_, v___y_1739_);
lean_inc_ref(v___y_1738_);
lean_inc_ref_n(v_v_1728_, 2);
v___x_1761_ = l_Lean_mkAppB(v___x_1760_, v_v_1728_, v___y_1738_);
v___x_1762_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13));
v___x_1763_ = l_Lean_Expr_const___override(v___x_1762_, v___y_1739_);
lean_inc_ref(v___y_1737_);
lean_inc_ref(v_m_1735_);
v___x_1764_ = l_Lean_mkApp3(v___x_1763_, v_m_1735_, v___y_1737_, v_v_1728_);
v___x_1765_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v___x_1761_, v___x_1764_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1776_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1776_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1776_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1770_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15));
lean_inc(v___y_1739_);
v___x_1771_ = l_Lean_Expr_const___override(v___x_1770_, v___y_1739_);
v___x_1772_ = l_Lean_mkApp8(v___x_1771_, v_m_1735_, v___y_1740_, v___y_1738_, v___y_1737_, v_v_1728_, v_a_1758_, v_a_1766_, v_w_1729_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1772_);
v___x_1774_ = v___x_1768_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
else
{
lean_dec(v_a_1758_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v_m_1735_);
lean_dec_ref(v_w_1729_);
lean_dec_ref(v_v_1728_);
return v___x_1765_;
}
}
else
{
lean_dec_ref(v___y_1740_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v_m_1735_);
lean_dec_ref(v_w_1729_);
lean_dec_ref(v_v_1728_);
return v___x_1757_;
}
}
v___jp_1777_:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_leCarrierIsSort(v_a_1732_, v_a_1733_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1781_; lean_object* v_nil_1782_; lean_object* v_i_1783_; lean_object* v_cons_1784_; lean_object* v_x_1785_; uint8_t v___x_1786_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref_known(v___x_1779_, 1);
v___x_1781_ = lean_box(0);
v_nil_1782_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_i_1783_ = l_Lean_mkNatLit(v_i_1726_);
v_cons_1784_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v_x_1785_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1782_, v_cons_1784_, v_x_1727_);
v___x_1786_ = lean_unbox(v_a_1780_);
lean_dec(v_a_1780_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21);
v___y_1737_ = v_x_1785_;
v___y_1738_ = v_i_1783_;
v___y_1739_ = v___x_1781_;
v___y_1740_ = v___y_1778_;
v_____do__lift_1741_ = v___x_1787_;
v___y_1742_ = v_a_1730_;
v___y_1743_ = v_a_1731_;
v___y_1744_ = v_a_1732_;
v___y_1745_ = v_a_1733_;
goto v___jp_1736_;
}
else
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16);
v___y_1737_ = v_x_1785_;
v___y_1738_ = v_i_1783_;
v___y_1739_ = v___x_1781_;
v___y_1740_ = v___y_1778_;
v_____do__lift_1741_ = v___x_1788_;
v___y_1742_ = v_a_1730_;
v___y_1743_ = v_a_1731_;
v___y_1744_ = v_a_1732_;
v___y_1745_ = v_a_1733_;
goto v___jp_1736_;
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v___y_1778_);
lean_dec_ref(v_m_1735_);
lean_dec_ref(v_w_1729_);
lean_dec_ref(v_v_1728_);
lean_dec(v_i_1726_);
v_a_1789_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1779_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1779_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___boxed(lean_object* v_m_1808_, lean_object* v_r_1809_, lean_object* v_i_1810_, lean_object* v_x_1811_, lean_object* v_v_1812_, lean_object* v_w_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1808_, v_r_1809_, v_i_1810_, v_x_1811_, v_v_1812_, v_w_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_x_1811_);
lean_dec(v_r_1809_);
return v_res_1819_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0(void){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_instMonadEIO(lean_box(0));
return v___x_1820_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0);
v___x_1822_ = l_StateRefT_x27_instMonad___redArg(v___x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(lean_object* v_c_1827_, lean_object* v_v_1828_, lean_object* v_assumptions_1829_, lean_object* v_x_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, uint8_t v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v___x_1841_; lean_object* v_toApplicative_1842_; lean_object* v_toFunctor_1843_; lean_object* v_toSeq_1844_; lean_object* v_toSeqLeft_1845_; lean_object* v_toSeqRight_1846_; lean_object* v___f_1847_; lean_object* v___f_1848_; lean_object* v___f_1849_; lean_object* v___f_1850_; lean_object* v___x_1851_; lean_object* v___f_1852_; lean_object* v___f_1853_; lean_object* v___f_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v_toApplicative_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1953_; 
v___x_1841_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1);
v_toApplicative_1842_ = lean_ctor_get(v___x_1841_, 0);
v_toFunctor_1843_ = lean_ctor_get(v_toApplicative_1842_, 0);
v_toSeq_1844_ = lean_ctor_get(v_toApplicative_1842_, 2);
v_toSeqLeft_1845_ = lean_ctor_get(v_toApplicative_1842_, 3);
v_toSeqRight_1846_ = lean_ctor_get(v_toApplicative_1842_, 4);
v___f_1847_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2));
v___f_1848_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1843_, 2);
v___f_1849_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1849_, 0, v_toFunctor_1843_);
v___f_1850_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1850_, 0, v_toFunctor_1843_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___f_1849_);
lean_ctor_set(v___x_1851_, 1, v___f_1850_);
lean_inc(v_toSeqRight_1846_);
v___f_1852_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1852_, 0, v_toSeqRight_1846_);
lean_inc(v_toSeqLeft_1845_);
v___f_1853_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1853_, 0, v_toSeqLeft_1845_);
lean_inc(v_toSeq_1844_);
v___f_1854_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1854_, 0, v_toSeq_1844_);
v___x_1855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1851_);
lean_ctor_set(v___x_1855_, 1, v___f_1847_);
lean_ctor_set(v___x_1855_, 2, v___f_1854_);
lean_ctor_set(v___x_1855_, 3, v___f_1853_);
lean_ctor_set(v___x_1855_, 4, v___f_1852_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v___f_1848_);
v___x_1857_ = l_StateRefT_x27_instMonad___redArg(v___x_1856_);
v_toApplicative_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; 
v_unused_1954_ = lean_ctor_get(v___x_1857_, 1);
lean_dec(v_unused_1954_);
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1953_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_toApplicative_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1953_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v_toFunctor_1862_; lean_object* v_toSeq_1863_; lean_object* v_toSeqLeft_1864_; lean_object* v_toSeqRight_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1951_; 
v_toFunctor_1862_ = lean_ctor_get(v_toApplicative_1858_, 0);
v_toSeq_1863_ = lean_ctor_get(v_toApplicative_1858_, 2);
v_toSeqLeft_1864_ = lean_ctor_get(v_toApplicative_1858_, 3);
v_toSeqRight_1865_ = lean_ctor_get(v_toApplicative_1858_, 4);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_toApplicative_1858_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v_toApplicative_1858_, 1);
lean_dec(v_unused_1952_);
v___x_1867_ = v_toApplicative_1858_;
v_isShared_1868_ = v_isSharedCheck_1951_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_toSeqRight_1865_);
lean_inc(v_toSeqLeft_1864_);
lean_inc(v_toSeq_1863_);
lean_inc(v_toFunctor_1862_);
lean_dec(v_toApplicative_1858_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1951_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___f_1869_; lean_object* v___f_1870_; lean_object* v___f_1871_; lean_object* v___f_1872_; lean_object* v___x_1873_; lean_object* v___f_1874_; lean_object* v___f_1875_; lean_object* v___f_1876_; lean_object* v___x_1878_; 
v___f_1869_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4));
v___f_1870_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5));
lean_inc_ref(v_toFunctor_1862_);
v___f_1871_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1871_, 0, v_toFunctor_1862_);
v___f_1872_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1872_, 0, v_toFunctor_1862_);
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___f_1871_);
lean_ctor_set(v___x_1873_, 1, v___f_1872_);
v___f_1874_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1874_, 0, v_toSeqRight_1865_);
v___f_1875_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1875_, 0, v_toSeqLeft_1864_);
v___f_1876_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1876_, 0, v_toSeq_1863_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 4, v___f_1874_);
lean_ctor_set(v___x_1867_, 3, v___f_1875_);
lean_ctor_set(v___x_1867_, 2, v___f_1876_);
lean_ctor_set(v___x_1867_, 1, v___f_1869_);
lean_ctor_set(v___x_1867_, 0, v___x_1873_);
v___x_1878_ = v___x_1867_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v___f_1869_);
lean_ctor_set(v_reuseFailAlloc_1950_, 2, v___f_1876_);
lean_ctor_set(v_reuseFailAlloc_1950_, 3, v___f_1875_);
lean_ctor_set(v_reuseFailAlloc_1950_, 4, v___f_1874_);
v___x_1878_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1880_; 
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 1, v___f_1870_);
lean_ctor_set(v___x_1860_, 0, v___x_1878_);
v___x_1880_ = v___x_1860_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v___f_1870_);
v___x_1880_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1881_ = l_StateRefT_x27_instMonad___redArg(v___x_1880_);
v___x_1882_ = l_ReaderT_instMonad___redArg(v___x_1881_);
v___x_1883_ = l_ReaderT_instMonad___redArg(v___x_1882_);
v___x_1884_ = l_StateRefT_x27_instMonad___redArg(v___x_1883_);
v___x_1885_ = l_StateRefT_x27_instMonad___redArg(v___x_1884_);
switch(lean_obj_tag(v_x_1830_))
{
case 0:
{
lean_object* v_i_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_4010__overap_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec_ref(v_v_1828_);
v_i_1886_ = lean_ctor_get(v_x_1830_, 2);
lean_inc(v_i_1886_);
lean_dec_ref_known(v_x_1830_, 3);
v___x_1887_ = l_Lean_instInhabitedExpr;
v___x_1888_ = l_instInhabitedOfMonad___redArg(v___x_1885_, v___x_1887_);
v___x_4010__overap_1889_ = lean_array_get(v___x_1888_, v_assumptions_1829_, v_i_1886_);
lean_dec(v_i_1886_);
lean_dec(v___x_1888_);
v___x_1890_ = lean_box(v_a_1834_);
lean_inc(v_a_1839_);
lean_inc_ref(v_a_1838_);
lean_inc(v_a_1837_);
lean_inc_ref(v_a_1836_);
lean_inc(v_a_1835_);
lean_inc_ref(v_a_1833_);
lean_inc(v_a_1832_);
lean_inc(v_a_1831_);
v___x_1891_ = lean_apply_10(v___x_4010__overap_1889_, v_a_1831_, v_a_1832_, v_a_1833_, v___x_1890_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, lean_box(0));
return v___x_1891_;
}
case 1:
{
lean_object* v_s_1892_; lean_object* v_c_1893_; lean_object* v_j_1894_; lean_object* v___x_1895_; 
lean_dec_ref(v___x_1885_);
v_s_1892_ = lean_ctor_get(v_x_1830_, 0);
lean_inc_ref(v_s_1892_);
v_c_1893_ = lean_ctor_get(v_x_1830_, 1);
lean_inc(v_c_1893_);
v_j_1894_ = lean_ctor_get(v_x_1830_, 2);
lean_inc_ref(v_j_1894_);
lean_dec_ref_known(v_x_1830_, 3);
lean_inc_ref(v_v_1828_);
v___x_1895_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1893_, v_v_1828_, v_assumptions_1829_, v_j_1894_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1904_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1904_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1904_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; lean_object* v___x_1902_; 
v___x_1900_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1892_, v_c_1893_, v_v_1828_, v_a_1896_);
lean_dec(v_c_1893_);
lean_dec_ref(v_s_1892_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1900_);
v___x_1902_ = v___x_1898_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
else
{
lean_dec(v_c_1893_);
lean_dec_ref(v_s_1892_);
lean_dec_ref(v_v_1828_);
return v___x_1895_;
}
}
case 2:
{
lean_object* v_s_1905_; lean_object* v_t_1906_; lean_object* v_j_1907_; lean_object* v_k_1908_; lean_object* v___x_1909_; 
lean_dec_ref(v___x_1885_);
v_s_1905_ = lean_ctor_get(v_x_1830_, 0);
lean_inc_ref(v_s_1905_);
v_t_1906_ = lean_ctor_get(v_x_1830_, 1);
lean_inc_ref(v_t_1906_);
v_j_1907_ = lean_ctor_get(v_x_1830_, 3);
lean_inc_ref(v_j_1907_);
v_k_1908_ = lean_ctor_get(v_x_1830_, 4);
lean_inc_ref(v_k_1908_);
lean_dec_ref_known(v_x_1830_, 5);
lean_inc_ref(v_v_1828_);
v___x_1909_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1827_, v_v_1828_, v_assumptions_1829_, v_j_1907_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1911_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
lean_inc_ref(v_v_1828_);
v___x_1911_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1827_, v_v_1828_, v_assumptions_1829_, v_k_1908_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1920_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1916_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1905_, v_t_1906_, v_c_1827_, v_v_1828_, v_a_1910_, v_a_1912_);
lean_dec_ref(v_t_1906_);
lean_dec_ref(v_s_1905_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v___x_1916_);
v___x_1918_ = v___x_1914_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
else
{
lean_dec(v_a_1910_);
lean_dec_ref(v_t_1906_);
lean_dec_ref(v_s_1905_);
lean_dec_ref(v_v_1828_);
return v___x_1911_;
}
}
else
{
lean_dec_ref(v_k_1908_);
lean_dec_ref(v_t_1906_);
lean_dec_ref(v_s_1905_);
lean_dec_ref(v_v_1828_);
return v___x_1909_;
}
}
case 3:
{
lean_object* v_s_1921_; lean_object* v_t_1922_; lean_object* v_x_1923_; lean_object* v_y_1924_; lean_object* v_a_1925_; lean_object* v_j_1926_; lean_object* v_b_1927_; lean_object* v_k_1928_; lean_object* v___x_1929_; 
lean_dec_ref(v___x_1885_);
v_s_1921_ = lean_ctor_get(v_x_1830_, 0);
lean_inc_ref(v_s_1921_);
v_t_1922_ = lean_ctor_get(v_x_1830_, 1);
lean_inc_ref(v_t_1922_);
v_x_1923_ = lean_ctor_get(v_x_1830_, 2);
lean_inc(v_x_1923_);
v_y_1924_ = lean_ctor_get(v_x_1830_, 3);
lean_inc(v_y_1924_);
v_a_1925_ = lean_ctor_get(v_x_1830_, 4);
lean_inc(v_a_1925_);
v_j_1926_ = lean_ctor_get(v_x_1830_, 5);
lean_inc_ref(v_j_1926_);
v_b_1927_ = lean_ctor_get(v_x_1830_, 6);
lean_inc(v_b_1927_);
v_k_1928_ = lean_ctor_get(v_x_1830_, 7);
lean_inc_ref(v_k_1928_);
lean_dec_ref_known(v_x_1830_, 8);
lean_inc_ref(v_v_1828_);
v___x_1929_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1923_, v_v_1828_, v_assumptions_1829_, v_j_1926_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1931_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
lean_inc_ref(v_v_1828_);
v___x_1931_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_y_1924_, v_v_1828_, v_assumptions_1829_, v_k_1928_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1940_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1940_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1940_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1936_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1921_, v_t_1922_, v_a_1925_, v_x_1923_, v_b_1927_, v_y_1924_, v_v_1828_, v_a_1930_, v_a_1932_);
lean_dec(v_y_1924_);
lean_dec(v_b_1927_);
lean_dec(v_x_1923_);
lean_dec(v_a_1925_);
lean_dec_ref(v_t_1922_);
lean_dec_ref(v_s_1921_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v___x_1936_);
v___x_1938_ = v___x_1934_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
else
{
lean_dec(v_a_1930_);
lean_dec(v_b_1927_);
lean_dec(v_a_1925_);
lean_dec(v_y_1924_);
lean_dec(v_x_1923_);
lean_dec_ref(v_t_1922_);
lean_dec_ref(v_s_1921_);
lean_dec_ref(v_v_1828_);
return v___x_1931_;
}
}
else
{
lean_dec_ref(v_k_1928_);
lean_dec(v_b_1927_);
lean_dec(v_a_1925_);
lean_dec(v_y_1924_);
lean_dec(v_x_1923_);
lean_dec_ref(v_t_1922_);
lean_dec_ref(v_s_1921_);
lean_dec_ref(v_v_1828_);
return v___x_1929_;
}
}
default: 
{
lean_object* v_m_1941_; lean_object* v_r_1942_; lean_object* v_i_1943_; lean_object* v_x_1944_; lean_object* v_j_1945_; lean_object* v___x_1946_; 
lean_dec_ref(v___x_1885_);
v_m_1941_ = lean_ctor_get(v_x_1830_, 0);
lean_inc(v_m_1941_);
v_r_1942_ = lean_ctor_get(v_x_1830_, 1);
lean_inc(v_r_1942_);
v_i_1943_ = lean_ctor_get(v_x_1830_, 2);
lean_inc(v_i_1943_);
v_x_1944_ = lean_ctor_get(v_x_1830_, 3);
lean_inc(v_x_1944_);
v_j_1945_ = lean_ctor_get(v_x_1830_, 4);
lean_inc_ref(v_j_1945_);
lean_dec_ref_known(v_x_1830_, 5);
lean_inc_ref(v_v_1828_);
v___x_1946_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1944_, v_v_1828_, v_assumptions_1829_, v_j_1945_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1948_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
v___x_1948_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1941_, v_r_1942_, v_i_1943_, v_x_1944_, v_v_1828_, v_a_1947_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec(v_x_1944_);
lean_dec(v_r_1942_);
return v___x_1948_;
}
else
{
lean_dec(v_x_1944_);
lean_dec(v_i_1943_);
lean_dec(v_r_1942_);
lean_dec(v_m_1941_);
lean_dec_ref(v_v_1828_);
return v___x_1946_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___boxed(lean_object* v_c_1955_, lean_object* v_v_1956_, lean_object* v_assumptions_1957_, lean_object* v_x_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
uint8_t v_a_boxed_1969_; lean_object* v_res_1970_; 
v_a_boxed_1969_ = lean_unbox(v_a_1962_);
v_res_1970_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1955_, v_v_1956_, v_assumptions_1957_, v_x_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_boxed_1969_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec(v_a_1959_);
lean_dec_ref(v_assumptions_1957_);
lean_dec(v_c_1955_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof(lean_object* v_s_1971_, lean_object* v_c_1972_, lean_object* v_v_1973_, lean_object* v_assumptions_1974_, lean_object* v_x_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, uint8_t v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1972_, v_v_1973_, v_assumptions_1974_, v_x_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___boxed(lean_object* v_s_1987_, lean_object* v_c_1988_, lean_object* v_v_1989_, lean_object* v_assumptions_1990_, lean_object* v_x_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
uint8_t v_a_boxed_2002_; lean_object* v_res_2003_; 
v_a_boxed_2002_ = lean_unbox(v_a_1995_);
v_res_2003_ = l_Lean_Elab_Tactic_Omega_Justification_proof(v_s_1987_, v_c_1988_, v_v_1989_, v_assumptions_1990_, v_x_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_boxed_2002_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1994_);
lean_dec(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec_ref(v_assumptions_1990_);
lean_dec(v_c_1988_);
lean_dec_ref(v_s_1987_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_instToString___lam__0(lean_object* v_f_2004_){
_start:
{
lean_object* v_coeffs_2005_; lean_object* v_constraint_2006_; lean_object* v_justification_2007_; lean_object* v___x_2008_; 
v_coeffs_2005_ = lean_ctor_get(v_f_2004_, 0);
lean_inc(v_coeffs_2005_);
v_constraint_2006_ = lean_ctor_get(v_f_2004_, 1);
lean_inc_ref(v_constraint_2006_);
v_justification_2007_ = lean_ctor_get(v_f_2004_, 2);
lean_inc_ref(v_justification_2007_);
lean_dec_ref(v_f_2004_);
v___x_2008_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_2006_, v_coeffs_2005_, v_justification_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_tidy(lean_object* v_f_2011_){
_start:
{
lean_object* v_coeffs_2012_; lean_object* v_constraint_2013_; lean_object* v_justification_2014_; lean_object* v___x_2015_; 
v_coeffs_2012_ = lean_ctor_get(v_f_2011_, 0);
v_constraint_2013_ = lean_ctor_get(v_f_2011_, 1);
v_justification_2014_ = lean_ctor_get(v_f_2011_, 2);
lean_inc_ref(v_justification_2014_);
lean_inc(v_coeffs_2012_);
lean_inc_ref(v_constraint_2013_);
v___x_2015_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(v_constraint_2013_, v_coeffs_2012_, v_justification_2014_);
if (lean_obj_tag(v___x_2015_) == 0)
{
return v_f_2011_;
}
else
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2027_; 
v_isSharedCheck_2027_ = !lean_is_exclusive(v_f_2011_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; lean_object* v_unused_2029_; lean_object* v_unused_2030_; 
v_unused_2028_ = lean_ctor_get(v_f_2011_, 2);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_f_2011_, 1);
lean_dec(v_unused_2029_);
v_unused_2030_ = lean_ctor_get(v_f_2011_, 0);
lean_dec(v_unused_2030_);
v___x_2017_ = v_f_2011_;
v_isShared_2018_ = v_isSharedCheck_2027_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v_f_2011_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2027_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v_val_2019_; lean_object* v_snd_2020_; lean_object* v_fst_2021_; lean_object* v_fst_2022_; lean_object* v_snd_2023_; lean_object* v___x_2025_; 
v_val_2019_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_val_2019_);
lean_dec_ref_known(v___x_2015_, 1);
v_snd_2020_ = lean_ctor_get(v_val_2019_, 1);
lean_inc(v_snd_2020_);
v_fst_2021_ = lean_ctor_get(v_val_2019_, 0);
lean_inc(v_fst_2021_);
lean_dec(v_val_2019_);
v_fst_2022_ = lean_ctor_get(v_snd_2020_, 0);
lean_inc(v_fst_2022_);
v_snd_2023_ = lean_ctor_get(v_snd_2020_, 1);
lean_inc(v_snd_2023_);
lean_dec(v_snd_2020_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 2, v_snd_2023_);
lean_ctor_set(v___x_2017_, 1, v_fst_2021_);
lean_ctor_set(v___x_2017_, 0, v_fst_2022_);
v___x_2025_ = v___x_2017_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_fst_2022_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_fst_2021_);
lean_ctor_set(v_reuseFailAlloc_2026_, 2, v_snd_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_combo(lean_object* v_a_2031_, lean_object* v_f_2032_, lean_object* v_b_2033_, lean_object* v_g_2034_){
_start:
{
lean_object* v_coeffs_2035_; lean_object* v_constraint_2036_; lean_object* v_justification_2037_; lean_object* v_coeffs_2038_; lean_object* v_constraint_2039_; lean_object* v_justification_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2050_; 
v_coeffs_2035_ = lean_ctor_get(v_f_2032_, 0);
lean_inc(v_coeffs_2035_);
v_constraint_2036_ = lean_ctor_get(v_f_2032_, 1);
lean_inc_ref(v_constraint_2036_);
v_justification_2037_ = lean_ctor_get(v_f_2032_, 2);
lean_inc_ref(v_justification_2037_);
lean_dec_ref(v_f_2032_);
v_coeffs_2038_ = lean_ctor_get(v_g_2034_, 0);
v_constraint_2039_ = lean_ctor_get(v_g_2034_, 1);
v_justification_2040_ = lean_ctor_get(v_g_2034_, 2);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_g_2034_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2042_ = v_g_2034_;
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_justification_2040_);
lean_inc(v_constraint_2039_);
lean_inc(v_coeffs_2038_);
lean_dec(v_g_2034_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
lean_inc(v_coeffs_2038_);
lean_inc(v_coeffs_2035_);
v___x_2044_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_2031_, v_b_2033_, v_coeffs_2035_, v_coeffs_2038_);
lean_inc_ref(v_constraint_2039_);
lean_inc(v_b_2033_);
lean_inc_ref(v_constraint_2036_);
lean_inc(v_a_2031_);
v___x_2045_ = l_Lean_Omega_Constraint_combo(v_a_2031_, v_constraint_2036_, v_b_2033_, v_constraint_2039_);
v___x_2046_ = lean_alloc_ctor(3, 8, 0);
lean_ctor_set(v___x_2046_, 0, v_constraint_2036_);
lean_ctor_set(v___x_2046_, 1, v_constraint_2039_);
lean_ctor_set(v___x_2046_, 2, v_coeffs_2035_);
lean_ctor_set(v___x_2046_, 3, v_coeffs_2038_);
lean_ctor_set(v___x_2046_, 4, v_a_2031_);
lean_ctor_set(v___x_2046_, 5, v_justification_2037_);
lean_ctor_set(v___x_2046_, 6, v_b_2033_);
lean_ctor_set(v___x_2046_, 7, v_justification_2040_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 2, v___x_2046_);
lean_ctor_set(v___x_2042_, 1, v___x_2045_);
lean_ctor_set(v___x_2042_, 0, v___x_2044_);
v___x_2048_ = v___x_2042_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__10));
v___x_2077_ = l_Lean_mkAtom(v___x_2076_);
return v___x_2077_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11);
v___x_2079_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2080_ = lean_array_push(v___x_2079_, v___x_2078_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2081_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12);
v___x_2082_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9));
v___x_2083_ = lean_box(2);
v___x_2084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___x_2082_);
lean_ctor_set(v___x_2084_, 2, v___x_2081_);
return v___x_2084_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13);
v___x_2086_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2087_ = lean_array_push(v___x_2086_, v___x_2085_);
return v___x_2087_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2088_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14);
v___x_2089_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7));
v___x_2090_ = lean_box(2);
v___x_2091_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v___x_2089_);
lean_ctor_set(v___x_2091_, 2, v___x_2088_);
return v___x_2091_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15);
v___x_2093_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2094_ = lean_array_push(v___x_2093_, v___x_2092_);
return v___x_2094_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2095_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16);
v___x_2096_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5));
v___x_2097_ = lean_box(2);
v___x_2098_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v___x_2096_);
lean_ctor_set(v___x_2098_, 2, v___x_2095_);
return v___x_2098_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17);
v___x_2100_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2101_ = lean_array_push(v___x_2100_, v___x_2099_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2102_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18);
v___x_2103_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2));
v___x_2104_ = lean_box(2);
v___x_2105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v___x_2103_);
lean_ctor_set(v___x_2105_, 2, v___x_2102_);
return v___x_2105_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam(void){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19);
return v___x_2106_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_isEmpty(lean_object* v_p_2107_){
_start:
{
lean_object* v_constraints_2108_; lean_object* v_size_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v_constraints_2108_ = lean_ctor_get(v_p_2107_, 2);
v_size_2109_ = lean_ctor_get(v_constraints_2108_, 0);
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = lean_nat_dec_eq(v_size_2109_, v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_isEmpty___boxed(lean_object* v_p_2112_){
_start:
{
uint8_t v_res_2113_; lean_object* v_r_2114_; 
v_res_2113_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2112_);
lean_dec_ref(v_p_2112_);
v_r_2114_ = lean_box(v_res_2113_);
return v_r_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object* v_x_2116_){
_start:
{
lean_object* v_snd_2117_; lean_object* v_constraint_2118_; lean_object* v_fst_2119_; lean_object* v_lowerBound_2120_; lean_object* v_upperBound_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___y_2127_; lean_object* v___y_2128_; 
v_snd_2117_ = lean_ctor_get(v_x_2116_, 1);
v_constraint_2118_ = lean_ctor_get(v_snd_2117_, 1);
lean_inc_ref(v_constraint_2118_);
v_fst_2119_ = lean_ctor_get(v_x_2116_, 0);
lean_inc(v_fst_2119_);
lean_dec_ref(v_x_2116_);
v_lowerBound_2120_ = lean_ctor_get(v_constraint_2118_, 0);
lean_inc(v_lowerBound_2120_);
v_upperBound_2121_ = lean_ctor_get(v_constraint_2118_, 1);
lean_inc(v_upperBound_2121_);
lean_dec_ref(v_constraint_2118_);
v___x_2122_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0___closed__0));
v___x_2123_ = l_List_toString___redArg(v___x_2122_, v_fst_2119_);
v___x_2124_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_2125_ = lean_string_append(v___x_2123_, v___x_2124_);
if (lean_obj_tag(v_lowerBound_2120_) == 0)
{
if (lean_obj_tag(v_upperBound_2121_) == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_2134_ = lean_string_append(v___x_2125_, v___x_2133_);
return v___x_2134_;
}
else
{
lean_object* v_val_2135_; lean_object* v___x_2136_; lean_object* v___y_2138_; lean_object* v_intZero_2143_; uint8_t v_isNeg_2144_; 
v_val_2135_ = lean_ctor_get(v_upperBound_2121_, 0);
lean_inc(v_val_2135_);
lean_dec_ref_known(v_upperBound_2121_, 1);
v___x_2136_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_2143_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2144_ = lean_int_dec_lt(v_val_2135_, v_intZero_2143_);
if (v_isNeg_2144_ == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; 
v_a_2145_ = lean_nat_abs(v_val_2135_);
lean_dec(v_val_2135_);
v___x_2146_ = l_Nat_reprFast(v_a_2145_);
v___y_2138_ = v___x_2146_;
goto v___jp_2137_;
}
else
{
lean_object* v_abs_2147_; lean_object* v_one_2148_; lean_object* v_a_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v_abs_2147_ = lean_nat_abs(v_val_2135_);
lean_dec(v_val_2135_);
v_one_2148_ = lean_unsigned_to_nat(1u);
v_a_2149_ = lean_nat_sub(v_abs_2147_, v_one_2148_);
lean_dec(v_abs_2147_);
v___x_2150_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2151_ = lean_nat_add(v_a_2149_, v_one_2148_);
lean_dec(v_a_2149_);
v___x_2152_ = l_Nat_reprFast(v___x_2151_);
v___x_2153_ = lean_string_append(v___x_2150_, v___x_2152_);
lean_dec_ref(v___x_2152_);
v___y_2138_ = v___x_2153_;
goto v___jp_2137_;
}
v___jp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2139_ = lean_string_append(v___x_2136_, v___y_2138_);
lean_dec_ref(v___y_2138_);
v___x_2140_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2141_ = lean_string_append(v___x_2139_, v___x_2140_);
v___x_2142_ = lean_string_append(v___x_2125_, v___x_2141_);
lean_dec_ref(v___x_2141_);
return v___x_2142_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_2121_) == 0)
{
lean_object* v_val_2154_; lean_object* v___x_2155_; lean_object* v___y_2157_; lean_object* v_intZero_2162_; uint8_t v_isNeg_2163_; 
v_val_2154_ = lean_ctor_get(v_lowerBound_2120_, 0);
lean_inc(v_val_2154_);
lean_dec_ref_known(v_lowerBound_2120_, 1);
v___x_2155_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2162_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2163_ = lean_int_dec_lt(v_val_2154_, v_intZero_2162_);
if (v_isNeg_2163_ == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2165_; 
v_a_2164_ = lean_nat_abs(v_val_2154_);
lean_dec(v_val_2154_);
v___x_2165_ = l_Nat_reprFast(v_a_2164_);
v___y_2157_ = v___x_2165_;
goto v___jp_2156_;
}
else
{
lean_object* v_abs_2166_; lean_object* v_one_2167_; lean_object* v_a_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_abs_2166_ = lean_nat_abs(v_val_2154_);
lean_dec(v_val_2154_);
v_one_2167_ = lean_unsigned_to_nat(1u);
v_a_2168_ = lean_nat_sub(v_abs_2166_, v_one_2167_);
lean_dec(v_abs_2166_);
v___x_2169_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2170_ = lean_nat_add(v_a_2168_, v_one_2167_);
lean_dec(v_a_2168_);
v___x_2171_ = l_Nat_reprFast(v___x_2170_);
v___x_2172_ = lean_string_append(v___x_2169_, v___x_2171_);
lean_dec_ref(v___x_2171_);
v___y_2157_ = v___x_2172_;
goto v___jp_2156_;
}
v___jp_2156_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2158_ = lean_string_append(v___x_2155_, v___y_2157_);
lean_dec_ref(v___y_2157_);
v___x_2159_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_2160_ = lean_string_append(v___x_2158_, v___x_2159_);
v___x_2161_ = lean_string_append(v___x_2125_, v___x_2160_);
lean_dec_ref(v___x_2160_);
return v___x_2161_;
}
}
else
{
lean_object* v_val_2173_; lean_object* v_val_2174_; uint8_t v___x_2175_; 
v_val_2173_ = lean_ctor_get(v_lowerBound_2120_, 0);
lean_inc(v_val_2173_);
lean_dec_ref_known(v_lowerBound_2120_, 1);
v_val_2174_ = lean_ctor_get(v_upperBound_2121_, 0);
lean_inc(v_val_2174_);
lean_dec_ref_known(v_upperBound_2121_, 1);
v___x_2175_ = lean_int_dec_lt(v_val_2174_, v_val_2173_);
if (v___x_2175_ == 0)
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_int_dec_eq(v_val_2173_, v_val_2174_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___y_2179_; lean_object* v_intZero_2194_; uint8_t v_isNeg_2195_; 
v___x_2177_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2194_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2195_ = lean_int_dec_lt(v_val_2173_, v_intZero_2194_);
if (v_isNeg_2195_ == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2197_; 
v_a_2196_ = lean_nat_abs(v_val_2173_);
lean_dec(v_val_2173_);
v___x_2197_ = l_Nat_reprFast(v_a_2196_);
v___y_2179_ = v___x_2197_;
goto v___jp_2178_;
}
else
{
lean_object* v_abs_2198_; lean_object* v_one_2199_; lean_object* v_a_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_abs_2198_ = lean_nat_abs(v_val_2173_);
lean_dec(v_val_2173_);
v_one_2199_ = lean_unsigned_to_nat(1u);
v_a_2200_ = lean_nat_sub(v_abs_2198_, v_one_2199_);
lean_dec(v_abs_2198_);
v___x_2201_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2202_ = lean_nat_add(v_a_2200_, v_one_2199_);
lean_dec(v_a_2200_);
v___x_2203_ = l_Nat_reprFast(v___x_2202_);
v___x_2204_ = lean_string_append(v___x_2201_, v___x_2203_);
lean_dec_ref(v___x_2203_);
v___y_2179_ = v___x_2204_;
goto v___jp_2178_;
}
v___jp_2178_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v_intZero_2183_; uint8_t v_isNeg_2184_; 
v___x_2180_ = lean_string_append(v___x_2177_, v___y_2179_);
lean_dec_ref(v___y_2179_);
v___x_2181_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_2182_ = lean_string_append(v___x_2180_, v___x_2181_);
v_intZero_2183_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2184_ = lean_int_dec_lt(v_val_2174_, v_intZero_2183_);
if (v_isNeg_2184_ == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2186_; 
v_a_2185_ = lean_nat_abs(v_val_2174_);
lean_dec(v_val_2174_);
v___x_2186_ = l_Nat_reprFast(v_a_2185_);
v___y_2127_ = v___x_2182_;
v___y_2128_ = v___x_2186_;
goto v___jp_2126_;
}
else
{
lean_object* v_abs_2187_; lean_object* v_one_2188_; lean_object* v_a_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_abs_2187_ = lean_nat_abs(v_val_2174_);
lean_dec(v_val_2174_);
v_one_2188_ = lean_unsigned_to_nat(1u);
v_a_2189_ = lean_nat_sub(v_abs_2187_, v_one_2188_);
lean_dec(v_abs_2187_);
v___x_2190_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2191_ = lean_nat_add(v_a_2189_, v_one_2188_);
lean_dec(v_a_2189_);
v___x_2192_ = l_Nat_reprFast(v___x_2191_);
v___x_2193_ = lean_string_append(v___x_2190_, v___x_2192_);
lean_dec_ref(v___x_2192_);
v___y_2127_ = v___x_2182_;
v___y_2128_ = v___x_2193_;
goto v___jp_2126_;
}
}
}
else
{
lean_object* v___x_2205_; lean_object* v___y_2207_; lean_object* v_intZero_2212_; uint8_t v_isNeg_2213_; 
lean_dec(v_val_2174_);
v___x_2205_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_2212_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2213_ = lean_int_dec_lt(v_val_2173_, v_intZero_2212_);
if (v_isNeg_2213_ == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2215_; 
v_a_2214_ = lean_nat_abs(v_val_2173_);
lean_dec(v_val_2173_);
v___x_2215_ = l_Nat_reprFast(v_a_2214_);
v___y_2207_ = v___x_2215_;
goto v___jp_2206_;
}
else
{
lean_object* v_abs_2216_; lean_object* v_one_2217_; lean_object* v_a_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_abs_2216_ = lean_nat_abs(v_val_2173_);
lean_dec(v_val_2173_);
v_one_2217_ = lean_unsigned_to_nat(1u);
v_a_2218_ = lean_nat_sub(v_abs_2216_, v_one_2217_);
lean_dec(v_abs_2216_);
v___x_2219_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2220_ = lean_nat_add(v_a_2218_, v_one_2217_);
lean_dec(v_a_2218_);
v___x_2221_ = l_Nat_reprFast(v___x_2220_);
v___x_2222_ = lean_string_append(v___x_2219_, v___x_2221_);
lean_dec_ref(v___x_2221_);
v___y_2207_ = v___x_2222_;
goto v___jp_2206_;
}
v___jp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2208_ = lean_string_append(v___x_2205_, v___y_2207_);
lean_dec_ref(v___y_2207_);
v___x_2209_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_2210_ = lean_string_append(v___x_2208_, v___x_2209_);
v___x_2211_ = lean_string_append(v___x_2125_, v___x_2210_);
lean_dec_ref(v___x_2210_);
return v___x_2211_;
}
}
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
lean_dec(v_val_2174_);
lean_dec(v_val_2173_);
v___x_2223_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_2224_ = lean_string_append(v___x_2125_, v___x_2223_);
return v___x_2224_;
}
}
}
v___jp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2129_ = lean_string_append(v___y_2127_, v___y_2128_);
lean_dec_ref(v___y_2128_);
v___x_2130_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2131_ = lean_string_append(v___x_2129_, v___x_2130_);
v___x_2132_ = lean_string_append(v___x_2125_, v___x_2131_);
lean_dec_ref(v___x_2131_);
return v___x_2132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object* v_a_2225_, lean_object* v_b_2226_, lean_object* v_d_2227_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2228_, 0, v_a_2225_);
lean_ctor_set(v___x_2228_, 1, v_b_2226_);
v___x_2229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set(v___x_2229_, 1, v_d_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2(lean_object* v___x_2230_, lean_object* v___f_2231_, lean_object* v_l_2232_, lean_object* v_acc_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2230_, v___f_2231_, v_acc_2233_, v_l_2232_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3(lean_object* v___f_2256_, lean_object* v___f_2257_, lean_object* v_p_2258_){
_start:
{
uint8_t v_possible_2259_; 
v_possible_2259_ = lean_ctor_get_uint8(v_p_2258_, sizeof(void*)*7);
if (v_possible_2259_ == 0)
{
lean_object* v___x_2260_; 
lean_dec_ref(v_p_2258_);
lean_dec_ref(v___f_2257_);
lean_dec_ref(v___f_2256_);
v___x_2260_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
return v___x_2260_;
}
else
{
lean_object* v_constraints_2261_; uint8_t v___x_2262_; 
v_constraints_2261_ = lean_ctor_get(v_p_2258_, 2);
lean_inc_ref(v_constraints_2261_);
v___x_2262_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2258_);
lean_dec_ref(v_p_2258_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; lean_object* v_buckets_2264_; lean_object* v___x_2265_; lean_object* v___y_2267_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2263_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10));
v_buckets_2264_ = lean_ctor_get(v_constraints_2261_, 1);
lean_inc_ref(v_buckets_2264_);
lean_dec_ref(v_constraints_2261_);
v___x_2265_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_2271_ = lean_box(0);
v___x_2272_ = lean_array_get_size(v_buckets_2264_);
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = lean_nat_dec_lt(v___x_2273_, v___x_2272_);
if (v___x_2274_ == 0)
{
lean_dec_ref(v_buckets_2264_);
lean_dec_ref(v___f_2257_);
v___y_2267_ = v___x_2271_;
goto v___jp_2266_;
}
else
{
lean_object* v___f_2275_; size_t v___x_2276_; size_t v___x_2277_; lean_object* v___x_2278_; 
v___f_2275_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2), 4, 2);
lean_closure_set(v___f_2275_, 0, v___x_2263_);
lean_closure_set(v___f_2275_, 1, v___f_2257_);
v___x_2276_ = lean_usize_of_nat(v___x_2272_);
v___x_2277_ = ((size_t)0ULL);
v___x_2278_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2263_, v___f_2275_, v_buckets_2264_, v___x_2276_, v___x_2277_, v___x_2271_);
v___y_2267_ = v___x_2278_;
goto v___jp_2266_;
}
v___jp_2266_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2268_ = lean_box(0);
v___x_2269_ = l_List_mapTR_loop___redArg(v___f_2256_, v___y_2267_, v___x_2268_);
v___x_2270_ = l_String_intercalate(v___x_2265_, v___x_2269_);
return v___x_2270_;
}
}
else
{
lean_object* v___x_2279_; 
lean_dec_ref(v_constraints_2261_);
lean_dec_ref(v___f_2257_);
lean_dec_ref(v___f_2256_);
v___x_2279_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
return v___x_2279_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = lean_box(0);
v___x_2293_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1));
v___x_2294_ = l_Lean_Expr_const___override(v___x_2293_, v___x_2292_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = lean_box(0);
v___x_2301_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5));
v___x_2302_ = l_Lean_Expr_const___override(v___x_2301_, v___x_2300_);
return v___x_2302_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = lean_box(0);
v___x_2310_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8));
v___x_2311_ = l_Lean_Expr_const___override(v___x_2310_, v___x_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse(lean_object* v_s_2312_, lean_object* v_x_2313_, lean_object* v_j_2314_, lean_object* v_assumptions_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, uint8_t v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2317_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2328_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc_n(v_a_2327_, 2);
lean_dec_ref_known(v___x_2326_, 1);
v___x_2328_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_2313_, v_a_2327_, v_assumptions_2315_, v_j_2314_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2330_; lean_object* v_lowerBound_2331_; lean_object* v_upperBound_2332_; lean_object* v_nil_2333_; lean_object* v_cons_2334_; lean_object* v___x_2335_; lean_object* v___y_2337_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___x_2360_; lean_object* v___y_2362_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2328_, 1);
v___x_2330_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_lowerBound_2331_ = lean_ctor_get(v_s_2312_, 0);
v_upperBound_2332_ = lean_ctor_get(v_s_2312_, 1);
v_nil_2333_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2334_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2335_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2333_, v_cons_2334_, v_x_2313_);
v___x_2360_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
if (lean_obj_tag(v_lowerBound_2331_) == 0)
{
lean_object* v___x_2378_; 
v___x_2378_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_2362_ = v___x_2378_;
goto v___jp_2361_;
}
else
{
lean_object* v_val_2379_; lean_object* v___x_2380_; lean_object* v___y_2382_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v_val_2379_ = lean_ctor_get(v_lowerBound_2331_, 0);
v___x_2380_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2384_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2385_ = lean_int_dec_le(v___x_2384_, v_val_2379_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2386_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2387_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2388_ = lean_int_neg(v_val_2379_);
v___x_2389_ = l_Int_toNat(v___x_2388_);
lean_dec(v___x_2388_);
v___x_2390_ = l_Lean_instToExprInt_mkNat(v___x_2389_);
v___x_2391_ = l_Lean_mkApp3(v___x_2386_, v___x_2330_, v___x_2387_, v___x_2390_);
v___y_2382_ = v___x_2391_;
goto v___jp_2381_;
}
else
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = l_Int_toNat(v_val_2379_);
v___x_2393_ = l_Lean_instToExprInt_mkNat(v___x_2392_);
v___y_2382_ = v___x_2393_;
goto v___jp_2381_;
}
v___jp_2381_:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lean_mkAppB(v___x_2380_, v___x_2330_, v___y_2382_);
v___y_2362_ = v___x_2383_;
goto v___jp_2361_;
}
}
v___jp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2338_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2);
lean_inc_ref(v___y_2337_);
v___x_2339_ = l_Lean_Expr_app___override(v___x_2338_, v___y_2337_);
v___x_2340_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6);
v___x_2341_ = l_Lean_Meta_mkEq(v___x_2339_, v___x_2340_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2343_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = l_Lean_Meta_mkDecideProof(v_a_2342_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2353_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2353_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2353_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2348_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9);
v___x_2349_ = l_Lean_mkApp5(v___x_2348_, v___y_2337_, v_a_2344_, v___x_2335_, v_a_2327_, v_a_2329_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2349_);
v___x_2351_ = v___x_2346_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
else
{
lean_dec_ref(v___y_2337_);
lean_dec_ref(v___x_2335_);
lean_dec(v_a_2329_);
lean_dec(v_a_2327_);
return v___x_2343_;
}
}
else
{
lean_dec_ref(v___y_2337_);
lean_dec_ref(v___x_2335_);
lean_dec(v_a_2329_);
lean_dec(v_a_2327_);
return v___x_2341_;
}
}
v___jp_2354_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_inc_ref(v___y_2355_);
v___x_2358_ = l_Lean_mkAppB(v___y_2355_, v___x_2330_, v___y_2357_);
v___x_2359_ = l_Lean_Expr_app___override(v___y_2356_, v___x_2358_);
v___y_2337_ = v___x_2359_;
goto v___jp_2336_;
}
v___jp_2361_:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_Expr_app___override(v___x_2360_, v___y_2362_);
if (lean_obj_tag(v_upperBound_2332_) == 0)
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_2365_ = l_Lean_Expr_app___override(v___x_2363_, v___x_2364_);
v___y_2337_ = v___x_2365_;
goto v___jp_2336_;
}
else
{
lean_object* v_val_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v_val_2366_ = lean_ctor_get(v_upperBound_2332_, 0);
v___x_2367_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2368_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2369_ = lean_int_dec_le(v___x_2368_, v_val_2366_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2370_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2371_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2372_ = lean_int_neg(v_val_2366_);
v___x_2373_ = l_Int_toNat(v___x_2372_);
lean_dec(v___x_2372_);
v___x_2374_ = l_Lean_instToExprInt_mkNat(v___x_2373_);
v___x_2375_ = l_Lean_mkApp3(v___x_2370_, v___x_2330_, v___x_2371_, v___x_2374_);
v___y_2355_ = v___x_2367_;
v___y_2356_ = v___x_2363_;
v___y_2357_ = v___x_2375_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = l_Int_toNat(v_val_2366_);
v___x_2377_ = l_Lean_instToExprInt_mkNat(v___x_2376_);
v___y_2355_ = v___x_2367_;
v___y_2356_ = v___x_2363_;
v___y_2357_ = v___x_2377_;
goto v___jp_2354_;
}
}
}
}
else
{
lean_dec(v_a_2327_);
return v___x_2328_;
}
}
else
{
lean_dec_ref(v_j_2314_);
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed(lean_object* v_s_2394_, lean_object* v_x_2395_, lean_object* v_j_2396_, lean_object* v_assumptions_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
uint8_t v_a_boxed_2408_; lean_object* v_res_2409_; 
v_a_boxed_2408_ = lean_unbox(v_a_2401_);
v_res_2409_ = l_Lean_Elab_Tactic_Omega_Problem_proveFalse(v_s_2394_, v_x_2395_, v_j_2396_, v_assumptions_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_boxed_2408_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2400_);
lean_dec(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_assumptions_2397_);
lean_dec(v_x_2395_);
lean_dec_ref(v_s_2394_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0(lean_object* v_constraint_2410_, lean_object* v_coeffs_2411_, lean_object* v_justification_2412_, lean_object* v_x_2413_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_2410_, v_coeffs_2411_, v_justification_2412_);
return v___x_2414_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(lean_object* v_a_2415_, lean_object* v_x_2416_){
_start:
{
if (lean_obj_tag(v_x_2416_) == 0)
{
uint8_t v___x_2417_; 
v___x_2417_ = 0;
return v___x_2417_;
}
else
{
lean_object* v_key_2418_; lean_object* v_tail_2419_; uint8_t v___x_2420_; 
v_key_2418_ = lean_ctor_get(v_x_2416_, 0);
v_tail_2419_ = lean_ctor_get(v_x_2416_, 2);
v___x_2420_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2418_, v_a_2415_);
if (v___x_2420_ == 0)
{
v_x_2416_ = v_tail_2419_;
goto _start;
}
else
{
return v___x_2420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg___boxed(lean_object* v_a_2422_, lean_object* v_x_2423_){
_start:
{
uint8_t v_res_2424_; lean_object* v_r_2425_; 
v_res_2424_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2422_, v_x_2423_);
lean_dec(v_x_2423_);
lean_dec(v_a_2422_);
v_r_2425_ = lean_box(v_res_2424_);
return v_r_2425_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(uint64_t v_x_2426_, lean_object* v_x_2427_){
_start:
{
if (lean_obj_tag(v_x_2427_) == 0)
{
return v_x_2426_;
}
else
{
lean_object* v_head_2428_; lean_object* v_tail_2429_; lean_object* v_intZero_2430_; uint8_t v_isNeg_2431_; 
v_head_2428_ = lean_ctor_get(v_x_2427_, 0);
v_tail_2429_ = lean_ctor_get(v_x_2427_, 1);
v_intZero_2430_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2431_ = lean_int_dec_lt(v_head_2428_, v_intZero_2430_);
if (v_isNeg_2431_ == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; uint64_t v___x_2435_; uint64_t v___x_2436_; 
v_a_2432_ = lean_nat_abs(v_head_2428_);
v___x_2433_ = lean_unsigned_to_nat(2u);
v___x_2434_ = lean_nat_mul(v___x_2433_, v_a_2432_);
lean_dec(v_a_2432_);
v___x_2435_ = lean_uint64_of_nat(v___x_2434_);
lean_dec(v___x_2434_);
v___x_2436_ = lean_uint64_mix_hash(v_x_2426_, v___x_2435_);
v_x_2426_ = v___x_2436_;
v_x_2427_ = v_tail_2429_;
goto _start;
}
else
{
lean_object* v_abs_2438_; lean_object* v_one_2439_; lean_object* v_a_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; uint64_t v___x_2444_; uint64_t v___x_2445_; 
v_abs_2438_ = lean_nat_abs(v_head_2428_);
v_one_2439_ = lean_unsigned_to_nat(1u);
v_a_2440_ = lean_nat_sub(v_abs_2438_, v_one_2439_);
lean_dec(v_abs_2438_);
v___x_2441_ = lean_unsigned_to_nat(2u);
v___x_2442_ = lean_nat_mul(v___x_2441_, v_a_2440_);
lean_dec(v_a_2440_);
v___x_2443_ = lean_nat_add(v___x_2442_, v_one_2439_);
lean_dec(v___x_2442_);
v___x_2444_ = lean_uint64_of_nat(v___x_2443_);
lean_dec(v___x_2443_);
v___x_2445_ = lean_uint64_mix_hash(v_x_2426_, v___x_2444_);
v_x_2426_ = v___x_2445_;
v_x_2427_ = v_tail_2429_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0___boxed(lean_object* v_x_2447_, lean_object* v_x_2448_){
_start:
{
uint64_t v_x_980__boxed_2449_; uint64_t v_res_2450_; lean_object* v_r_2451_; 
v_x_980__boxed_2449_ = lean_unbox_uint64(v_x_2447_);
lean_dec_ref(v_x_2447_);
v_res_2450_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v_x_980__boxed_2449_, v_x_2448_);
lean_dec(v_x_2448_);
v_r_2451_ = lean_box_uint64(v_res_2450_);
return v_r_2451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_2452_, lean_object* v_x_2453_){
_start:
{
if (lean_obj_tag(v_x_2453_) == 0)
{
return v_x_2452_;
}
else
{
lean_object* v_key_2454_; lean_object* v_value_2455_; lean_object* v_tail_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2480_; 
v_key_2454_ = lean_ctor_get(v_x_2453_, 0);
v_value_2455_ = lean_ctor_get(v_x_2453_, 1);
v_tail_2456_ = lean_ctor_get(v_x_2453_, 2);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_x_2453_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2458_ = v_x_2453_;
v_isShared_2459_ = v_isSharedCheck_2480_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_tail_2456_);
lean_inc(v_value_2455_);
lean_inc(v_key_2454_);
lean_dec(v_x_2453_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2480_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; uint64_t v___x_2461_; uint64_t v___x_2462_; uint64_t v___x_2463_; uint64_t v___x_2464_; uint64_t v_fold_2465_; uint64_t v___x_2466_; uint64_t v___x_2467_; uint64_t v___x_2468_; size_t v___x_2469_; size_t v___x_2470_; size_t v___x_2471_; size_t v___x_2472_; size_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2460_ = lean_array_get_size(v_x_2452_);
v___x_2461_ = 7ULL;
v___x_2462_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2461_, v_key_2454_);
v___x_2463_ = 32ULL;
v___x_2464_ = lean_uint64_shift_right(v___x_2462_, v___x_2463_);
v_fold_2465_ = lean_uint64_xor(v___x_2462_, v___x_2464_);
v___x_2466_ = 16ULL;
v___x_2467_ = lean_uint64_shift_right(v_fold_2465_, v___x_2466_);
v___x_2468_ = lean_uint64_xor(v_fold_2465_, v___x_2467_);
v___x_2469_ = lean_uint64_to_usize(v___x_2468_);
v___x_2470_ = lean_usize_of_nat(v___x_2460_);
v___x_2471_ = ((size_t)1ULL);
v___x_2472_ = lean_usize_sub(v___x_2470_, v___x_2471_);
v___x_2473_ = lean_usize_land(v___x_2469_, v___x_2472_);
v___x_2474_ = lean_array_uget_borrowed(v_x_2452_, v___x_2473_);
lean_inc(v___x_2474_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 2, v___x_2474_);
v___x_2476_ = v___x_2458_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_key_2454_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_value_2455_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_array_uset(v_x_2452_, v___x_2473_, v___x_2476_);
v_x_2452_ = v___x_2477_;
v_x_2453_ = v_tail_2456_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(lean_object* v_i_2481_, lean_object* v_source_2482_, lean_object* v_target_2483_){
_start:
{
lean_object* v___x_2484_; uint8_t v___x_2485_; 
v___x_2484_ = lean_array_get_size(v_source_2482_);
v___x_2485_ = lean_nat_dec_lt(v_i_2481_, v___x_2484_);
if (v___x_2485_ == 0)
{
lean_dec_ref(v_source_2482_);
lean_dec(v_i_2481_);
return v_target_2483_;
}
else
{
lean_object* v_es_2486_; lean_object* v___x_2487_; lean_object* v_source_2488_; lean_object* v_target_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_es_2486_ = lean_array_fget(v_source_2482_, v_i_2481_);
v___x_2487_ = lean_box(0);
v_source_2488_ = lean_array_fset(v_source_2482_, v_i_2481_, v___x_2487_);
v_target_2489_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_target_2483_, v_es_2486_);
v___x_2490_ = lean_unsigned_to_nat(1u);
v___x_2491_ = lean_nat_add(v_i_2481_, v___x_2490_);
lean_dec(v_i_2481_);
v_i_2481_ = v___x_2491_;
v_source_2482_ = v_source_2488_;
v_target_2483_ = v_target_2489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(lean_object* v_data_2493_){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v_nbuckets_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2494_ = lean_array_get_size(v_data_2493_);
v___x_2495_ = lean_unsigned_to_nat(2u);
v_nbuckets_2496_ = lean_nat_mul(v___x_2494_, v___x_2495_);
v___x_2497_ = lean_unsigned_to_nat(0u);
v___x_2498_ = lean_box(0);
v___x_2499_ = lean_mk_array(v_nbuckets_2496_, v___x_2498_);
v___x_2500_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v___x_2497_, v_data_2493_, v___x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(lean_object* v_m_2501_, lean_object* v_a_2502_, lean_object* v_b_2503_){
_start:
{
lean_object* v_size_2504_; lean_object* v_buckets_2505_; lean_object* v___x_2506_; uint64_t v___x_2507_; uint64_t v___x_2508_; uint64_t v___x_2509_; uint64_t v___x_2510_; uint64_t v_fold_2511_; uint64_t v___x_2512_; uint64_t v___x_2513_; uint64_t v___x_2514_; size_t v___x_2515_; size_t v___x_2516_; size_t v___x_2517_; size_t v___x_2518_; size_t v___x_2519_; lean_object* v_bkt_2520_; uint8_t v___x_2521_; 
v_size_2504_ = lean_ctor_get(v_m_2501_, 0);
v_buckets_2505_ = lean_ctor_get(v_m_2501_, 1);
v___x_2506_ = lean_array_get_size(v_buckets_2505_);
v___x_2507_ = 7ULL;
v___x_2508_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2507_, v_a_2502_);
v___x_2509_ = 32ULL;
v___x_2510_ = lean_uint64_shift_right(v___x_2508_, v___x_2509_);
v_fold_2511_ = lean_uint64_xor(v___x_2508_, v___x_2510_);
v___x_2512_ = 16ULL;
v___x_2513_ = lean_uint64_shift_right(v_fold_2511_, v___x_2512_);
v___x_2514_ = lean_uint64_xor(v_fold_2511_, v___x_2513_);
v___x_2515_ = lean_uint64_to_usize(v___x_2514_);
v___x_2516_ = lean_usize_of_nat(v___x_2506_);
v___x_2517_ = ((size_t)1ULL);
v___x_2518_ = lean_usize_sub(v___x_2516_, v___x_2517_);
v___x_2519_ = lean_usize_land(v___x_2515_, v___x_2518_);
v_bkt_2520_ = lean_array_uget_borrowed(v_buckets_2505_, v___x_2519_);
v___x_2521_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2502_, v_bkt_2520_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2542_; 
lean_inc_ref(v_buckets_2505_);
lean_inc(v_size_2504_);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_m_2501_);
if (v_isSharedCheck_2542_ == 0)
{
lean_object* v_unused_2543_; lean_object* v_unused_2544_; 
v_unused_2543_ = lean_ctor_get(v_m_2501_, 1);
lean_dec(v_unused_2543_);
v_unused_2544_ = lean_ctor_get(v_m_2501_, 0);
lean_dec(v_unused_2544_);
v___x_2523_ = v_m_2501_;
v_isShared_2524_ = v_isSharedCheck_2542_;
goto v_resetjp_2522_;
}
else
{
lean_dec(v_m_2501_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2542_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v_size_x27_2526_; lean_object* v___x_2527_; lean_object* v_buckets_x27_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2525_ = lean_unsigned_to_nat(1u);
v_size_x27_2526_ = lean_nat_add(v_size_2504_, v___x_2525_);
lean_dec(v_size_2504_);
lean_inc(v_bkt_2520_);
v___x_2527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2527_, 0, v_a_2502_);
lean_ctor_set(v___x_2527_, 1, v_b_2503_);
lean_ctor_set(v___x_2527_, 2, v_bkt_2520_);
v_buckets_x27_2528_ = lean_array_uset(v_buckets_2505_, v___x_2519_, v___x_2527_);
v___x_2529_ = lean_unsigned_to_nat(4u);
v___x_2530_ = lean_nat_mul(v_size_x27_2526_, v___x_2529_);
v___x_2531_ = lean_unsigned_to_nat(3u);
v___x_2532_ = lean_nat_div(v___x_2530_, v___x_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_array_get_size(v_buckets_x27_2528_);
v___x_2534_ = lean_nat_dec_le(v___x_2532_, v___x_2533_);
lean_dec(v___x_2532_);
if (v___x_2534_ == 0)
{
lean_object* v_val_2535_; lean_object* v___x_2537_; 
v_val_2535_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2528_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 1, v_val_2535_);
lean_ctor_set(v___x_2523_, 0, v_size_x27_2526_);
v___x_2537_ = v___x_2523_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_size_x27_2526_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_val_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
else
{
lean_object* v___x_2540_; 
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 1, v_buckets_x27_2528_);
lean_ctor_set(v___x_2523_, 0, v_size_x27_2526_);
v___x_2540_ = v___x_2523_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_size_x27_2526_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_buckets_x27_2528_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_dec(v_b_2503_);
lean_dec(v_a_2502_);
return v_m_2501_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(lean_object* v_a_2545_, lean_object* v_b_2546_, lean_object* v_x_2547_){
_start:
{
if (lean_obj_tag(v_x_2547_) == 0)
{
lean_dec(v_b_2546_);
lean_dec(v_a_2545_);
return v_x_2547_;
}
else
{
lean_object* v_key_2548_; lean_object* v_value_2549_; lean_object* v_tail_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2562_; 
v_key_2548_ = lean_ctor_get(v_x_2547_, 0);
v_value_2549_ = lean_ctor_get(v_x_2547_, 1);
v_tail_2550_ = lean_ctor_get(v_x_2547_, 2);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_x_2547_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2552_ = v_x_2547_;
v_isShared_2553_ = v_isSharedCheck_2562_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_tail_2550_);
lean_inc(v_value_2549_);
lean_inc(v_key_2548_);
lean_dec(v_x_2547_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2562_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
uint8_t v___x_2554_; 
v___x_2554_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2548_, v_a_2545_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2555_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2545_, v_b_2546_, v_tail_2550_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 2, v___x_2555_);
v___x_2557_ = v___x_2552_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_key_2548_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_value_2549_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
else
{
lean_object* v___x_2560_; 
lean_dec(v_value_2549_);
lean_dec(v_key_2548_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v_b_2546_);
lean_ctor_set(v___x_2552_, 0, v_a_2545_);
v___x_2560_ = v___x_2552_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2545_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_b_2546_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_tail_2550_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(lean_object* v_m_2563_, lean_object* v_a_2564_, lean_object* v_b_2565_){
_start:
{
lean_object* v_size_2566_; lean_object* v_buckets_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2611_; 
v_size_2566_ = lean_ctor_get(v_m_2563_, 0);
v_buckets_2567_ = lean_ctor_get(v_m_2563_, 1);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_m_2563_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2569_ = v_m_2563_;
v_isShared_2570_ = v_isSharedCheck_2611_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_buckets_2567_);
lean_inc(v_size_2566_);
lean_dec(v_m_2563_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2611_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; uint64_t v___x_2572_; uint64_t v___x_2573_; uint64_t v___x_2574_; uint64_t v___x_2575_; uint64_t v_fold_2576_; uint64_t v___x_2577_; uint64_t v___x_2578_; uint64_t v___x_2579_; size_t v___x_2580_; size_t v___x_2581_; size_t v___x_2582_; size_t v___x_2583_; size_t v___x_2584_; lean_object* v_bkt_2585_; uint8_t v___x_2586_; 
v___x_2571_ = lean_array_get_size(v_buckets_2567_);
v___x_2572_ = 7ULL;
v___x_2573_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2572_, v_a_2564_);
v___x_2574_ = 32ULL;
v___x_2575_ = lean_uint64_shift_right(v___x_2573_, v___x_2574_);
v_fold_2576_ = lean_uint64_xor(v___x_2573_, v___x_2575_);
v___x_2577_ = 16ULL;
v___x_2578_ = lean_uint64_shift_right(v_fold_2576_, v___x_2577_);
v___x_2579_ = lean_uint64_xor(v_fold_2576_, v___x_2578_);
v___x_2580_ = lean_uint64_to_usize(v___x_2579_);
v___x_2581_ = lean_usize_of_nat(v___x_2571_);
v___x_2582_ = ((size_t)1ULL);
v___x_2583_ = lean_usize_sub(v___x_2581_, v___x_2582_);
v___x_2584_ = lean_usize_land(v___x_2580_, v___x_2583_);
v_bkt_2585_ = lean_array_uget_borrowed(v_buckets_2567_, v___x_2584_);
v___x_2586_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2564_, v_bkt_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v_size_x27_2588_; lean_object* v___x_2589_; lean_object* v_buckets_x27_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
v___x_2587_ = lean_unsigned_to_nat(1u);
v_size_x27_2588_ = lean_nat_add(v_size_2566_, v___x_2587_);
lean_dec(v_size_2566_);
lean_inc(v_bkt_2585_);
v___x_2589_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2589_, 0, v_a_2564_);
lean_ctor_set(v___x_2589_, 1, v_b_2565_);
lean_ctor_set(v___x_2589_, 2, v_bkt_2585_);
v_buckets_x27_2590_ = lean_array_uset(v_buckets_2567_, v___x_2584_, v___x_2589_);
v___x_2591_ = lean_unsigned_to_nat(4u);
v___x_2592_ = lean_nat_mul(v_size_x27_2588_, v___x_2591_);
v___x_2593_ = lean_unsigned_to_nat(3u);
v___x_2594_ = lean_nat_div(v___x_2592_, v___x_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_array_get_size(v_buckets_x27_2590_);
v___x_2596_ = lean_nat_dec_le(v___x_2594_, v___x_2595_);
lean_dec(v___x_2594_);
if (v___x_2596_ == 0)
{
lean_object* v_val_2597_; lean_object* v___x_2599_; 
v_val_2597_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2590_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 1, v_val_2597_);
lean_ctor_set(v___x_2569_, 0, v_size_x27_2588_);
v___x_2599_ = v___x_2569_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_size_x27_2588_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_val_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
else
{
lean_object* v___x_2602_; 
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 1, v_buckets_x27_2590_);
lean_ctor_set(v___x_2569_, 0, v_size_x27_2588_);
v___x_2602_ = v___x_2569_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_size_x27_2588_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_buckets_x27_2590_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
else
{
lean_object* v___x_2604_; lean_object* v_buckets_x27_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; 
lean_inc(v_bkt_2585_);
v___x_2604_ = lean_box(0);
v_buckets_x27_2605_ = lean_array_uset(v_buckets_2567_, v___x_2584_, v___x_2604_);
v___x_2606_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2564_, v_b_2565_, v_bkt_2585_);
v___x_2607_ = lean_array_uset(v_buckets_x27_2605_, v___x_2584_, v___x_2606_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 1, v___x_2607_);
v___x_2609_ = v___x_2569_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_size_2566_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(lean_object* v_p_2612_, lean_object* v_x_2613_){
_start:
{
lean_object* v_coeffs_2614_; lean_object* v_constraint_2615_; lean_object* v_justification_2616_; uint8_t v___x_2617_; 
v_coeffs_2614_ = lean_ctor_get(v_x_2613_, 0);
lean_inc(v_coeffs_2614_);
v_constraint_2615_ = lean_ctor_get(v_x_2613_, 1);
lean_inc_ref(v_constraint_2615_);
v_justification_2616_ = lean_ctor_get(v_x_2613_, 2);
v___x_2617_ = l_Lean_Omega_Constraint_isImpossible(v_constraint_2615_);
if (v___x_2617_ == 0)
{
lean_object* v_assumptions_2618_; lean_object* v_numVars_2619_; lean_object* v_constraints_2620_; lean_object* v_equalities_2621_; lean_object* v_eliminations_2622_; uint8_t v_possible_2623_; lean_object* v_proveFalse_x3f_2624_; lean_object* v_explanation_x3f_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2643_; 
v_assumptions_2618_ = lean_ctor_get(v_p_2612_, 0);
v_numVars_2619_ = lean_ctor_get(v_p_2612_, 1);
v_constraints_2620_ = lean_ctor_get(v_p_2612_, 2);
v_equalities_2621_ = lean_ctor_get(v_p_2612_, 3);
v_eliminations_2622_ = lean_ctor_get(v_p_2612_, 4);
v_possible_2623_ = lean_ctor_get_uint8(v_p_2612_, sizeof(void*)*7);
v_proveFalse_x3f_2624_ = lean_ctor_get(v_p_2612_, 5);
v_explanation_x3f_2625_ = lean_ctor_get(v_p_2612_, 6);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_p_2612_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2627_ = v_p_2612_;
v_isShared_2628_ = v_isSharedCheck_2643_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_explanation_x3f_2625_);
lean_inc(v_proveFalse_x3f_2624_);
lean_inc(v_eliminations_2622_);
lean_inc(v_equalities_2621_);
lean_inc(v_constraints_2620_);
lean_inc(v_numVars_2619_);
lean_inc(v_assumptions_2618_);
lean_dec(v_p_2612_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2643_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___y_2630_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2641_ = l_List_lengthTR___redArg(v_coeffs_2614_);
v___x_2642_ = lean_nat_dec_le(v_numVars_2619_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_dec(v___x_2641_);
v___y_2630_ = v_numVars_2619_;
goto v___jp_2629_;
}
else
{
lean_dec(v_numVars_2619_);
v___y_2630_ = v___x_2641_;
goto v___jp_2629_;
}
v___jp_2629_:
{
lean_object* v___x_2631_; uint8_t v___x_2632_; 
lean_inc(v_coeffs_2614_);
v___x_2631_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_constraints_2620_, v_coeffs_2614_, v_x_2613_);
v___x_2632_ = l_Lean_Omega_Constraint_isExact(v_constraint_2615_);
lean_dec_ref(v_constraint_2615_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2634_; 
lean_dec(v_coeffs_2614_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 2, v___x_2631_);
lean_ctor_set(v___x_2627_, 1, v___y_2630_);
v___x_2634_ = v___x_2627_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_assumptions_2618_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v___y_2630_);
lean_ctor_set(v_reuseFailAlloc_2635_, 2, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2635_, 3, v_equalities_2621_);
lean_ctor_set(v_reuseFailAlloc_2635_, 4, v_eliminations_2622_);
lean_ctor_set(v_reuseFailAlloc_2635_, 5, v_proveFalse_x3f_2624_);
lean_ctor_set(v_reuseFailAlloc_2635_, 6, v_explanation_x3f_2625_);
lean_ctor_set_uint8(v_reuseFailAlloc_2635_, sizeof(void*)*7, v_possible_2623_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
else
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2636_ = lean_box(0);
v___x_2637_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_equalities_2621_, v_coeffs_2614_, v___x_2636_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 3, v___x_2637_);
lean_ctor_set(v___x_2627_, 2, v___x_2631_);
lean_ctor_set(v___x_2627_, 1, v___y_2630_);
v___x_2639_ = v___x_2627_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_assumptions_2618_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v___y_2630_);
lean_ctor_set(v_reuseFailAlloc_2640_, 2, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2640_, 3, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2640_, 4, v_eliminations_2622_);
lean_ctor_set(v_reuseFailAlloc_2640_, 5, v_proveFalse_x3f_2624_);
lean_ctor_set(v_reuseFailAlloc_2640_, 6, v_explanation_x3f_2625_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, sizeof(void*)*7, v_possible_2623_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
else
{
lean_object* v_assumptions_2644_; lean_object* v_numVars_2645_; lean_object* v_constraints_2646_; lean_object* v_equalities_2647_; lean_object* v_eliminations_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2660_; 
lean_inc_ref(v_justification_2616_);
lean_dec_ref(v_x_2613_);
v_assumptions_2644_ = lean_ctor_get(v_p_2612_, 0);
v_numVars_2645_ = lean_ctor_get(v_p_2612_, 1);
v_constraints_2646_ = lean_ctor_get(v_p_2612_, 2);
v_equalities_2647_ = lean_ctor_get(v_p_2612_, 3);
v_eliminations_2648_ = lean_ctor_get(v_p_2612_, 4);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_p_2612_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; lean_object* v_unused_2662_; 
v_unused_2661_ = lean_ctor_get(v_p_2612_, 6);
lean_dec(v_unused_2661_);
v_unused_2662_ = lean_ctor_get(v_p_2612_, 5);
lean_dec(v_unused_2662_);
v___x_2650_ = v_p_2612_;
v_isShared_2651_ = v_isSharedCheck_2660_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_eliminations_2648_);
lean_inc(v_equalities_2647_);
lean_inc(v_constraints_2646_);
lean_inc(v_numVars_2645_);
lean_inc(v_assumptions_2644_);
lean_dec(v_p_2612_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2660_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___f_2652_; uint8_t v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
lean_inc_ref(v_justification_2616_);
lean_inc(v_coeffs_2614_);
lean_inc_ref(v_constraint_2615_);
v___f_2652_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0), 4, 3);
lean_closure_set(v___f_2652_, 0, v_constraint_2615_);
lean_closure_set(v___f_2652_, 1, v_coeffs_2614_);
lean_closure_set(v___f_2652_, 2, v_justification_2616_);
v___x_2653_ = 0;
lean_inc_ref(v_assumptions_2644_);
v___x_2654_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed), 14, 4);
lean_closure_set(v___x_2654_, 0, v_constraint_2615_);
lean_closure_set(v___x_2654_, 1, v_coeffs_2614_);
lean_closure_set(v___x_2654_, 2, v_justification_2616_);
lean_closure_set(v___x_2654_, 3, v_assumptions_2644_);
v___x_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
v___x_2656_ = lean_mk_thunk(v___f_2652_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 6, v___x_2656_);
lean_ctor_set(v___x_2650_, 5, v___x_2655_);
v___x_2658_ = v___x_2650_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_assumptions_2644_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_numVars_2645_);
lean_ctor_set(v_reuseFailAlloc_2659_, 2, v_constraints_2646_);
lean_ctor_set(v_reuseFailAlloc_2659_, 3, v_equalities_2647_);
lean_ctor_set(v_reuseFailAlloc_2659_, 4, v_eliminations_2648_);
lean_ctor_set(v_reuseFailAlloc_2659_, 5, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2659_, 6, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*7, v___x_2653_);
return v___x_2658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0(lean_object* v_00_u03b2_2663_, lean_object* v_m_2664_, lean_object* v_a_2665_, lean_object* v_b_2666_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_m_2664_, v_a_2665_, v_b_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1(lean_object* v_00_u03b2_2668_, lean_object* v_m_2669_, lean_object* v_a_2670_, lean_object* v_b_2671_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_m_2669_, v_a_2670_, v_b_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_object* v_00_u03b2_2673_, lean_object* v_a_2674_, lean_object* v_x_2675_){
_start:
{
uint8_t v___x_2676_; 
v___x_2676_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2674_, v_x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2677_, lean_object* v_a_2678_, lean_object* v_x_2679_){
_start:
{
uint8_t v_res_2680_; lean_object* v_r_2681_; 
v_res_2680_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(v_00_u03b2_2677_, v_a_2678_, v_x_2679_);
lean_dec(v_x_2679_);
lean_dec(v_a_2678_);
v_r_2681_ = lean_box(v_res_2680_);
return v_r_2681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2(lean_object* v_00_u03b2_2682_, lean_object* v_data_2683_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_data_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3(lean_object* v_00_u03b2_2685_, lean_object* v_a_2686_, lean_object* v_b_2687_, lean_object* v_x_2688_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2686_, v_b_2687_, v_x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2690_, lean_object* v_i_2691_, lean_object* v_source_2692_, lean_object* v_target_2693_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v_i_2691_, v_source_2692_, v_target_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2695_, lean_object* v_x_2696_, lean_object* v_x_2697_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_x_2696_, v_x_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(lean_object* v_a_2699_, lean_object* v_x_2700_){
_start:
{
if (lean_obj_tag(v_x_2700_) == 0)
{
lean_object* v___x_2701_; 
v___x_2701_ = lean_box(0);
return v___x_2701_;
}
else
{
lean_object* v_key_2702_; lean_object* v_value_2703_; lean_object* v_tail_2704_; uint8_t v___x_2705_; 
v_key_2702_ = lean_ctor_get(v_x_2700_, 0);
v_value_2703_ = lean_ctor_get(v_x_2700_, 1);
v_tail_2704_ = lean_ctor_get(v_x_2700_, 2);
v___x_2705_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2702_, v_a_2699_);
if (v___x_2705_ == 0)
{
v_x_2700_ = v_tail_2704_;
goto _start;
}
else
{
lean_object* v___x_2707_; 
lean_inc(v_value_2703_);
v___x_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2707_, 0, v_value_2703_);
return v___x_2707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg___boxed(lean_object* v_a_2708_, lean_object* v_x_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2708_, v_x_2709_);
lean_dec(v_x_2709_);
lean_dec(v_a_2708_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(lean_object* v_m_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_buckets_2713_; lean_object* v___x_2714_; uint64_t v___x_2715_; uint64_t v___x_2716_; uint64_t v___x_2717_; uint64_t v___x_2718_; uint64_t v_fold_2719_; uint64_t v___x_2720_; uint64_t v___x_2721_; uint64_t v___x_2722_; size_t v___x_2723_; size_t v___x_2724_; size_t v___x_2725_; size_t v___x_2726_; size_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v_buckets_2713_ = lean_ctor_get(v_m_2711_, 1);
v___x_2714_ = lean_array_get_size(v_buckets_2713_);
v___x_2715_ = 7ULL;
v___x_2716_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2715_, v_a_2712_);
v___x_2717_ = 32ULL;
v___x_2718_ = lean_uint64_shift_right(v___x_2716_, v___x_2717_);
v_fold_2719_ = lean_uint64_xor(v___x_2716_, v___x_2718_);
v___x_2720_ = 16ULL;
v___x_2721_ = lean_uint64_shift_right(v_fold_2719_, v___x_2720_);
v___x_2722_ = lean_uint64_xor(v_fold_2719_, v___x_2721_);
v___x_2723_ = lean_uint64_to_usize(v___x_2722_);
v___x_2724_ = lean_usize_of_nat(v___x_2714_);
v___x_2725_ = ((size_t)1ULL);
v___x_2726_ = lean_usize_sub(v___x_2724_, v___x_2725_);
v___x_2727_ = lean_usize_land(v___x_2723_, v___x_2726_);
v___x_2728_ = lean_array_uget_borrowed(v_buckets_2713_, v___x_2727_);
v___x_2729_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2712_, v___x_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg___boxed(lean_object* v_m_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2730_, v_a_2731_);
lean_dec(v_a_2731_);
lean_dec_ref(v_m_2730_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addConstraint(lean_object* v_p_2733_, lean_object* v_x_2734_){
_start:
{
uint8_t v_possible_2735_; 
v_possible_2735_ = lean_ctor_get_uint8(v_p_2733_, sizeof(void*)*7);
if (v_possible_2735_ == 0)
{
lean_dec_ref(v_x_2734_);
return v_p_2733_;
}
else
{
lean_object* v_coeffs_2736_; lean_object* v_constraint_2737_; lean_object* v_justification_2738_; lean_object* v_constraints_2739_; lean_object* v___x_2740_; 
v_coeffs_2736_ = lean_ctor_get(v_x_2734_, 0);
v_constraint_2737_ = lean_ctor_get(v_x_2734_, 1);
v_justification_2738_ = lean_ctor_get(v_x_2734_, 2);
v_constraints_2739_ = lean_ctor_get(v_p_2733_, 2);
v___x_2740_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2739_, v_coeffs_2736_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_lowerBound_2741_; 
v_lowerBound_2741_ = lean_ctor_get(v_constraint_2737_, 0);
if (lean_obj_tag(v_lowerBound_2741_) == 0)
{
lean_object* v_upperBound_2742_; 
v_upperBound_2742_ = lean_ctor_get(v_constraint_2737_, 1);
if (lean_obj_tag(v_upperBound_2742_) == 0)
{
lean_dec_ref(v_x_2734_);
return v_p_2733_;
}
else
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2733_, v_x_2734_);
return v___x_2743_;
}
}
else
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2733_, v_x_2734_);
return v___x_2744_;
}
}
else
{
lean_object* v_val_2745_; lean_object* v_coeffs_2746_; lean_object* v_constraint_2747_; lean_object* v_justification_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2763_; 
v_val_2745_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_val_2745_);
lean_dec_ref_known(v___x_2740_, 1);
v_coeffs_2746_ = lean_ctor_get(v_val_2745_, 0);
v_constraint_2747_ = lean_ctor_get(v_val_2745_, 1);
v_justification_2748_ = lean_ctor_get(v_val_2745_, 2);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_val_2745_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2750_ = v_val_2745_;
v_isShared_2751_ = v_isSharedCheck_2763_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_justification_2748_);
lean_inc(v_constraint_2747_);
lean_inc(v_coeffs_2746_);
lean_dec(v_val_2745_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2763_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2752_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc(v_coeffs_2736_);
v___x_2753_ = l_instDecidableEqList___redArg(v___x_2752_, v_coeffs_2736_, v_coeffs_2746_);
if (v___x_2753_ == 0)
{
lean_del_object(v___x_2750_);
lean_dec_ref(v_justification_2748_);
lean_dec_ref(v_constraint_2747_);
lean_dec_ref(v_x_2734_);
return v_p_2733_;
}
else
{
lean_object* v_r_2754_; uint8_t v___x_2755_; 
lean_inc_ref_n(v_constraint_2747_, 2);
lean_inc_ref(v_constraint_2737_);
v_r_2754_ = l_Lean_Omega_Constraint_combine(v_constraint_2737_, v_constraint_2747_);
lean_inc_ref(v_r_2754_);
v___x_2755_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2754_, v_constraint_2747_);
if (v___x_2755_ == 0)
{
uint8_t v___x_2756_; 
lean_inc_ref(v_constraint_2737_);
lean_inc_ref(v_r_2754_);
v___x_2756_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2754_, v_constraint_2737_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; lean_object* v___x_2759_; 
lean_inc_ref(v_justification_2738_);
lean_inc_ref(v_constraint_2737_);
lean_inc_n(v_coeffs_2736_, 2);
lean_dec_ref(v_x_2734_);
v___x_2757_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_2757_, 0, v_constraint_2737_);
lean_ctor_set(v___x_2757_, 1, v_constraint_2747_);
lean_ctor_set(v___x_2757_, 2, v_coeffs_2736_);
lean_ctor_set(v___x_2757_, 3, v_justification_2738_);
lean_ctor_set(v___x_2757_, 4, v_justification_2748_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 2, v___x_2757_);
lean_ctor_set(v___x_2750_, 1, v_r_2754_);
lean_ctor_set(v___x_2750_, 0, v_coeffs_2736_);
v___x_2759_ = v___x_2750_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_coeffs_2736_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_r_2754_);
lean_ctor_set(v_reuseFailAlloc_2761_, 2, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2733_, v___x_2759_);
return v___x_2760_;
}
}
else
{
lean_object* v___x_2762_; 
lean_dec_ref(v_r_2754_);
lean_del_object(v___x_2750_);
lean_dec_ref(v_justification_2748_);
lean_dec_ref(v_constraint_2747_);
v___x_2762_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2733_, v_x_2734_);
return v___x_2762_;
}
}
else
{
lean_dec_ref(v_r_2754_);
lean_del_object(v___x_2750_);
lean_dec_ref(v_justification_2748_);
lean_dec_ref(v_constraint_2747_);
lean_dec_ref(v_x_2734_);
return v_p_2733_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(lean_object* v_00_u03b2_2764_, lean_object* v_m_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2765_, v_a_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___boxed(lean_object* v_00_u03b2_2768_, lean_object* v_m_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(v_00_u03b2_2768_, v_m_2769_, v_a_2770_);
lean_dec(v_a_2770_);
lean_dec_ref(v_m_2769_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(lean_object* v_00_u03b2_2772_, lean_object* v_a_2773_, lean_object* v_x_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2773_, v_x_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2776_, lean_object* v_a_2777_, lean_object* v_x_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(v_00_u03b2_2776_, v_a_2777_, v_x_2778_);
lean_dec(v_x_2778_);
lean_dec(v_a_2777_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(lean_object* v_x_2780_, lean_object* v_x_2781_){
_start:
{
if (lean_obj_tag(v_x_2781_) == 0)
{
return v_x_2780_;
}
else
{
if (lean_obj_tag(v_x_2780_) == 0)
{
lean_object* v_key_2782_; lean_object* v_tail_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_key_2782_ = lean_ctor_get(v_x_2781_, 0);
lean_inc_n(v_key_2782_, 2);
v_tail_2783_ = lean_ctor_get(v_x_2781_, 2);
lean_inc(v_tail_2783_);
lean_dec_ref_known(v_x_2781_, 3);
v___x_2784_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2782_);
v___x_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2785_, 0, v_key_2782_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
v___x_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
v_x_2780_ = v___x_2786_;
v_x_2781_ = v_tail_2783_;
goto _start;
}
else
{
lean_object* v_val_2788_; lean_object* v_key_2789_; lean_object* v_tail_2790_; lean_object* v_fst_2791_; lean_object* v_snd_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2820_; 
v_val_2788_ = lean_ctor_get(v_x_2780_, 0);
lean_inc(v_val_2788_);
v_key_2789_ = lean_ctor_get(v_x_2781_, 0);
lean_inc(v_key_2789_);
v_tail_2790_ = lean_ctor_get(v_x_2781_, 2);
lean_inc(v_tail_2790_);
lean_dec_ref_known(v_x_2781_, 3);
v_fst_2791_ = lean_ctor_get(v_val_2788_, 0);
v_snd_2792_ = lean_ctor_get(v_val_2788_, 1);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_val_2788_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2794_ = v_val_2788_;
v_isShared_2795_ = v_isSharedCheck_2820_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_snd_2792_);
lean_inc(v_fst_2791_);
lean_dec(v_val_2788_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2820_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2796_; uint8_t v___x_2797_; 
v___x_2796_ = lean_unsigned_to_nat(2u);
v___x_2797_ = lean_nat_dec_le(v___x_2796_, v_snd_2792_);
if (v___x_2797_ == 0)
{
lean_del_object(v___x_2794_);
lean_dec(v_snd_2792_);
lean_dec(v_fst_2791_);
lean_dec(v_key_2789_);
v_x_2781_ = v_tail_2790_;
goto _start;
}
else
{
lean_object* v_m_x27_2799_; uint8_t v___y_2801_; uint8_t v___x_2815_; 
lean_inc(v_key_2789_);
v_m_x27_2799_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2789_);
v___x_2815_ = lean_nat_dec_lt(v_m_x27_2799_, v_snd_2792_);
if (v___x_2815_ == 0)
{
uint8_t v___x_2816_; 
v___x_2816_ = lean_nat_dec_eq(v_m_x27_2799_, v_snd_2792_);
lean_dec(v_snd_2792_);
if (v___x_2816_ == 0)
{
lean_dec(v_fst_2791_);
v___y_2801_ = v___x_2816_;
goto v___jp_2800_;
}
else
{
lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
lean_inc(v_key_2789_);
v___x_2817_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_key_2789_);
v___x_2818_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_fst_2791_);
v___x_2819_ = lean_nat_dec_lt(v___x_2817_, v___x_2818_);
lean_dec(v___x_2818_);
lean_dec(v___x_2817_);
v___y_2801_ = v___x_2819_;
goto v___jp_2800_;
}
}
else
{
lean_dec(v_snd_2792_);
lean_dec(v_fst_2791_);
v___y_2801_ = v___x_2815_;
goto v___jp_2800_;
}
v___jp_2800_:
{
if (v___y_2801_ == 0)
{
lean_dec(v_m_x27_2799_);
lean_del_object(v___x_2794_);
lean_dec(v_key_2789_);
v_x_2781_ = v_tail_2790_;
goto _start;
}
else
{
lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2813_; 
v_isSharedCheck_2813_ = !lean_is_exclusive(v_x_2780_);
if (v_isSharedCheck_2813_ == 0)
{
lean_object* v_unused_2814_; 
v_unused_2814_ = lean_ctor_get(v_x_2780_, 0);
lean_dec(v_unused_2814_);
v___x_2804_ = v_x_2780_;
v_isShared_2805_ = v_isSharedCheck_2813_;
goto v_resetjp_2803_;
}
else
{
lean_dec(v_x_2780_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2813_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 1, v_m_x27_2799_);
lean_ctor_set(v___x_2794_, 0, v_key_2789_);
v___x_2807_ = v___x_2794_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_key_2789_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_m_x27_2799_);
v___x_2807_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2809_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2807_);
v___x_2809_ = v___x_2804_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2807_);
v___x_2809_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
v_x_2780_ = v___x_2809_;
v_x_2781_ = v_tail_2790_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(lean_object* v_as_2821_, size_t v_i_2822_, size_t v_stop_2823_, lean_object* v_b_2824_){
_start:
{
uint8_t v___x_2825_; 
v___x_2825_ = lean_usize_dec_eq(v_i_2822_, v_stop_2823_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2827_; size_t v___x_2828_; size_t v___x_2829_; 
v___x_2826_ = lean_array_uget_borrowed(v_as_2821_, v_i_2822_);
lean_inc(v___x_2826_);
v___x_2827_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(v_b_2824_, v___x_2826_);
v___x_2828_ = ((size_t)1ULL);
v___x_2829_ = lean_usize_add(v_i_2822_, v___x_2828_);
v_i_2822_ = v___x_2829_;
v_b_2824_ = v___x_2827_;
goto _start;
}
else
{
return v_b_2824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1___boxed(lean_object* v_as_2831_, lean_object* v_i_2832_, lean_object* v_stop_2833_, lean_object* v_b_2834_){
_start:
{
size_t v_i_boxed_2835_; size_t v_stop_boxed_2836_; lean_object* v_res_2837_; 
v_i_boxed_2835_ = lean_unbox_usize(v_i_2832_);
lean_dec(v_i_2832_);
v_stop_boxed_2836_ = lean_unbox_usize(v_stop_2833_);
lean_dec(v_stop_2833_);
v_res_2837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_as_2831_, v_i_boxed_2835_, v_stop_boxed_2836_, v_b_2834_);
lean_dec_ref(v_as_2831_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality(lean_object* v_p_2838_){
_start:
{
lean_object* v_equalities_2839_; lean_object* v_buckets_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v_equalities_2839_ = lean_ctor_get(v_p_2838_, 3);
v_buckets_2840_ = lean_ctor_get(v_equalities_2839_, 1);
v___x_2841_ = lean_box(0);
v___x_2842_ = lean_unsigned_to_nat(0u);
v___x_2843_ = lean_array_get_size(v_buckets_2840_);
v___x_2844_ = lean_nat_dec_lt(v___x_2842_, v___x_2843_);
if (v___x_2844_ == 0)
{
return v___x_2841_;
}
else
{
uint8_t v___x_2845_; 
v___x_2845_ = lean_nat_dec_le(v___x_2843_, v___x_2843_);
if (v___x_2845_ == 0)
{
if (v___x_2844_ == 0)
{
return v___x_2841_;
}
else
{
size_t v___x_2846_; size_t v___x_2847_; lean_object* v___x_2848_; 
v___x_2846_ = ((size_t)0ULL);
v___x_2847_ = lean_usize_of_nat(v___x_2843_);
v___x_2848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2840_, v___x_2846_, v___x_2847_, v___x_2841_);
return v___x_2848_;
}
}
else
{
size_t v___x_2849_; size_t v___x_2850_; lean_object* v___x_2851_; 
v___x_2849_ = ((size_t)0ULL);
v___x_2850_ = lean_usize_of_nat(v___x_2843_);
v___x_2851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2840_, v___x_2849_, v___x_2850_, v___x_2841_);
return v___x_2851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality___boxed(lean_object* v_p_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_2852_);
lean_dec_ref(v_p_2852_);
return v_res_2853_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_unsigned_to_nat(1u);
v___x_2855_ = lean_nat_to_int(v___x_2854_);
return v___x_2855_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2857_ = lean_int_neg(v___x_2856_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(lean_object* v_as_2858_, size_t v_i_2859_, size_t v_stop_2860_, lean_object* v_b_2861_){
_start:
{
uint8_t v___x_2862_; 
v___x_2862_ = lean_usize_dec_eq(v_i_2859_, v_stop_2860_);
if (v___x_2862_ == 0)
{
size_t v___x_2863_; size_t v___x_2864_; lean_object* v___x_2865_; lean_object* v_snd_2866_; lean_object* v_fst_2867_; lean_object* v_fst_2868_; lean_object* v_snd_2869_; lean_object* v_coeffs_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2863_ = ((size_t)1ULL);
v___x_2864_ = lean_usize_sub(v_i_2859_, v___x_2863_);
v___x_2865_ = lean_array_uget_borrowed(v_as_2858_, v___x_2864_);
v_snd_2866_ = lean_ctor_get(v___x_2865_, 1);
v_fst_2867_ = lean_ctor_get(v___x_2865_, 0);
v_fst_2868_ = lean_ctor_get(v_snd_2866_, 0);
v_snd_2869_ = lean_ctor_get(v_snd_2866_, 1);
v_coeffs_2870_ = lean_ctor_get(v_b_2861_, 0);
lean_inc(v_fst_2868_);
v___x_2871_ = l_Lean_Omega_IntList_get(v_coeffs_2870_, v_fst_2868_);
v___x_2872_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2873_ = lean_int_dec_eq(v___x_2871_, v___x_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2874_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2875_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2876_ = lean_int_mul(v___x_2875_, v_snd_2869_);
v___x_2877_ = lean_int_mul(v___x_2876_, v___x_2871_);
lean_dec(v___x_2871_);
lean_dec(v___x_2876_);
lean_inc(v_fst_2867_);
v___x_2878_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v___x_2877_, v_fst_2867_, v___x_2874_, v_b_2861_);
v_i_2859_ = v___x_2864_;
v_b_2861_ = v___x_2878_;
goto _start;
}
else
{
lean_dec(v___x_2871_);
v_i_2859_ = v___x_2864_;
goto _start;
}
}
else
{
return v_b_2861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___boxed(lean_object* v_as_2881_, lean_object* v_i_2882_, lean_object* v_stop_2883_, lean_object* v_b_2884_){
_start:
{
size_t v_i_boxed_2885_; size_t v_stop_boxed_2886_; lean_object* v_res_2887_; 
v_i_boxed_2885_ = lean_unbox_usize(v_i_2882_);
lean_dec(v_i_2882_);
v_stop_boxed_2886_ = lean_unbox_usize(v_stop_2883_);
lean_dec(v_stop_2883_);
v_res_2887_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v_as_2881_, v_i_boxed_2885_, v_stop_boxed_2886_, v_b_2884_);
lean_dec_ref(v_as_2881_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(lean_object* v_init_2888_, lean_object* v_l_2889_){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; uint8_t v___x_2893_; 
v___x_2890_ = lean_array_mk(v_l_2889_);
v___x_2891_ = lean_array_get_size(v___x_2890_);
v___x_2892_ = lean_unsigned_to_nat(0u);
v___x_2893_ = lean_nat_dec_lt(v___x_2892_, v___x_2891_);
if (v___x_2893_ == 0)
{
lean_dec_ref(v___x_2890_);
return v_init_2888_;
}
else
{
size_t v___x_2894_; size_t v___x_2895_; lean_object* v___x_2896_; 
v___x_2894_ = lean_usize_of_nat(v___x_2891_);
v___x_2895_ = ((size_t)0ULL);
v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v___x_2890_, v___x_2894_, v___x_2895_, v_init_2888_);
lean_dec_ref(v___x_2890_);
return v___x_2896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(lean_object* v_p_2897_, lean_object* v_f_2898_){
_start:
{
lean_object* v_eliminations_2899_; lean_object* v___x_2900_; 
v_eliminations_2899_ = lean_ctor_get(v_p_2897_, 4);
lean_inc(v_eliminations_2899_);
lean_dec_ref(v_p_2897_);
v___x_2900_ = l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(v_f_2898_, v_eliminations_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__0(lean_object* v_x_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(lean_object* v___y_2903_, lean_object* v_sign_2904_, lean_object* v_val_2905_, lean_object* v_x_2906_, lean_object* v_x_2907_){
_start:
{
if (lean_obj_tag(v_x_2907_) == 0)
{
lean_dec_ref(v_val_2905_);
lean_dec(v___y_2903_);
return v_x_2906_;
}
else
{
lean_object* v_key_2908_; lean_object* v_value_2909_; lean_object* v_tail_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; uint8_t v___x_2913_; 
v_key_2908_ = lean_ctor_get(v_x_2907_, 0);
lean_inc(v_key_2908_);
v_value_2909_ = lean_ctor_get(v_x_2907_, 1);
lean_inc(v_value_2909_);
v_tail_2910_ = lean_ctor_get(v_x_2907_, 2);
lean_inc(v_tail_2910_);
lean_dec_ref_known(v_x_2907_, 3);
lean_inc(v___y_2903_);
v___x_2911_ = l_Lean_Omega_IntList_get(v_key_2908_, v___y_2903_);
lean_dec(v_key_2908_);
v___x_2912_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2913_ = lean_int_dec_eq(v___x_2911_, v___x_2912_);
if (v___x_2913_ == 0)
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v_k_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2914_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2915_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2916_ = lean_int_mul(v___x_2915_, v_sign_2904_);
v_k_2917_ = lean_int_mul(v___x_2916_, v___x_2911_);
lean_dec(v___x_2911_);
lean_dec(v___x_2916_);
lean_inc_ref(v_val_2905_);
v___x_2918_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_k_2917_, v_val_2905_, v___x_2914_, v_value_2909_);
v___x_2919_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_2918_);
v___x_2920_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2906_, v___x_2919_);
v_x_2906_ = v___x_2920_;
v_x_2907_ = v_tail_2910_;
goto _start;
}
else
{
lean_object* v___x_2922_; 
lean_dec(v___x_2911_);
v___x_2922_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2906_, v_value_2909_);
v_x_2906_ = v___x_2922_;
v_x_2907_ = v_tail_2910_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0___boxed(lean_object* v___y_2924_, lean_object* v_sign_2925_, lean_object* v_val_2926_, lean_object* v_x_2927_, lean_object* v_x_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2924_, v_sign_2925_, v_val_2926_, v_x_2927_, v_x_2928_);
lean_dec(v_sign_2925_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object* v___y_2930_, lean_object* v_sign_2931_, lean_object* v_val_2932_, lean_object* v_as_2933_, size_t v_i_2934_, size_t v_stop_2935_, lean_object* v_b_2936_){
_start:
{
uint8_t v___x_2937_; 
v___x_2937_ = lean_usize_dec_eq(v_i_2934_, v_stop_2935_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2939_; size_t v___x_2940_; size_t v___x_2941_; 
v___x_2938_ = lean_array_uget_borrowed(v_as_2933_, v_i_2934_);
lean_inc(v___x_2938_);
lean_inc_ref(v_val_2932_);
lean_inc(v___y_2930_);
v___x_2939_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2930_, v_sign_2931_, v_val_2932_, v_b_2936_, v___x_2938_);
v___x_2940_ = ((size_t)1ULL);
v___x_2941_ = lean_usize_add(v_i_2934_, v___x_2940_);
v_i_2934_ = v___x_2941_;
v_b_2936_ = v___x_2939_;
goto _start;
}
else
{
lean_dec_ref(v_val_2932_);
lean_dec(v___y_2930_);
return v_b_2936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1___boxed(lean_object* v___y_2943_, lean_object* v_sign_2944_, lean_object* v_val_2945_, lean_object* v_as_2946_, lean_object* v_i_2947_, lean_object* v_stop_2948_, lean_object* v_b_2949_){
_start:
{
size_t v_i_boxed_2950_; size_t v_stop_boxed_2951_; lean_object* v_res_2952_; 
v_i_boxed_2950_ = lean_unbox_usize(v_i_2947_);
lean_dec(v_i_2947_);
v_stop_boxed_2951_ = lean_unbox_usize(v_stop_2948_);
lean_dec(v_stop_2948_);
v_res_2952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2943_, v_sign_2944_, v_val_2945_, v_as_2946_, v_i_boxed_2950_, v_stop_boxed_2951_, v_b_2949_);
lean_dec_ref(v_as_2946_);
lean_dec(v_sign_2944_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
if (lean_obj_tag(v_a_2953_) == 0)
{
lean_object* v___x_2955_; 
lean_dec(v_a_2954_);
v___x_2955_ = lean_box(0);
return v___x_2955_;
}
else
{
lean_object* v_head_2956_; lean_object* v_tail_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v_head_2956_ = lean_ctor_get(v_a_2953_, 0);
v_tail_2957_ = lean_ctor_get(v_a_2953_, 1);
v___x_2958_ = lean_nat_abs(v_head_2956_);
v___x_2959_ = lean_unsigned_to_nat(1u);
v___x_2960_ = lean_nat_dec_eq(v___x_2958_, v___x_2959_);
lean_dec(v___x_2958_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_nat_add(v_a_2954_, v___x_2959_);
lean_dec(v_a_2954_);
v_a_2953_ = v_tail_2957_;
v_a_2954_ = v___x_2961_;
goto _start;
}
else
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2963_, 0, v_a_2954_);
return v___x_2963_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2___boxed(lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(v_a_2964_, v_a_2965_);
lean_dec(v_a_2964_);
return v_res_2966_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1(void){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = lean_box(0);
v___x_2969_ = lean_unsigned_to_nat(16u);
v___x_2970_ = lean_mk_array(v___x_2969_, v___x_2968_);
return v___x_2970_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2(void){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1);
v___x_2972_ = lean_unsigned_to_nat(0u);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v___x_2971_);
return v___x_2973_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3(void){
_start:
{
lean_object* v___f_2974_; lean_object* v___x_2975_; 
v___f_2974_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0));
v___x_2975_ = lean_mk_thunk(v___f_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(lean_object* v_p_2976_, lean_object* v_c_2977_){
_start:
{
lean_object* v___y_2979_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = lean_unsigned_to_nat(0u);
v___x_3027_ = l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(v_c_2977_, v___x_3026_);
if (lean_obj_tag(v___x_3027_) == 0)
{
v___y_2979_ = v___x_3026_;
goto v___jp_2978_;
}
else
{
lean_object* v_val_3028_; 
v_val_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_val_3028_);
lean_dec_ref_known(v___x_3027_, 1);
v___y_2979_ = v_val_3028_;
goto v___jp_2978_;
}
v___jp_2978_:
{
lean_object* v_assumptions_2980_; lean_object* v_constraints_2981_; lean_object* v_eliminations_2982_; lean_object* v___x_2983_; 
v_assumptions_2980_ = lean_ctor_get(v_p_2976_, 0);
v_constraints_2981_ = lean_ctor_get(v_p_2976_, 2);
lean_inc_ref(v_constraints_2981_);
v_eliminations_2982_ = lean_ctor_get(v_p_2976_, 4);
v___x_2983_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2981_, v_c_2977_);
if (lean_obj_tag(v___x_2983_) == 1)
{
lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3018_; 
lean_inc(v_eliminations_2982_);
lean_inc_ref(v_assumptions_2980_);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_p_2976_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; lean_object* v_unused_3020_; lean_object* v_unused_3021_; lean_object* v_unused_3022_; lean_object* v_unused_3023_; lean_object* v_unused_3024_; lean_object* v_unused_3025_; 
v_unused_3019_ = lean_ctor_get(v_p_2976_, 6);
lean_dec(v_unused_3019_);
v_unused_3020_ = lean_ctor_get(v_p_2976_, 5);
lean_dec(v_unused_3020_);
v_unused_3021_ = lean_ctor_get(v_p_2976_, 4);
lean_dec(v_unused_3021_);
v_unused_3022_ = lean_ctor_get(v_p_2976_, 3);
lean_dec(v_unused_3022_);
v_unused_3023_ = lean_ctor_get(v_p_2976_, 2);
lean_dec(v_unused_3023_);
v_unused_3024_ = lean_ctor_get(v_p_2976_, 1);
lean_dec(v_unused_3024_);
v_unused_3025_ = lean_ctor_get(v_p_2976_, 0);
lean_dec(v_unused_3025_);
v___x_2985_ = v_p_2976_;
v_isShared_2986_ = v_isSharedCheck_3018_;
goto v_resetjp_2984_;
}
else
{
lean_dec(v_p_2976_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3018_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v_val_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v_buckets_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3016_; 
v_val_2987_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_val_2987_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2988_ = lean_unsigned_to_nat(0u);
v___x_2989_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v_buckets_2990_ = lean_ctor_get(v_constraints_2981_, 1);
v_isSharedCheck_3016_ = !lean_is_exclusive(v_constraints_2981_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; 
v_unused_3017_ = lean_ctor_get(v_constraints_2981_, 0);
lean_dec(v_unused_3017_);
v___x_2992_ = v_constraints_2981_;
v_isShared_2993_ = v_isSharedCheck_3016_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_buckets_2990_);
lean_dec(v_constraints_2981_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3016_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; lean_object* v_sign_2995_; lean_object* v___x_2997_; 
lean_inc_n(v___y_2979_, 2);
v___x_2994_ = l_Lean_Omega_IntList_get(v_c_2977_, v___y_2979_);
v_sign_2995_ = l_Int_sign(v___x_2994_);
lean_dec(v___x_2994_);
lean_inc(v_sign_2995_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v_sign_2995_);
lean_ctor_set(v___x_2992_, 0, v___y_2979_);
v___x_2997_ = v___x_2992_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___y_2979_);
lean_ctor_set(v_reuseFailAlloc_3015_, 1, v_sign_2995_);
v___x_2997_ = v_reuseFailAlloc_3015_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v_init_3004_; 
lean_inc(v_val_2987_);
v___x_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2998_, 0, v_val_2987_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
lean_ctor_set(v___x_2999_, 1, v_eliminations_2982_);
v___x_3000_ = 1;
v___x_3001_ = lean_box(0);
v___x_3002_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 6, v___x_3002_);
lean_ctor_set(v___x_2985_, 5, v___x_3001_);
lean_ctor_set(v___x_2985_, 4, v___x_2999_);
lean_ctor_set(v___x_2985_, 3, v___x_2989_);
lean_ctor_set(v___x_2985_, 2, v___x_2989_);
lean_ctor_set(v___x_2985_, 1, v___x_2988_);
v_init_3004_ = v___x_2985_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_assumptions_2980_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_3014_, 2, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_3014_, 3, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_3014_, 4, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3014_, 5, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3014_, 6, v___x_3002_);
v_init_3004_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
lean_object* v___x_3005_; uint8_t v___x_3006_; 
lean_ctor_set_uint8(v_init_3004_, sizeof(void*)*7, v___x_3000_);
v___x_3005_ = lean_array_get_size(v_buckets_2990_);
v___x_3006_ = lean_nat_dec_lt(v___x_2988_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_dec(v_sign_2995_);
lean_dec_ref(v_buckets_2990_);
lean_dec(v_val_2987_);
lean_dec(v___y_2979_);
return v_init_3004_;
}
else
{
uint8_t v___x_3007_; 
v___x_3007_ = lean_nat_dec_le(v___x_3005_, v___x_3005_);
if (v___x_3007_ == 0)
{
if (v___x_3006_ == 0)
{
lean_dec(v_sign_2995_);
lean_dec_ref(v_buckets_2990_);
lean_dec(v_val_2987_);
lean_dec(v___y_2979_);
return v_init_3004_;
}
else
{
size_t v___x_3008_; size_t v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = ((size_t)0ULL);
v___x_3009_ = lean_usize_of_nat(v___x_3005_);
v___x_3010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2979_, v_sign_2995_, v_val_2987_, v_buckets_2990_, v___x_3008_, v___x_3009_, v_init_3004_);
lean_dec_ref(v_buckets_2990_);
lean_dec(v_sign_2995_);
return v___x_3010_;
}
}
else
{
size_t v___x_3011_; size_t v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = ((size_t)0ULL);
v___x_3012_ = lean_usize_of_nat(v___x_3005_);
v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2979_, v_sign_2995_, v_val_2987_, v_buckets_2990_, v___x_3011_, v___x_3012_, v_init_3004_);
lean_dec_ref(v_buckets_2990_);
lean_dec(v_sign_2995_);
return v___x_3013_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2983_);
lean_dec_ref(v_constraints_2981_);
lean_dec(v___y_2979_);
return v_p_2976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___boxed(lean_object* v_p_3029_, lean_object* v_c_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_3029_, v_c_3030_);
lean_dec(v_c_3030_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(lean_object* v_msgData_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v___x_3038_; lean_object* v_env_3039_; lean_object* v___x_3040_; lean_object* v_mctx_3041_; lean_object* v_lctx_3042_; lean_object* v_options_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3038_ = lean_st_ref_get(v___y_3036_);
v_env_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc_ref(v_env_3039_);
lean_dec(v___x_3038_);
v___x_3040_ = lean_st_ref_get(v___y_3034_);
v_mctx_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc_ref(v_mctx_3041_);
lean_dec(v___x_3040_);
v_lctx_3042_ = lean_ctor_get(v___y_3033_, 2);
v_options_3043_ = lean_ctor_get(v___y_3035_, 2);
lean_inc_ref(v_options_3043_);
lean_inc_ref(v_lctx_3042_);
v___x_3044_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3044_, 0, v_env_3039_);
lean_ctor_set(v___x_3044_, 1, v_mctx_3041_);
lean_ctor_set(v___x_3044_, 2, v_lctx_3042_);
lean_ctor_set(v___x_3044_, 3, v_options_3043_);
v___x_3045_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v_msgData_3032_);
v___x_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0___boxed(lean_object* v_msgData_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msgData_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(lean_object* v_msg_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_ref_3060_; lean_object* v___x_3061_; lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3070_; 
v_ref_3060_ = lean_ctor_get(v___y_3057_, 5);
v___x_3061_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3064_ = v___x_3061_;
v_isShared_3065_ = v_isSharedCheck_3070_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3070_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3066_; lean_object* v___x_3068_; 
lean_inc(v_ref_3060_);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v_ref_3060_);
lean_ctor_set(v___x_3066_, 1, v_a_3062_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set_tag(v___x_3064_, 1);
lean_ctor_set(v___x_3064_, 0, v___x_3066_);
v___x_3068_ = v___x_3064_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg___boxed(lean_object* v_msg_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
return v_res_3077_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = lean_box(0);
v___x_3079_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13));
v___x_3080_ = l_Lean_Expr_const___override(v___x_3079_, v___x_3078_);
return v___x_3080_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2(void){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1));
v___x_3083_ = l_Lean_stringToMessageData(v___x_3082_);
return v___x_3083_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4(void){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3));
v___x_3086_ = l_Lean_stringToMessageData(v___x_3085_);
return v___x_3086_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__6(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5));
v___x_3089_ = l_Lean_stringToMessageData(v___x_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(lean_object* v_p_3090_, lean_object* v_c_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, uint8_t v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v_constraints_3102_; lean_object* v___x_3103_; 
v_constraints_3102_ = lean_ctor_get(v_p_3090_, 2);
v___x_3103_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_3102_, v_c_3091_);
if (lean_obj_tag(v___x_3103_) == 1)
{
lean_object* v_val_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3203_; 
v_val_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3203_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_val_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3203_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v_constraint_3108_; lean_object* v_lowerBound_3109_; 
v_constraint_3108_ = lean_ctor_get(v_val_3104_, 1);
v_lowerBound_3109_ = lean_ctor_get(v_constraint_3108_, 0);
lean_inc(v_lowerBound_3109_);
if (lean_obj_tag(v_lowerBound_3109_) == 1)
{
lean_object* v_upperBound_3110_; 
lean_del_object(v___x_3106_);
v_upperBound_3110_ = lean_ctor_get(v_constraint_3108_, 1);
lean_inc(v_upperBound_3110_);
if (lean_obj_tag(v_upperBound_3110_) == 1)
{
lean_object* v_coeffs_3111_; lean_object* v_justification_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3190_; 
v_coeffs_3111_ = lean_ctor_get(v_val_3104_, 0);
v_justification_3112_ = lean_ctor_get(v_val_3104_, 2);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_val_3104_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; 
v_unused_3191_ = lean_ctor_get(v_val_3104_, 1);
lean_dec(v_unused_3191_);
v___x_3114_ = v_val_3104_;
v_isShared_3115_ = v_isSharedCheck_3190_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_justification_3112_);
lean_inc(v_coeffs_3111_);
lean_dec(v_val_3104_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3190_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v_val_3116_; lean_object* v_val_3117_; lean_object* v___x_3118_; 
v_val_3116_ = lean_ctor_get(v_lowerBound_3109_, 0);
lean_inc(v_val_3116_);
lean_dec_ref_known(v_lowerBound_3109_, 1);
v_val_3117_ = lean_ctor_get(v_upperBound_3110_, 0);
lean_inc(v_val_3117_);
lean_dec_ref_known(v_upperBound_3110_, 1);
v___x_3118_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3093_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v_m_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v_nil_3125_; lean_object* v_cons_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v___x_3118_, 1);
lean_inc(v_c_3091_);
v___x_3120_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_c_3091_);
v___x_3121_ = lean_unsigned_to_nat(1u);
v_m_3122_ = lean_nat_add(v___x_3120_, v___x_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0);
lean_inc(v_m_3122_);
v___x_3124_ = l_Lean_mkNatLit(v_m_3122_);
v_nil_3125_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3126_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3127_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3125_, v_cons_3126_, v_c_3091_);
lean_dec(v_c_3091_);
v___x_3128_ = l_Lean_mkApp3(v___x_3123_, v___x_3124_, v___x_3127_, v_a_3119_);
v___x_3129_ = l_Lean_Elab_Tactic_Omega_lookup(v___x_3128_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3173_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3132_ = v___x_3129_;
v_isShared_3133_ = v_isSharedCheck_3173_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3173_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v_fst_3134_; lean_object* v_snd_3135_; uint8_t v___x_3148_; 
v_fst_3134_ = lean_ctor_get(v_a_3130_, 0);
lean_inc(v_fst_3134_);
v_snd_3135_ = lean_ctor_get(v_a_3130_, 1);
lean_inc(v_snd_3135_);
lean_dec(v_a_3130_);
v___x_3148_ = lean_int_dec_eq(v_val_3117_, v_val_3116_);
lean_dec(v_val_3117_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec(v_snd_3135_);
lean_dec(v_fst_3134_);
lean_del_object(v___x_3132_);
lean_dec(v_m_3122_);
lean_dec(v_val_3116_);
lean_del_object(v___x_3114_);
lean_dec_ref(v_justification_3112_);
lean_dec(v_coeffs_3111_);
lean_dec_ref(v_p_3090_);
v___x_3149_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2);
v___x_3150_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3149_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
return v___x_3150_;
}
else
{
if (lean_obj_tag(v_snd_3135_) == 0)
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v_fst_3134_);
lean_del_object(v___x_3132_);
lean_dec(v_m_3122_);
lean_dec(v_val_3116_);
lean_del_object(v___x_3114_);
lean_dec_ref(v_justification_3112_);
lean_dec(v_coeffs_3111_);
lean_dec_ref(v_p_3090_);
v___x_3151_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4);
v___x_3152_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3151_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
else
{
lean_object* v_val_3161_; uint8_t v___x_3162_; 
v_val_3161_ = lean_ctor_get(v_snd_3135_, 0);
lean_inc(v_val_3161_);
lean_dec_ref_known(v_snd_3135_, 1);
v___x_3162_ = l_List_isEmpty___redArg(v_val_3161_);
lean_dec(v_val_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_dec(v_fst_3134_);
lean_del_object(v___x_3132_);
lean_dec(v_m_3122_);
lean_dec(v_val_3116_);
lean_del_object(v___x_3114_);
lean_dec_ref(v_justification_3112_);
lean_dec(v_coeffs_3111_);
lean_dec_ref(v_p_3090_);
v___x_3163_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__6);
v___x_3164_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3163_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3164_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3164_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
else
{
goto v___jp_3136_;
}
}
}
v___jp_3136_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3142_; 
lean_inc(v_coeffs_3111_);
lean_inc_n(v_m_3122_, 2);
v___x_3137_ = l_Lean_Omega_bmod__coeffs(v_m_3122_, v_fst_3134_, v_coeffs_3111_);
v___x_3138_ = l_Int_bmod(v_val_3116_, v_m_3122_);
v___x_3139_ = l_Lean_Omega_Constraint_exact(v___x_3138_);
v___x_3140_ = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(v___x_3140_, 0, v_m_3122_);
lean_ctor_set(v___x_3140_, 1, v_val_3116_);
lean_ctor_set(v___x_3140_, 2, v_fst_3134_);
lean_ctor_set(v___x_3140_, 3, v_coeffs_3111_);
lean_ctor_set(v___x_3140_, 4, v_justification_3112_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 2, v___x_3140_);
lean_ctor_set(v___x_3114_, 1, v___x_3139_);
lean_ctor_set(v___x_3114_, 0, v___x_3137_);
v___x_3142_ = v___x_3114_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3143_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_3090_, v___x_3142_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v___x_3143_);
v___x_3145_ = v___x_3132_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec(v_m_3122_);
lean_dec(v_val_3117_);
lean_dec(v_val_3116_);
lean_del_object(v___x_3114_);
lean_dec_ref(v_justification_3112_);
lean_dec(v_coeffs_3111_);
lean_dec_ref(v_p_3090_);
v_a_3174_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3129_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3129_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec(v_val_3117_);
lean_dec(v_val_3116_);
lean_del_object(v___x_3114_);
lean_dec_ref(v_justification_3112_);
lean_dec(v_coeffs_3111_);
lean_dec(v_c_3091_);
lean_dec_ref(v_p_3090_);
v_a_3182_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3118_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3118_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
else
{
lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec(v_upperBound_3110_);
lean_dec(v_val_3104_);
lean_dec(v_c_3091_);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_lowerBound_3109_);
if (v_isSharedCheck_3198_ == 0)
{
lean_object* v_unused_3199_; 
v_unused_3199_ = lean_ctor_get(v_lowerBound_3109_, 0);
lean_dec(v_unused_3199_);
v___x_3193_ = v_lowerBound_3109_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_dec(v_lowerBound_3109_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
lean_ctor_set_tag(v___x_3193_, 0);
lean_ctor_set(v___x_3193_, 0, v_p_3090_);
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_p_3090_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
else
{
lean_object* v___x_3201_; 
lean_dec(v_lowerBound_3109_);
lean_dec(v_val_3104_);
lean_dec(v_c_3091_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set_tag(v___x_3106_, 0);
lean_ctor_set(v___x_3106_, 0, v_p_3090_);
v___x_3201_ = v___x_3106_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_p_3090_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
else
{
lean_object* v___x_3204_; 
lean_dec(v___x_3103_);
lean_dec(v_c_3091_);
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v_p_3090_);
return v___x_3204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___boxed(lean_object* v_p_3205_, lean_object* v_c_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
uint8_t v_a_boxed_3217_; lean_object* v_res_3218_; 
v_a_boxed_3217_ = lean_unbox(v_a_3210_);
v_res_3218_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3205_, v_c_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_boxed_3217_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
lean_dec(v_a_3215_);
lean_dec_ref(v_a_3214_);
lean_dec(v_a_3213_);
lean_dec_ref(v_a_3212_);
lean_dec(v_a_3211_);
lean_dec_ref(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec(v_a_3207_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_object* v_00_u03b1_3219_, lean_object* v_msg_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, uint8_t v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3220_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___boxed(lean_object* v_00_u03b1_3232_, lean_object* v_msg_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
uint8_t v___y_14927__boxed_3244_; lean_object* v_res_3245_; 
v___y_14927__boxed_3244_ = lean_unbox(v___y_3237_);
v_res_3245_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(v_00_u03b1_3232_, v_msg_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_14927__boxed_3244_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec(v___y_3234_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality(lean_object* v_p_3246_, lean_object* v_c_3247_, lean_object* v_m_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, uint8_t v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v___x_3259_; uint8_t v___x_3260_; 
v___x_3259_ = lean_unsigned_to_nat(1u);
v___x_3260_ = lean_nat_dec_eq(v_m_3248_, v___x_3259_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3246_, v_c_3247_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
return v___x_3261_;
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_3246_, v_c_3247_);
lean_dec(v_c_3247_);
v___x_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
return v___x_3263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality___boxed(lean_object* v_p_3264_, lean_object* v_c_3265_, lean_object* v_m_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_){
_start:
{
uint8_t v_a_boxed_3277_; lean_object* v_res_3278_; 
v_a_boxed_3277_ = lean_unbox(v_a_3270_);
v_res_3278_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3264_, v_c_3265_, v_m_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_boxed_3277_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec(v_a_3273_);
lean_dec_ref(v_a_3272_);
lean_dec(v_a_3271_);
lean_dec_ref(v_a_3269_);
lean_dec(v_a_3268_);
lean_dec(v_a_3267_);
lean_dec(v_m_3266_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(lean_object* v_p_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, uint8_t v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_){
_start:
{
uint8_t v_possible_3290_; 
v_possible_3290_ = lean_ctor_get_uint8(v_p_3279_, sizeof(void*)*7);
if (v_possible_3290_ == 0)
{
lean_object* v___x_3291_; 
v___x_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3291_, 0, v_p_3279_);
return v___x_3291_;
}
else
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_3279_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v___x_3293_; 
v___x_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3293_, 0, v_p_3279_);
return v___x_3293_;
}
else
{
lean_object* v_val_3294_; lean_object* v_fst_3295_; lean_object* v_snd_3296_; lean_object* v___x_3297_; 
v_val_3294_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_val_3294_);
lean_dec_ref_known(v___x_3292_, 1);
v_fst_3295_ = lean_ctor_get(v_val_3294_, 0);
lean_inc(v_fst_3295_);
v_snd_3296_ = lean_ctor_get(v_val_3294_, 1);
lean_inc(v_snd_3296_);
lean_dec(v_val_3294_);
v___x_3297_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3279_, v_fst_3295_, v_snd_3296_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
lean_dec(v_snd_3296_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
v_p_3279_ = v_a_3298_;
goto _start;
}
else
{
return v___x_3297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities___boxed(lean_object* v_p_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
uint8_t v_a_boxed_3311_; lean_object* v_res_3312_; 
v_a_boxed_3311_ = lean_unbox(v_a_3304_);
v_res_3312_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_boxed_3311_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3303_);
lean_dec(v_a_3302_);
lean_dec(v_a_3301_);
return v_res_3312_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3319_ = lean_box(0);
v___x_3320_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1));
v___x_3321_ = l_Lean_Expr_const___override(v___x_3320_, v___x_3319_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object* v_c_3322_, lean_object* v_x_3323_, lean_object* v_p_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, uint8_t v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3326_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
v___x_3337_ = lean_box(v_a_3328_);
lean_inc(v_a_3333_);
lean_inc_ref(v_a_3332_);
lean_inc(v_a_3331_);
lean_inc_ref(v_a_3330_);
lean_inc(v_a_3329_);
lean_inc_ref(v_a_3327_);
lean_inc(v_a_3326_);
lean_inc(v_a_3325_);
v___x_3338_ = lean_apply_10(v_p_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v___x_3337_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, lean_box(0));
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3364_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3341_ = v___x_3338_;
v_isShared_3342_ = v_isSharedCheck_3364_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3338_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3364_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; lean_object* v___y_3345_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v___x_3343_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2);
v___x_3353_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3354_ = lean_int_dec_le(v___x_3353_, v_c_3322_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3355_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3356_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3357_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3358_ = lean_int_neg(v_c_3322_);
v___x_3359_ = l_Int_toNat(v___x_3358_);
lean_dec(v___x_3358_);
v___x_3360_ = l_Lean_instToExprInt_mkNat(v___x_3359_);
v___x_3361_ = l_Lean_mkApp3(v___x_3355_, v___x_3356_, v___x_3357_, v___x_3360_);
v___y_3345_ = v___x_3361_;
goto v___jp_3344_;
}
else
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = l_Int_toNat(v_c_3322_);
v___x_3363_ = l_Lean_instToExprInt_mkNat(v___x_3362_);
v___y_3345_ = v___x_3363_;
goto v___jp_3344_;
}
v___jp_3344_:
{
lean_object* v_nil_3346_; lean_object* v_cons_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3351_; 
v_nil_3346_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3347_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3348_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3346_, v_cons_3347_, v_x_3323_);
v___x_3349_ = l_Lean_mkApp4(v___x_3343_, v___y_3345_, v___x_3348_, v_a_3336_, v_a_3339_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v___x_3349_);
v___x_3351_ = v___x_3341_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
else
{
lean_dec(v_a_3336_);
return v___x_3338_;
}
}
else
{
lean_dec_ref(v_p_3324_);
return v___x_3335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object* v_c_3365_, lean_object* v_x_3366_, lean_object* v_p_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_){
_start:
{
uint8_t v_a_boxed_3378_; lean_object* v_res_3379_; 
v_a_boxed_3378_ = lean_unbox(v_a_3371_);
v_res_3379_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(v_c_3365_, v_x_3366_, v_p_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_boxed_3378_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
lean_dec(v_a_3376_);
lean_dec_ref(v_a_3375_);
lean_dec(v_a_3374_);
lean_dec_ref(v_a_3373_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3370_);
lean_dec(v_a_3369_);
lean_dec(v_a_3368_);
lean_dec(v_x_3366_);
lean_dec(v_c_3365_);
return v_res_3379_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3386_ = lean_box(0);
v___x_3387_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1));
v___x_3388_ = l_Lean_Expr_const___override(v___x_3387_, v___x_3386_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(lean_object* v_c_3389_, lean_object* v_x_3390_, lean_object* v_p_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, uint8_t v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3393_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3402_, 1);
v___x_3404_ = lean_box(v_a_3395_);
lean_inc(v_a_3400_);
lean_inc_ref(v_a_3399_);
lean_inc(v_a_3398_);
lean_inc_ref(v_a_3397_);
lean_inc(v_a_3396_);
lean_inc_ref(v_a_3394_);
lean_inc(v_a_3393_);
lean_inc(v_a_3392_);
v___x_3405_ = lean_apply_10(v_p_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v___x_3404_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, lean_box(0));
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3431_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3408_ = v___x_3405_;
v_isShared_3409_ = v_isSharedCheck_3431_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3405_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3431_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3410_; lean_object* v___y_3412_; lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3410_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2);
v___x_3420_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3421_ = lean_int_dec_le(v___x_3420_, v_c_3389_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3422_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3423_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3424_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3425_ = lean_int_neg(v_c_3389_);
v___x_3426_ = l_Int_toNat(v___x_3425_);
lean_dec(v___x_3425_);
v___x_3427_ = l_Lean_instToExprInt_mkNat(v___x_3426_);
v___x_3428_ = l_Lean_mkApp3(v___x_3422_, v___x_3423_, v___x_3424_, v___x_3427_);
v___y_3412_ = v___x_3428_;
goto v___jp_3411_;
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = l_Int_toNat(v_c_3389_);
v___x_3430_ = l_Lean_instToExprInt_mkNat(v___x_3429_);
v___y_3412_ = v___x_3430_;
goto v___jp_3411_;
}
v___jp_3411_:
{
lean_object* v_nil_3413_; lean_object* v_cons_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3418_; 
v_nil_3413_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3414_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3415_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3413_, v_cons_3414_, v_x_3390_);
v___x_3416_ = l_Lean_mkApp4(v___x_3410_, v___y_3412_, v___x_3415_, v_a_3403_, v_a_3406_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v___x_3416_);
v___x_3418_ = v___x_3408_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
else
{
lean_dec(v_a_3403_);
return v___x_3405_;
}
}
else
{
lean_dec_ref(v_p_3391_);
return v___x_3402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed(lean_object* v_c_3432_, lean_object* v_x_3433_, lean_object* v_p_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_){
_start:
{
uint8_t v_a_boxed_3445_; lean_object* v_res_3446_; 
v_a_boxed_3445_ = lean_unbox(v_a_3438_);
v_res_3446_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(v_c_3432_, v_x_3433_, v_p_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_boxed_3445_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
lean_dec(v_a_3443_);
lean_dec_ref(v_a_3442_);
lean_dec(v_a_3441_);
lean_dec_ref(v_a_3440_);
lean_dec(v_a_3439_);
lean_dec_ref(v_a_3437_);
lean_dec(v_a_3436_);
lean_dec(v_a_3435_);
lean_dec(v_x_3433_);
lean_dec(v_c_3432_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(lean_object* v_prf_x3f_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, uint8_t v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
if (lean_obj_tag(v_prf_x3f_3447_) == 0)
{
lean_object* v___x_3458_; uint8_t v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3458_ = lean_box(0);
v___x_3459_ = 0;
v___x_3460_ = lean_box(0);
v___x_3461_ = l_Lean_Meta_mkFreshExprMVar(v___x_3458_, v___x_3459_, v___x_3460_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; uint8_t v___x_3463_; lean_object* v___x_3464_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v___x_3461_, 1);
v___x_3463_ = 0;
v___x_3464_ = l_Lean_Meta_mkSorry(v_a_3462_, v___x_3463_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
return v___x_3464_;
}
else
{
return v___x_3461_;
}
}
else
{
lean_object* v_val_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_val_3465_ = lean_ctor_get(v_prf_x3f_3447_, 0);
lean_inc(v_val_3465_);
lean_dec_ref_known(v_prf_x3f_3447_, 1);
v___x_3466_ = lean_box(v___y_3451_);
lean_inc(v___y_3456_);
lean_inc_ref(v___y_3455_);
lean_inc(v___y_3454_);
lean_inc_ref(v___y_3453_);
lean_inc(v___y_3452_);
lean_inc_ref(v___y_3450_);
lean_inc(v___y_3449_);
lean_inc(v___y_3448_);
v___x_3467_ = lean_apply_10(v_val_3465_, v___y_3448_, v___y_3449_, v___y_3450_, v___x_3466_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, lean_box(0));
return v___x_3467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed(lean_object* v_prf_x3f_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
uint8_t v___y_833__boxed_3479_; lean_object* v_res_3480_; 
v___y_833__boxed_3479_ = lean_unbox(v___y_3472_);
v_res_3480_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(v_prf_x3f_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_833__boxed_3479_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec(v___y_3469_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality(lean_object* v_p_3481_, lean_object* v_const_3482_, lean_object* v_coeffs_3483_, lean_object* v_prf_x3f_3484_){
_start:
{
lean_object* v_assumptions_3485_; lean_object* v_numVars_3486_; lean_object* v_constraints_3487_; lean_object* v_equalities_3488_; lean_object* v_eliminations_3489_; uint8_t v_possible_3490_; lean_object* v_proveFalse_x3f_3491_; lean_object* v_explanation_x3f_3492_; lean_object* v_prf_3493_; lean_object* v_i_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v_p_x27_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v_f_3503_; lean_object* v_f_3504_; lean_object* v_f_3505_; lean_object* v___x_3506_; 
v_assumptions_3485_ = lean_ctor_get(v_p_3481_, 0);
v_numVars_3486_ = lean_ctor_get(v_p_3481_, 1);
v_constraints_3487_ = lean_ctor_get(v_p_3481_, 2);
v_equalities_3488_ = lean_ctor_get(v_p_3481_, 3);
v_eliminations_3489_ = lean_ctor_get(v_p_3481_, 4);
v_possible_3490_ = lean_ctor_get_uint8(v_p_3481_, sizeof(void*)*7);
v_proveFalse_x3f_3491_ = lean_ctor_get(v_p_3481_, 5);
v_explanation_x3f_3492_ = lean_ctor_get(v_p_3481_, 6);
v_prf_3493_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3493_, 0, v_prf_x3f_3484_);
v_i_3494_ = lean_array_get_size(v_assumptions_3485_);
lean_inc_n(v_coeffs_3483_, 2);
lean_inc(v_const_3482_);
v___x_3495_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed), 13, 3);
lean_closure_set(v___x_3495_, 0, v_const_3482_);
lean_closure_set(v___x_3495_, 1, v_coeffs_3483_);
lean_closure_set(v___x_3495_, 2, v_prf_3493_);
lean_inc_ref(v_assumptions_3485_);
v___x_3496_ = lean_array_push(v_assumptions_3485_, v___x_3495_);
lean_inc_ref(v_explanation_x3f_3492_);
lean_inc(v_proveFalse_x3f_3491_);
lean_inc(v_eliminations_3489_);
lean_inc_ref(v_equalities_3488_);
lean_inc_ref(v_constraints_3487_);
lean_inc(v_numVars_3486_);
v_p_x27_3497_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3497_, 0, v___x_3496_);
lean_ctor_set(v_p_x27_3497_, 1, v_numVars_3486_);
lean_ctor_set(v_p_x27_3497_, 2, v_constraints_3487_);
lean_ctor_set(v_p_x27_3497_, 3, v_equalities_3488_);
lean_ctor_set(v_p_x27_3497_, 4, v_eliminations_3489_);
lean_ctor_set(v_p_x27_3497_, 5, v_proveFalse_x3f_3491_);
lean_ctor_set(v_p_x27_3497_, 6, v_explanation_x3f_3492_);
lean_ctor_set_uint8(v_p_x27_3497_, sizeof(void*)*7, v_possible_3490_);
v___x_3498_ = lean_int_neg(v_const_3482_);
lean_dec(v_const_3482_);
v___x_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
v___x_3500_ = lean_box(0);
v___x_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3499_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
lean_inc_ref(v___x_3501_);
v___x_3502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_ctor_set(v___x_3502_, 1, v_coeffs_3483_);
lean_ctor_set(v___x_3502_, 2, v_i_3494_);
v_f_3503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3503_, 0, v_coeffs_3483_);
lean_ctor_set(v_f_3503_, 1, v___x_3501_);
lean_ctor_set(v_f_3503_, 2, v___x_3502_);
v_f_3504_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3481_, v_f_3503_);
v_f_3505_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3504_);
v___x_3506_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3497_, v_f_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality(lean_object* v_p_3507_, lean_object* v_const_3508_, lean_object* v_coeffs_3509_, lean_object* v_prf_x3f_3510_){
_start:
{
lean_object* v_assumptions_3511_; lean_object* v_numVars_3512_; lean_object* v_constraints_3513_; lean_object* v_equalities_3514_; lean_object* v_eliminations_3515_; uint8_t v_possible_3516_; lean_object* v_proveFalse_x3f_3517_; lean_object* v_explanation_x3f_3518_; lean_object* v_prf_3519_; lean_object* v_i_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v_p_x27_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v_f_3528_; lean_object* v_f_3529_; lean_object* v_f_3530_; lean_object* v___x_3531_; 
v_assumptions_3511_ = lean_ctor_get(v_p_3507_, 0);
v_numVars_3512_ = lean_ctor_get(v_p_3507_, 1);
v_constraints_3513_ = lean_ctor_get(v_p_3507_, 2);
v_equalities_3514_ = lean_ctor_get(v_p_3507_, 3);
v_eliminations_3515_ = lean_ctor_get(v_p_3507_, 4);
v_possible_3516_ = lean_ctor_get_uint8(v_p_3507_, sizeof(void*)*7);
v_proveFalse_x3f_3517_ = lean_ctor_get(v_p_3507_, 5);
v_explanation_x3f_3518_ = lean_ctor_get(v_p_3507_, 6);
v_prf_3519_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3519_, 0, v_prf_x3f_3510_);
v_i_3520_ = lean_array_get_size(v_assumptions_3511_);
lean_inc_n(v_coeffs_3509_, 2);
lean_inc(v_const_3508_);
v___x_3521_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed), 13, 3);
lean_closure_set(v___x_3521_, 0, v_const_3508_);
lean_closure_set(v___x_3521_, 1, v_coeffs_3509_);
lean_closure_set(v___x_3521_, 2, v_prf_3519_);
lean_inc_ref(v_assumptions_3511_);
v___x_3522_ = lean_array_push(v_assumptions_3511_, v___x_3521_);
lean_inc_ref(v_explanation_x3f_3518_);
lean_inc(v_proveFalse_x3f_3517_);
lean_inc(v_eliminations_3515_);
lean_inc_ref(v_equalities_3514_);
lean_inc_ref(v_constraints_3513_);
lean_inc(v_numVars_3512_);
v_p_x27_3523_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3523_, 0, v___x_3522_);
lean_ctor_set(v_p_x27_3523_, 1, v_numVars_3512_);
lean_ctor_set(v_p_x27_3523_, 2, v_constraints_3513_);
lean_ctor_set(v_p_x27_3523_, 3, v_equalities_3514_);
lean_ctor_set(v_p_x27_3523_, 4, v_eliminations_3515_);
lean_ctor_set(v_p_x27_3523_, 5, v_proveFalse_x3f_3517_);
lean_ctor_set(v_p_x27_3523_, 6, v_explanation_x3f_3518_);
lean_ctor_set_uint8(v_p_x27_3523_, sizeof(void*)*7, v_possible_3516_);
v___x_3524_ = lean_int_neg(v_const_3508_);
lean_dec(v_const_3508_);
v___x_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
lean_inc_ref(v___x_3525_);
v___x_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
lean_inc_ref(v___x_3526_);
v___x_3527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
lean_ctor_set(v___x_3527_, 1, v_coeffs_3509_);
lean_ctor_set(v___x_3527_, 2, v_i_3520_);
v_f_3528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3528_, 0, v_coeffs_3509_);
lean_ctor_set(v_f_3528_, 1, v___x_3526_);
lean_ctor_set(v_f_3528_, 2, v___x_3527_);
v_f_3529_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3507_, v_f_3528_);
v_f_3530_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3529_);
v___x_3531_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3523_, v_f_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(lean_object* v_x_3532_, lean_object* v_x_3533_){
_start:
{
if (lean_obj_tag(v_x_3533_) == 0)
{
return v_x_3532_;
}
else
{
lean_object* v_head_3534_; lean_object* v_snd_3535_; lean_object* v_tail_3536_; lean_object* v_fst_3537_; lean_object* v_fst_3538_; lean_object* v_snd_3539_; lean_object* v___x_3540_; 
v_head_3534_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_head_3534_);
v_snd_3535_ = lean_ctor_get(v_head_3534_, 1);
lean_inc(v_snd_3535_);
v_tail_3536_ = lean_ctor_get(v_x_3533_, 1);
lean_inc(v_tail_3536_);
lean_dec_ref_known(v_x_3533_, 2);
v_fst_3537_ = lean_ctor_get(v_head_3534_, 0);
lean_inc(v_fst_3537_);
lean_dec(v_head_3534_);
v_fst_3538_ = lean_ctor_get(v_snd_3535_, 0);
lean_inc(v_fst_3538_);
v_snd_3539_ = lean_ctor_get(v_snd_3535_, 1);
lean_inc(v_snd_3539_);
lean_dec(v_snd_3535_);
v___x_3540_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality(v_x_3532_, v_fst_3537_, v_fst_3538_, v_snd_3539_);
v_x_3532_ = v___x_3540_;
v_x_3533_ = v_tail_3536_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequalities(lean_object* v_p_3542_, lean_object* v_ineqs_3543_){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(v_p_3542_, v_ineqs_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(lean_object* v_x_3545_, lean_object* v_x_3546_){
_start:
{
if (lean_obj_tag(v_x_3546_) == 0)
{
return v_x_3545_;
}
else
{
lean_object* v_head_3547_; lean_object* v_snd_3548_; lean_object* v_tail_3549_; lean_object* v_fst_3550_; lean_object* v_fst_3551_; lean_object* v_snd_3552_; lean_object* v___x_3553_; 
v_head_3547_ = lean_ctor_get(v_x_3546_, 0);
lean_inc(v_head_3547_);
v_snd_3548_ = lean_ctor_get(v_head_3547_, 1);
lean_inc(v_snd_3548_);
v_tail_3549_ = lean_ctor_get(v_x_3546_, 1);
lean_inc(v_tail_3549_);
lean_dec_ref_known(v_x_3546_, 2);
v_fst_3550_ = lean_ctor_get(v_head_3547_, 0);
lean_inc(v_fst_3550_);
lean_dec(v_head_3547_);
v_fst_3551_ = lean_ctor_get(v_snd_3548_, 0);
lean_inc(v_fst_3551_);
v_snd_3552_ = lean_ctor_get(v_snd_3548_, 1);
lean_inc(v_snd_3552_);
lean_dec(v_snd_3548_);
v___x_3553_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality(v_x_3545_, v_fst_3550_, v_fst_3551_, v_snd_3552_);
v_x_3545_ = v___x_3553_;
v_x_3546_ = v_tail_3549_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEqualities(lean_object* v_p_3555_, lean_object* v_eqs_3556_){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(v_p_3555_, v_eqs_3556_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0(lean_object* v___x_3564_, lean_object* v_x_3565_){
_start:
{
lean_object* v_constraint_3566_; lean_object* v_coeffs_3567_; lean_object* v_lowerBound_3568_; lean_object* v_upperBound_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___y_3574_; lean_object* v___y_3575_; 
v_constraint_3566_ = lean_ctor_get(v_x_3565_, 1);
lean_inc_ref(v_constraint_3566_);
v_coeffs_3567_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_coeffs_3567_);
lean_dec_ref(v_x_3565_);
v_lowerBound_3568_ = lean_ctor_get(v_constraint_3566_, 0);
lean_inc(v_lowerBound_3568_);
v_upperBound_3569_ = lean_ctor_get(v_constraint_3566_, 1);
lean_inc(v_upperBound_3569_);
lean_dec_ref(v_constraint_3566_);
v___x_3570_ = l_List_toString___redArg(v___x_3564_, v_coeffs_3567_);
v___x_3571_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3572_ = lean_string_append(v___x_3570_, v___x_3571_);
if (lean_obj_tag(v_lowerBound_3568_) == 0)
{
if (lean_obj_tag(v_upperBound_3569_) == 0)
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3581_ = lean_string_append(v___x_3572_, v___x_3580_);
return v___x_3581_;
}
else
{
lean_object* v_val_3582_; lean_object* v___x_3583_; lean_object* v___y_3585_; lean_object* v_intZero_3590_; uint8_t v_isNeg_3591_; 
v_val_3582_ = lean_ctor_get(v_upperBound_3569_, 0);
lean_inc(v_val_3582_);
lean_dec_ref_known(v_upperBound_3569_, 1);
v___x_3583_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3590_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3591_ = lean_int_dec_lt(v_val_3582_, v_intZero_3590_);
if (v_isNeg_3591_ == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3593_; 
v_a_3592_ = lean_nat_abs(v_val_3582_);
lean_dec(v_val_3582_);
v___x_3593_ = l_Nat_reprFast(v_a_3592_);
v___y_3585_ = v___x_3593_;
goto v___jp_3584_;
}
else
{
lean_object* v_abs_3594_; lean_object* v_one_3595_; lean_object* v_a_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v_abs_3594_ = lean_nat_abs(v_val_3582_);
lean_dec(v_val_3582_);
v_one_3595_ = lean_unsigned_to_nat(1u);
v_a_3596_ = lean_nat_sub(v_abs_3594_, v_one_3595_);
lean_dec(v_abs_3594_);
v___x_3597_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3598_ = lean_nat_add(v_a_3596_, v_one_3595_);
lean_dec(v_a_3596_);
v___x_3599_ = l_Nat_reprFast(v___x_3598_);
v___x_3600_ = lean_string_append(v___x_3597_, v___x_3599_);
lean_dec_ref(v___x_3599_);
v___y_3585_ = v___x_3600_;
goto v___jp_3584_;
}
v___jp_3584_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3586_ = lean_string_append(v___x_3583_, v___y_3585_);
lean_dec_ref(v___y_3585_);
v___x_3587_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3588_ = lean_string_append(v___x_3586_, v___x_3587_);
v___x_3589_ = lean_string_append(v___x_3572_, v___x_3588_);
lean_dec_ref(v___x_3588_);
return v___x_3589_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3569_) == 0)
{
lean_object* v_val_3601_; lean_object* v___x_3602_; lean_object* v___y_3604_; lean_object* v_intZero_3609_; uint8_t v_isNeg_3610_; 
v_val_3601_ = lean_ctor_get(v_lowerBound_3568_, 0);
lean_inc(v_val_3601_);
lean_dec_ref_known(v_lowerBound_3568_, 1);
v___x_3602_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3609_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3610_ = lean_int_dec_lt(v_val_3601_, v_intZero_3609_);
if (v_isNeg_3610_ == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3612_; 
v_a_3611_ = lean_nat_abs(v_val_3601_);
lean_dec(v_val_3601_);
v___x_3612_ = l_Nat_reprFast(v_a_3611_);
v___y_3604_ = v___x_3612_;
goto v___jp_3603_;
}
else
{
lean_object* v_abs_3613_; lean_object* v_one_3614_; lean_object* v_a_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v_abs_3613_ = lean_nat_abs(v_val_3601_);
lean_dec(v_val_3601_);
v_one_3614_ = lean_unsigned_to_nat(1u);
v_a_3615_ = lean_nat_sub(v_abs_3613_, v_one_3614_);
lean_dec(v_abs_3613_);
v___x_3616_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3617_ = lean_nat_add(v_a_3615_, v_one_3614_);
lean_dec(v_a_3615_);
v___x_3618_ = l_Nat_reprFast(v___x_3617_);
v___x_3619_ = lean_string_append(v___x_3616_, v___x_3618_);
lean_dec_ref(v___x_3618_);
v___y_3604_ = v___x_3619_;
goto v___jp_3603_;
}
v___jp_3603_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3605_ = lean_string_append(v___x_3602_, v___y_3604_);
lean_dec_ref(v___y_3604_);
v___x_3606_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3607_ = lean_string_append(v___x_3605_, v___x_3606_);
v___x_3608_ = lean_string_append(v___x_3572_, v___x_3607_);
lean_dec_ref(v___x_3607_);
return v___x_3608_;
}
}
else
{
lean_object* v_val_3620_; lean_object* v_val_3621_; uint8_t v___x_3622_; 
v_val_3620_ = lean_ctor_get(v_lowerBound_3568_, 0);
lean_inc(v_val_3620_);
lean_dec_ref_known(v_lowerBound_3568_, 1);
v_val_3621_ = lean_ctor_get(v_upperBound_3569_, 0);
lean_inc(v_val_3621_);
lean_dec_ref_known(v_upperBound_3569_, 1);
v___x_3622_ = lean_int_dec_lt(v_val_3621_, v_val_3620_);
if (v___x_3622_ == 0)
{
uint8_t v___x_3623_; 
v___x_3623_ = lean_int_dec_eq(v_val_3620_, v_val_3621_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; lean_object* v___y_3626_; lean_object* v_intZero_3641_; uint8_t v_isNeg_3642_; 
v___x_3624_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3641_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3642_ = lean_int_dec_lt(v_val_3620_, v_intZero_3641_);
if (v_isNeg_3642_ == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3644_; 
v_a_3643_ = lean_nat_abs(v_val_3620_);
lean_dec(v_val_3620_);
v___x_3644_ = l_Nat_reprFast(v_a_3643_);
v___y_3626_ = v___x_3644_;
goto v___jp_3625_;
}
else
{
lean_object* v_abs_3645_; lean_object* v_one_3646_; lean_object* v_a_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v_abs_3645_ = lean_nat_abs(v_val_3620_);
lean_dec(v_val_3620_);
v_one_3646_ = lean_unsigned_to_nat(1u);
v_a_3647_ = lean_nat_sub(v_abs_3645_, v_one_3646_);
lean_dec(v_abs_3645_);
v___x_3648_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3649_ = lean_nat_add(v_a_3647_, v_one_3646_);
lean_dec(v_a_3647_);
v___x_3650_ = l_Nat_reprFast(v___x_3649_);
v___x_3651_ = lean_string_append(v___x_3648_, v___x_3650_);
lean_dec_ref(v___x_3650_);
v___y_3626_ = v___x_3651_;
goto v___jp_3625_;
}
v___jp_3625_:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v_intZero_3630_; uint8_t v_isNeg_3631_; 
v___x_3627_ = lean_string_append(v___x_3624_, v___y_3626_);
lean_dec_ref(v___y_3626_);
v___x_3628_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3629_ = lean_string_append(v___x_3627_, v___x_3628_);
v_intZero_3630_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3631_ = lean_int_dec_lt(v_val_3621_, v_intZero_3630_);
if (v_isNeg_3631_ == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3633_; 
v_a_3632_ = lean_nat_abs(v_val_3621_);
lean_dec(v_val_3621_);
v___x_3633_ = l_Nat_reprFast(v_a_3632_);
v___y_3574_ = v___x_3629_;
v___y_3575_ = v___x_3633_;
goto v___jp_3573_;
}
else
{
lean_object* v_abs_3634_; lean_object* v_one_3635_; lean_object* v_a_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v_abs_3634_ = lean_nat_abs(v_val_3621_);
lean_dec(v_val_3621_);
v_one_3635_ = lean_unsigned_to_nat(1u);
v_a_3636_ = lean_nat_sub(v_abs_3634_, v_one_3635_);
lean_dec(v_abs_3634_);
v___x_3637_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3638_ = lean_nat_add(v_a_3636_, v_one_3635_);
lean_dec(v_a_3636_);
v___x_3639_ = l_Nat_reprFast(v___x_3638_);
v___x_3640_ = lean_string_append(v___x_3637_, v___x_3639_);
lean_dec_ref(v___x_3639_);
v___y_3574_ = v___x_3629_;
v___y_3575_ = v___x_3640_;
goto v___jp_3573_;
}
}
}
else
{
lean_object* v___x_3652_; lean_object* v___y_3654_; lean_object* v_intZero_3659_; uint8_t v_isNeg_3660_; 
lean_dec(v_val_3621_);
v___x_3652_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3659_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3660_ = lean_int_dec_lt(v_val_3620_, v_intZero_3659_);
if (v_isNeg_3660_ == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3662_; 
v_a_3661_ = lean_nat_abs(v_val_3620_);
lean_dec(v_val_3620_);
v___x_3662_ = l_Nat_reprFast(v_a_3661_);
v___y_3654_ = v___x_3662_;
goto v___jp_3653_;
}
else
{
lean_object* v_abs_3663_; lean_object* v_one_3664_; lean_object* v_a_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v_abs_3663_ = lean_nat_abs(v_val_3620_);
lean_dec(v_val_3620_);
v_one_3664_ = lean_unsigned_to_nat(1u);
v_a_3665_ = lean_nat_sub(v_abs_3663_, v_one_3664_);
lean_dec(v_abs_3663_);
v___x_3666_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3667_ = lean_nat_add(v_a_3665_, v_one_3664_);
lean_dec(v_a_3665_);
v___x_3668_ = l_Nat_reprFast(v___x_3667_);
v___x_3669_ = lean_string_append(v___x_3666_, v___x_3668_);
lean_dec_ref(v___x_3668_);
v___y_3654_ = v___x_3669_;
goto v___jp_3653_;
}
v___jp_3653_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3655_ = lean_string_append(v___x_3652_, v___y_3654_);
lean_dec_ref(v___y_3654_);
v___x_3656_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3657_ = lean_string_append(v___x_3655_, v___x_3656_);
v___x_3658_ = lean_string_append(v___x_3572_, v___x_3657_);
lean_dec_ref(v___x_3657_);
return v___x_3658_;
}
}
}
else
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
lean_dec(v_val_3621_);
lean_dec(v_val_3620_);
v___x_3670_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3671_ = lean_string_append(v___x_3572_, v___x_3670_);
return v___x_3671_;
}
}
}
v___jp_3573_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3576_ = lean_string_append(v___y_3574_, v___y_3575_);
lean_dec_ref(v___y_3575_);
v___x_3577_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3578_ = lean_string_append(v___x_3576_, v___x_3577_);
v___x_3579_ = lean_string_append(v___x_3572_, v___x_3578_);
lean_dec_ref(v___x_3578_);
return v___x_3579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1(lean_object* v___x_3672_, lean_object* v_x_3673_){
_start:
{
lean_object* v_fst_3674_; lean_object* v_constraint_3675_; lean_object* v_coeffs_3676_; lean_object* v_lowerBound_3677_; lean_object* v_upperBound_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___y_3683_; lean_object* v___y_3684_; 
v_fst_3674_ = lean_ctor_get(v_x_3673_, 0);
lean_inc(v_fst_3674_);
lean_dec_ref(v_x_3673_);
v_constraint_3675_ = lean_ctor_get(v_fst_3674_, 1);
lean_inc_ref(v_constraint_3675_);
v_coeffs_3676_ = lean_ctor_get(v_fst_3674_, 0);
lean_inc(v_coeffs_3676_);
lean_dec(v_fst_3674_);
v_lowerBound_3677_ = lean_ctor_get(v_constraint_3675_, 0);
lean_inc(v_lowerBound_3677_);
v_upperBound_3678_ = lean_ctor_get(v_constraint_3675_, 1);
lean_inc(v_upperBound_3678_);
lean_dec_ref(v_constraint_3675_);
v___x_3679_ = l_List_toString___redArg(v___x_3672_, v_coeffs_3676_);
v___x_3680_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3681_ = lean_string_append(v___x_3679_, v___x_3680_);
if (lean_obj_tag(v_lowerBound_3677_) == 0)
{
if (lean_obj_tag(v_upperBound_3678_) == 0)
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3690_ = lean_string_append(v___x_3681_, v___x_3689_);
return v___x_3690_;
}
else
{
lean_object* v_val_3691_; lean_object* v___x_3692_; lean_object* v___y_3694_; lean_object* v_intZero_3699_; uint8_t v_isNeg_3700_; 
v_val_3691_ = lean_ctor_get(v_upperBound_3678_, 0);
lean_inc(v_val_3691_);
lean_dec_ref_known(v_upperBound_3678_, 1);
v___x_3692_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3699_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3700_ = lean_int_dec_lt(v_val_3691_, v_intZero_3699_);
if (v_isNeg_3700_ == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3702_; 
v_a_3701_ = lean_nat_abs(v_val_3691_);
lean_dec(v_val_3691_);
v___x_3702_ = l_Nat_reprFast(v_a_3701_);
v___y_3694_ = v___x_3702_;
goto v___jp_3693_;
}
else
{
lean_object* v_abs_3703_; lean_object* v_one_3704_; lean_object* v_a_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v_abs_3703_ = lean_nat_abs(v_val_3691_);
lean_dec(v_val_3691_);
v_one_3704_ = lean_unsigned_to_nat(1u);
v_a_3705_ = lean_nat_sub(v_abs_3703_, v_one_3704_);
lean_dec(v_abs_3703_);
v___x_3706_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3707_ = lean_nat_add(v_a_3705_, v_one_3704_);
lean_dec(v_a_3705_);
v___x_3708_ = l_Nat_reprFast(v___x_3707_);
v___x_3709_ = lean_string_append(v___x_3706_, v___x_3708_);
lean_dec_ref(v___x_3708_);
v___y_3694_ = v___x_3709_;
goto v___jp_3693_;
}
v___jp_3693_:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3695_ = lean_string_append(v___x_3692_, v___y_3694_);
lean_dec_ref(v___y_3694_);
v___x_3696_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3697_ = lean_string_append(v___x_3695_, v___x_3696_);
v___x_3698_ = lean_string_append(v___x_3681_, v___x_3697_);
lean_dec_ref(v___x_3697_);
return v___x_3698_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3678_) == 0)
{
lean_object* v_val_3710_; lean_object* v___x_3711_; lean_object* v___y_3713_; lean_object* v_intZero_3718_; uint8_t v_isNeg_3719_; 
v_val_3710_ = lean_ctor_get(v_lowerBound_3677_, 0);
lean_inc(v_val_3710_);
lean_dec_ref_known(v_lowerBound_3677_, 1);
v___x_3711_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3718_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3719_ = lean_int_dec_lt(v_val_3710_, v_intZero_3718_);
if (v_isNeg_3719_ == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3721_; 
v_a_3720_ = lean_nat_abs(v_val_3710_);
lean_dec(v_val_3710_);
v___x_3721_ = l_Nat_reprFast(v_a_3720_);
v___y_3713_ = v___x_3721_;
goto v___jp_3712_;
}
else
{
lean_object* v_abs_3722_; lean_object* v_one_3723_; lean_object* v_a_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v_abs_3722_ = lean_nat_abs(v_val_3710_);
lean_dec(v_val_3710_);
v_one_3723_ = lean_unsigned_to_nat(1u);
v_a_3724_ = lean_nat_sub(v_abs_3722_, v_one_3723_);
lean_dec(v_abs_3722_);
v___x_3725_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3726_ = lean_nat_add(v_a_3724_, v_one_3723_);
lean_dec(v_a_3724_);
v___x_3727_ = l_Nat_reprFast(v___x_3726_);
v___x_3728_ = lean_string_append(v___x_3725_, v___x_3727_);
lean_dec_ref(v___x_3727_);
v___y_3713_ = v___x_3728_;
goto v___jp_3712_;
}
v___jp_3712_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3714_ = lean_string_append(v___x_3711_, v___y_3713_);
lean_dec_ref(v___y_3713_);
v___x_3715_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3716_ = lean_string_append(v___x_3714_, v___x_3715_);
v___x_3717_ = lean_string_append(v___x_3681_, v___x_3716_);
lean_dec_ref(v___x_3716_);
return v___x_3717_;
}
}
else
{
lean_object* v_val_3729_; lean_object* v_val_3730_; uint8_t v___x_3731_; 
v_val_3729_ = lean_ctor_get(v_lowerBound_3677_, 0);
lean_inc(v_val_3729_);
lean_dec_ref_known(v_lowerBound_3677_, 1);
v_val_3730_ = lean_ctor_get(v_upperBound_3678_, 0);
lean_inc(v_val_3730_);
lean_dec_ref_known(v_upperBound_3678_, 1);
v___x_3731_ = lean_int_dec_lt(v_val_3730_, v_val_3729_);
if (v___x_3731_ == 0)
{
uint8_t v___x_3732_; 
v___x_3732_ = lean_int_dec_eq(v_val_3729_, v_val_3730_);
if (v___x_3732_ == 0)
{
lean_object* v___x_3733_; lean_object* v___y_3735_; lean_object* v_intZero_3750_; uint8_t v_isNeg_3751_; 
v___x_3733_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3750_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3751_ = lean_int_dec_lt(v_val_3729_, v_intZero_3750_);
if (v_isNeg_3751_ == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3753_; 
v_a_3752_ = lean_nat_abs(v_val_3729_);
lean_dec(v_val_3729_);
v___x_3753_ = l_Nat_reprFast(v_a_3752_);
v___y_3735_ = v___x_3753_;
goto v___jp_3734_;
}
else
{
lean_object* v_abs_3754_; lean_object* v_one_3755_; lean_object* v_a_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v_abs_3754_ = lean_nat_abs(v_val_3729_);
lean_dec(v_val_3729_);
v_one_3755_ = lean_unsigned_to_nat(1u);
v_a_3756_ = lean_nat_sub(v_abs_3754_, v_one_3755_);
lean_dec(v_abs_3754_);
v___x_3757_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3758_ = lean_nat_add(v_a_3756_, v_one_3755_);
lean_dec(v_a_3756_);
v___x_3759_ = l_Nat_reprFast(v___x_3758_);
v___x_3760_ = lean_string_append(v___x_3757_, v___x_3759_);
lean_dec_ref(v___x_3759_);
v___y_3735_ = v___x_3760_;
goto v___jp_3734_;
}
v___jp_3734_:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v_intZero_3739_; uint8_t v_isNeg_3740_; 
v___x_3736_ = lean_string_append(v___x_3733_, v___y_3735_);
lean_dec_ref(v___y_3735_);
v___x_3737_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3738_ = lean_string_append(v___x_3736_, v___x_3737_);
v_intZero_3739_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3740_ = lean_int_dec_lt(v_val_3730_, v_intZero_3739_);
if (v_isNeg_3740_ == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3742_; 
v_a_3741_ = lean_nat_abs(v_val_3730_);
lean_dec(v_val_3730_);
v___x_3742_ = l_Nat_reprFast(v_a_3741_);
v___y_3683_ = v___x_3738_;
v___y_3684_ = v___x_3742_;
goto v___jp_3682_;
}
else
{
lean_object* v_abs_3743_; lean_object* v_one_3744_; lean_object* v_a_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v_abs_3743_ = lean_nat_abs(v_val_3730_);
lean_dec(v_val_3730_);
v_one_3744_ = lean_unsigned_to_nat(1u);
v_a_3745_ = lean_nat_sub(v_abs_3743_, v_one_3744_);
lean_dec(v_abs_3743_);
v___x_3746_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3747_ = lean_nat_add(v_a_3745_, v_one_3744_);
lean_dec(v_a_3745_);
v___x_3748_ = l_Nat_reprFast(v___x_3747_);
v___x_3749_ = lean_string_append(v___x_3746_, v___x_3748_);
lean_dec_ref(v___x_3748_);
v___y_3683_ = v___x_3738_;
v___y_3684_ = v___x_3749_;
goto v___jp_3682_;
}
}
}
else
{
lean_object* v___x_3761_; lean_object* v___y_3763_; lean_object* v_intZero_3768_; uint8_t v_isNeg_3769_; 
lean_dec(v_val_3730_);
v___x_3761_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3768_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3769_ = lean_int_dec_lt(v_val_3729_, v_intZero_3768_);
if (v_isNeg_3769_ == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3771_; 
v_a_3770_ = lean_nat_abs(v_val_3729_);
lean_dec(v_val_3729_);
v___x_3771_ = l_Nat_reprFast(v_a_3770_);
v___y_3763_ = v___x_3771_;
goto v___jp_3762_;
}
else
{
lean_object* v_abs_3772_; lean_object* v_one_3773_; lean_object* v_a_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v_abs_3772_ = lean_nat_abs(v_val_3729_);
lean_dec(v_val_3729_);
v_one_3773_ = lean_unsigned_to_nat(1u);
v_a_3774_ = lean_nat_sub(v_abs_3772_, v_one_3773_);
lean_dec(v_abs_3772_);
v___x_3775_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3776_ = lean_nat_add(v_a_3774_, v_one_3773_);
lean_dec(v_a_3774_);
v___x_3777_ = l_Nat_reprFast(v___x_3776_);
v___x_3778_ = lean_string_append(v___x_3775_, v___x_3777_);
lean_dec_ref(v___x_3777_);
v___y_3763_ = v___x_3778_;
goto v___jp_3762_;
}
v___jp_3762_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3764_ = lean_string_append(v___x_3761_, v___y_3763_);
lean_dec_ref(v___y_3763_);
v___x_3765_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3766_ = lean_string_append(v___x_3764_, v___x_3765_);
v___x_3767_ = lean_string_append(v___x_3681_, v___x_3766_);
lean_dec_ref(v___x_3766_);
return v___x_3767_;
}
}
}
else
{
lean_object* v___x_3779_; lean_object* v___x_3780_; 
lean_dec(v_val_3730_);
lean_dec(v_val_3729_);
v___x_3779_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3780_ = lean_string_append(v___x_3681_, v___x_3779_);
return v___x_3780_;
}
}
}
v___jp_3682_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3685_ = lean_string_append(v___y_3683_, v___y_3684_);
lean_dec_ref(v___y_3684_);
v___x_3686_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3687_ = lean_string_append(v___x_3685_, v___x_3686_);
v___x_3688_ = lean_string_append(v___x_3681_, v___x_3687_);
lean_dec_ref(v___x_3687_);
return v___x_3688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2(lean_object* v___f_3785_, lean_object* v___f_3786_, lean_object* v___f_3787_, lean_object* v_d_3788_){
_start:
{
lean_object* v_var_3789_; lean_object* v_irrelevant_3790_; lean_object* v_lowerBounds_3791_; lean_object* v_upperBounds_3792_; lean_object* v___x_3793_; lean_object* v_irrelevant_3794_; lean_object* v_lowerBounds_3795_; lean_object* v_upperBounds_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v_var_3789_ = lean_ctor_get(v_d_3788_, 0);
lean_inc(v_var_3789_);
v_irrelevant_3790_ = lean_ctor_get(v_d_3788_, 1);
lean_inc(v_irrelevant_3790_);
v_lowerBounds_3791_ = lean_ctor_get(v_d_3788_, 2);
lean_inc(v_lowerBounds_3791_);
v_upperBounds_3792_ = lean_ctor_get(v_d_3788_, 3);
lean_inc(v_upperBounds_3792_);
lean_dec_ref(v_d_3788_);
v___x_3793_ = lean_box(0);
v_irrelevant_3794_ = l_List_mapTR_loop___redArg(v___f_3785_, v_irrelevant_3790_, v___x_3793_);
lean_inc_ref(v___f_3786_);
v_lowerBounds_3795_ = l_List_mapTR_loop___redArg(v___f_3786_, v_lowerBounds_3791_, v___x_3793_);
v_upperBounds_3796_ = l_List_mapTR_loop___redArg(v___f_3786_, v_upperBounds_3792_, v___x_3793_);
v___x_3797_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0));
v___x_3798_ = l_Nat_reprFast(v_var_3789_);
v___x_3799_ = lean_string_append(v___x_3797_, v___x_3798_);
lean_dec_ref(v___x_3798_);
v___x_3800_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_3801_ = lean_string_append(v___x_3799_, v___x_3800_);
v___x_3802_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1));
lean_inc_ref_n(v___f_3787_, 2);
v___x_3803_ = l_List_toString___redArg(v___f_3787_, v_irrelevant_3794_);
v___x_3804_ = lean_string_append(v___x_3802_, v___x_3803_);
lean_dec_ref(v___x_3803_);
v___x_3805_ = lean_string_append(v___x_3804_, v___x_3800_);
v___x_3806_ = lean_string_append(v___x_3801_, v___x_3805_);
lean_dec_ref(v___x_3805_);
v___x_3807_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2));
v___x_3808_ = l_List_toString___redArg(v___f_3787_, v_lowerBounds_3795_);
v___x_3809_ = lean_string_append(v___x_3807_, v___x_3808_);
lean_dec_ref(v___x_3808_);
v___x_3810_ = lean_string_append(v___x_3809_, v___x_3800_);
v___x_3811_ = lean_string_append(v___x_3806_, v___x_3810_);
lean_dec_ref(v___x_3810_);
v___x_3812_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3));
v___x_3813_ = l_List_toString___redArg(v___f_3787_, v_upperBounds_3796_);
v___x_3814_ = lean_string_append(v___x_3812_, v___x_3813_);
lean_dec_ref(v___x_3813_);
v___x_3815_ = lean_string_append(v___x_3811_, v___x_3814_);
lean_dec_ref(v___x_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(lean_object* v_d_3826_){
_start:
{
lean_object* v_lowerBounds_3827_; lean_object* v_upperBounds_3828_; uint8_t v___x_3829_; 
v_lowerBounds_3827_ = lean_ctor_get(v_d_3826_, 2);
v_upperBounds_3828_ = lean_ctor_get(v_d_3826_, 3);
v___x_3829_ = l_List_isEmpty___redArg(v_lowerBounds_3827_);
if (v___x_3829_ == 0)
{
return v___x_3829_;
}
else
{
uint8_t v___x_3830_; 
v___x_3830_ = l_List_isEmpty___redArg(v_upperBounds_3828_);
return v___x_3830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty___boxed(lean_object* v_d_3831_){
_start:
{
uint8_t v_res_3832_; lean_object* v_r_3833_; 
v_res_3832_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v_d_3831_);
lean_dec_ref(v_d_3831_);
v_r_3833_ = lean_box(v_res_3832_);
return v_r_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(lean_object* v_d_3834_){
_start:
{
lean_object* v_lowerBounds_3835_; lean_object* v_upperBounds_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v_lowerBounds_3835_ = lean_ctor_get(v_d_3834_, 2);
v_upperBounds_3836_ = lean_ctor_get(v_d_3834_, 3);
v___x_3837_ = l_List_lengthTR___redArg(v_lowerBounds_3835_);
v___x_3838_ = l_List_lengthTR___redArg(v_upperBounds_3836_);
v___x_3839_ = lean_nat_mul(v___x_3837_, v___x_3838_);
lean_dec(v___x_3838_);
lean_dec(v___x_3837_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size___boxed(lean_object* v_d_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_d_3840_);
lean_dec_ref(v_d_3840_);
return v_res_3841_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(lean_object* v_d_3842_){
_start:
{
uint8_t v_lowerExact_3843_; 
v_lowerExact_3843_ = lean_ctor_get_uint8(v_d_3842_, sizeof(void*)*4);
if (v_lowerExact_3843_ == 0)
{
uint8_t v_upperExact_3844_; 
v_upperExact_3844_ = lean_ctor_get_uint8(v_d_3842_, sizeof(void*)*4 + 1);
return v_upperExact_3844_;
}
else
{
return v_lowerExact_3843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact___boxed(lean_object* v_d_3845_){
_start:
{
uint8_t v_res_3846_; lean_object* v_r_3847_; 
v_res_3846_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_d_3845_);
lean_dec_ref(v_d_3845_);
v_r_3847_ = lean_box(v_res_3846_);
return v_r_3847_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(lean_object* v_x_3848_, lean_object* v_x_3849_){
_start:
{
if (lean_obj_tag(v_x_3849_) == 0)
{
return v_x_3848_;
}
else
{
lean_object* v_head_3850_; lean_object* v_tail_3851_; lean_object* v___x_3852_; uint8_t v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v_head_3850_ = lean_ctor_get(v_x_3849_, 0);
v_tail_3851_ = lean_ctor_get(v_x_3849_, 1);
v___x_3852_ = lean_box(0);
v___x_3853_ = 1;
lean_inc(v_head_3850_);
v___x_3854_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3854_, 0, v_head_3850_);
lean_ctor_set(v___x_3854_, 1, v___x_3852_);
lean_ctor_set(v___x_3854_, 2, v___x_3852_);
lean_ctor_set(v___x_3854_, 3, v___x_3852_);
lean_ctor_set_uint8(v___x_3854_, sizeof(void*)*4, v___x_3853_);
lean_ctor_set_uint8(v___x_3854_, sizeof(void*)*4 + 1, v___x_3853_);
v___x_3855_ = lean_array_push(v_x_3848_, v___x_3854_);
v_x_3848_ = v___x_3855_;
v_x_3849_ = v_tail_3851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2___boxed(lean_object* v_x_3857_, lean_object* v_x_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v_x_3857_, v_x_3858_);
lean_dec(v_x_3858_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object* v___x_3860_, lean_object* v_b_3861_, lean_object* v___x_3862_, lean_object* v_____r_3863_, lean_object* v_d_x27_3864_){
_start:
{
lean_object* v_upperBound_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3892_; 
v_upperBound_3865_ = lean_ctor_get(v___x_3860_, 1);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3892_ == 0)
{
lean_object* v_unused_3893_; 
v_unused_3893_ = lean_ctor_get(v___x_3860_, 0);
lean_dec(v_unused_3893_);
v___x_3867_ = v___x_3860_;
v_isShared_3868_ = v_isSharedCheck_3892_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_upperBound_3865_);
lean_dec(v___x_3860_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3892_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
if (lean_obj_tag(v_upperBound_3865_) == 0)
{
lean_del_object(v___x_3867_);
lean_dec(v___x_3862_);
lean_dec_ref(v_b_3861_);
return v_d_x27_3864_;
}
else
{
lean_object* v_var_3869_; lean_object* v_irrelevant_3870_; lean_object* v_lowerBounds_3871_; lean_object* v_upperBounds_3872_; uint8_t v_lowerExact_3873_; uint8_t v_upperExact_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3891_; 
lean_dec_ref_known(v_upperBound_3865_, 1);
v_var_3869_ = lean_ctor_get(v_d_x27_3864_, 0);
v_irrelevant_3870_ = lean_ctor_get(v_d_x27_3864_, 1);
v_lowerBounds_3871_ = lean_ctor_get(v_d_x27_3864_, 2);
v_upperBounds_3872_ = lean_ctor_get(v_d_x27_3864_, 3);
v_lowerExact_3873_ = lean_ctor_get_uint8(v_d_x27_3864_, sizeof(void*)*4);
v_upperExact_3874_ = lean_ctor_get_uint8(v_d_x27_3864_, sizeof(void*)*4 + 1);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_d_x27_3864_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3876_ = v_d_x27_3864_;
v_isShared_3877_ = v_isSharedCheck_3891_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_upperBounds_3872_);
lean_inc(v_lowerBounds_3871_);
lean_inc(v_irrelevant_3870_);
lean_inc(v_var_3869_);
lean_dec(v_d_x27_3864_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3891_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
lean_inc(v___x_3862_);
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 1, v___x_3862_);
lean_ctor_set(v___x_3867_, 0, v_b_3861_);
v___x_3879_ = v___x_3867_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_b_3861_);
lean_ctor_set(v_reuseFailAlloc_3890_, 1, v___x_3862_);
v___x_3879_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
lean_object* v___x_3880_; 
v___x_3880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
lean_ctor_set(v___x_3880_, 1, v_upperBounds_3872_);
if (v_upperExact_3874_ == 0)
{
lean_object* v___x_3882_; 
lean_dec(v___x_3862_);
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 3, v___x_3880_);
v___x_3882_ = v___x_3876_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_var_3869_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v_irrelevant_3870_);
lean_ctor_set(v_reuseFailAlloc_3883_, 2, v_lowerBounds_3871_);
lean_ctor_set(v_reuseFailAlloc_3883_, 3, v___x_3880_);
lean_ctor_set_uint8(v_reuseFailAlloc_3883_, sizeof(void*)*4, v_lowerExact_3873_);
lean_ctor_set_uint8(v_reuseFailAlloc_3883_, sizeof(void*)*4 + 1, v_upperExact_3874_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
else
{
lean_object* v___x_3884_; lean_object* v___x_3885_; uint8_t v___x_3886_; lean_object* v___x_3888_; 
v___x_3884_ = lean_nat_abs(v___x_3862_);
lean_dec(v___x_3862_);
v___x_3885_ = lean_unsigned_to_nat(1u);
v___x_3886_ = lean_nat_dec_eq(v___x_3884_, v___x_3885_);
lean_dec(v___x_3884_);
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 3, v___x_3880_);
v___x_3888_ = v___x_3876_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_var_3869_);
lean_ctor_set(v_reuseFailAlloc_3889_, 1, v_irrelevant_3870_);
lean_ctor_set(v_reuseFailAlloc_3889_, 2, v_lowerBounds_3871_);
lean_ctor_set(v_reuseFailAlloc_3889_, 3, v___x_3880_);
lean_ctor_set_uint8(v_reuseFailAlloc_3889_, sizeof(void*)*4, v_lowerExact_3873_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_ctor_set_uint8(v___x_3888_, sizeof(void*)*4 + 1, v___x_3886_);
return v___x_3888_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(lean_object* v_upperBound_3894_, lean_object* v_coeffs_3895_, lean_object* v_constraint_3896_, lean_object* v_b_3897_, lean_object* v_a_3898_, lean_object* v_b_3899_){
_start:
{
lean_object* v_a_3901_; uint8_t v___x_3905_; 
v___x_3905_ = lean_nat_dec_lt(v_a_3898_, v_upperBound_3894_);
if (v___x_3905_ == 0)
{
lean_dec(v_a_3898_);
lean_dec_ref(v_b_3897_);
lean_dec_ref(v_constraint_3896_);
return v_b_3899_;
}
else
{
lean_object* v___x_3906_; uint8_t v___x_3907_; 
v___x_3906_ = lean_array_get_size(v_b_3899_);
v___x_3907_ = lean_nat_dec_lt(v_a_3898_, v___x_3906_);
if (v___x_3907_ == 0)
{
v_a_3901_ = v_b_3899_;
goto v___jp_3900_;
}
else
{
lean_object* v___x_3908_; lean_object* v_v_3909_; lean_object* v___x_3910_; lean_object* v_xs_x27_3911_; lean_object* v___y_3913_; lean_object* v___x_3915_; uint8_t v___x_3916_; 
lean_inc(v_a_3898_);
v___x_3908_ = l_Lean_Omega_IntList_get(v_coeffs_3895_, v_a_3898_);
v_v_3909_ = lean_array_fget(v_b_3899_, v_a_3898_);
v___x_3910_ = lean_box(0);
v_xs_x27_3911_ = lean_array_fset(v_b_3899_, v_a_3898_, v___x_3910_);
v___x_3915_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3916_ = lean_int_dec_eq(v___x_3908_, v___x_3915_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v_lowerBound_3918_; 
lean_inc_ref(v_constraint_3896_);
lean_inc(v___x_3908_);
v___x_3917_ = l_Lean_Omega_Constraint_scale(v___x_3908_, v_constraint_3896_);
v_lowerBound_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_lowerBound_3918_);
if (lean_obj_tag(v_lowerBound_3918_) == 0)
{
lean_object* v___x_3919_; 
lean_inc_ref(v_b_3897_);
v___x_3919_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3917_, v_b_3897_, v___x_3908_, v___x_3910_, v_v_3909_);
v___y_3913_ = v___x_3919_;
goto v___jp_3912_;
}
else
{
lean_object* v_var_3920_; lean_object* v_irrelevant_3921_; lean_object* v_lowerBounds_3922_; lean_object* v_upperBounds_3923_; uint8_t v_lowerExact_3924_; uint8_t v_upperExact_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3940_; 
lean_dec_ref_known(v_lowerBound_3918_, 1);
v_var_3920_ = lean_ctor_get(v_v_3909_, 0);
v_irrelevant_3921_ = lean_ctor_get(v_v_3909_, 1);
v_lowerBounds_3922_ = lean_ctor_get(v_v_3909_, 2);
v_upperBounds_3923_ = lean_ctor_get(v_v_3909_, 3);
v_lowerExact_3924_ = lean_ctor_get_uint8(v_v_3909_, sizeof(void*)*4);
v_upperExact_3925_ = lean_ctor_get_uint8(v_v_3909_, sizeof(void*)*4 + 1);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_v_3909_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3927_ = v_v_3909_;
v_isShared_3928_ = v_isSharedCheck_3940_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_upperBounds_3923_);
lean_inc(v_lowerBounds_3922_);
lean_inc(v_irrelevant_3921_);
lean_inc(v_var_3920_);
lean_dec(v_v_3909_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3940_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; uint8_t v___y_3932_; 
lean_inc(v___x_3908_);
lean_inc_ref(v_b_3897_);
v___x_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3929_, 0, v_b_3897_);
lean_ctor_set(v___x_3929_, 1, v___x_3908_);
v___x_3930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
lean_ctor_set(v___x_3930_, 1, v_lowerBounds_3922_);
if (v_lowerExact_3924_ == 0)
{
v___y_3932_ = v_lowerExact_3924_;
goto v___jp_3931_;
}
else
{
lean_object* v___x_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
v___x_3937_ = lean_nat_abs(v___x_3908_);
v___x_3938_ = lean_unsigned_to_nat(1u);
v___x_3939_ = lean_nat_dec_eq(v___x_3937_, v___x_3938_);
lean_dec(v___x_3937_);
v___y_3932_ = v___x_3939_;
goto v___jp_3931_;
}
v___jp_3931_:
{
lean_object* v___x_3934_; 
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 2, v___x_3930_);
v___x_3934_ = v___x_3927_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_var_3920_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_irrelevant_3921_);
lean_ctor_set(v_reuseFailAlloc_3936_, 2, v___x_3930_);
lean_ctor_set(v_reuseFailAlloc_3936_, 3, v_upperBounds_3923_);
lean_ctor_set_uint8(v_reuseFailAlloc_3936_, sizeof(void*)*4 + 1, v_upperExact_3925_);
v___x_3934_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3935_; 
lean_ctor_set_uint8(v___x_3934_, sizeof(void*)*4, v___y_3932_);
lean_inc_ref(v_b_3897_);
v___x_3935_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3917_, v_b_3897_, v___x_3908_, v___x_3910_, v___x_3934_);
v___y_3913_ = v___x_3935_;
goto v___jp_3912_;
}
}
}
}
}
else
{
lean_object* v_var_3941_; lean_object* v_irrelevant_3942_; lean_object* v_lowerBounds_3943_; lean_object* v_upperBounds_3944_; uint8_t v_lowerExact_3945_; uint8_t v_upperExact_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3954_; 
lean_dec(v___x_3908_);
v_var_3941_ = lean_ctor_get(v_v_3909_, 0);
v_irrelevant_3942_ = lean_ctor_get(v_v_3909_, 1);
v_lowerBounds_3943_ = lean_ctor_get(v_v_3909_, 2);
v_upperBounds_3944_ = lean_ctor_get(v_v_3909_, 3);
v_lowerExact_3945_ = lean_ctor_get_uint8(v_v_3909_, sizeof(void*)*4);
v_upperExact_3946_ = lean_ctor_get_uint8(v_v_3909_, sizeof(void*)*4 + 1);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_v_3909_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3948_ = v_v_3909_;
v_isShared_3949_ = v_isSharedCheck_3954_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_upperBounds_3944_);
lean_inc(v_lowerBounds_3943_);
lean_inc(v_irrelevant_3942_);
lean_inc(v_var_3941_);
lean_dec(v_v_3909_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3954_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3950_; lean_object* v___x_3952_; 
lean_inc_ref(v_b_3897_);
v___x_3950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3950_, 0, v_b_3897_);
lean_ctor_set(v___x_3950_, 1, v_irrelevant_3942_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v___x_3950_);
v___x_3952_ = v___x_3948_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_var_3941_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v___x_3950_);
lean_ctor_set(v_reuseFailAlloc_3953_, 2, v_lowerBounds_3943_);
lean_ctor_set(v_reuseFailAlloc_3953_, 3, v_upperBounds_3944_);
lean_ctor_set_uint8(v_reuseFailAlloc_3953_, sizeof(void*)*4, v_lowerExact_3945_);
lean_ctor_set_uint8(v_reuseFailAlloc_3953_, sizeof(void*)*4 + 1, v_upperExact_3946_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
v___y_3913_ = v___x_3952_;
goto v___jp_3912_;
}
}
}
v___jp_3912_:
{
lean_object* v___x_3914_; 
v___x_3914_ = lean_array_fset(v_xs_x27_3911_, v_a_3898_, v___y_3913_);
v_a_3901_ = v___x_3914_;
goto v___jp_3900_;
}
}
}
v___jp_3900_:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = lean_unsigned_to_nat(1u);
v___x_3903_ = lean_nat_add(v_a_3898_, v___x_3902_);
lean_dec(v_a_3898_);
v_a_3898_ = v___x_3903_;
v_b_3899_ = v_a_3901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___boxed(lean_object* v_upperBound_3955_, lean_object* v_coeffs_3956_, lean_object* v_constraint_3957_, lean_object* v_b_3958_, lean_object* v_a_3959_, lean_object* v_b_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3955_, v_coeffs_3956_, v_constraint_3957_, v_b_3958_, v_a_3959_, v_b_3960_);
lean_dec(v_coeffs_3956_);
lean_dec(v_upperBound_3955_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(lean_object* v_n_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
if (lean_obj_tag(v_a_3963_) == 0)
{
lean_object* v___x_3965_; 
v___x_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3965_, 0, v_a_3964_);
return v___x_3965_;
}
else
{
lean_object* v_value_3966_; lean_object* v_tail_3967_; lean_object* v_coeffs_3968_; lean_object* v_constraint_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v_value_3966_ = lean_ctor_get(v_a_3963_, 1);
lean_inc(v_value_3966_);
v_tail_3967_ = lean_ctor_get(v_a_3963_, 2);
lean_inc(v_tail_3967_);
lean_dec_ref_known(v_a_3963_, 3);
v_coeffs_3968_ = lean_ctor_get(v_value_3966_, 0);
lean_inc(v_coeffs_3968_);
v_constraint_3969_ = lean_ctor_get(v_value_3966_, 1);
lean_inc_ref(v_constraint_3969_);
v___x_3970_ = lean_unsigned_to_nat(0u);
v___x_3971_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_n_3962_, v_coeffs_3968_, v_constraint_3969_, v_value_3966_, v___x_3970_, v_a_3964_);
lean_dec(v_coeffs_3968_);
v_a_3963_ = v_tail_3967_;
v_a_3964_ = v___x_3971_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1___boxed(lean_object* v_n_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3973_, v_a_3974_, v_a_3975_);
lean_dec(v_n_3973_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(lean_object* v_n_3977_, lean_object* v_as_3978_, size_t v_sz_3979_, size_t v_i_3980_, lean_object* v_b_3981_){
_start:
{
uint8_t v___x_3982_; 
v___x_3982_ = lean_usize_dec_lt(v_i_3980_, v_sz_3979_);
if (v___x_3982_ == 0)
{
return v_b_3981_;
}
else
{
lean_object* v_a_3983_; lean_object* v___x_3984_; 
v_a_3983_ = lean_array_uget_borrowed(v_as_3978_, v_i_3980_);
lean_inc(v_a_3983_);
v___x_3984_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3977_, v_a_3983_, v_b_3981_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref_known(v___x_3984_, 1);
return v_a_3985_;
}
else
{
lean_object* v_a_3986_; size_t v___x_3987_; size_t v___x_3988_; 
v_a_3986_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3986_);
lean_dec_ref_known(v___x_3984_, 1);
v___x_3987_ = ((size_t)1ULL);
v___x_3988_ = lean_usize_add(v_i_3980_, v___x_3987_);
v_i_3980_ = v___x_3988_;
v_b_3981_ = v_a_3986_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3___boxed(lean_object* v_n_3990_, lean_object* v_as_3991_, lean_object* v_sz_3992_, lean_object* v_i_3993_, lean_object* v_b_3994_){
_start:
{
size_t v_sz_boxed_3995_; size_t v_i_boxed_3996_; lean_object* v_res_3997_; 
v_sz_boxed_3995_ = lean_unbox_usize(v_sz_3992_);
lean_dec(v_sz_3992_);
v_i_boxed_3996_ = lean_unbox_usize(v_i_3993_);
lean_dec(v_i_3993_);
v_res_3997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_n_3990_, v_as_3991_, v_sz_boxed_3995_, v_i_boxed_3996_, v_b_3994_);
lean_dec_ref(v_as_3991_);
lean_dec(v_n_3990_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(lean_object* v_p_4000_){
_start:
{
lean_object* v_constraints_4001_; lean_object* v_numVars_4002_; lean_object* v_buckets_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v_data_4006_; size_t v_sz_4007_; size_t v___x_4008_; lean_object* v___x_4009_; 
v_constraints_4001_ = lean_ctor_get(v_p_4000_, 2);
lean_inc_ref(v_constraints_4001_);
v_numVars_4002_ = lean_ctor_get(v_p_4000_, 1);
lean_inc_n(v_numVars_4002_, 2);
lean_dec_ref(v_p_4000_);
v_buckets_4003_ = lean_ctor_get(v_constraints_4001_, 1);
lean_inc_ref(v_buckets_4003_);
lean_dec_ref(v_constraints_4001_);
v___x_4004_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_4005_ = l_List_range(v_numVars_4002_);
v_data_4006_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v___x_4004_, v___x_4005_);
lean_dec(v___x_4005_);
v_sz_4007_ = lean_array_size(v_buckets_4003_);
v___x_4008_ = ((size_t)0ULL);
v___x_4009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_numVars_4002_, v_buckets_4003_, v_sz_4007_, v___x_4008_, v_data_4006_);
lean_dec_ref(v_buckets_4003_);
lean_dec(v_numVars_4002_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(lean_object* v_upperBound_4010_, lean_object* v_coeffs_4011_, lean_object* v_constraint_4012_, lean_object* v_b_4013_, lean_object* v_inst_4014_, lean_object* v_R_4015_, lean_object* v_a_4016_, lean_object* v_b_4017_, lean_object* v_c_4018_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_4010_, v_coeffs_4011_, v_constraint_4012_, v_b_4013_, v_a_4016_, v_b_4017_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___boxed(lean_object* v_upperBound_4020_, lean_object* v_coeffs_4021_, lean_object* v_constraint_4022_, lean_object* v_b_4023_, lean_object* v_inst_4024_, lean_object* v_R_4025_, lean_object* v_a_4026_, lean_object* v_b_4027_, lean_object* v_c_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(v_upperBound_4020_, v_coeffs_4021_, v_constraint_4022_, v_b_4023_, v_inst_4024_, v_R_4025_, v_a_4026_, v_b_4027_, v_c_4028_);
lean_dec(v_coeffs_4021_);
lean_dec(v_upperBound_4020_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(lean_object* v_cls_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_options_4039_; uint8_t v_hasTrace_4040_; 
v_options_4039_ = lean_ctor_get(v___y_4036_, 2);
v_hasTrace_4040_ = lean_ctor_get_uint8(v_options_4039_, sizeof(void*)*1);
if (v_hasTrace_4040_ == 0)
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_dec(v_cls_4033_);
v___x_4041_ = lean_box(v_hasTrace_4040_);
v___x_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
return v___x_4042_;
}
else
{
lean_object* v_inheritedTraceOptions_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v_inheritedTraceOptions_4043_ = lean_ctor_get(v___y_4036_, 13);
v___x_4044_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4045_ = l_Lean_Name_append(v___x_4044_, v_cls_4033_);
v___x_4046_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4043_, v_options_4039_, v___x_4045_);
lean_dec(v___x_4045_);
v___x_4047_ = lean_box(v___x_4046_);
v___x_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
return v___x_4048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___boxed(lean_object* v_cls_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(lean_object* v___x_4056_, lean_object* v_fst_4057_, lean_object* v_snd_4058_, lean_object* v_fst_4059_, lean_object* v_____r_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4056_);
v___x_4067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4067_, 0, v_fst_4057_);
lean_ctor_set(v___x_4067_, 1, v_snd_4058_);
v___x_4068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4068_, 0, v_fst_4059_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
v___x_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4066_);
lean_ctor_set(v___x_4069_, 1, v___x_4068_);
v___x_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4069_);
v___x_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0___boxed(lean_object* v___x_4072_, lean_object* v_fst_4073_, lean_object* v_snd_4074_, lean_object* v_fst_4075_, lean_object* v_____r_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4072_, v_fst_4073_, v_snd_4074_, v_fst_4075_, v_____r_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
return v_res_4082_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4083_; double v___x_4084_; 
v___x_4083_ = lean_unsigned_to_nat(0u);
v___x_4084_ = lean_float_of_nat(v___x_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(lean_object* v_cls_4087_, lean_object* v_msg_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v_ref_4094_; lean_object* v___x_4095_; lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4140_; 
v_ref_4094_ = lean_ctor_get(v___y_4091_, 5);
v___x_4095_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4098_ = v___x_4095_;
v_isShared_4099_ = v_isSharedCheck_4140_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4095_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4140_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4100_; lean_object* v_traceState_4101_; lean_object* v_env_4102_; lean_object* v_nextMacroScope_4103_; lean_object* v_ngen_4104_; lean_object* v_auxDeclNGen_4105_; lean_object* v_cache_4106_; lean_object* v_messages_4107_; lean_object* v_infoState_4108_; lean_object* v_snapshotTasks_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4139_; 
v___x_4100_ = lean_st_ref_take(v___y_4092_);
v_traceState_4101_ = lean_ctor_get(v___x_4100_, 4);
v_env_4102_ = lean_ctor_get(v___x_4100_, 0);
v_nextMacroScope_4103_ = lean_ctor_get(v___x_4100_, 1);
v_ngen_4104_ = lean_ctor_get(v___x_4100_, 2);
v_auxDeclNGen_4105_ = lean_ctor_get(v___x_4100_, 3);
v_cache_4106_ = lean_ctor_get(v___x_4100_, 5);
v_messages_4107_ = lean_ctor_get(v___x_4100_, 6);
v_infoState_4108_ = lean_ctor_get(v___x_4100_, 7);
v_snapshotTasks_4109_ = lean_ctor_get(v___x_4100_, 8);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4111_ = v___x_4100_;
v_isShared_4112_ = v_isSharedCheck_4139_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_snapshotTasks_4109_);
lean_inc(v_infoState_4108_);
lean_inc(v_messages_4107_);
lean_inc(v_cache_4106_);
lean_inc(v_traceState_4101_);
lean_inc(v_auxDeclNGen_4105_);
lean_inc(v_ngen_4104_);
lean_inc(v_nextMacroScope_4103_);
lean_inc(v_env_4102_);
lean_dec(v___x_4100_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4139_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
uint64_t v_tid_4113_; lean_object* v_traces_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4138_; 
v_tid_4113_ = lean_ctor_get_uint64(v_traceState_4101_, sizeof(void*)*1);
v_traces_4114_ = lean_ctor_get(v_traceState_4101_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v_traceState_4101_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4116_ = v_traceState_4101_;
v_isShared_4117_ = v_isSharedCheck_4138_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_traces_4114_);
lean_dec(v_traceState_4101_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4138_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4118_; double v___x_4119_; uint8_t v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4128_; 
v___x_4118_ = lean_box(0);
v___x_4119_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4120_ = 0;
v___x_4121_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4122_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4122_, 0, v_cls_4087_);
lean_ctor_set(v___x_4122_, 1, v___x_4118_);
lean_ctor_set(v___x_4122_, 2, v___x_4121_);
lean_ctor_set_float(v___x_4122_, sizeof(void*)*3, v___x_4119_);
lean_ctor_set_float(v___x_4122_, sizeof(void*)*3 + 8, v___x_4119_);
lean_ctor_set_uint8(v___x_4122_, sizeof(void*)*3 + 16, v___x_4120_);
v___x_4123_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4124_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4122_);
lean_ctor_set(v___x_4124_, 1, v_a_4096_);
lean_ctor_set(v___x_4124_, 2, v___x_4123_);
lean_inc(v_ref_4094_);
v___x_4125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4125_, 0, v_ref_4094_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = l_Lean_PersistentArray_push___redArg(v_traces_4114_, v___x_4125_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 0, v___x_4126_);
v___x_4128_ = v___x_4116_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4126_);
lean_ctor_set_uint64(v_reuseFailAlloc_4137_, sizeof(void*)*1, v_tid_4113_);
v___x_4128_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
lean_object* v___x_4130_; 
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 4, v___x_4128_);
v___x_4130_ = v___x_4111_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_env_4102_);
lean_ctor_set(v_reuseFailAlloc_4136_, 1, v_nextMacroScope_4103_);
lean_ctor_set(v_reuseFailAlloc_4136_, 2, v_ngen_4104_);
lean_ctor_set(v_reuseFailAlloc_4136_, 3, v_auxDeclNGen_4105_);
lean_ctor_set(v_reuseFailAlloc_4136_, 4, v___x_4128_);
lean_ctor_set(v_reuseFailAlloc_4136_, 5, v_cache_4106_);
lean_ctor_set(v_reuseFailAlloc_4136_, 6, v_messages_4107_);
lean_ctor_set(v_reuseFailAlloc_4136_, 7, v_infoState_4108_);
lean_ctor_set(v_reuseFailAlloc_4136_, 8, v_snapshotTasks_4109_);
v___x_4130_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4134_; 
v___x_4131_ = lean_st_ref_set(v___y_4092_, v___x_4130_);
v___x_4132_ = lean_box(0);
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 0, v___x_4132_);
v___x_4134_ = v___x_4098_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___x_4132_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___boxed(lean_object* v_cls_4141_, lean_object* v_msg_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4141_, v_msg_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
return v_res_4148_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v_cls_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v_cls_4149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4150_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4151_ = l_Lean_Name_append(v___x_4150_, v_cls_4149_);
return v___x_4151_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4153_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__1));
v___x_4154_ = l_Lean_stringToMessageData(v___x_4153_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(lean_object* v_upperBound_4155_, lean_object* v___y_4156_, lean_object* v_a_4157_, lean_object* v_b_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v_a_4165_; lean_object* v___y_4170_; uint8_t v___x_4189_; 
v___x_4189_ = lean_nat_dec_lt(v_a_4157_, v_upperBound_4155_);
if (v___x_4189_ == 0)
{
lean_object* v___x_4190_; 
lean_dec(v_a_4157_);
v___x_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4190_, 0, v_b_4158_);
return v___x_4190_;
}
else
{
lean_object* v_snd_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4261_; 
v_snd_4191_ = lean_ctor_get(v_b_4158_, 1);
v_isSharedCheck_4261_ = !lean_is_exclusive(v_b_4158_);
if (v_isSharedCheck_4261_ == 0)
{
lean_object* v_unused_4262_; 
v_unused_4262_ = lean_ctor_get(v_b_4158_, 0);
lean_dec(v_unused_4262_);
v___x_4193_ = v_b_4158_;
v_isShared_4194_ = v_isSharedCheck_4261_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_snd_4191_);
lean_dec(v_b_4158_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4261_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v_snd_4195_; lean_object* v_fst_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4260_; 
v_snd_4195_ = lean_ctor_get(v_snd_4191_, 1);
v_fst_4196_ = lean_ctor_get(v_snd_4191_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v_snd_4191_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4198_ = v_snd_4191_;
v_isShared_4199_ = v_isSharedCheck_4260_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_snd_4195_);
lean_inc(v_fst_4196_);
lean_dec(v_snd_4191_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4260_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v_fst_4200_; lean_object* v_snd_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4259_; 
v_fst_4200_ = lean_ctor_get(v_snd_4195_, 0);
v_snd_4201_ = lean_ctor_get(v_snd_4195_, 1);
v_isSharedCheck_4259_ = !lean_is_exclusive(v_snd_4195_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4203_ = v_snd_4195_;
v_isShared_4204_ = v_isSharedCheck_4259_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_snd_4201_);
lean_inc(v_fst_4200_);
lean_dec(v_snd_4195_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4259_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v_bestIdx_4205_; lean_object* v___x_4206_; lean_object* v_cls_4217_; lean_object* v___x_4218_; uint8_t v___x_4222_; lean_object* v___x_4223_; uint8_t v___x_4224_; uint8_t v___y_4253_; uint8_t v___y_4256_; 
v_bestIdx_4205_ = lean_unsigned_to_nat(0u);
v___x_4206_ = lean_box(0);
v_cls_4217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4218_ = lean_array_fget_borrowed(v___y_4156_, v_a_4157_);
v___x_4222_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4218_);
v___x_4223_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4218_);
v___x_4224_ = lean_nat_dec_eq(v___x_4223_, v_bestIdx_4205_);
if (v___x_4224_ == 0)
{
uint8_t v___x_4258_; 
v___x_4258_ = lean_unbox(v_snd_4201_);
if (v___x_4258_ == 0)
{
v___y_4256_ = v___x_4222_;
goto v___jp_4255_;
}
else
{
if (v___x_4224_ == 0)
{
v___y_4256_ = v___x_4224_;
goto v___jp_4255_;
}
else
{
v___y_4256_ = v___x_4222_;
goto v___jp_4255_;
}
}
}
else
{
v___y_4256_ = v___x_4224_;
goto v___jp_4255_;
}
v___jp_4207_:
{
lean_object* v___x_4209_; 
if (v_isShared_4204_ == 0)
{
v___x_4209_ = v___x_4203_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_fst_4200_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v_snd_4201_);
v___x_4209_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
lean_object* v___x_4211_; 
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 1, v___x_4209_);
v___x_4211_ = v___x_4198_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_fst_4196_);
lean_ctor_set(v_reuseFailAlloc_4215_, 1, v___x_4209_);
v___x_4211_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
lean_object* v___x_4213_; 
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 1, v___x_4211_);
lean_ctor_set(v___x_4193_, 0, v___x_4206_);
v___x_4213_ = v___x_4193_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4206_);
lean_ctor_set(v_reuseFailAlloc_4214_, 1, v___x_4211_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
v_a_4165_ = v___x_4213_;
goto v___jp_4164_;
}
}
}
}
v___jp_4219_:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4220_ = lean_box(0);
lean_inc(v___x_4218_);
v___x_4221_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4218_, v_fst_4200_, v_snd_4201_, v_fst_4196_, v___x_4220_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
v___y_4170_ = v___x_4221_;
goto v___jp_4169_;
}
v___jp_4225_:
{
if (v___x_4224_ == 0)
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
lean_dec(v_snd_4201_);
lean_dec(v_fst_4200_);
lean_dec(v_fst_4196_);
v___x_4226_ = lean_box(v___x_4222_);
v___x_4227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4223_);
lean_ctor_set(v___x_4227_, 1, v___x_4226_);
lean_inc(v_a_4157_);
v___x_4228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4228_, 0, v_a_4157_);
lean_ctor_set(v___x_4228_, 1, v___x_4227_);
v___x_4229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4206_);
lean_ctor_set(v___x_4229_, 1, v___x_4228_);
v_a_4165_ = v___x_4229_;
goto v___jp_4164_;
}
else
{
lean_object* v_options_4230_; uint8_t v_hasTrace_4231_; 
lean_dec(v___x_4223_);
v_options_4230_ = lean_ctor_get(v___y_4161_, 2);
v_hasTrace_4231_ = lean_ctor_get_uint8(v_options_4230_, sizeof(void*)*1);
if (v_hasTrace_4231_ == 0)
{
goto v___jp_4219_;
}
else
{
lean_object* v_inheritedTraceOptions_4232_; lean_object* v___x_4233_; uint8_t v___x_4234_; 
v_inheritedTraceOptions_4232_ = lean_ctor_get(v___y_4161_, 13);
v___x_4233_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_4234_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4232_, v_options_4230_, v___x_4233_);
if (v___x_4234_ == 0)
{
goto v___jp_4219_;
}
else
{
lean_object* v_var_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v_var_4235_ = lean_ctor_get(v___x_4218_, 0);
v___x_4236_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4235_);
v___x_4237_ = l_Nat_reprFast(v_var_4235_);
v___x_4238_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
v___x_4239_ = l_Lean_MessageData_ofFormat(v___x_4238_);
v___x_4240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4236_);
lean_ctor_set(v___x_4240_, 1, v___x_4239_);
v___x_4241_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4217_, v___x_4240_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4243_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref_known(v___x_4241_, 1);
lean_inc(v___x_4218_);
v___x_4243_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4218_, v_fst_4200_, v_snd_4201_, v_fst_4196_, v_a_4242_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
v___y_4170_ = v___x_4243_;
goto v___jp_4169_;
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
lean_dec(v_snd_4201_);
lean_dec(v_fst_4200_);
lean_dec(v_fst_4196_);
lean_dec(v_a_4157_);
v_a_4244_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4241_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4241_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
}
}
}
v___jp_4252_:
{
if (v___y_4253_ == 0)
{
lean_dec(v___x_4223_);
goto v___jp_4207_;
}
else
{
uint8_t v___x_4254_; 
v___x_4254_ = lean_nat_dec_lt(v___x_4223_, v_fst_4200_);
if (v___x_4254_ == 0)
{
lean_dec(v___x_4223_);
goto v___jp_4207_;
}
else
{
lean_del_object(v___x_4203_);
lean_del_object(v___x_4198_);
lean_del_object(v___x_4193_);
goto v___jp_4225_;
}
}
}
v___jp_4255_:
{
if (v___y_4256_ == 0)
{
uint8_t v___x_4257_; 
v___x_4257_ = lean_unbox(v_snd_4201_);
if (v___x_4257_ == 0)
{
if (v___x_4222_ == 0)
{
v___y_4253_ = v___x_4189_;
goto v___jp_4252_;
}
else
{
lean_dec(v___x_4223_);
goto v___jp_4207_;
}
}
else
{
v___y_4253_ = v___x_4222_;
goto v___jp_4252_;
}
}
else
{
lean_del_object(v___x_4203_);
lean_del_object(v___x_4198_);
lean_del_object(v___x_4193_);
goto v___jp_4225_;
}
}
}
}
}
}
v___jp_4164_:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4166_ = lean_unsigned_to_nat(1u);
v___x_4167_ = lean_nat_add(v_a_4157_, v___x_4166_);
lean_dec(v_a_4157_);
v_a_4157_ = v___x_4167_;
v_b_4158_ = v_a_4165_;
goto _start;
}
v___jp_4169_:
{
if (lean_obj_tag(v___y_4170_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4180_; 
v_a_4171_ = lean_ctor_get(v___y_4170_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___y_4170_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4173_ = v___y_4170_;
v_isShared_4174_ = v_isSharedCheck_4180_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___y_4170_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4180_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
if (lean_obj_tag(v_a_4171_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4177_; 
lean_dec(v_a_4157_);
v_a_4175_ = lean_ctor_get(v_a_4171_, 0);
lean_inc(v_a_4175_);
lean_dec_ref_known(v_a_4171_, 1);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 0, v_a_4175_);
v___x_4177_ = v___x_4173_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4175_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
else
{
lean_object* v_a_4179_; 
lean_del_object(v___x_4173_);
v_a_4179_ = lean_ctor_get(v_a_4171_, 0);
lean_inc(v_a_4179_);
lean_dec_ref_known(v_a_4171_, 1);
v_a_4165_ = v_a_4179_;
goto v___jp_4164_;
}
}
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
lean_dec(v_a_4157_);
v_a_4181_ = lean_ctor_get(v___y_4170_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___y_4170_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___y_4170_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___y_4170_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___boxed(lean_object* v_upperBound_4263_, lean_object* v___y_4264_, lean_object* v_a_4265_, lean_object* v_b_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4263_, v___y_4264_, v_a_4265_, v_b_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec_ref(v___y_4264_);
lean_dec(v_upperBound_4263_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(lean_object* v_as_4273_, size_t v_i_4274_, size_t v_stop_4275_, lean_object* v_b_4276_){
_start:
{
lean_object* v___y_4278_; uint8_t v___x_4282_; 
v___x_4282_ = lean_usize_dec_eq(v_i_4274_, v_stop_4275_);
if (v___x_4282_ == 0)
{
lean_object* v___x_4283_; uint8_t v___x_4286_; 
v___x_4283_ = lean_array_uget_borrowed(v_as_4273_, v_i_4274_);
v___x_4286_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v___x_4283_);
if (v___x_4286_ == 0)
{
goto v___jp_4284_;
}
else
{
if (v___x_4282_ == 0)
{
v___y_4278_ = v_b_4276_;
goto v___jp_4277_;
}
else
{
goto v___jp_4284_;
}
}
v___jp_4284_:
{
lean_object* v___x_4285_; 
lean_inc(v___x_4283_);
v___x_4285_ = lean_array_push(v_b_4276_, v___x_4283_);
v___y_4278_ = v___x_4285_;
goto v___jp_4277_;
}
}
else
{
return v_b_4276_;
}
v___jp_4277_:
{
size_t v___x_4279_; size_t v___x_4280_; 
v___x_4279_ = ((size_t)1ULL);
v___x_4280_ = lean_usize_add(v_i_4274_, v___x_4279_);
v_i_4274_ = v___x_4280_;
v_b_4276_ = v___y_4278_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___boxed(lean_object* v_as_4287_, lean_object* v_i_4288_, lean_object* v_stop_4289_, lean_object* v_b_4290_){
_start:
{
size_t v_i_boxed_4291_; size_t v_stop_boxed_4292_; lean_object* v_res_4293_; 
v_i_boxed_4291_ = lean_unbox_usize(v_i_4288_);
lean_dec(v_i_4288_);
v_stop_boxed_4292_ = lean_unbox_usize(v_stop_4289_);
lean_dec(v_stop_4289_);
v_res_4293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_as_4287_, v_i_boxed_4291_, v_stop_boxed_4292_, v_b_4290_);
lean_dec_ref(v_as_4287_);
return v_res_4293_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2(void){
_start:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4297_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__1));
v___x_4298_ = l_Lean_MessageData_ofFormat(v___x_4297_);
return v___x_4298_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4299_ = lean_box(1);
v___x_4300_ = l_Lean_MessageData_ofFormat(v___x_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(lean_object* v_a_4302_, lean_object* v_a_4303_){
_start:
{
if (lean_obj_tag(v_a_4302_) == 0)
{
lean_object* v___x_4304_; 
v___x_4304_ = l_List_reverse___redArg(v_a_4303_);
return v___x_4304_;
}
else
{
lean_object* v_head_4305_; lean_object* v_snd_4306_; lean_object* v_tail_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4354_; 
v_head_4305_ = lean_ctor_get(v_a_4302_, 0);
lean_inc(v_head_4305_);
v_snd_4306_ = lean_ctor_get(v_head_4305_, 1);
lean_inc(v_snd_4306_);
v_tail_4307_ = lean_ctor_get(v_a_4302_, 1);
v_isSharedCheck_4354_ = !lean_is_exclusive(v_a_4302_);
if (v_isSharedCheck_4354_ == 0)
{
lean_object* v_unused_4355_; 
v_unused_4355_ = lean_ctor_get(v_a_4302_, 0);
lean_dec(v_unused_4355_);
v___x_4309_ = v_a_4302_;
v_isShared_4310_ = v_isSharedCheck_4354_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_tail_4307_);
lean_dec(v_a_4302_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4354_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v_fst_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4352_; 
v_fst_4311_ = lean_ctor_get(v_head_4305_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v_head_4305_);
if (v_isSharedCheck_4352_ == 0)
{
lean_object* v_unused_4353_; 
v_unused_4353_ = lean_ctor_get(v_head_4305_, 1);
lean_dec(v_unused_4353_);
v___x_4313_ = v_head_4305_;
v_isShared_4314_ = v_isSharedCheck_4352_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_fst_4311_);
lean_dec(v_head_4305_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4352_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v_fst_4315_; lean_object* v_snd_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4351_; 
v_fst_4315_ = lean_ctor_get(v_snd_4306_, 0);
v_snd_4316_ = lean_ctor_get(v_snd_4306_, 1);
v_isSharedCheck_4351_ = !lean_is_exclusive(v_snd_4306_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4318_ = v_snd_4306_;
v_isShared_4319_ = v_isSharedCheck_4351_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_snd_4316_);
lean_inc(v_fst_4315_);
lean_dec(v_snd_4306_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4351_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4325_; 
v___x_4320_ = l_Nat_reprFast(v_fst_4311_);
v___x_4321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4320_);
v___x_4322_ = l_Lean_MessageData_ofFormat(v___x_4321_);
v___x_4323_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2);
if (v_isShared_4319_ == 0)
{
lean_ctor_set_tag(v___x_4318_, 7);
lean_ctor_set(v___x_4318_, 1, v___x_4323_);
lean_ctor_set(v___x_4318_, 0, v___x_4322_);
v___x_4325_ = v___x_4318_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4322_);
lean_ctor_set(v_reuseFailAlloc_4350_, 1, v___x_4323_);
v___x_4325_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
lean_object* v___x_4326_; lean_object* v___x_4328_; 
v___x_4326_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3);
if (v_isShared_4314_ == 0)
{
lean_ctor_set_tag(v___x_4313_, 7);
lean_ctor_set(v___x_4313_, 1, v___x_4326_);
lean_ctor_set(v___x_4313_, 0, v___x_4325_);
v___x_4328_ = v___x_4313_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v___x_4325_);
lean_ctor_set(v_reuseFailAlloc_4349_, 1, v___x_4326_);
v___x_4328_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___y_4335_; uint8_t v___x_4346_; 
v___x_4329_ = l_Nat_reprFast(v_fst_4315_);
v___x_4330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4329_);
v___x_4331_ = l_Lean_MessageData_ofFormat(v___x_4330_);
v___x_4332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4331_);
lean_ctor_set(v___x_4332_, 1, v___x_4323_);
v___x_4333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4332_);
lean_ctor_set(v___x_4333_, 1, v___x_4326_);
v___x_4346_ = lean_unbox(v_snd_4316_);
lean_dec(v_snd_4316_);
if (v___x_4346_ == 0)
{
lean_object* v___x_4347_; 
v___x_4347_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__4));
v___y_4335_ = v___x_4347_;
goto v___jp_4334_;
}
else
{
lean_object* v___x_4348_; 
v___x_4348_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4));
v___y_4335_ = v___x_4348_;
goto v___jp_4334_;
}
v___jp_4334_:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4343_; 
lean_inc_ref(v___y_4335_);
v___x_4336_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4336_, 0, v___y_4335_);
v___x_4337_ = l_Lean_MessageData_ofFormat(v___x_4336_);
v___x_4338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4333_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
v___x_4339_ = l_Lean_MessageData_paren(v___x_4338_);
v___x_4340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4328_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_4341_ = l_Lean_MessageData_paren(v___x_4340_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 1, v_a_4303_);
lean_ctor_set(v___x_4309_, 0, v___x_4341_);
v___x_4343_ = v___x_4309_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4341_);
lean_ctor_set(v_reuseFailAlloc_4345_, 1, v_a_4303_);
v___x_4343_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
v_a_4302_ = v_tail_4307_;
v_a_4303_ = v___x_4343_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(size_t v_sz_4356_, size_t v_i_4357_, lean_object* v_bs_4358_){
_start:
{
uint8_t v___x_4359_; 
v___x_4359_ = lean_usize_dec_lt(v_i_4357_, v_sz_4356_);
if (v___x_4359_ == 0)
{
return v_bs_4358_;
}
else
{
lean_object* v_v_4360_; lean_object* v_var_4361_; lean_object* v___x_4362_; lean_object* v_bs_x27_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; size_t v___x_4369_; size_t v___x_4370_; lean_object* v___x_4371_; 
v_v_4360_ = lean_array_uget(v_bs_4358_, v_i_4357_);
v_var_4361_ = lean_ctor_get(v_v_4360_, 0);
lean_inc(v_var_4361_);
v___x_4362_ = lean_unsigned_to_nat(0u);
v_bs_x27_4363_ = lean_array_uset(v_bs_4358_, v_i_4357_, v___x_4362_);
v___x_4364_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_v_4360_);
v___x_4365_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_v_4360_);
lean_dec(v_v_4360_);
v___x_4366_ = lean_box(v___x_4365_);
v___x_4367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4364_);
lean_ctor_set(v___x_4367_, 1, v___x_4366_);
v___x_4368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4368_, 0, v_var_4361_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
v___x_4369_ = ((size_t)1ULL);
v___x_4370_ = lean_usize_add(v_i_4357_, v___x_4369_);
v___x_4371_ = lean_array_uset(v_bs_x27_4363_, v_i_4357_, v___x_4368_);
v_i_4357_ = v___x_4370_;
v_bs_4358_ = v___x_4371_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___boxed(lean_object* v_sz_4373_, lean_object* v_i_4374_, lean_object* v_bs_4375_){
_start:
{
size_t v_sz_boxed_4376_; size_t v_i_boxed_4377_; lean_object* v_res_4378_; 
v_sz_boxed_4376_ = lean_unbox_usize(v_sz_4373_);
lean_dec(v_sz_4373_);
v_i_boxed_4377_ = lean_unbox_usize(v_i_4374_);
lean_dec(v_i_4374_);
v_res_4378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_boxed_4376_, v_i_boxed_4377_, v_bs_4375_);
return v_res_4378_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1(void){
_start:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4380_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0));
v___x_4381_ = l_Lean_stringToMessageData(v___x_4380_);
return v___x_4381_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4(void){
_start:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3));
v___x_4386_ = l_Lean_stringToMessageData(v___x_4385_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(lean_object* v_data_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_){
_start:
{
lean_object* v___x_4393_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v_bestIdx_4399_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4528_; lean_object* v___x_4552_; lean_object* v___x_4553_; uint8_t v___x_4554_; 
v___x_4393_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default));
v_bestIdx_4399_ = lean_unsigned_to_nat(0u);
v___x_4552_ = lean_array_get_size(v_data_4387_);
v___x_4553_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_4554_ = lean_nat_dec_lt(v_bestIdx_4399_, v___x_4552_);
if (v___x_4554_ == 0)
{
v___y_4528_ = v___x_4553_;
goto v___jp_4527_;
}
else
{
uint8_t v___x_4555_; 
v___x_4555_ = lean_nat_dec_le(v___x_4552_, v___x_4552_);
if (v___x_4555_ == 0)
{
if (v___x_4554_ == 0)
{
v___y_4528_ = v___x_4553_;
goto v___jp_4527_;
}
else
{
size_t v___x_4556_; size_t v___x_4557_; lean_object* v___x_4558_; 
v___x_4556_ = ((size_t)0ULL);
v___x_4557_ = lean_usize_of_nat(v___x_4552_);
v___x_4558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4387_, v___x_4556_, v___x_4557_, v___x_4553_);
v___y_4528_ = v___x_4558_;
goto v___jp_4527_;
}
}
else
{
size_t v___x_4559_; size_t v___x_4560_; lean_object* v___x_4561_; 
v___x_4559_ = ((size_t)0ULL);
v___x_4560_ = lean_usize_of_nat(v___x_4552_);
v___x_4561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4387_, v___x_4559_, v___x_4560_, v___x_4553_);
v___y_4528_ = v___x_4561_;
goto v___jp_4527_;
}
}
v___jp_4394_:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4397_ = lean_array_get(v___x_4393_, v___y_4396_, v___y_4395_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4396_);
v___x_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4397_);
return v___x_4398_;
}
v___jp_4400_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; uint8_t v___x_4410_; 
v___x_4408_ = lean_array_get_borrowed(v___x_4393_, v___y_4403_, v_bestIdx_4399_);
v___x_4409_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4408_);
v___x_4410_ = lean_nat_dec_eq(v___x_4409_, v_bestIdx_4399_);
if (v___x_4410_ == 0)
{
lean_object* v___x_4411_; lean_object* v___x_4412_; uint8_t v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4411_ = lean_unsigned_to_nat(1u);
v___x_4412_ = lean_array_get_size(v___y_4403_);
v___x_4413_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4408_);
v___x_4414_ = lean_box(0);
v___x_4415_ = lean_box(v___x_4413_);
v___x_4416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4409_);
lean_ctor_set(v___x_4416_, 1, v___x_4415_);
v___x_4417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4417_, 0, v_bestIdx_4399_);
lean_ctor_set(v___x_4417_, 1, v___x_4416_);
v___x_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4414_);
lean_ctor_set(v___x_4418_, 1, v___x_4417_);
v___x_4419_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v___x_4412_, v___y_4403_, v___x_4411_, v___x_4418_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4475_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4422_ = v___x_4419_;
v_isShared_4423_ = v_isSharedCheck_4475_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4419_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4475_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v_fst_4424_; 
v_fst_4424_ = lean_ctor_get(v_a_4420_, 0);
if (lean_obj_tag(v_fst_4424_) == 0)
{
lean_object* v_snd_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4469_; 
lean_del_object(v___x_4422_);
v_snd_4425_ = lean_ctor_get(v_a_4420_, 1);
v_isSharedCheck_4469_ = !lean_is_exclusive(v_a_4420_);
if (v_isSharedCheck_4469_ == 0)
{
lean_object* v_unused_4470_; 
v_unused_4470_ = lean_ctor_get(v_a_4420_, 0);
lean_dec(v_unused_4470_);
v___x_4427_ = v_a_4420_;
v_isShared_4428_ = v_isSharedCheck_4469_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_snd_4425_);
lean_dec(v_a_4420_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4469_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4429_; 
lean_inc_ref(v___y_4402_);
lean_inc(v___y_4407_);
lean_inc_ref(v___y_4406_);
lean_inc(v___y_4405_);
lean_inc_ref(v___y_4404_);
v___x_4429_ = lean_apply_5(v___y_4402_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, lean_box(0));
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; uint8_t v___x_4431_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
lean_inc(v_a_4430_);
lean_dec_ref_known(v___x_4429_, 1);
v___x_4431_ = lean_unbox(v_a_4430_);
lean_dec(v_a_4430_);
if (v___x_4431_ == 0)
{
lean_object* v_fst_4432_; 
lean_del_object(v___x_4427_);
lean_dec(v___y_4401_);
v_fst_4432_ = lean_ctor_get(v_snd_4425_, 0);
lean_inc(v_fst_4432_);
lean_dec(v_snd_4425_);
v___y_4395_ = v_fst_4432_;
v___y_4396_ = v___y_4403_;
goto v___jp_4394_;
}
else
{
lean_object* v_fst_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4459_; 
v_fst_4433_ = lean_ctor_get(v_snd_4425_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v_snd_4425_);
if (v_isSharedCheck_4459_ == 0)
{
lean_object* v_unused_4460_; 
v_unused_4460_ = lean_ctor_get(v_snd_4425_, 1);
lean_dec(v_unused_4460_);
v___x_4435_ = v_snd_4425_;
v_isShared_4436_ = v_isSharedCheck_4459_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_fst_4433_);
lean_dec(v_snd_4425_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4459_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4437_; lean_object* v_var_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4444_; 
v___x_4437_ = lean_array_get_borrowed(v___x_4393_, v___y_4403_, v_fst_4433_);
v_var_4438_ = lean_ctor_get(v___x_4437_, 0);
v___x_4439_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4438_);
v___x_4440_ = l_Nat_reprFast(v_var_4438_);
v___x_4441_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4440_);
v___x_4442_ = l_Lean_MessageData_ofFormat(v___x_4441_);
if (v_isShared_4436_ == 0)
{
lean_ctor_set_tag(v___x_4435_, 7);
lean_ctor_set(v___x_4435_, 1, v___x_4442_);
lean_ctor_set(v___x_4435_, 0, v___x_4439_);
v___x_4444_ = v___x_4435_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v___x_4439_);
lean_ctor_set(v_reuseFailAlloc_4458_, 1, v___x_4442_);
v___x_4444_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
lean_object* v___x_4445_; lean_object* v___x_4447_; 
v___x_4445_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
if (v_isShared_4428_ == 0)
{
lean_ctor_set_tag(v___x_4427_, 7);
lean_ctor_set(v___x_4427_, 1, v___x_4445_);
lean_ctor_set(v___x_4427_, 0, v___x_4444_);
v___x_4447_ = v___x_4427_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4444_);
lean_ctor_set(v_reuseFailAlloc_4457_, 1, v___x_4445_);
v___x_4447_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
lean_object* v___x_4448_; 
v___x_4448_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4401_, v___x_4447_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_dec_ref_known(v___x_4448_, 1);
v___y_4395_ = v_fst_4433_;
v___y_4396_ = v___y_4403_;
goto v___jp_4394_;
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_dec(v_fst_4433_);
lean_dec_ref(v___y_4403_);
v_a_4449_ = lean_ctor_get(v___x_4448_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4448_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4448_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
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
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_del_object(v___x_4427_);
lean_dec(v_snd_4425_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4401_);
v_a_4461_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4429_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4429_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
}
else
{
lean_object* v_val_4471_; lean_object* v___x_4473_; 
lean_inc_ref(v_fst_4424_);
lean_dec(v_a_4420_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4401_);
v_val_4471_ = lean_ctor_get(v_fst_4424_, 0);
lean_inc(v_val_4471_);
lean_dec_ref_known(v_fst_4424_, 1);
if (v_isShared_4423_ == 0)
{
lean_ctor_set(v___x_4422_, 0, v_val_4471_);
v___x_4473_ = v___x_4422_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_val_4471_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4401_);
v_a_4476_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4419_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4419_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
else
{
lean_object* v___x_4484_; 
lean_inc(v___x_4408_);
lean_dec(v___x_4409_);
lean_dec_ref(v___y_4403_);
lean_inc_ref(v___y_4402_);
lean_inc(v___y_4407_);
lean_inc_ref(v___y_4406_);
lean_inc(v___y_4405_);
lean_inc_ref(v___y_4404_);
v___x_4484_ = lean_apply_5(v___y_4402_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, lean_box(0));
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4518_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4487_ = v___x_4484_;
v_isShared_4488_ = v_isSharedCheck_4518_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4484_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4518_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
uint8_t v___x_4489_; 
v___x_4489_ = lean_unbox(v_a_4485_);
lean_dec(v_a_4485_);
if (v___x_4489_ == 0)
{
lean_object* v___x_4491_; 
lean_dec(v___y_4401_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 0, v___x_4408_);
v___x_4491_ = v___x_4487_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___x_4408_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
else
{
lean_object* v_var_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
lean_del_object(v___x_4487_);
v_var_4493_ = lean_ctor_get(v___x_4408_, 0);
v___x_4494_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4493_);
v___x_4495_ = l_Nat_reprFast(v_var_4493_);
v___x_4496_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
v___x_4497_ = l_Lean_MessageData_ofFormat(v___x_4496_);
v___x_4498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4494_);
lean_ctor_set(v___x_4498_, 1, v___x_4497_);
v___x_4499_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
v___x_4500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4498_);
lean_ctor_set(v___x_4500_, 1, v___x_4499_);
v___x_4501_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4401_, v___x_4500_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4508_ == 0)
{
lean_object* v_unused_4509_; 
v_unused_4509_ = lean_ctor_get(v___x_4501_, 0);
lean_dec(v_unused_4509_);
v___x_4503_ = v___x_4501_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_dec(v___x_4501_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 0, v___x_4408_);
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4408_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
lean_dec(v___x_4408_);
v_a_4510_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4501_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4501_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4515_; 
if (v_isShared_4513_ == 0)
{
v___x_4515_ = v___x_4512_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4510_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
}
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec(v___x_4408_);
lean_dec(v___y_4401_);
v_a_4519_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4484_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4484_);
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
v___jp_4527_:
{
lean_object* v_cls_4529_; lean_object* v___f_4530_; lean_object* v___x_4531_; lean_object* v_a_4532_; uint8_t v___x_4533_; 
v_cls_4529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___f_4530_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2));
v___x_4531_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4529_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_);
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4532_);
lean_dec_ref(v___x_4531_);
v___x_4533_ = lean_unbox(v_a_4532_);
lean_dec(v_a_4532_);
if (v___x_4533_ == 0)
{
v___y_4401_ = v_cls_4529_;
v___y_4402_ = v___f_4530_;
v___y_4403_ = v___y_4528_;
v___y_4404_ = v_a_4388_;
v___y_4405_ = v_a_4389_;
v___y_4406_ = v_a_4390_;
v___y_4407_ = v_a_4391_;
goto v___jp_4400_;
}
else
{
lean_object* v___x_4534_; size_t v_sz_4535_; size_t v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4534_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4);
v_sz_4535_ = lean_array_size(v___y_4528_);
v___x_4536_ = ((size_t)0ULL);
lean_inc_ref(v___y_4528_);
v___x_4537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_4535_, v___x_4536_, v___y_4528_);
v___x_4538_ = lean_array_to_list(v___x_4537_);
v___x_4539_ = lean_box(0);
v___x_4540_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v___x_4538_, v___x_4539_);
v___x_4541_ = l_Lean_MessageData_ofList(v___x_4540_);
v___x_4542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4534_);
lean_ctor_set(v___x_4542_, 1, v___x_4541_);
v___x_4543_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4529_, v___x_4542_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_dec_ref_known(v___x_4543_, 1);
v___y_4401_ = v_cls_4529_;
v___y_4402_ = v___f_4530_;
v___y_4403_ = v___y_4528_;
v___y_4404_ = v_a_4388_;
v___y_4405_ = v_a_4389_;
v___y_4406_ = v_a_4390_;
v___y_4407_ = v_a_4391_;
goto v___jp_4400_;
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
lean_dec_ref(v___y_4528_);
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4543_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4543_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object* v_data_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
lean_dec(v_a_4566_);
lean_dec_ref(v_a_4565_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
lean_dec_ref(v_data_4562_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object* v_upperBound_4569_, lean_object* v___y_4570_, lean_object* v_inst_4571_, lean_object* v_R_4572_, lean_object* v_a_4573_, lean_object* v_b_4574_, lean_object* v_c_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v___x_4581_; 
v___x_4581_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4569_, v___y_4570_, v_a_4573_, v_b_4574_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object* v_upperBound_4582_, lean_object* v___y_4583_, lean_object* v_inst_4584_, lean_object* v_R_4585_, lean_object* v_a_4586_, lean_object* v_b_4587_, lean_object* v_c_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_upperBound_4582_, v___y_4583_, v_inst_4584_, v_R_4585_, v_a_4586_, v_b_4587_, v_c_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec_ref(v___y_4583_);
lean_dec(v_upperBound_4582_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(lean_object* v_snd_4595_, lean_object* v_fst_4596_, lean_object* v_as_x27_4597_, lean_object* v_b_4598_){
_start:
{
if (lean_obj_tag(v_as_x27_4597_) == 0)
{
lean_object* v___x_4600_; 
lean_dec_ref(v_fst_4596_);
v___x_4600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4600_, 0, v_b_4598_);
return v___x_4600_;
}
else
{
lean_object* v_head_4601_; lean_object* v_tail_4602_; lean_object* v_fst_4603_; lean_object* v_snd_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v_head_4601_ = lean_ctor_get(v_as_x27_4597_, 0);
v_tail_4602_ = lean_ctor_get(v_as_x27_4597_, 1);
v_fst_4603_ = lean_ctor_get(v_head_4601_, 0);
v_snd_4604_ = lean_ctor_get(v_head_4601_, 1);
v___x_4605_ = lean_int_neg(v_snd_4595_);
lean_inc(v_fst_4603_);
lean_inc_ref(v_fst_4596_);
lean_inc(v_snd_4604_);
v___x_4606_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_snd_4604_, v_fst_4596_, v___x_4605_, v_fst_4603_);
v___x_4607_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_4606_);
v___x_4608_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_b_4598_, v___x_4607_);
v_as_x27_4597_ = v_tail_4602_;
v_b_4598_ = v___x_4608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg___boxed(lean_object* v_snd_4610_, lean_object* v_fst_4611_, lean_object* v_as_x27_4612_, lean_object* v_b_4613_, lean_object* v___y_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4610_, v_fst_4611_, v_as_x27_4612_, v_b_4613_);
lean_dec(v_as_x27_4612_);
lean_dec(v_snd_4610_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(lean_object* v_upperBounds_4616_, lean_object* v_as_x27_4617_, lean_object* v_b_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_){
_start:
{
if (lean_obj_tag(v_as_x27_4617_) == 0)
{
lean_object* v___x_4624_; 
v___x_4624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4624_, 0, v_b_4618_);
return v___x_4624_;
}
else
{
lean_object* v_head_4625_; lean_object* v_tail_4626_; lean_object* v_fst_4627_; lean_object* v_snd_4628_; lean_object* v___x_4629_; lean_object* v_a_4630_; 
v_head_4625_ = lean_ctor_get(v_as_x27_4617_, 0);
v_tail_4626_ = lean_ctor_get(v_as_x27_4617_, 1);
v_fst_4627_ = lean_ctor_get(v_head_4625_, 0);
v_snd_4628_ = lean_ctor_get(v_head_4625_, 1);
lean_inc(v_fst_4627_);
v___x_4629_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4628_, v_fst_4627_, v_upperBounds_4616_, v_b_4618_);
v_a_4630_ = lean_ctor_get(v___x_4629_, 0);
lean_inc(v_a_4630_);
lean_dec_ref(v___x_4629_);
v_as_x27_4617_ = v_tail_4626_;
v_b_4618_ = v_a_4630_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg___boxed(lean_object* v_upperBounds_4632_, lean_object* v_as_x27_4633_, lean_object* v_b_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4632_, v_as_x27_4633_, v_b_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
lean_dec(v_as_x27_4633_);
lean_dec(v_upperBounds_4632_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(lean_object* v_as_x27_4641_, lean_object* v_b_4642_){
_start:
{
if (lean_obj_tag(v_as_x27_4641_) == 0)
{
lean_object* v___x_4644_; 
v___x_4644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4644_, 0, v_b_4642_);
return v___x_4644_;
}
else
{
lean_object* v_head_4645_; lean_object* v_tail_4646_; lean_object* v___x_4647_; 
v_head_4645_ = lean_ctor_get(v_as_x27_4641_, 0);
v_tail_4646_ = lean_ctor_get(v_as_x27_4641_, 1);
lean_inc(v_head_4645_);
v___x_4647_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_b_4642_, v_head_4645_);
v_as_x27_4641_ = v_tail_4646_;
v_b_4642_ = v___x_4647_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg___boxed(lean_object* v_as_x27_4649_, lean_object* v_b_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4649_, v_b_4650_);
lean_dec(v_as_x27_4649_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(lean_object* v_p_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_){
_start:
{
lean_object* v_data_4659_; lean_object* v___x_4660_; 
lean_inc_ref(v_p_4653_);
v_data_4659_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(v_p_4653_);
v___x_4660_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4659_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
lean_dec_ref(v_data_4659_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; lean_object* v_irrelevant_4662_; lean_object* v_lowerBounds_4663_; lean_object* v_upperBounds_4664_; lean_object* v_assumptions_4665_; lean_object* v_eliminations_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4681_; 
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4661_);
lean_dec_ref_known(v___x_4660_, 1);
v_irrelevant_4662_ = lean_ctor_get(v_a_4661_, 1);
lean_inc(v_irrelevant_4662_);
v_lowerBounds_4663_ = lean_ctor_get(v_a_4661_, 2);
lean_inc(v_lowerBounds_4663_);
v_upperBounds_4664_ = lean_ctor_get(v_a_4661_, 3);
lean_inc(v_upperBounds_4664_);
lean_dec(v_a_4661_);
v_assumptions_4665_ = lean_ctor_get(v_p_4653_, 0);
v_eliminations_4666_ = lean_ctor_get(v_p_4653_, 4);
v_isSharedCheck_4681_ = !lean_is_exclusive(v_p_4653_);
if (v_isSharedCheck_4681_ == 0)
{
lean_object* v_unused_4682_; lean_object* v_unused_4683_; lean_object* v_unused_4684_; lean_object* v_unused_4685_; lean_object* v_unused_4686_; 
v_unused_4682_ = lean_ctor_get(v_p_4653_, 6);
lean_dec(v_unused_4682_);
v_unused_4683_ = lean_ctor_get(v_p_4653_, 5);
lean_dec(v_unused_4683_);
v_unused_4684_ = lean_ctor_get(v_p_4653_, 3);
lean_dec(v_unused_4684_);
v_unused_4685_ = lean_ctor_get(v_p_4653_, 2);
lean_dec(v_unused_4685_);
v_unused_4686_ = lean_ctor_get(v_p_4653_, 1);
lean_dec(v_unused_4686_);
v___x_4668_ = v_p_4653_;
v_isShared_4669_ = v_isSharedCheck_4681_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_eliminations_4666_);
lean_inc(v_assumptions_4665_);
lean_dec(v_p_4653_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4681_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; uint8_t v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4676_; 
v___x_4670_ = lean_unsigned_to_nat(0u);
v___x_4671_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v___x_4672_ = 1;
v___x_4673_ = lean_box(0);
v___x_4674_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 6, v___x_4674_);
lean_ctor_set(v___x_4668_, 5, v___x_4673_);
lean_ctor_set(v___x_4668_, 3, v___x_4671_);
lean_ctor_set(v___x_4668_, 2, v___x_4671_);
lean_ctor_set(v___x_4668_, 1, v___x_4670_);
v___x_4676_ = v___x_4668_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_assumptions_4665_);
lean_ctor_set(v_reuseFailAlloc_4680_, 1, v___x_4670_);
lean_ctor_set(v_reuseFailAlloc_4680_, 2, v___x_4671_);
lean_ctor_set(v_reuseFailAlloc_4680_, 3, v___x_4671_);
lean_ctor_set(v_reuseFailAlloc_4680_, 4, v_eliminations_4666_);
lean_ctor_set(v_reuseFailAlloc_4680_, 5, v___x_4673_);
lean_ctor_set(v_reuseFailAlloc_4680_, 6, v___x_4674_);
v___x_4676_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
lean_object* v___x_4677_; lean_object* v_a_4678_; lean_object* v___x_4679_; 
lean_ctor_set_uint8(v___x_4676_, sizeof(void*)*7, v___x_4672_);
v___x_4677_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_irrelevant_4662_, v___x_4676_);
lean_dec(v_irrelevant_4662_);
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref(v___x_4677_);
v___x_4679_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4664_, v_lowerBounds_4663_, v_a_4678_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
lean_dec(v_lowerBounds_4663_);
lean_dec(v_upperBounds_4664_);
return v___x_4679_;
}
}
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
lean_dec_ref(v_p_4653_);
v_a_4687_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4660_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4660_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin___boxed(lean_object* v_p_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
lean_dec(v_a_4697_);
lean_dec_ref(v_a_4696_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(lean_object* v_snd_4702_, lean_object* v_fst_4703_, lean_object* v_as_4704_, lean_object* v_as_x27_4705_, lean_object* v_b_4706_, lean_object* v_a_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
lean_object* v___x_4713_; 
v___x_4713_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4702_, v_fst_4703_, v_as_x27_4705_, v_b_4706_);
return v___x_4713_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___boxed(lean_object* v_snd_4714_, lean_object* v_fst_4715_, lean_object* v_as_4716_, lean_object* v_as_x27_4717_, lean_object* v_b_4718_, lean_object* v_a_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(v_snd_4714_, v_fst_4715_, v_as_4716_, v_as_x27_4717_, v_b_4718_, v_a_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v_as_x27_4717_);
lean_dec(v_as_4716_);
lean_dec(v_snd_4714_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(lean_object* v_as_4726_, lean_object* v_as_x27_4727_, lean_object* v_b_4728_, lean_object* v_a_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
lean_object* v___x_4735_; 
v___x_4735_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4727_, v_b_4728_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___boxed(lean_object* v_as_4736_, lean_object* v_as_x27_4737_, lean_object* v_b_4738_, lean_object* v_a_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(v_as_4736_, v_as_x27_4737_, v_b_4738_, v_a_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec(v___y_4741_);
lean_dec_ref(v___y_4740_);
lean_dec(v_as_x27_4737_);
lean_dec(v_as_4736_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(lean_object* v_upperBounds_4746_, lean_object* v_as_4747_, lean_object* v_as_x27_4748_, lean_object* v_b_4749_, lean_object* v_a_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4746_, v_as_x27_4748_, v_b_4749_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___boxed(lean_object* v_upperBounds_4757_, lean_object* v_as_4758_, lean_object* v_as_x27_4759_, lean_object* v_b_4760_, lean_object* v_a_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(v_upperBounds_4757_, v_as_4758_, v_as_x27_4759_, v_b_4760_, v_a_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
lean_dec(v_as_x27_4759_);
lean_dec(v_as_4758_);
lean_dec(v_upperBounds_4757_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object* v_x_4768_, lean_object* v_x_4769_){
_start:
{
if (lean_obj_tag(v_x_4769_) == 0)
{
lean_inc(v_x_4768_);
return v_x_4768_;
}
else
{
lean_object* v_key_4770_; lean_object* v_value_4771_; lean_object* v_tail_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v_key_4770_ = lean_ctor_get(v_x_4769_, 0);
v_value_4771_ = lean_ctor_get(v_x_4769_, 1);
v_tail_4772_ = lean_ctor_get(v_x_4769_, 2);
v___x_4773_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4768_, v_tail_4772_);
lean_inc(v_value_4771_);
lean_inc(v_key_4770_);
v___x_4774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4774_, 0, v_key_4770_);
lean_ctor_set(v___x_4774_, 1, v_value_4771_);
v___x_4775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4775_, 0, v___x_4774_);
lean_ctor_set(v___x_4775_, 1, v___x_4773_);
return v___x_4775_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2___boxed(lean_object* v_x_4776_, lean_object* v_x_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4776_, v_x_4777_);
lean_dec(v_x_4777_);
lean_dec(v_x_4776_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object* v_as_4779_, size_t v_i_4780_, size_t v_stop_4781_, lean_object* v_b_4782_){
_start:
{
uint8_t v___x_4783_; 
v___x_4783_ = lean_usize_dec_eq(v_i_4780_, v_stop_4781_);
if (v___x_4783_ == 0)
{
size_t v___x_4784_; size_t v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4784_ = ((size_t)1ULL);
v___x_4785_ = lean_usize_sub(v_i_4780_, v___x_4784_);
v___x_4786_ = lean_array_uget_borrowed(v_as_4779_, v___x_4785_);
v___x_4787_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_b_4782_, v___x_4786_);
lean_dec(v_b_4782_);
v_i_4780_ = v___x_4785_;
v_b_4782_ = v___x_4787_;
goto _start;
}
else
{
return v_b_4782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object* v_as_4789_, lean_object* v_i_4790_, lean_object* v_stop_4791_, lean_object* v_b_4792_){
_start:
{
size_t v_i_boxed_4793_; size_t v_stop_boxed_4794_; lean_object* v_res_4795_; 
v_i_boxed_4793_ = lean_unbox_usize(v_i_4790_);
lean_dec(v_i_4790_);
v_stop_boxed_4794_ = lean_unbox_usize(v_stop_4791_);
lean_dec(v_stop_4791_);
v_res_4795_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_as_4789_, v_i_boxed_4793_, v_stop_boxed_4794_, v_b_4792_);
lean_dec_ref(v_as_4789_);
return v_res_4795_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object* v_a_4796_, lean_object* v_a_4797_){
_start:
{
if (lean_obj_tag(v_a_4796_) == 0)
{
lean_object* v___x_4798_; 
v___x_4798_ = l_List_reverse___redArg(v_a_4797_);
return v___x_4798_;
}
else
{
lean_object* v_head_4799_; lean_object* v_tail_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4917_; 
v_head_4799_ = lean_ctor_get(v_a_4796_, 0);
v_tail_4800_ = lean_ctor_get(v_a_4796_, 1);
v_isSharedCheck_4917_ = !lean_is_exclusive(v_a_4796_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4802_ = v_a_4796_;
v_isShared_4803_ = v_isSharedCheck_4917_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_tail_4800_);
lean_inc(v_head_4799_);
lean_dec(v_a_4796_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4917_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___y_4805_; lean_object* v_snd_4810_; lean_object* v_constraint_4811_; lean_object* v_fst_4812_; lean_object* v_lowerBound_4813_; lean_object* v_upperBound_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___y_4819_; lean_object* v___y_4820_; 
v_snd_4810_ = lean_ctor_get(v_head_4799_, 1);
v_constraint_4811_ = lean_ctor_get(v_snd_4810_, 1);
lean_inc_ref(v_constraint_4811_);
v_fst_4812_ = lean_ctor_get(v_head_4799_, 0);
lean_inc(v_fst_4812_);
lean_dec(v_head_4799_);
v_lowerBound_4813_ = lean_ctor_get(v_constraint_4811_, 0);
lean_inc(v_lowerBound_4813_);
v_upperBound_4814_ = lean_ctor_get(v_constraint_4811_, 1);
lean_inc(v_upperBound_4814_);
lean_dec_ref(v_constraint_4811_);
v___x_4815_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_fst_4812_);
lean_dec(v_fst_4812_);
v___x_4816_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_4817_ = lean_string_append(v___x_4815_, v___x_4816_);
if (lean_obj_tag(v_lowerBound_4813_) == 0)
{
if (lean_obj_tag(v_upperBound_4814_) == 0)
{
lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4825_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_4826_ = lean_string_append(v___x_4817_, v___x_4825_);
v___y_4805_ = v___x_4826_;
goto v___jp_4804_;
}
else
{
lean_object* v_val_4827_; lean_object* v___x_4828_; lean_object* v___y_4830_; lean_object* v_intZero_4835_; uint8_t v_isNeg_4836_; 
v_val_4827_ = lean_ctor_get(v_upperBound_4814_, 0);
lean_inc(v_val_4827_);
lean_dec_ref_known(v_upperBound_4814_, 1);
v___x_4828_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_4835_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4836_ = lean_int_dec_lt(v_val_4827_, v_intZero_4835_);
if (v_isNeg_4836_ == 0)
{
lean_object* v_a_4837_; lean_object* v___x_4838_; 
v_a_4837_ = lean_nat_abs(v_val_4827_);
lean_dec(v_val_4827_);
v___x_4838_ = l_Nat_reprFast(v_a_4837_);
v___y_4830_ = v___x_4838_;
goto v___jp_4829_;
}
else
{
lean_object* v_abs_4839_; lean_object* v_one_4840_; lean_object* v_a_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v_abs_4839_ = lean_nat_abs(v_val_4827_);
lean_dec(v_val_4827_);
v_one_4840_ = lean_unsigned_to_nat(1u);
v_a_4841_ = lean_nat_sub(v_abs_4839_, v_one_4840_);
lean_dec(v_abs_4839_);
v___x_4842_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4843_ = lean_nat_add(v_a_4841_, v_one_4840_);
lean_dec(v_a_4841_);
v___x_4844_ = l_Nat_reprFast(v___x_4843_);
v___x_4845_ = lean_string_append(v___x_4842_, v___x_4844_);
lean_dec_ref(v___x_4844_);
v___y_4830_ = v___x_4845_;
goto v___jp_4829_;
}
v___jp_4829_:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4831_ = lean_string_append(v___x_4828_, v___y_4830_);
lean_dec_ref(v___y_4830_);
v___x_4832_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4833_ = lean_string_append(v___x_4831_, v___x_4832_);
v___x_4834_ = lean_string_append(v___x_4817_, v___x_4833_);
lean_dec_ref(v___x_4833_);
v___y_4805_ = v___x_4834_;
goto v___jp_4804_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_4814_) == 0)
{
lean_object* v_val_4846_; lean_object* v___x_4847_; lean_object* v___y_4849_; lean_object* v_intZero_4854_; uint8_t v_isNeg_4855_; 
v_val_4846_ = lean_ctor_get(v_lowerBound_4813_, 0);
lean_inc(v_val_4846_);
lean_dec_ref_known(v_lowerBound_4813_, 1);
v___x_4847_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4854_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4855_ = lean_int_dec_lt(v_val_4846_, v_intZero_4854_);
if (v_isNeg_4855_ == 0)
{
lean_object* v_a_4856_; lean_object* v___x_4857_; 
v_a_4856_ = lean_nat_abs(v_val_4846_);
lean_dec(v_val_4846_);
v___x_4857_ = l_Nat_reprFast(v_a_4856_);
v___y_4849_ = v___x_4857_;
goto v___jp_4848_;
}
else
{
lean_object* v_abs_4858_; lean_object* v_one_4859_; lean_object* v_a_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
v_abs_4858_ = lean_nat_abs(v_val_4846_);
lean_dec(v_val_4846_);
v_one_4859_ = lean_unsigned_to_nat(1u);
v_a_4860_ = lean_nat_sub(v_abs_4858_, v_one_4859_);
lean_dec(v_abs_4858_);
v___x_4861_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4862_ = lean_nat_add(v_a_4860_, v_one_4859_);
lean_dec(v_a_4860_);
v___x_4863_ = l_Nat_reprFast(v___x_4862_);
v___x_4864_ = lean_string_append(v___x_4861_, v___x_4863_);
lean_dec_ref(v___x_4863_);
v___y_4849_ = v___x_4864_;
goto v___jp_4848_;
}
v___jp_4848_:
{
lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4850_ = lean_string_append(v___x_4847_, v___y_4849_);
lean_dec_ref(v___y_4849_);
v___x_4851_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_4852_ = lean_string_append(v___x_4850_, v___x_4851_);
v___x_4853_ = lean_string_append(v___x_4817_, v___x_4852_);
lean_dec_ref(v___x_4852_);
v___y_4805_ = v___x_4853_;
goto v___jp_4804_;
}
}
else
{
lean_object* v_val_4865_; lean_object* v_val_4866_; uint8_t v___x_4867_; 
v_val_4865_ = lean_ctor_get(v_lowerBound_4813_, 0);
lean_inc(v_val_4865_);
lean_dec_ref_known(v_lowerBound_4813_, 1);
v_val_4866_ = lean_ctor_get(v_upperBound_4814_, 0);
lean_inc(v_val_4866_);
lean_dec_ref_known(v_upperBound_4814_, 1);
v___x_4867_ = lean_int_dec_lt(v_val_4866_, v_val_4865_);
if (v___x_4867_ == 0)
{
uint8_t v___x_4868_; 
v___x_4868_ = lean_int_dec_eq(v_val_4865_, v_val_4866_);
if (v___x_4868_ == 0)
{
lean_object* v___x_4869_; lean_object* v___y_4871_; lean_object* v_intZero_4886_; uint8_t v_isNeg_4887_; 
v___x_4869_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4886_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4887_ = lean_int_dec_lt(v_val_4865_, v_intZero_4886_);
if (v_isNeg_4887_ == 0)
{
lean_object* v_a_4888_; lean_object* v___x_4889_; 
v_a_4888_ = lean_nat_abs(v_val_4865_);
lean_dec(v_val_4865_);
v___x_4889_ = l_Nat_reprFast(v_a_4888_);
v___y_4871_ = v___x_4889_;
goto v___jp_4870_;
}
else
{
lean_object* v_abs_4890_; lean_object* v_one_4891_; lean_object* v_a_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; 
v_abs_4890_ = lean_nat_abs(v_val_4865_);
lean_dec(v_val_4865_);
v_one_4891_ = lean_unsigned_to_nat(1u);
v_a_4892_ = lean_nat_sub(v_abs_4890_, v_one_4891_);
lean_dec(v_abs_4890_);
v___x_4893_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4894_ = lean_nat_add(v_a_4892_, v_one_4891_);
lean_dec(v_a_4892_);
v___x_4895_ = l_Nat_reprFast(v___x_4894_);
v___x_4896_ = lean_string_append(v___x_4893_, v___x_4895_);
lean_dec_ref(v___x_4895_);
v___y_4871_ = v___x_4896_;
goto v___jp_4870_;
}
v___jp_4870_:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v_intZero_4875_; uint8_t v_isNeg_4876_; 
v___x_4872_ = lean_string_append(v___x_4869_, v___y_4871_);
lean_dec_ref(v___y_4871_);
v___x_4873_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_4874_ = lean_string_append(v___x_4872_, v___x_4873_);
v_intZero_4875_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4876_ = lean_int_dec_lt(v_val_4866_, v_intZero_4875_);
if (v_isNeg_4876_ == 0)
{
lean_object* v_a_4877_; lean_object* v___x_4878_; 
v_a_4877_ = lean_nat_abs(v_val_4866_);
lean_dec(v_val_4866_);
v___x_4878_ = l_Nat_reprFast(v_a_4877_);
v___y_4819_ = v___x_4874_;
v___y_4820_ = v___x_4878_;
goto v___jp_4818_;
}
else
{
lean_object* v_abs_4879_; lean_object* v_one_4880_; lean_object* v_a_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
v_abs_4879_ = lean_nat_abs(v_val_4866_);
lean_dec(v_val_4866_);
v_one_4880_ = lean_unsigned_to_nat(1u);
v_a_4881_ = lean_nat_sub(v_abs_4879_, v_one_4880_);
lean_dec(v_abs_4879_);
v___x_4882_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4883_ = lean_nat_add(v_a_4881_, v_one_4880_);
lean_dec(v_a_4881_);
v___x_4884_ = l_Nat_reprFast(v___x_4883_);
v___x_4885_ = lean_string_append(v___x_4882_, v___x_4884_);
lean_dec_ref(v___x_4884_);
v___y_4819_ = v___x_4874_;
v___y_4820_ = v___x_4885_;
goto v___jp_4818_;
}
}
}
else
{
lean_object* v___x_4897_; lean_object* v___y_4899_; lean_object* v_intZero_4904_; uint8_t v_isNeg_4905_; 
lean_dec(v_val_4866_);
v___x_4897_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_4904_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4905_ = lean_int_dec_lt(v_val_4865_, v_intZero_4904_);
if (v_isNeg_4905_ == 0)
{
lean_object* v_a_4906_; lean_object* v___x_4907_; 
v_a_4906_ = lean_nat_abs(v_val_4865_);
lean_dec(v_val_4865_);
v___x_4907_ = l_Nat_reprFast(v_a_4906_);
v___y_4899_ = v___x_4907_;
goto v___jp_4898_;
}
else
{
lean_object* v_abs_4908_; lean_object* v_one_4909_; lean_object* v_a_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; 
v_abs_4908_ = lean_nat_abs(v_val_4865_);
lean_dec(v_val_4865_);
v_one_4909_ = lean_unsigned_to_nat(1u);
v_a_4910_ = lean_nat_sub(v_abs_4908_, v_one_4909_);
lean_dec(v_abs_4908_);
v___x_4911_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4912_ = lean_nat_add(v_a_4910_, v_one_4909_);
lean_dec(v_a_4910_);
v___x_4913_ = l_Nat_reprFast(v___x_4912_);
v___x_4914_ = lean_string_append(v___x_4911_, v___x_4913_);
lean_dec_ref(v___x_4913_);
v___y_4899_ = v___x_4914_;
goto v___jp_4898_;
}
v___jp_4898_:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4900_ = lean_string_append(v___x_4897_, v___y_4899_);
lean_dec_ref(v___y_4899_);
v___x_4901_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_4902_ = lean_string_append(v___x_4900_, v___x_4901_);
v___x_4903_ = lean_string_append(v___x_4817_, v___x_4902_);
lean_dec_ref(v___x_4902_);
v___y_4805_ = v___x_4903_;
goto v___jp_4804_;
}
}
}
else
{
lean_object* v___x_4915_; lean_object* v___x_4916_; 
lean_dec(v_val_4866_);
lean_dec(v_val_4865_);
v___x_4915_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_4916_ = lean_string_append(v___x_4817_, v___x_4915_);
v___y_4805_ = v___x_4916_;
goto v___jp_4804_;
}
}
}
v___jp_4804_:
{
lean_object* v___x_4807_; 
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 1, v_a_4797_);
lean_ctor_set(v___x_4802_, 0, v___y_4805_);
v___x_4807_ = v___x_4802_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___y_4805_);
lean_ctor_set(v_reuseFailAlloc_4809_, 1, v_a_4797_);
v___x_4807_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
v_a_4796_ = v_tail_4800_;
v_a_4797_ = v___x_4807_;
goto _start;
}
}
v___jp_4818_:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4821_ = lean_string_append(v___y_4819_, v___y_4820_);
lean_dec_ref(v___y_4820_);
v___x_4822_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4823_ = lean_string_append(v___x_4821_, v___x_4822_);
v___x_4824_ = lean_string_append(v___x_4817_, v___x_4823_);
lean_dec_ref(v___x_4823_);
v___y_4805_ = v___x_4824_;
goto v___jp_4804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object* v_cls_4918_, lean_object* v_msg_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_){
_start:
{
lean_object* v_ref_4925_; lean_object* v___x_4926_; lean_object* v_a_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4971_; 
v_ref_4925_ = lean_ctor_get(v___y_4922_, 5);
v___x_4926_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
v_a_4927_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4929_ = v___x_4926_;
v_isShared_4930_ = v_isSharedCheck_4971_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_a_4927_);
lean_dec(v___x_4926_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4971_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4931_; lean_object* v_traceState_4932_; lean_object* v_env_4933_; lean_object* v_nextMacroScope_4934_; lean_object* v_ngen_4935_; lean_object* v_auxDeclNGen_4936_; lean_object* v_cache_4937_; lean_object* v_messages_4938_; lean_object* v_infoState_4939_; lean_object* v_snapshotTasks_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4970_; 
v___x_4931_ = lean_st_ref_take(v___y_4923_);
v_traceState_4932_ = lean_ctor_get(v___x_4931_, 4);
v_env_4933_ = lean_ctor_get(v___x_4931_, 0);
v_nextMacroScope_4934_ = lean_ctor_get(v___x_4931_, 1);
v_ngen_4935_ = lean_ctor_get(v___x_4931_, 2);
v_auxDeclNGen_4936_ = lean_ctor_get(v___x_4931_, 3);
v_cache_4937_ = lean_ctor_get(v___x_4931_, 5);
v_messages_4938_ = lean_ctor_get(v___x_4931_, 6);
v_infoState_4939_ = lean_ctor_get(v___x_4931_, 7);
v_snapshotTasks_4940_ = lean_ctor_get(v___x_4931_, 8);
v_isSharedCheck_4970_ = !lean_is_exclusive(v___x_4931_);
if (v_isSharedCheck_4970_ == 0)
{
v___x_4942_ = v___x_4931_;
v_isShared_4943_ = v_isSharedCheck_4970_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_snapshotTasks_4940_);
lean_inc(v_infoState_4939_);
lean_inc(v_messages_4938_);
lean_inc(v_cache_4937_);
lean_inc(v_traceState_4932_);
lean_inc(v_auxDeclNGen_4936_);
lean_inc(v_ngen_4935_);
lean_inc(v_nextMacroScope_4934_);
lean_inc(v_env_4933_);
lean_dec(v___x_4931_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4970_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
uint64_t v_tid_4944_; lean_object* v_traces_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4969_; 
v_tid_4944_ = lean_ctor_get_uint64(v_traceState_4932_, sizeof(void*)*1);
v_traces_4945_ = lean_ctor_get(v_traceState_4932_, 0);
v_isSharedCheck_4969_ = !lean_is_exclusive(v_traceState_4932_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4947_ = v_traceState_4932_;
v_isShared_4948_ = v_isSharedCheck_4969_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_traces_4945_);
lean_dec(v_traceState_4932_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4969_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v___x_4949_; double v___x_4950_; uint8_t v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4959_; 
v___x_4949_ = lean_box(0);
v___x_4950_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4951_ = 0;
v___x_4952_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4953_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4953_, 0, v_cls_4918_);
lean_ctor_set(v___x_4953_, 1, v___x_4949_);
lean_ctor_set(v___x_4953_, 2, v___x_4952_);
lean_ctor_set_float(v___x_4953_, sizeof(void*)*3, v___x_4950_);
lean_ctor_set_float(v___x_4953_, sizeof(void*)*3 + 8, v___x_4950_);
lean_ctor_set_uint8(v___x_4953_, sizeof(void*)*3 + 16, v___x_4951_);
v___x_4954_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4955_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4953_);
lean_ctor_set(v___x_4955_, 1, v_a_4927_);
lean_ctor_set(v___x_4955_, 2, v___x_4954_);
lean_inc(v_ref_4925_);
v___x_4956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4956_, 0, v_ref_4925_);
lean_ctor_set(v___x_4956_, 1, v___x_4955_);
v___x_4957_ = l_Lean_PersistentArray_push___redArg(v_traces_4945_, v___x_4956_);
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 0, v___x_4957_);
v___x_4959_ = v___x_4947_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v___x_4957_);
lean_ctor_set_uint64(v_reuseFailAlloc_4968_, sizeof(void*)*1, v_tid_4944_);
v___x_4959_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
lean_object* v___x_4961_; 
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 4, v___x_4959_);
v___x_4961_ = v___x_4942_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_env_4933_);
lean_ctor_set(v_reuseFailAlloc_4967_, 1, v_nextMacroScope_4934_);
lean_ctor_set(v_reuseFailAlloc_4967_, 2, v_ngen_4935_);
lean_ctor_set(v_reuseFailAlloc_4967_, 3, v_auxDeclNGen_4936_);
lean_ctor_set(v_reuseFailAlloc_4967_, 4, v___x_4959_);
lean_ctor_set(v_reuseFailAlloc_4967_, 5, v_cache_4937_);
lean_ctor_set(v_reuseFailAlloc_4967_, 6, v_messages_4938_);
lean_ctor_set(v_reuseFailAlloc_4967_, 7, v_infoState_4939_);
lean_ctor_set(v_reuseFailAlloc_4967_, 8, v_snapshotTasks_4940_);
v___x_4961_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4965_; 
v___x_4962_ = lean_st_ref_set(v___y_4923_, v___x_4961_);
v___x_4963_ = lean_box(0);
if (v_isShared_4930_ == 0)
{
lean_ctor_set(v___x_4929_, 0, v___x_4963_);
v___x_4965_ = v___x_4929_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4963_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg___boxed(lean_object* v_cls_4972_, lean_object* v_msg_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4972_, v_msg_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
return v_res_4979_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1(void){
_start:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4981_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__0));
v___x_4982_ = l_Lean_stringToMessageData(v___x_4981_);
return v___x_4982_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1(void){
_start:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4984_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__0));
v___x_4985_ = l_Lean_stringToMessageData(v___x_4984_);
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega(lean_object* v_p_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, uint8_t v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v___y_4998_; lean_object* v___y_4999_; lean_object* v___y_5000_; uint8_t v___y_5001_; lean_object* v___y_5002_; lean_object* v___y_5003_; lean_object* v___y_5004_; lean_object* v___y_5005_; lean_object* v___y_5006_; lean_object* v_options_5012_; uint8_t v_hasTrace_5013_; 
v_options_5012_ = lean_ctor_get(v_a_4994_, 2);
v_hasTrace_5013_ = lean_ctor_get_uint8(v_options_5012_, sizeof(void*)*1);
if (v_hasTrace_5013_ == 0)
{
v___y_4998_ = v_a_4987_;
v___y_4999_ = v_a_4988_;
v___y_5000_ = v_a_4989_;
v___y_5001_ = v_a_4990_;
v___y_5002_ = v_a_4991_;
v___y_5003_ = v_a_4992_;
v___y_5004_ = v_a_4993_;
v___y_5005_ = v_a_4994_;
v___y_5006_ = v_a_4995_;
goto v___jp_4997_;
}
else
{
lean_object* v_inheritedTraceOptions_5014_; lean_object* v_cls_5015_; lean_object* v___x_5016_; uint8_t v___x_5017_; 
v_inheritedTraceOptions_5014_ = lean_ctor_get(v_a_4994_, 13);
v_cls_5015_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_5016_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_5017_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5014_, v_options_5012_, v___x_5016_);
if (v___x_5017_ == 0)
{
v___y_4998_ = v_a_4987_;
v___y_4999_ = v_a_4988_;
v___y_5000_ = v_a_4989_;
v___y_5001_ = v_a_4990_;
v___y_5002_ = v_a_4991_;
v___y_5003_ = v_a_4992_;
v___y_5004_ = v_a_4993_;
v___y_5005_ = v_a_4994_;
v___y_5006_ = v_a_4995_;
goto v___jp_4997_;
}
else
{
lean_object* v_constraints_5018_; uint8_t v_possible_5019_; lean_object* v___x_5020_; lean_object* v___y_5022_; 
v_constraints_5018_ = lean_ctor_get(v_p_4986_, 2);
v_possible_5019_ = lean_ctor_get_uint8(v_p_4986_, sizeof(void*)*7);
v___x_5020_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1);
if (v_possible_5019_ == 0)
{
lean_object* v___x_5035_; 
v___x_5035_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
v___y_5022_ = v___x_5035_;
goto v___jp_5021_;
}
else
{
uint8_t v___x_5036_; 
v___x_5036_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_4986_);
if (v___x_5036_ == 0)
{
lean_object* v_buckets_5037_; lean_object* v___x_5038_; lean_object* v___y_5040_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; uint8_t v___x_5047_; 
v_buckets_5037_ = lean_ctor_get(v_constraints_5018_, 1);
v___x_5038_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5044_ = lean_box(0);
v___x_5045_ = lean_array_get_size(v_buckets_5037_);
v___x_5046_ = lean_unsigned_to_nat(0u);
v___x_5047_ = lean_nat_dec_lt(v___x_5046_, v___x_5045_);
if (v___x_5047_ == 0)
{
v___y_5040_ = v___x_5044_;
goto v___jp_5039_;
}
else
{
size_t v___x_5048_; size_t v___x_5049_; lean_object* v___x_5050_; 
v___x_5048_ = lean_usize_of_nat(v___x_5045_);
v___x_5049_ = ((size_t)0ULL);
v___x_5050_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5037_, v___x_5048_, v___x_5049_, v___x_5044_);
v___y_5040_ = v___x_5050_;
goto v___jp_5039_;
}
v___jp_5039_:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; 
v___x_5041_ = lean_box(0);
v___x_5042_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5040_, v___x_5041_);
v___x_5043_ = l_String_intercalate(v___x_5038_, v___x_5042_);
v___y_5022_ = v___x_5043_;
goto v___jp_5021_;
}
}
else
{
lean_object* v___x_5051_; 
v___x_5051_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_5022_ = v___x_5051_;
goto v___jp_5021_;
}
}
v___jp_5021_:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
v___x_5023_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5023_, 0, v___y_5022_);
v___x_5024_ = l_Lean_MessageData_ofFormat(v___x_5023_);
v___x_5025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5025_, 0, v___x_5020_);
lean_ctor_set(v___x_5025_, 1, v___x_5024_);
v___x_5026_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5015_, v___x_5025_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
if (lean_obj_tag(v___x_5026_) == 0)
{
lean_dec_ref_known(v___x_5026_, 1);
v___y_4998_ = v_a_4987_;
v___y_4999_ = v_a_4988_;
v___y_5000_ = v_a_4989_;
v___y_5001_ = v_a_4990_;
v___y_5002_ = v_a_4991_;
v___y_5003_ = v_a_4992_;
v___y_5004_ = v_a_4993_;
v___y_5005_ = v_a_4994_;
v___y_5006_ = v_a_4995_;
goto v___jp_4997_;
}
else
{
lean_object* v_a_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5034_; 
lean_dec_ref(v_p_4986_);
v_a_5027_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5034_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5034_ == 0)
{
v___x_5029_ = v___x_5026_;
v_isShared_5030_ = v_isSharedCheck_5034_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_a_5027_);
lean_dec(v___x_5026_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5034_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v___x_5032_; 
if (v_isShared_5030_ == 0)
{
v___x_5032_ = v___x_5029_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v_a_5027_);
v___x_5032_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
return v___x_5032_;
}
}
}
}
}
}
v___jp_4997_:
{
uint8_t v_possible_5007_; 
v_possible_5007_ = lean_ctor_get_uint8(v_p_4986_, sizeof(void*)*7);
if (v_possible_5007_ == 0)
{
lean_object* v___x_5008_; 
v___x_5008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5008_, 0, v_p_4986_);
return v___x_5008_;
}
else
{
lean_object* v___x_5009_; 
v___x_5009_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_4986_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v_a_5010_; lean_object* v___x_5011_; 
v_a_5010_ = lean_ctor_get(v___x_5009_, 0);
lean_inc(v_a_5010_);
lean_dec_ref_known(v___x_5009_, 1);
v___x_5011_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_a_5010_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
return v___x_5011_;
}
else
{
return v___x_5009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination(lean_object* v_p_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, uint8_t v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v___y_5064_; lean_object* v___y_5065_; lean_object* v___y_5066_; uint8_t v___y_5067_; lean_object* v___y_5068_; lean_object* v___y_5069_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___y_5072_; uint8_t v_possible_5076_; 
v_possible_5076_ = lean_ctor_get_uint8(v_p_5052_, sizeof(void*)*7);
if (v_possible_5076_ == 0)
{
lean_object* v___x_5077_; 
v___x_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5077_, 0, v_p_5052_);
return v___x_5077_;
}
else
{
lean_object* v_constraints_5078_; uint8_t v___x_5079_; 
v_constraints_5078_ = lean_ctor_get(v_p_5052_, 2);
v___x_5079_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_5052_);
if (v___x_5079_ == 0)
{
lean_object* v_options_5080_; uint8_t v_hasTrace_5081_; 
v_options_5080_ = lean_ctor_get(v_a_5060_, 2);
v_hasTrace_5081_ = lean_ctor_get_uint8(v_options_5080_, sizeof(void*)*1);
if (v_hasTrace_5081_ == 0)
{
v___y_5064_ = v_a_5053_;
v___y_5065_ = v_a_5054_;
v___y_5066_ = v_a_5055_;
v___y_5067_ = v_a_5056_;
v___y_5068_ = v_a_5057_;
v___y_5069_ = v_a_5058_;
v___y_5070_ = v_a_5059_;
v___y_5071_ = v_a_5060_;
v___y_5072_ = v_a_5061_;
goto v___jp_5063_;
}
else
{
lean_object* v_inheritedTraceOptions_5082_; lean_object* v_cls_5083_; lean_object* v___x_5084_; uint8_t v___x_5085_; 
v_inheritedTraceOptions_5082_ = lean_ctor_get(v_a_5060_, 13);
v_cls_5083_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_5084_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_5085_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5082_, v_options_5080_, v___x_5084_);
if (v___x_5085_ == 0)
{
v___y_5064_ = v_a_5053_;
v___y_5065_ = v_a_5054_;
v___y_5066_ = v_a_5055_;
v___y_5067_ = v_a_5056_;
v___y_5068_ = v_a_5057_;
v___y_5069_ = v_a_5058_;
v___y_5070_ = v_a_5059_;
v___y_5071_ = v_a_5060_;
v___y_5072_ = v_a_5061_;
goto v___jp_5063_;
}
else
{
lean_object* v___x_5086_; lean_object* v___y_5088_; 
v___x_5086_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1);
if (v___x_5079_ == 0)
{
lean_object* v_buckets_5101_; lean_object* v___x_5102_; lean_object* v___y_5104_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; uint8_t v___x_5111_; 
v_buckets_5101_ = lean_ctor_get(v_constraints_5078_, 1);
v___x_5102_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5108_ = lean_box(0);
v___x_5109_ = lean_array_get_size(v_buckets_5101_);
v___x_5110_ = lean_unsigned_to_nat(0u);
v___x_5111_ = lean_nat_dec_lt(v___x_5110_, v___x_5109_);
if (v___x_5111_ == 0)
{
v___y_5104_ = v___x_5108_;
goto v___jp_5103_;
}
else
{
size_t v___x_5112_; size_t v___x_5113_; lean_object* v___x_5114_; 
v___x_5112_ = lean_usize_of_nat(v___x_5109_);
v___x_5113_ = ((size_t)0ULL);
v___x_5114_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5101_, v___x_5112_, v___x_5113_, v___x_5108_);
v___y_5104_ = v___x_5114_;
goto v___jp_5103_;
}
v___jp_5103_:
{
lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5105_ = lean_box(0);
v___x_5106_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5104_, v___x_5105_);
v___x_5107_ = l_String_intercalate(v___x_5102_, v___x_5106_);
v___y_5088_ = v___x_5107_;
goto v___jp_5087_;
}
}
else
{
lean_object* v___x_5115_; 
v___x_5115_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_5088_ = v___x_5115_;
goto v___jp_5087_;
}
v___jp_5087_:
{
lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; 
v___x_5089_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5089_, 0, v___y_5088_);
v___x_5090_ = l_Lean_MessageData_ofFormat(v___x_5089_);
v___x_5091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5086_);
lean_ctor_set(v___x_5091_, 1, v___x_5090_);
v___x_5092_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5083_, v___x_5091_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_);
if (lean_obj_tag(v___x_5092_) == 0)
{
lean_dec_ref_known(v___x_5092_, 1);
v___y_5064_ = v_a_5053_;
v___y_5065_ = v_a_5054_;
v___y_5066_ = v_a_5055_;
v___y_5067_ = v_a_5056_;
v___y_5068_ = v_a_5057_;
v___y_5069_ = v_a_5058_;
v___y_5070_ = v_a_5059_;
v___y_5071_ = v_a_5060_;
v___y_5072_ = v_a_5061_;
goto v___jp_5063_;
}
else
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5100_; 
lean_dec_ref(v_p_5052_);
v_a_5093_ = lean_ctor_get(v___x_5092_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5095_ = v___x_5092_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5092_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5096_ == 0)
{
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5093_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5116_; 
v___x_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5116_, 0, v_p_5052_);
return v___x_5116_;
}
}
v___jp_5063_:
{
lean_object* v___x_5073_; 
v___x_5073_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_5052_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_object* v_a_5074_; lean_object* v___x_5075_; 
v_a_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc(v_a_5074_);
lean_dec_ref_known(v___x_5073_, 1);
v___x_5075_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_a_5074_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_);
return v___x_5075_;
}
else
{
return v___x_5073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___boxed(lean_object* v_p_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_){
_start:
{
uint8_t v_a_boxed_5128_; lean_object* v_res_5129_; 
v_a_boxed_5128_ = lean_unbox(v_a_5121_);
v_res_5129_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_p_5117_, v_a_5118_, v_a_5119_, v_a_5120_, v_a_boxed_5128_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_);
lean_dec(v_a_5126_);
lean_dec_ref(v_a_5125_);
lean_dec(v_a_5124_);
lean_dec_ref(v_a_5123_);
lean_dec(v_a_5122_);
lean_dec_ref(v_a_5120_);
lean_dec(v_a_5119_);
lean_dec(v_a_5118_);
return v_res_5129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___boxed(lean_object* v_p_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_){
_start:
{
uint8_t v_a_boxed_5141_; lean_object* v_res_5142_; 
v_a_boxed_5141_ = lean_unbox(v_a_5134_);
v_res_5142_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_p_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_boxed_5141_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
lean_dec(v_a_5139_);
lean_dec_ref(v_a_5138_);
lean_dec(v_a_5137_);
lean_dec_ref(v_a_5136_);
lean_dec(v_a_5135_);
lean_dec_ref(v_a_5133_);
lean_dec(v_a_5132_);
lean_dec(v_a_5131_);
return v_res_5142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(lean_object* v_cls_5143_, lean_object* v_msg_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, uint8_t v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_){
_start:
{
lean_object* v___x_5155_; 
v___x_5155_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5143_, v_msg_5144_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_);
return v___x_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___boxed(lean_object* v_cls_5156_, lean_object* v_msg_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_){
_start:
{
uint8_t v___y_22385__boxed_5168_; lean_object* v_res_5169_; 
v___y_22385__boxed_5168_ = lean_unbox(v___y_5161_);
v_res_5169_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(v_cls_5156_, v_msg_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_22385__boxed_5168_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_);
lean_dec(v___y_5166_);
lean_dec_ref(v___y_5165_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5160_);
lean_dec(v___y_5159_);
lean_dec(v___y_5158_);
return v_res_5169_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(uint8_t builtin);
lean_object* runtime_initialize_Lean_OrderLevel(uint8_t builtin);
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
res = runtime_initialize_Lean_OrderLevel(builtin);
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
lean_object* initialize_Lean_OrderLevel(uint8_t builtin);
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
res = initialize_Lean_OrderLevel(builtin);
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
