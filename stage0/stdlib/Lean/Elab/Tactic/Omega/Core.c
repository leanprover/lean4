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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__value)} };
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
lean_inc_ref(v___y_196_);
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
v___x_488_ = l_String_instDecidableLtRaw___aux__1(v_basePos_483_, v___x_486_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString(lean_object* v_s_668_, lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
switch(lean_obj_tag(v_x_670_))
{
case 0:
{
lean_object* v_i_671_; lean_object* v_lowerBound_672_; lean_object* v_upperBound_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___y_678_; lean_object* v___y_685_; lean_object* v___y_686_; 
v_i_671_ = lean_ctor_get(v_x_670_, 2);
lean_inc(v_i_671_);
lean_dec_ref(v_x_670_);
v_lowerBound_672_ = lean_ctor_get(v_s_668_, 0);
lean_inc(v_lowerBound_672_);
v_upperBound_673_ = lean_ctor_get(v_s_668_, 1);
lean_inc(v_upperBound_673_);
lean_dec_ref(v_s_668_);
v___x_674_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_669_);
lean_dec(v_x_669_);
v___x_675_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_676_ = lean_string_append(v___x_674_, v___x_675_);
if (lean_obj_tag(v_lowerBound_672_) == 0)
{
if (lean_obj_tag(v_upperBound_673_) == 0)
{
lean_object* v___x_690_; 
v___x_690_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_678_ = v___x_690_;
goto v___jp_677_;
}
else
{
lean_object* v_val_691_; lean_object* v___x_692_; lean_object* v___y_694_; lean_object* v_intZero_698_; uint8_t v_isNeg_699_; 
v_val_691_ = lean_ctor_get(v_upperBound_673_, 0);
lean_inc(v_val_691_);
lean_dec_ref(v_upperBound_673_);
v___x_692_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_698_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_699_ = lean_int_dec_lt(v_val_691_, v_intZero_698_);
if (v_isNeg_699_ == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; 
v_a_700_ = lean_nat_abs(v_val_691_);
lean_dec(v_val_691_);
v___x_701_ = l_Nat_reprFast(v_a_700_);
v___y_694_ = v___x_701_;
goto v___jp_693_;
}
else
{
lean_object* v_abs_702_; lean_object* v_one_703_; lean_object* v_a_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_abs_702_ = lean_nat_abs(v_val_691_);
lean_dec(v_val_691_);
v_one_703_ = lean_unsigned_to_nat(1u);
v_a_704_ = lean_nat_sub(v_abs_702_, v_one_703_);
lean_dec(v_abs_702_);
v___x_705_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_706_ = lean_nat_add(v_a_704_, v_one_703_);
lean_dec(v_a_704_);
v___x_707_ = l_Nat_reprFast(v___x_706_);
v___x_708_ = lean_string_append(v___x_705_, v___x_707_);
lean_dec_ref(v___x_707_);
v___y_694_ = v___x_708_;
goto v___jp_693_;
}
v___jp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_string_append(v___x_692_, v___y_694_);
lean_dec_ref(v___y_694_);
v___x_696_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_697_ = lean_string_append(v___x_695_, v___x_696_);
v___y_678_ = v___x_697_;
goto v___jp_677_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_673_) == 0)
{
lean_object* v_val_709_; lean_object* v___x_710_; lean_object* v___y_712_; lean_object* v_intZero_716_; uint8_t v_isNeg_717_; 
v_val_709_ = lean_ctor_get(v_lowerBound_672_, 0);
lean_inc(v_val_709_);
lean_dec_ref(v_lowerBound_672_);
v___x_710_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_716_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_717_ = lean_int_dec_lt(v_val_709_, v_intZero_716_);
if (v_isNeg_717_ == 0)
{
lean_object* v_a_718_; lean_object* v___x_719_; 
v_a_718_ = lean_nat_abs(v_val_709_);
lean_dec(v_val_709_);
v___x_719_ = l_Nat_reprFast(v_a_718_);
v___y_712_ = v___x_719_;
goto v___jp_711_;
}
else
{
lean_object* v_abs_720_; lean_object* v_one_721_; lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_abs_720_ = lean_nat_abs(v_val_709_);
lean_dec(v_val_709_);
v_one_721_ = lean_unsigned_to_nat(1u);
v_a_722_ = lean_nat_sub(v_abs_720_, v_one_721_);
lean_dec(v_abs_720_);
v___x_723_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_724_ = lean_nat_add(v_a_722_, v_one_721_);
lean_dec(v_a_722_);
v___x_725_ = l_Nat_reprFast(v___x_724_);
v___x_726_ = lean_string_append(v___x_723_, v___x_725_);
lean_dec_ref(v___x_725_);
v___y_712_ = v___x_726_;
goto v___jp_711_;
}
v___jp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_713_ = lean_string_append(v___x_710_, v___y_712_);
lean_dec_ref(v___y_712_);
v___x_714_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_715_ = lean_string_append(v___x_713_, v___x_714_);
v___y_678_ = v___x_715_;
goto v___jp_677_;
}
}
else
{
lean_object* v_val_727_; lean_object* v_val_728_; uint8_t v___x_729_; 
v_val_727_ = lean_ctor_get(v_lowerBound_672_, 0);
lean_inc(v_val_727_);
lean_dec_ref(v_lowerBound_672_);
v_val_728_ = lean_ctor_get(v_upperBound_673_, 0);
lean_inc(v_val_728_);
lean_dec_ref(v_upperBound_673_);
v___x_729_ = lean_int_dec_lt(v_val_728_, v_val_727_);
if (v___x_729_ == 0)
{
uint8_t v___x_730_; 
v___x_730_ = lean_int_dec_eq(v_val_727_, v_val_728_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___y_733_; lean_object* v_intZero_748_; uint8_t v_isNeg_749_; 
v___x_731_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_748_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_749_ = lean_int_dec_lt(v_val_727_, v_intZero_748_);
if (v_isNeg_749_ == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; 
v_a_750_ = lean_nat_abs(v_val_727_);
lean_dec(v_val_727_);
v___x_751_ = l_Nat_reprFast(v_a_750_);
v___y_733_ = v___x_751_;
goto v___jp_732_;
}
else
{
lean_object* v_abs_752_; lean_object* v_one_753_; lean_object* v_a_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_abs_752_ = lean_nat_abs(v_val_727_);
lean_dec(v_val_727_);
v_one_753_ = lean_unsigned_to_nat(1u);
v_a_754_ = lean_nat_sub(v_abs_752_, v_one_753_);
lean_dec(v_abs_752_);
v___x_755_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_756_ = lean_nat_add(v_a_754_, v_one_753_);
lean_dec(v_a_754_);
v___x_757_ = l_Nat_reprFast(v___x_756_);
v___x_758_ = lean_string_append(v___x_755_, v___x_757_);
lean_dec_ref(v___x_757_);
v___y_733_ = v___x_758_;
goto v___jp_732_;
}
v___jp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_intZero_737_; uint8_t v_isNeg_738_; 
v___x_734_ = lean_string_append(v___x_731_, v___y_733_);
lean_dec_ref(v___y_733_);
v___x_735_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_736_ = lean_string_append(v___x_734_, v___x_735_);
v_intZero_737_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_738_ = lean_int_dec_lt(v_val_728_, v_intZero_737_);
if (v_isNeg_738_ == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_nat_abs(v_val_728_);
lean_dec(v_val_728_);
v___x_740_ = l_Nat_reprFast(v_a_739_);
v___y_685_ = v___x_736_;
v___y_686_ = v___x_740_;
goto v___jp_684_;
}
else
{
lean_object* v_abs_741_; lean_object* v_one_742_; lean_object* v_a_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_abs_741_ = lean_nat_abs(v_val_728_);
lean_dec(v_val_728_);
v_one_742_ = lean_unsigned_to_nat(1u);
v_a_743_ = lean_nat_sub(v_abs_741_, v_one_742_);
lean_dec(v_abs_741_);
v___x_744_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_745_ = lean_nat_add(v_a_743_, v_one_742_);
lean_dec(v_a_743_);
v___x_746_ = l_Nat_reprFast(v___x_745_);
v___x_747_ = lean_string_append(v___x_744_, v___x_746_);
lean_dec_ref(v___x_746_);
v___y_685_ = v___x_736_;
v___y_686_ = v___x_747_;
goto v___jp_684_;
}
}
}
else
{
lean_object* v___x_759_; lean_object* v___y_761_; lean_object* v_intZero_765_; uint8_t v_isNeg_766_; 
lean_dec(v_val_728_);
v___x_759_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_765_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_766_ = lean_int_dec_lt(v_val_727_, v_intZero_765_);
if (v_isNeg_766_ == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; 
v_a_767_ = lean_nat_abs(v_val_727_);
lean_dec(v_val_727_);
v___x_768_ = l_Nat_reprFast(v_a_767_);
v___y_761_ = v___x_768_;
goto v___jp_760_;
}
else
{
lean_object* v_abs_769_; lean_object* v_one_770_; lean_object* v_a_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_abs_769_ = lean_nat_abs(v_val_727_);
lean_dec(v_val_727_);
v_one_770_ = lean_unsigned_to_nat(1u);
v_a_771_ = lean_nat_sub(v_abs_769_, v_one_770_);
lean_dec(v_abs_769_);
v___x_772_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_773_ = lean_nat_add(v_a_771_, v_one_770_);
lean_dec(v_a_771_);
v___x_774_ = l_Nat_reprFast(v___x_773_);
v___x_775_ = lean_string_append(v___x_772_, v___x_774_);
lean_dec_ref(v___x_774_);
v___y_761_ = v___x_775_;
goto v___jp_760_;
}
v___jp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_string_append(v___x_759_, v___y_761_);
lean_dec_ref(v___y_761_);
v___x_763_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_764_ = lean_string_append(v___x_762_, v___x_763_);
v___y_678_ = v___x_764_;
goto v___jp_677_;
}
}
}
else
{
lean_object* v___x_776_; 
lean_dec(v_val_728_);
lean_dec(v_val_727_);
v___x_776_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_678_ = v___x_776_;
goto v___jp_677_;
}
}
}
v___jp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_679_ = lean_string_append(v___x_676_, v___y_678_);
lean_dec_ref(v___y_678_);
v___x_680_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__1));
v___x_681_ = lean_string_append(v___x_679_, v___x_680_);
v___x_682_ = l_Nat_reprFast(v_i_671_);
v___x_683_ = lean_string_append(v___x_681_, v___x_682_);
lean_dec_ref(v___x_682_);
return v___x_683_;
}
v___jp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_string_append(v___y_685_, v___y_686_);
lean_dec_ref(v___y_686_);
v___x_688_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_689_ = lean_string_append(v___x_687_, v___x_688_);
v___y_678_ = v___x_689_;
goto v___jp_677_;
}
}
case 1:
{
lean_object* v_s_777_; lean_object* v_c_778_; lean_object* v_j_779_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; uint8_t v___y_837_; uint8_t v___x_900_; 
v_s_777_ = lean_ctor_get(v_x_670_, 0);
lean_inc_ref(v_s_777_);
v_c_778_ = lean_ctor_get(v_x_670_, 1);
lean_inc(v_c_778_);
v_j_779_ = lean_ctor_get(v_x_670_, 2);
lean_inc_ref(v_j_779_);
lean_dec_ref(v_x_670_);
v___x_900_ = l_Lean_Omega_instBEqConstraint_beq(v_s_668_, v_s_777_);
if (v___x_900_ == 0)
{
v___y_837_ = v___x_900_;
goto v___jp_836_;
}
else
{
uint8_t v___x_901_; 
v___x_901_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_669_, v_c_778_);
v___y_837_ = v___x_901_;
goto v___jp_836_;
}
v___jp_780_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_783_ = lean_string_append(v___y_781_, v___y_782_);
lean_dec_ref(v___y_782_);
v___x_784_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9));
v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
v___x_786_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_777_, v_c_778_, v_j_779_);
v___x_787_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_786_);
v___x_788_ = lean_string_append(v___x_785_, v___x_787_);
lean_dec_ref(v___x_787_);
return v___x_788_;
}
v___jp_789_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_inc_ref(v___y_790_);
v___x_793_ = lean_string_append(v___y_790_, v___y_792_);
lean_dec_ref(v___y_792_);
v___x_794_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_795_ = lean_string_append(v___x_793_, v___x_794_);
v___y_781_ = v___y_791_;
v___y_782_ = v___x_795_;
goto v___jp_780_;
}
v___jp_796_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_inc_ref(v___y_797_);
v___x_800_ = lean_string_append(v___y_797_, v___y_799_);
lean_dec_ref(v___y_799_);
v___x_801_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_802_ = lean_string_append(v___x_800_, v___x_801_);
v___y_781_ = v___y_798_;
v___y_782_ = v___x_802_;
goto v___jp_780_;
}
v___jp_803_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_807_ = lean_string_append(v___y_805_, v___y_806_);
lean_dec_ref(v___y_806_);
v___x_808_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_809_ = lean_string_append(v___x_807_, v___x_808_);
v___y_781_ = v___y_804_;
v___y_782_ = v___x_809_;
goto v___jp_780_;
}
v___jp_810_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_intZero_818_; uint8_t v_isNeg_819_; 
lean_inc_ref(v___y_812_);
v___x_815_ = lean_string_append(v___y_812_, v___y_814_);
lean_dec_ref(v___y_814_);
v___x_816_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_817_ = lean_string_append(v___x_815_, v___x_816_);
v_intZero_818_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_819_ = lean_int_dec_lt(v___y_811_, v_intZero_818_);
if (v_isNeg_819_ == 0)
{
lean_object* v_a_820_; lean_object* v___x_821_; 
v_a_820_ = lean_nat_abs(v___y_811_);
lean_dec(v___y_811_);
v___x_821_ = l_Nat_reprFast(v_a_820_);
v___y_804_ = v___y_813_;
v___y_805_ = v___x_817_;
v___y_806_ = v___x_821_;
goto v___jp_803_;
}
else
{
lean_object* v_abs_822_; lean_object* v_one_823_; lean_object* v_a_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_abs_822_ = lean_nat_abs(v___y_811_);
lean_dec(v___y_811_);
v_one_823_ = lean_unsigned_to_nat(1u);
v_a_824_ = lean_nat_sub(v_abs_822_, v_one_823_);
lean_dec(v_abs_822_);
v___x_825_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_826_ = lean_nat_add(v_a_824_, v_one_823_);
lean_dec(v_a_824_);
v___x_827_ = l_Nat_reprFast(v___x_826_);
v___x_828_ = lean_string_append(v___x_825_, v___x_827_);
lean_dec_ref(v___x_827_);
v___y_804_ = v___y_813_;
v___y_805_ = v___x_817_;
v___y_806_ = v___x_828_;
goto v___jp_803_;
}
}
v___jp_829_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_inc_ref(v___y_831_);
v___x_833_ = lean_string_append(v___y_831_, v___y_832_);
lean_dec_ref(v___y_832_);
v___x_834_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_835_ = lean_string_append(v___x_833_, v___x_834_);
v___y_781_ = v___y_830_;
v___y_782_ = v___x_835_;
goto v___jp_780_;
}
v___jp_836_:
{
if (v___y_837_ == 0)
{
lean_object* v_lowerBound_838_; lean_object* v_upperBound_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_lowerBound_838_ = lean_ctor_get(v_s_668_, 0);
lean_inc(v_lowerBound_838_);
v_upperBound_839_ = lean_ctor_get(v_s_668_, 1);
lean_inc(v_upperBound_839_);
lean_dec_ref(v_s_668_);
v___x_840_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_669_);
lean_dec(v_x_669_);
v___x_841_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_842_ = lean_string_append(v___x_840_, v___x_841_);
if (lean_obj_tag(v_lowerBound_838_) == 0)
{
if (lean_obj_tag(v_upperBound_839_) == 0)
{
lean_object* v___x_843_; 
v___x_843_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_781_ = v___x_842_;
v___y_782_ = v___x_843_;
goto v___jp_780_;
}
else
{
lean_object* v_val_844_; lean_object* v___x_845_; lean_object* v_intZero_846_; uint8_t v_isNeg_847_; 
v_val_844_ = lean_ctor_get(v_upperBound_839_, 0);
lean_inc(v_val_844_);
lean_dec_ref(v_upperBound_839_);
v___x_845_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_846_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_847_ = lean_int_dec_lt(v_val_844_, v_intZero_846_);
if (v_isNeg_847_ == 0)
{
lean_object* v_a_848_; lean_object* v___x_849_; 
v_a_848_ = lean_nat_abs(v_val_844_);
lean_dec(v_val_844_);
v___x_849_ = l_Nat_reprFast(v_a_848_);
v___y_790_ = v___x_845_;
v___y_791_ = v___x_842_;
v___y_792_ = v___x_849_;
goto v___jp_789_;
}
else
{
lean_object* v_abs_850_; lean_object* v_one_851_; lean_object* v_a_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_abs_850_ = lean_nat_abs(v_val_844_);
lean_dec(v_val_844_);
v_one_851_ = lean_unsigned_to_nat(1u);
v_a_852_ = lean_nat_sub(v_abs_850_, v_one_851_);
lean_dec(v_abs_850_);
v___x_853_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_854_ = lean_nat_add(v_a_852_, v_one_851_);
lean_dec(v_a_852_);
v___x_855_ = l_Nat_reprFast(v___x_854_);
v___x_856_ = lean_string_append(v___x_853_, v___x_855_);
lean_dec_ref(v___x_855_);
v___y_790_ = v___x_845_;
v___y_791_ = v___x_842_;
v___y_792_ = v___x_856_;
goto v___jp_789_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_839_) == 0)
{
lean_object* v_val_857_; lean_object* v___x_858_; lean_object* v_intZero_859_; uint8_t v_isNeg_860_; 
v_val_857_ = lean_ctor_get(v_lowerBound_838_, 0);
lean_inc(v_val_857_);
lean_dec_ref(v_lowerBound_838_);
v___x_858_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_859_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_860_ = lean_int_dec_lt(v_val_857_, v_intZero_859_);
if (v_isNeg_860_ == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; 
v_a_861_ = lean_nat_abs(v_val_857_);
lean_dec(v_val_857_);
v___x_862_ = l_Nat_reprFast(v_a_861_);
v___y_797_ = v___x_858_;
v___y_798_ = v___x_842_;
v___y_799_ = v___x_862_;
goto v___jp_796_;
}
else
{
lean_object* v_abs_863_; lean_object* v_one_864_; lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_abs_863_ = lean_nat_abs(v_val_857_);
lean_dec(v_val_857_);
v_one_864_ = lean_unsigned_to_nat(1u);
v_a_865_ = lean_nat_sub(v_abs_863_, v_one_864_);
lean_dec(v_abs_863_);
v___x_866_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_867_ = lean_nat_add(v_a_865_, v_one_864_);
lean_dec(v_a_865_);
v___x_868_ = l_Nat_reprFast(v___x_867_);
v___x_869_ = lean_string_append(v___x_866_, v___x_868_);
lean_dec_ref(v___x_868_);
v___y_797_ = v___x_858_;
v___y_798_ = v___x_842_;
v___y_799_ = v___x_869_;
goto v___jp_796_;
}
}
else
{
lean_object* v_val_870_; lean_object* v_val_871_; uint8_t v___x_872_; 
v_val_870_ = lean_ctor_get(v_lowerBound_838_, 0);
lean_inc(v_val_870_);
lean_dec_ref(v_lowerBound_838_);
v_val_871_ = lean_ctor_get(v_upperBound_839_, 0);
lean_inc(v_val_871_);
lean_dec_ref(v_upperBound_839_);
v___x_872_ = lean_int_dec_lt(v_val_871_, v_val_870_);
if (v___x_872_ == 0)
{
uint8_t v___x_873_; 
v___x_873_ = lean_int_dec_eq(v_val_870_, v_val_871_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v_intZero_875_; uint8_t v_isNeg_876_; 
v___x_874_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_875_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_876_ = lean_int_dec_lt(v_val_870_, v_intZero_875_);
if (v_isNeg_876_ == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; 
v_a_877_ = lean_nat_abs(v_val_870_);
lean_dec(v_val_870_);
v___x_878_ = l_Nat_reprFast(v_a_877_);
v___y_811_ = v_val_871_;
v___y_812_ = v___x_874_;
v___y_813_ = v___x_842_;
v___y_814_ = v___x_878_;
goto v___jp_810_;
}
else
{
lean_object* v_abs_879_; lean_object* v_one_880_; lean_object* v_a_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_abs_879_ = lean_nat_abs(v_val_870_);
lean_dec(v_val_870_);
v_one_880_ = lean_unsigned_to_nat(1u);
v_a_881_ = lean_nat_sub(v_abs_879_, v_one_880_);
lean_dec(v_abs_879_);
v___x_882_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_883_ = lean_nat_add(v_a_881_, v_one_880_);
lean_dec(v_a_881_);
v___x_884_ = l_Nat_reprFast(v___x_883_);
v___x_885_ = lean_string_append(v___x_882_, v___x_884_);
lean_dec_ref(v___x_884_);
v___y_811_ = v_val_871_;
v___y_812_ = v___x_874_;
v___y_813_ = v___x_842_;
v___y_814_ = v___x_885_;
goto v___jp_810_;
}
}
else
{
lean_object* v___x_886_; lean_object* v_intZero_887_; uint8_t v_isNeg_888_; 
lean_dec(v_val_871_);
v___x_886_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_887_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_888_ = lean_int_dec_lt(v_val_870_, v_intZero_887_);
if (v_isNeg_888_ == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; 
v_a_889_ = lean_nat_abs(v_val_870_);
lean_dec(v_val_870_);
v___x_890_ = l_Nat_reprFast(v_a_889_);
v___y_830_ = v___x_842_;
v___y_831_ = v___x_886_;
v___y_832_ = v___x_890_;
goto v___jp_829_;
}
else
{
lean_object* v_abs_891_; lean_object* v_one_892_; lean_object* v_a_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_abs_891_ = lean_nat_abs(v_val_870_);
lean_dec(v_val_870_);
v_one_892_ = lean_unsigned_to_nat(1u);
v_a_893_ = lean_nat_sub(v_abs_891_, v_one_892_);
lean_dec(v_abs_891_);
v___x_894_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_895_ = lean_nat_add(v_a_893_, v_one_892_);
lean_dec(v_a_893_);
v___x_896_ = l_Nat_reprFast(v___x_895_);
v___x_897_ = lean_string_append(v___x_894_, v___x_896_);
lean_dec_ref(v___x_896_);
v___y_830_ = v___x_842_;
v___y_831_ = v___x_886_;
v___y_832_ = v___x_897_;
goto v___jp_829_;
}
}
}
else
{
lean_object* v___x_898_; 
lean_dec(v_val_871_);
lean_dec(v_val_870_);
v___x_898_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_781_ = v___x_842_;
v___y_782_ = v___x_898_;
goto v___jp_780_;
}
}
}
}
else
{
lean_dec(v_x_669_);
lean_dec_ref(v_s_668_);
v_s_668_ = v_s_777_;
v_x_669_ = v_c_778_;
v_x_670_ = v_j_779_;
goto _start;
}
}
}
case 2:
{
lean_object* v_s_902_; lean_object* v_t_903_; lean_object* v_j_904_; lean_object* v_k_905_; lean_object* v_lowerBound_906_; lean_object* v_upperBound_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___y_912_; lean_object* v___y_925_; lean_object* v___y_926_; 
v_s_902_ = lean_ctor_get(v_x_670_, 0);
lean_inc_ref(v_s_902_);
v_t_903_ = lean_ctor_get(v_x_670_, 1);
lean_inc_ref(v_t_903_);
v_j_904_ = lean_ctor_get(v_x_670_, 3);
lean_inc_ref(v_j_904_);
v_k_905_ = lean_ctor_get(v_x_670_, 4);
lean_inc_ref(v_k_905_);
lean_dec_ref(v_x_670_);
v_lowerBound_906_ = lean_ctor_get(v_s_668_, 0);
lean_inc(v_lowerBound_906_);
v_upperBound_907_ = lean_ctor_get(v_s_668_, 1);
lean_inc(v_upperBound_907_);
lean_dec_ref(v_s_668_);
v___x_908_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_669_);
v___x_909_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_910_ = lean_string_append(v___x_908_, v___x_909_);
if (lean_obj_tag(v_lowerBound_906_) == 0)
{
if (lean_obj_tag(v_upperBound_907_) == 0)
{
lean_object* v___x_930_; 
v___x_930_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_912_ = v___x_930_;
goto v___jp_911_;
}
else
{
lean_object* v_val_931_; lean_object* v___x_932_; lean_object* v___y_934_; lean_object* v_intZero_938_; uint8_t v_isNeg_939_; 
v_val_931_ = lean_ctor_get(v_upperBound_907_, 0);
lean_inc(v_val_931_);
lean_dec_ref(v_upperBound_907_);
v___x_932_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_938_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_939_ = lean_int_dec_lt(v_val_931_, v_intZero_938_);
if (v_isNeg_939_ == 0)
{
lean_object* v_a_940_; lean_object* v___x_941_; 
v_a_940_ = lean_nat_abs(v_val_931_);
lean_dec(v_val_931_);
v___x_941_ = l_Nat_reprFast(v_a_940_);
v___y_934_ = v___x_941_;
goto v___jp_933_;
}
else
{
lean_object* v_abs_942_; lean_object* v_one_943_; lean_object* v_a_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_abs_942_ = lean_nat_abs(v_val_931_);
lean_dec(v_val_931_);
v_one_943_ = lean_unsigned_to_nat(1u);
v_a_944_ = lean_nat_sub(v_abs_942_, v_one_943_);
lean_dec(v_abs_942_);
v___x_945_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_946_ = lean_nat_add(v_a_944_, v_one_943_);
lean_dec(v_a_944_);
v___x_947_ = l_Nat_reprFast(v___x_946_);
v___x_948_ = lean_string_append(v___x_945_, v___x_947_);
lean_dec_ref(v___x_947_);
v___y_934_ = v___x_948_;
goto v___jp_933_;
}
v___jp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_string_append(v___x_932_, v___y_934_);
lean_dec_ref(v___y_934_);
v___x_936_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_937_ = lean_string_append(v___x_935_, v___x_936_);
v___y_912_ = v___x_937_;
goto v___jp_911_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_907_) == 0)
{
lean_object* v_val_949_; lean_object* v___x_950_; lean_object* v___y_952_; lean_object* v_intZero_956_; uint8_t v_isNeg_957_; 
v_val_949_ = lean_ctor_get(v_lowerBound_906_, 0);
lean_inc(v_val_949_);
lean_dec_ref(v_lowerBound_906_);
v___x_950_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_956_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_957_ = lean_int_dec_lt(v_val_949_, v_intZero_956_);
if (v_isNeg_957_ == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; 
v_a_958_ = lean_nat_abs(v_val_949_);
lean_dec(v_val_949_);
v___x_959_ = l_Nat_reprFast(v_a_958_);
v___y_952_ = v___x_959_;
goto v___jp_951_;
}
else
{
lean_object* v_abs_960_; lean_object* v_one_961_; lean_object* v_a_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_abs_960_ = lean_nat_abs(v_val_949_);
lean_dec(v_val_949_);
v_one_961_ = lean_unsigned_to_nat(1u);
v_a_962_ = lean_nat_sub(v_abs_960_, v_one_961_);
lean_dec(v_abs_960_);
v___x_963_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_964_ = lean_nat_add(v_a_962_, v_one_961_);
lean_dec(v_a_962_);
v___x_965_ = l_Nat_reprFast(v___x_964_);
v___x_966_ = lean_string_append(v___x_963_, v___x_965_);
lean_dec_ref(v___x_965_);
v___y_952_ = v___x_966_;
goto v___jp_951_;
}
v___jp_951_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = lean_string_append(v___x_950_, v___y_952_);
lean_dec_ref(v___y_952_);
v___x_954_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_955_ = lean_string_append(v___x_953_, v___x_954_);
v___y_912_ = v___x_955_;
goto v___jp_911_;
}
}
else
{
lean_object* v_val_967_; lean_object* v_val_968_; uint8_t v___x_969_; 
v_val_967_ = lean_ctor_get(v_lowerBound_906_, 0);
lean_inc(v_val_967_);
lean_dec_ref(v_lowerBound_906_);
v_val_968_ = lean_ctor_get(v_upperBound_907_, 0);
lean_inc(v_val_968_);
lean_dec_ref(v_upperBound_907_);
v___x_969_ = lean_int_dec_lt(v_val_968_, v_val_967_);
if (v___x_969_ == 0)
{
uint8_t v___x_970_; 
v___x_970_ = lean_int_dec_eq(v_val_967_, v_val_968_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___y_973_; lean_object* v_intZero_988_; uint8_t v_isNeg_989_; 
v___x_971_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_988_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_989_ = lean_int_dec_lt(v_val_967_, v_intZero_988_);
if (v_isNeg_989_ == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; 
v_a_990_ = lean_nat_abs(v_val_967_);
lean_dec(v_val_967_);
v___x_991_ = l_Nat_reprFast(v_a_990_);
v___y_973_ = v___x_991_;
goto v___jp_972_;
}
else
{
lean_object* v_abs_992_; lean_object* v_one_993_; lean_object* v_a_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_abs_992_ = lean_nat_abs(v_val_967_);
lean_dec(v_val_967_);
v_one_993_ = lean_unsigned_to_nat(1u);
v_a_994_ = lean_nat_sub(v_abs_992_, v_one_993_);
lean_dec(v_abs_992_);
v___x_995_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_996_ = lean_nat_add(v_a_994_, v_one_993_);
lean_dec(v_a_994_);
v___x_997_ = l_Nat_reprFast(v___x_996_);
v___x_998_ = lean_string_append(v___x_995_, v___x_997_);
lean_dec_ref(v___x_997_);
v___y_973_ = v___x_998_;
goto v___jp_972_;
}
v___jp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_intZero_977_; uint8_t v_isNeg_978_; 
v___x_974_ = lean_string_append(v___x_971_, v___y_973_);
lean_dec_ref(v___y_973_);
v___x_975_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_976_ = lean_string_append(v___x_974_, v___x_975_);
v_intZero_977_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_978_ = lean_int_dec_lt(v_val_968_, v_intZero_977_);
if (v_isNeg_978_ == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; 
v_a_979_ = lean_nat_abs(v_val_968_);
lean_dec(v_val_968_);
v___x_980_ = l_Nat_reprFast(v_a_979_);
v___y_925_ = v___x_976_;
v___y_926_ = v___x_980_;
goto v___jp_924_;
}
else
{
lean_object* v_abs_981_; lean_object* v_one_982_; lean_object* v_a_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_abs_981_ = lean_nat_abs(v_val_968_);
lean_dec(v_val_968_);
v_one_982_ = lean_unsigned_to_nat(1u);
v_a_983_ = lean_nat_sub(v_abs_981_, v_one_982_);
lean_dec(v_abs_981_);
v___x_984_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_985_ = lean_nat_add(v_a_983_, v_one_982_);
lean_dec(v_a_983_);
v___x_986_ = l_Nat_reprFast(v___x_985_);
v___x_987_ = lean_string_append(v___x_984_, v___x_986_);
lean_dec_ref(v___x_986_);
v___y_925_ = v___x_976_;
v___y_926_ = v___x_987_;
goto v___jp_924_;
}
}
}
else
{
lean_object* v___x_999_; lean_object* v___y_1001_; lean_object* v_intZero_1005_; uint8_t v_isNeg_1006_; 
lean_dec(v_val_968_);
v___x_999_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1005_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1006_ = lean_int_dec_lt(v_val_967_, v_intZero_1005_);
if (v_isNeg_1006_ == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; 
v_a_1007_ = lean_nat_abs(v_val_967_);
lean_dec(v_val_967_);
v___x_1008_ = l_Nat_reprFast(v_a_1007_);
v___y_1001_ = v___x_1008_;
goto v___jp_1000_;
}
else
{
lean_object* v_abs_1009_; lean_object* v_one_1010_; lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_abs_1009_ = lean_nat_abs(v_val_967_);
lean_dec(v_val_967_);
v_one_1010_ = lean_unsigned_to_nat(1u);
v_a_1011_ = lean_nat_sub(v_abs_1009_, v_one_1010_);
lean_dec(v_abs_1009_);
v___x_1012_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1013_ = lean_nat_add(v_a_1011_, v_one_1010_);
lean_dec(v_a_1011_);
v___x_1014_ = l_Nat_reprFast(v___x_1013_);
v___x_1015_ = lean_string_append(v___x_1012_, v___x_1014_);
lean_dec_ref(v___x_1014_);
v___y_1001_ = v___x_1015_;
goto v___jp_1000_;
}
v___jp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_string_append(v___x_999_, v___y_1001_);
lean_dec_ref(v___y_1001_);
v___x_1003_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1004_ = lean_string_append(v___x_1002_, v___x_1003_);
v___y_912_ = v___x_1004_;
goto v___jp_911_;
}
}
}
else
{
lean_object* v___x_1016_; 
lean_dec(v_val_968_);
lean_dec(v_val_967_);
v___x_1016_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_912_ = v___x_1016_;
goto v___jp_911_;
}
}
}
v___jp_911_:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_913_ = lean_string_append(v___x_910_, v___y_912_);
lean_dec_ref(v___y_912_);
v___x_914_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__10));
v___x_915_ = lean_string_append(v___x_913_, v___x_914_);
lean_inc(v_x_669_);
v___x_916_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_902_, v_x_669_, v_j_904_);
v___x_917_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_916_);
v___x_918_ = lean_string_append(v___x_915_, v___x_917_);
lean_dec_ref(v___x_917_);
v___x_919_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_920_ = lean_string_append(v___x_918_, v___x_919_);
v___x_921_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_903_, v_x_669_, v_k_905_);
v___x_922_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_921_);
v___x_923_ = lean_string_append(v___x_920_, v___x_922_);
lean_dec_ref(v___x_922_);
return v___x_923_;
}
v___jp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_string_append(v___y_925_, v___y_926_);
lean_dec_ref(v___y_926_);
v___x_928_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_929_ = lean_string_append(v___x_927_, v___x_928_);
v___y_912_ = v___x_929_;
goto v___jp_911_;
}
}
case 3:
{
lean_object* v_s_1017_; lean_object* v_t_1018_; lean_object* v_x_1019_; lean_object* v_y_1020_; lean_object* v_a_1021_; lean_object* v_j_1022_; lean_object* v_b_1023_; lean_object* v_k_1024_; lean_object* v_lowerBound_1025_; lean_object* v_upperBound_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___y_1031_; lean_object* v___y_1052_; lean_object* v___y_1053_; 
v_s_1017_ = lean_ctor_get(v_x_670_, 0);
lean_inc_ref(v_s_1017_);
v_t_1018_ = lean_ctor_get(v_x_670_, 1);
lean_inc_ref(v_t_1018_);
v_x_1019_ = lean_ctor_get(v_x_670_, 2);
lean_inc(v_x_1019_);
v_y_1020_ = lean_ctor_get(v_x_670_, 3);
lean_inc(v_y_1020_);
v_a_1021_ = lean_ctor_get(v_x_670_, 4);
lean_inc(v_a_1021_);
v_j_1022_ = lean_ctor_get(v_x_670_, 5);
lean_inc_ref(v_j_1022_);
v_b_1023_ = lean_ctor_get(v_x_670_, 6);
lean_inc(v_b_1023_);
v_k_1024_ = lean_ctor_get(v_x_670_, 7);
lean_inc_ref(v_k_1024_);
lean_dec_ref(v_x_670_);
v_lowerBound_1025_ = lean_ctor_get(v_s_668_, 0);
lean_inc(v_lowerBound_1025_);
v_upperBound_1026_ = lean_ctor_get(v_s_668_, 1);
lean_inc(v_upperBound_1026_);
lean_dec_ref(v_s_668_);
v___x_1027_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_669_);
lean_dec(v_x_669_);
v___x_1028_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1029_ = lean_string_append(v___x_1027_, v___x_1028_);
if (lean_obj_tag(v_lowerBound_1025_) == 0)
{
if (lean_obj_tag(v_upperBound_1026_) == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1031_ = v___x_1057_;
goto v___jp_1030_;
}
else
{
lean_object* v_val_1058_; lean_object* v___x_1059_; lean_object* v___y_1061_; lean_object* v_intZero_1065_; uint8_t v_isNeg_1066_; 
v_val_1058_ = lean_ctor_get(v_upperBound_1026_, 0);
lean_inc(v_val_1058_);
lean_dec_ref(v_upperBound_1026_);
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1065_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1066_ = lean_int_dec_lt(v_val_1058_, v_intZero_1065_);
if (v_isNeg_1066_ == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; 
v_a_1067_ = lean_nat_abs(v_val_1058_);
lean_dec(v_val_1058_);
v___x_1068_ = l_Nat_reprFast(v_a_1067_);
v___y_1061_ = v___x_1068_;
goto v___jp_1060_;
}
else
{
lean_object* v_abs_1069_; lean_object* v_one_1070_; lean_object* v_a_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_abs_1069_ = lean_nat_abs(v_val_1058_);
lean_dec(v_val_1058_);
v_one_1070_ = lean_unsigned_to_nat(1u);
v_a_1071_ = lean_nat_sub(v_abs_1069_, v_one_1070_);
lean_dec(v_abs_1069_);
v___x_1072_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1073_ = lean_nat_add(v_a_1071_, v_one_1070_);
lean_dec(v_a_1071_);
v___x_1074_ = l_Nat_reprFast(v___x_1073_);
v___x_1075_ = lean_string_append(v___x_1072_, v___x_1074_);
lean_dec_ref(v___x_1074_);
v___y_1061_ = v___x_1075_;
goto v___jp_1060_;
}
v___jp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_string_append(v___x_1059_, v___y_1061_);
lean_dec_ref(v___y_1061_);
v___x_1063_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1064_ = lean_string_append(v___x_1062_, v___x_1063_);
v___y_1031_ = v___x_1064_;
goto v___jp_1030_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1026_) == 0)
{
lean_object* v_val_1076_; lean_object* v___x_1077_; lean_object* v___y_1079_; lean_object* v_intZero_1083_; uint8_t v_isNeg_1084_; 
v_val_1076_ = lean_ctor_get(v_lowerBound_1025_, 0);
lean_inc(v_val_1076_);
lean_dec_ref(v_lowerBound_1025_);
v___x_1077_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1083_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1084_ = lean_int_dec_lt(v_val_1076_, v_intZero_1083_);
if (v_isNeg_1084_ == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; 
v_a_1085_ = lean_nat_abs(v_val_1076_);
lean_dec(v_val_1076_);
v___x_1086_ = l_Nat_reprFast(v_a_1085_);
v___y_1079_ = v___x_1086_;
goto v___jp_1078_;
}
else
{
lean_object* v_abs_1087_; lean_object* v_one_1088_; lean_object* v_a_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_abs_1087_ = lean_nat_abs(v_val_1076_);
lean_dec(v_val_1076_);
v_one_1088_ = lean_unsigned_to_nat(1u);
v_a_1089_ = lean_nat_sub(v_abs_1087_, v_one_1088_);
lean_dec(v_abs_1087_);
v___x_1090_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1091_ = lean_nat_add(v_a_1089_, v_one_1088_);
lean_dec(v_a_1089_);
v___x_1092_ = l_Nat_reprFast(v___x_1091_);
v___x_1093_ = lean_string_append(v___x_1090_, v___x_1092_);
lean_dec_ref(v___x_1092_);
v___y_1079_ = v___x_1093_;
goto v___jp_1078_;
}
v___jp_1078_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_string_append(v___x_1077_, v___y_1079_);
lean_dec_ref(v___y_1079_);
v___x_1081_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1082_ = lean_string_append(v___x_1080_, v___x_1081_);
v___y_1031_ = v___x_1082_;
goto v___jp_1030_;
}
}
else
{
lean_object* v_val_1094_; lean_object* v_val_1095_; uint8_t v___x_1096_; 
v_val_1094_ = lean_ctor_get(v_lowerBound_1025_, 0);
lean_inc(v_val_1094_);
lean_dec_ref(v_lowerBound_1025_);
v_val_1095_ = lean_ctor_get(v_upperBound_1026_, 0);
lean_inc(v_val_1095_);
lean_dec_ref(v_upperBound_1026_);
v___x_1096_ = lean_int_dec_lt(v_val_1095_, v_val_1094_);
if (v___x_1096_ == 0)
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_int_dec_eq(v_val_1094_, v_val_1095_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___y_1100_; lean_object* v_intZero_1115_; uint8_t v_isNeg_1116_; 
v___x_1098_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1115_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1116_ = lean_int_dec_lt(v_val_1094_, v_intZero_1115_);
if (v_isNeg_1116_ == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; 
v_a_1117_ = lean_nat_abs(v_val_1094_);
lean_dec(v_val_1094_);
v___x_1118_ = l_Nat_reprFast(v_a_1117_);
v___y_1100_ = v___x_1118_;
goto v___jp_1099_;
}
else
{
lean_object* v_abs_1119_; lean_object* v_one_1120_; lean_object* v_a_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_abs_1119_ = lean_nat_abs(v_val_1094_);
lean_dec(v_val_1094_);
v_one_1120_ = lean_unsigned_to_nat(1u);
v_a_1121_ = lean_nat_sub(v_abs_1119_, v_one_1120_);
lean_dec(v_abs_1119_);
v___x_1122_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1123_ = lean_nat_add(v_a_1121_, v_one_1120_);
lean_dec(v_a_1121_);
v___x_1124_ = l_Nat_reprFast(v___x_1123_);
v___x_1125_ = lean_string_append(v___x_1122_, v___x_1124_);
lean_dec_ref(v___x_1124_);
v___y_1100_ = v___x_1125_;
goto v___jp_1099_;
}
v___jp_1099_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v_intZero_1104_; uint8_t v_isNeg_1105_; 
v___x_1101_ = lean_string_append(v___x_1098_, v___y_1100_);
lean_dec_ref(v___y_1100_);
v___x_1102_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1103_ = lean_string_append(v___x_1101_, v___x_1102_);
v_intZero_1104_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1105_ = lean_int_dec_lt(v_val_1095_, v_intZero_1104_);
if (v_isNeg_1105_ == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1107_; 
v_a_1106_ = lean_nat_abs(v_val_1095_);
lean_dec(v_val_1095_);
v___x_1107_ = l_Nat_reprFast(v_a_1106_);
v___y_1052_ = v___x_1103_;
v___y_1053_ = v___x_1107_;
goto v___jp_1051_;
}
else
{
lean_object* v_abs_1108_; lean_object* v_one_1109_; lean_object* v_a_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v_abs_1108_ = lean_nat_abs(v_val_1095_);
lean_dec(v_val_1095_);
v_one_1109_ = lean_unsigned_to_nat(1u);
v_a_1110_ = lean_nat_sub(v_abs_1108_, v_one_1109_);
lean_dec(v_abs_1108_);
v___x_1111_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1112_ = lean_nat_add(v_a_1110_, v_one_1109_);
lean_dec(v_a_1110_);
v___x_1113_ = l_Nat_reprFast(v___x_1112_);
v___x_1114_ = lean_string_append(v___x_1111_, v___x_1113_);
lean_dec_ref(v___x_1113_);
v___y_1052_ = v___x_1103_;
v___y_1053_ = v___x_1114_;
goto v___jp_1051_;
}
}
}
else
{
lean_object* v___x_1126_; lean_object* v___y_1128_; lean_object* v_intZero_1132_; uint8_t v_isNeg_1133_; 
lean_dec(v_val_1095_);
v___x_1126_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1132_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1133_ = lean_int_dec_lt(v_val_1094_, v_intZero_1132_);
if (v_isNeg_1133_ == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1135_; 
v_a_1134_ = lean_nat_abs(v_val_1094_);
lean_dec(v_val_1094_);
v___x_1135_ = l_Nat_reprFast(v_a_1134_);
v___y_1128_ = v___x_1135_;
goto v___jp_1127_;
}
else
{
lean_object* v_abs_1136_; lean_object* v_one_1137_; lean_object* v_a_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_abs_1136_ = lean_nat_abs(v_val_1094_);
lean_dec(v_val_1094_);
v_one_1137_ = lean_unsigned_to_nat(1u);
v_a_1138_ = lean_nat_sub(v_abs_1136_, v_one_1137_);
lean_dec(v_abs_1136_);
v___x_1139_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1140_ = lean_nat_add(v_a_1138_, v_one_1137_);
lean_dec(v_a_1138_);
v___x_1141_ = l_Nat_reprFast(v___x_1140_);
v___x_1142_ = lean_string_append(v___x_1139_, v___x_1141_);
lean_dec_ref(v___x_1141_);
v___y_1128_ = v___x_1142_;
goto v___jp_1127_;
}
v___jp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = lean_string_append(v___x_1126_, v___y_1128_);
lean_dec_ref(v___y_1128_);
v___x_1130_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1131_ = lean_string_append(v___x_1129_, v___x_1130_);
v___y_1031_ = v___x_1131_;
goto v___jp_1030_;
}
}
}
else
{
lean_object* v___x_1143_; 
lean_dec(v_val_1095_);
lean_dec(v_val_1094_);
v___x_1143_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1031_ = v___x_1143_;
goto v___jp_1030_;
}
}
}
v___jp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1032_ = lean_string_append(v___x_1029_, v___y_1031_);
lean_dec_ref(v___y_1031_);
v___x_1033_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__11));
v___x_1034_ = lean_string_append(v___x_1032_, v___x_1033_);
v___x_1035_ = l_Int_repr(v_a_1021_);
lean_dec(v_a_1021_);
v___x_1036_ = lean_string_append(v___x_1034_, v___x_1035_);
lean_dec_ref(v___x_1035_);
v___x_1037_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__12));
v___x_1038_ = lean_string_append(v___x_1036_, v___x_1037_);
v___x_1039_ = l_Int_repr(v_b_1023_);
lean_dec(v_b_1023_);
v___x_1040_ = lean_string_append(v___x_1038_, v___x_1039_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__13));
v___x_1042_ = lean_string_append(v___x_1040_, v___x_1041_);
v___x_1043_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_1017_, v_x_1019_, v_j_1022_);
v___x_1044_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1043_);
v___x_1045_ = lean_string_append(v___x_1042_, v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_1047_ = lean_string_append(v___x_1045_, v___x_1046_);
v___x_1048_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_1018_, v_y_1020_, v_k_1024_);
v___x_1049_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1048_);
v___x_1050_ = lean_string_append(v___x_1047_, v___x_1049_);
lean_dec_ref(v___x_1049_);
return v___x_1050_;
}
v___jp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = lean_string_append(v___y_1052_, v___y_1053_);
lean_dec_ref(v___y_1053_);
v___x_1055_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1056_ = lean_string_append(v___x_1054_, v___x_1055_);
v___y_1031_ = v___x_1056_;
goto v___jp_1030_;
}
}
default: 
{
lean_object* v_m_1144_; lean_object* v_r_1145_; lean_object* v_i_1146_; lean_object* v_x_1147_; lean_object* v_j_1148_; lean_object* v_lowerBound_1149_; lean_object* v_upperBound_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___y_1155_; lean_object* v___y_1172_; lean_object* v___y_1173_; 
v_m_1144_ = lean_ctor_get(v_x_670_, 0);
lean_inc(v_m_1144_);
v_r_1145_ = lean_ctor_get(v_x_670_, 1);
lean_inc(v_r_1145_);
v_i_1146_ = lean_ctor_get(v_x_670_, 2);
lean_inc(v_i_1146_);
v_x_1147_ = lean_ctor_get(v_x_670_, 3);
lean_inc(v_x_1147_);
v_j_1148_ = lean_ctor_get(v_x_670_, 4);
lean_inc_ref(v_j_1148_);
lean_dec_ref(v_x_670_);
v_lowerBound_1149_ = lean_ctor_get(v_s_668_, 0);
lean_inc(v_lowerBound_1149_);
v_upperBound_1150_ = lean_ctor_get(v_s_668_, 1);
lean_inc(v_upperBound_1150_);
lean_dec_ref(v_s_668_);
v___x_1151_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_669_);
lean_dec(v_x_669_);
v___x_1152_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1153_ = lean_string_append(v___x_1151_, v___x_1152_);
if (lean_obj_tag(v_lowerBound_1149_) == 0)
{
if (lean_obj_tag(v_upperBound_1150_) == 0)
{
lean_object* v___x_1177_; 
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1155_ = v___x_1177_;
goto v___jp_1154_;
}
else
{
lean_object* v_val_1178_; lean_object* v___x_1179_; lean_object* v___y_1181_; lean_object* v_intZero_1185_; uint8_t v_isNeg_1186_; 
v_val_1178_ = lean_ctor_get(v_upperBound_1150_, 0);
lean_inc(v_val_1178_);
lean_dec_ref(v_upperBound_1150_);
v___x_1179_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1185_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1186_ = lean_int_dec_lt(v_val_1178_, v_intZero_1185_);
if (v_isNeg_1186_ == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1188_; 
v_a_1187_ = lean_nat_abs(v_val_1178_);
lean_dec(v_val_1178_);
v___x_1188_ = l_Nat_reprFast(v_a_1187_);
v___y_1181_ = v___x_1188_;
goto v___jp_1180_;
}
else
{
lean_object* v_abs_1189_; lean_object* v_one_1190_; lean_object* v_a_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_abs_1189_ = lean_nat_abs(v_val_1178_);
lean_dec(v_val_1178_);
v_one_1190_ = lean_unsigned_to_nat(1u);
v_a_1191_ = lean_nat_sub(v_abs_1189_, v_one_1190_);
lean_dec(v_abs_1189_);
v___x_1192_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1193_ = lean_nat_add(v_a_1191_, v_one_1190_);
lean_dec(v_a_1191_);
v___x_1194_ = l_Nat_reprFast(v___x_1193_);
v___x_1195_ = lean_string_append(v___x_1192_, v___x_1194_);
lean_dec_ref(v___x_1194_);
v___y_1181_ = v___x_1195_;
goto v___jp_1180_;
}
v___jp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_string_append(v___x_1179_, v___y_1181_);
lean_dec_ref(v___y_1181_);
v___x_1183_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1184_ = lean_string_append(v___x_1182_, v___x_1183_);
v___y_1155_ = v___x_1184_;
goto v___jp_1154_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1150_) == 0)
{
lean_object* v_val_1196_; lean_object* v___x_1197_; lean_object* v___y_1199_; lean_object* v_intZero_1203_; uint8_t v_isNeg_1204_; 
v_val_1196_ = lean_ctor_get(v_lowerBound_1149_, 0);
lean_inc(v_val_1196_);
lean_dec_ref(v_lowerBound_1149_);
v___x_1197_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1203_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1204_ = lean_int_dec_lt(v_val_1196_, v_intZero_1203_);
if (v_isNeg_1204_ == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1206_; 
v_a_1205_ = lean_nat_abs(v_val_1196_);
lean_dec(v_val_1196_);
v___x_1206_ = l_Nat_reprFast(v_a_1205_);
v___y_1199_ = v___x_1206_;
goto v___jp_1198_;
}
else
{
lean_object* v_abs_1207_; lean_object* v_one_1208_; lean_object* v_a_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_abs_1207_ = lean_nat_abs(v_val_1196_);
lean_dec(v_val_1196_);
v_one_1208_ = lean_unsigned_to_nat(1u);
v_a_1209_ = lean_nat_sub(v_abs_1207_, v_one_1208_);
lean_dec(v_abs_1207_);
v___x_1210_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1211_ = lean_nat_add(v_a_1209_, v_one_1208_);
lean_dec(v_a_1209_);
v___x_1212_ = l_Nat_reprFast(v___x_1211_);
v___x_1213_ = lean_string_append(v___x_1210_, v___x_1212_);
lean_dec_ref(v___x_1212_);
v___y_1199_ = v___x_1213_;
goto v___jp_1198_;
}
v___jp_1198_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_string_append(v___x_1197_, v___y_1199_);
lean_dec_ref(v___y_1199_);
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1202_ = lean_string_append(v___x_1200_, v___x_1201_);
v___y_1155_ = v___x_1202_;
goto v___jp_1154_;
}
}
else
{
lean_object* v_val_1214_; lean_object* v_val_1215_; uint8_t v___x_1216_; 
v_val_1214_ = lean_ctor_get(v_lowerBound_1149_, 0);
lean_inc(v_val_1214_);
lean_dec_ref(v_lowerBound_1149_);
v_val_1215_ = lean_ctor_get(v_upperBound_1150_, 0);
lean_inc(v_val_1215_);
lean_dec_ref(v_upperBound_1150_);
v___x_1216_ = lean_int_dec_lt(v_val_1215_, v_val_1214_);
if (v___x_1216_ == 0)
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_int_dec_eq(v_val_1214_, v_val_1215_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___y_1220_; lean_object* v_intZero_1235_; uint8_t v_isNeg_1236_; 
v___x_1218_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1235_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1236_ = lean_int_dec_lt(v_val_1214_, v_intZero_1235_);
if (v_isNeg_1236_ == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1238_; 
v_a_1237_ = lean_nat_abs(v_val_1214_);
lean_dec(v_val_1214_);
v___x_1238_ = l_Nat_reprFast(v_a_1237_);
v___y_1220_ = v___x_1238_;
goto v___jp_1219_;
}
else
{
lean_object* v_abs_1239_; lean_object* v_one_1240_; lean_object* v_a_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_abs_1239_ = lean_nat_abs(v_val_1214_);
lean_dec(v_val_1214_);
v_one_1240_ = lean_unsigned_to_nat(1u);
v_a_1241_ = lean_nat_sub(v_abs_1239_, v_one_1240_);
lean_dec(v_abs_1239_);
v___x_1242_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1243_ = lean_nat_add(v_a_1241_, v_one_1240_);
lean_dec(v_a_1241_);
v___x_1244_ = l_Nat_reprFast(v___x_1243_);
v___x_1245_ = lean_string_append(v___x_1242_, v___x_1244_);
lean_dec_ref(v___x_1244_);
v___y_1220_ = v___x_1245_;
goto v___jp_1219_;
}
v___jp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_intZero_1224_; uint8_t v_isNeg_1225_; 
v___x_1221_ = lean_string_append(v___x_1218_, v___y_1220_);
lean_dec_ref(v___y_1220_);
v___x_1222_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1223_ = lean_string_append(v___x_1221_, v___x_1222_);
v_intZero_1224_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1225_ = lean_int_dec_lt(v_val_1215_, v_intZero_1224_);
if (v_isNeg_1225_ == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1227_; 
v_a_1226_ = lean_nat_abs(v_val_1215_);
lean_dec(v_val_1215_);
v___x_1227_ = l_Nat_reprFast(v_a_1226_);
v___y_1172_ = v___x_1223_;
v___y_1173_ = v___x_1227_;
goto v___jp_1171_;
}
else
{
lean_object* v_abs_1228_; lean_object* v_one_1229_; lean_object* v_a_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_abs_1228_ = lean_nat_abs(v_val_1215_);
lean_dec(v_val_1215_);
v_one_1229_ = lean_unsigned_to_nat(1u);
v_a_1230_ = lean_nat_sub(v_abs_1228_, v_one_1229_);
lean_dec(v_abs_1228_);
v___x_1231_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1232_ = lean_nat_add(v_a_1230_, v_one_1229_);
lean_dec(v_a_1230_);
v___x_1233_ = l_Nat_reprFast(v___x_1232_);
v___x_1234_ = lean_string_append(v___x_1231_, v___x_1233_);
lean_dec_ref(v___x_1233_);
v___y_1172_ = v___x_1223_;
v___y_1173_ = v___x_1234_;
goto v___jp_1171_;
}
}
}
else
{
lean_object* v___x_1246_; lean_object* v___y_1248_; lean_object* v_intZero_1252_; uint8_t v_isNeg_1253_; 
lean_dec(v_val_1215_);
v___x_1246_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1252_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1253_ = lean_int_dec_lt(v_val_1214_, v_intZero_1252_);
if (v_isNeg_1253_ == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1255_; 
v_a_1254_ = lean_nat_abs(v_val_1214_);
lean_dec(v_val_1214_);
v___x_1255_ = l_Nat_reprFast(v_a_1254_);
v___y_1248_ = v___x_1255_;
goto v___jp_1247_;
}
else
{
lean_object* v_abs_1256_; lean_object* v_one_1257_; lean_object* v_a_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_abs_1256_ = lean_nat_abs(v_val_1214_);
lean_dec(v_val_1214_);
v_one_1257_ = lean_unsigned_to_nat(1u);
v_a_1258_ = lean_nat_sub(v_abs_1256_, v_one_1257_);
lean_dec(v_abs_1256_);
v___x_1259_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1260_ = lean_nat_add(v_a_1258_, v_one_1257_);
lean_dec(v_a_1258_);
v___x_1261_ = l_Nat_reprFast(v___x_1260_);
v___x_1262_ = lean_string_append(v___x_1259_, v___x_1261_);
lean_dec_ref(v___x_1261_);
v___y_1248_ = v___x_1262_;
goto v___jp_1247_;
}
v___jp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = lean_string_append(v___x_1246_, v___y_1248_);
lean_dec_ref(v___y_1248_);
v___x_1250_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1251_ = lean_string_append(v___x_1249_, v___x_1250_);
v___y_1155_ = v___x_1251_;
goto v___jp_1154_;
}
}
}
else
{
lean_object* v___x_1263_; 
lean_dec(v_val_1215_);
lean_dec(v_val_1214_);
v___x_1263_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1155_ = v___x_1263_;
goto v___jp_1154_;
}
}
}
v___jp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1156_ = lean_string_append(v___x_1153_, v___y_1155_);
lean_dec_ref(v___y_1155_);
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__14));
v___x_1158_ = lean_string_append(v___x_1156_, v___x_1157_);
v___x_1159_ = l_Nat_reprFast(v_m_1144_);
v___x_1160_ = lean_string_append(v___x_1158_, v___x_1159_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__15));
v___x_1162_ = lean_string_append(v___x_1160_, v___x_1161_);
v___x_1163_ = l_Nat_reprFast(v_i_1146_);
v___x_1164_ = lean_string_append(v___x_1162_, v___x_1163_);
lean_dec_ref(v___x_1163_);
v___x_1165_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__16));
v___x_1166_ = lean_string_append(v___x_1164_, v___x_1165_);
v___x_1167_ = l_Lean_Omega_Constraint_exact(v_r_1145_);
v___x_1168_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v___x_1167_, v_x_1147_, v_j_1148_);
v___x_1169_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1168_);
v___x_1170_ = lean_string_append(v___x_1166_, v___x_1169_);
lean_dec_ref(v___x_1169_);
return v___x_1170_;
}
v___jp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = lean_string_append(v___y_1172_, v___y_1173_);
lean_dec_ref(v___y_1173_);
v___x_1175_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1176_ = lean_string_append(v___x_1174_, v___x_1175_);
v___y_1155_ = v___x_1176_;
goto v___jp_1154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_instToString(lean_object* v_s_1264_, lean_object* v_x_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Justification_toString), 3, 2);
lean_closure_set(v___x_1266_, 0, v_s_1264_);
lean_closure_set(v___x_1266_, 1, v_x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(lean_object* v_nilFn_1267_, lean_object* v_consFn_1268_, lean_object* v_x_1269_){
_start:
{
if (lean_obj_tag(v_x_1269_) == 0)
{
lean_dec_ref(v_consFn_1268_);
lean_inc_ref(v_nilFn_1267_);
return v_nilFn_1267_;
}
else
{
lean_object* v_head_1270_; lean_object* v_tail_1271_; lean_object* v___y_1273_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v_head_1270_ = lean_ctor_get(v_x_1269_, 0);
v_tail_1271_ = lean_ctor_get(v_x_1269_, 1);
v___x_1276_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1277_ = lean_int_dec_le(v___x_1276_, v_head_1270_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1278_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1279_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1280_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1281_ = lean_int_neg(v_head_1270_);
v___x_1282_ = l_Int_toNat(v___x_1281_);
lean_dec(v___x_1281_);
v___x_1283_ = l_Lean_instToExprInt_mkNat(v___x_1282_);
v___x_1284_ = l_Lean_mkApp3(v___x_1278_, v___x_1279_, v___x_1280_, v___x_1283_);
v___y_1273_ = v___x_1284_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = l_Int_toNat(v_head_1270_);
v___x_1286_ = l_Lean_instToExprInt_mkNat(v___x_1285_);
v___y_1273_ = v___x_1286_;
goto v___jp_1272_;
}
v___jp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_inc_ref(v_consFn_1268_);
v___x_1274_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1267_, v_consFn_1268_, v_tail_1271_);
v___x_1275_ = l_Lean_mkAppB(v_consFn_1268_, v___y_1273_, v___x_1274_);
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0___boxed(lean_object* v_nilFn_1287_, lean_object* v_consFn_1288_, lean_object* v_x_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1287_, v_consFn_1288_, v_x_1289_);
lean_dec(v_x_1289_);
lean_dec_ref(v_nilFn_1287_);
return v_res_1290_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1));
v___x_1298_ = l_Lean_Expr_const___override(v___x_1297_, v___x_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof(lean_object* v_s_1299_, lean_object* v_x_1300_, lean_object* v_v_1301_, lean_object* v_prf_1302_){
_start:
{
lean_object* v___x_1303_; lean_object* v___y_1305_; lean_object* v_lowerBound_1310_; lean_object* v_upperBound_1311_; lean_object* v___x_1312_; lean_object* v_type_1313_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1321_; 
v___x_1303_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2);
v_lowerBound_1310_ = lean_ctor_get(v_s_1299_, 0);
v_upperBound_1311_ = lean_ctor_get(v_s_1299_, 1);
v___x_1312_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1313_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1310_) == 0)
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1321_ = v___x_1337_;
goto v___jp_1320_;
}
else
{
lean_object* v_val_1338_; lean_object* v___x_1339_; lean_object* v___y_1341_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_val_1338_ = lean_ctor_get(v_lowerBound_1310_, 0);
v___x_1339_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1343_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1344_ = lean_int_dec_le(v___x_1343_, v_val_1338_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1345_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1346_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1347_ = lean_int_neg(v_val_1338_);
v___x_1348_ = l_Int_toNat(v___x_1347_);
lean_dec(v___x_1347_);
v___x_1349_ = l_Lean_instToExprInt_mkNat(v___x_1348_);
v___x_1350_ = l_Lean_mkApp3(v___x_1345_, v_type_1313_, v___x_1346_, v___x_1349_);
v___y_1341_ = v___x_1350_;
goto v___jp_1340_;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = l_Int_toNat(v_val_1338_);
v___x_1352_ = l_Lean_instToExprInt_mkNat(v___x_1351_);
v___y_1341_ = v___x_1352_;
goto v___jp_1340_;
}
v___jp_1340_:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_mkAppB(v___x_1339_, v_type_1313_, v___y_1341_);
v___y_1321_ = v___x_1342_;
goto v___jp_1320_;
}
}
v___jp_1304_:
{
lean_object* v_nil_1306_; lean_object* v_cons_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_nil_1306_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1307_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1308_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1306_, v_cons_1307_, v_x_1300_);
v___x_1309_ = l_Lean_mkApp4(v___x_1303_, v___y_1305_, v___x_1308_, v_v_1301_, v_prf_1302_);
return v___x_1309_;
}
v___jp_1314_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_inc_ref(v___y_1315_);
v___x_1318_ = l_Lean_mkAppB(v___y_1315_, v_type_1313_, v___y_1317_);
v___x_1319_ = l_Lean_Expr_app___override(v___y_1316_, v___x_1318_);
v___y_1305_ = v___x_1319_;
goto v___jp_1304_;
}
v___jp_1320_:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Expr_app___override(v___x_1312_, v___y_1321_);
if (lean_obj_tag(v_upperBound_1311_) == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1324_ = l_Lean_Expr_app___override(v___x_1322_, v___x_1323_);
v___y_1305_ = v___x_1324_;
goto v___jp_1304_;
}
else
{
lean_object* v_val_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v_val_1325_ = lean_ctor_get(v_upperBound_1311_, 0);
v___x_1326_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1327_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1328_ = lean_int_dec_le(v___x_1327_, v_val_1325_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1329_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1330_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1331_ = lean_int_neg(v_val_1325_);
v___x_1332_ = l_Int_toNat(v___x_1331_);
lean_dec(v___x_1331_);
v___x_1333_ = l_Lean_instToExprInt_mkNat(v___x_1332_);
v___x_1334_ = l_Lean_mkApp3(v___x_1329_, v_type_1313_, v___x_1330_, v___x_1333_);
v___y_1315_ = v___x_1326_;
v___y_1316_ = v___x_1322_;
v___y_1317_ = v___x_1334_;
goto v___jp_1314_;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = l_Int_toNat(v_val_1325_);
v___x_1336_ = l_Lean_instToExprInt_mkNat(v___x_1335_);
v___y_1315_ = v___x_1326_;
v___y_1316_ = v___x_1322_;
v___y_1317_ = v___x_1336_;
goto v___jp_1314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___boxed(lean_object* v_s_1353_, lean_object* v_x_1354_, lean_object* v_v_1355_, lean_object* v_prf_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1353_, v_x_1354_, v_v_1355_, v_prf_1356_);
lean_dec(v_x_1354_);
lean_dec_ref(v_s_1353_);
return v_res_1357_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = lean_box(0);
v___x_1365_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1));
v___x_1366_ = l_Lean_Expr_const___override(v___x_1365_, v___x_1364_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof(lean_object* v_s_1367_, lean_object* v_t_1368_, lean_object* v_x_1369_, lean_object* v_v_1370_, lean_object* v_ps_1371_, lean_object* v_pt_1372_){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1424_; lean_object* v_lowerBound_1442_; lean_object* v_upperBound_1443_; lean_object* v___x_1444_; lean_object* v_type_1445_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1453_; 
v___x_1373_ = lean_box(0);
v___x_1374_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2);
v_lowerBound_1442_ = lean_ctor_get(v_s_1367_, 0);
v_upperBound_1443_ = lean_ctor_get(v_s_1367_, 1);
v___x_1444_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1445_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1442_) == 0)
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1453_ = v___x_1469_;
goto v___jp_1452_;
}
else
{
lean_object* v_val_1470_; lean_object* v___x_1471_; lean_object* v___y_1473_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v_val_1470_ = lean_ctor_get(v_lowerBound_1442_, 0);
v___x_1471_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1475_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1476_ = lean_int_dec_le(v___x_1475_, v_val_1470_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1477_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1478_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1479_ = lean_int_neg(v_val_1470_);
v___x_1480_ = l_Int_toNat(v___x_1479_);
lean_dec(v___x_1479_);
v___x_1481_ = l_Lean_instToExprInt_mkNat(v___x_1480_);
v___x_1482_ = l_Lean_mkApp3(v___x_1477_, v_type_1445_, v___x_1478_, v___x_1481_);
v___y_1473_ = v___x_1482_;
goto v___jp_1472_;
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = l_Int_toNat(v_val_1470_);
v___x_1484_ = l_Lean_instToExprInt_mkNat(v___x_1483_);
v___y_1473_ = v___x_1484_;
goto v___jp_1472_;
}
v___jp_1472_:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_mkAppB(v___x_1471_, v_type_1445_, v___y_1473_);
v___y_1453_ = v___x_1474_;
goto v___jp_1452_;
}
}
v___jp_1375_:
{
lean_object* v_nil_1378_; lean_object* v_cons_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_nil_1378_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1379_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1380_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1378_, v_cons_1379_, v_x_1369_);
v___x_1381_ = l_Lean_mkApp6(v___x_1374_, v___y_1376_, v___y_1377_, v___x_1380_, v_v_1370_, v_ps_1371_, v_pt_1372_);
return v___x_1381_;
}
v___jp_1382_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_inc_ref(v___y_1386_);
v___x_1388_ = l_Lean_mkAppB(v___y_1386_, v___y_1384_, v___y_1387_);
v___x_1389_ = l_Lean_Expr_app___override(v___y_1383_, v___x_1388_);
v___y_1376_ = v___y_1385_;
v___y_1377_ = v___x_1389_;
goto v___jp_1375_;
}
v___jp_1390_:
{
lean_object* v_upperBound_1396_; lean_object* v___x_1397_; 
v_upperBound_1396_ = lean_ctor_get(v_t_1368_, 1);
lean_inc_ref(v___y_1393_);
v___x_1397_ = l_Lean_Expr_app___override(v___y_1393_, v___y_1395_);
if (lean_obj_tag(v_upperBound_1396_) == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1399_ = l_Lean_Expr_app___override(v___x_1398_, v___y_1392_);
v___x_1400_ = l_Lean_Expr_app___override(v___x_1397_, v___x_1399_);
v___y_1376_ = v___y_1394_;
v___y_1377_ = v___x_1400_;
goto v___jp_1375_;
}
else
{
lean_object* v_val_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_val_1401_ = lean_ctor_get(v_upperBound_1396_, 0);
v___x_1402_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1403_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1404_ = lean_int_dec_le(v___x_1403_, v_val_1401_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1405_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1406_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1391_);
v___x_1407_ = l_Lean_Name_mkStr2(v___y_1391_, v___x_1406_);
v___x_1408_ = l_Lean_Expr_const___override(v___x_1407_, v___x_1373_);
v___x_1409_ = lean_int_neg(v_val_1401_);
v___x_1410_ = l_Int_toNat(v___x_1409_);
lean_dec(v___x_1409_);
v___x_1411_ = l_Lean_instToExprInt_mkNat(v___x_1410_);
lean_inc_ref(v___y_1392_);
v___x_1412_ = l_Lean_mkApp3(v___x_1405_, v___y_1392_, v___x_1408_, v___x_1411_);
v___y_1383_ = v___x_1397_;
v___y_1384_ = v___y_1392_;
v___y_1385_ = v___y_1394_;
v___y_1386_ = v___x_1402_;
v___y_1387_ = v___x_1412_;
goto v___jp_1382_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = l_Int_toNat(v_val_1401_);
v___x_1414_ = l_Lean_instToExprInt_mkNat(v___x_1413_);
v___y_1383_ = v___x_1397_;
v___y_1384_ = v___y_1392_;
v___y_1385_ = v___y_1394_;
v___y_1386_ = v___x_1402_;
v___y_1387_ = v___x_1414_;
goto v___jp_1382_;
}
}
}
v___jp_1415_:
{
lean_object* v___x_1422_; 
lean_inc_ref(v___y_1417_);
lean_inc_ref(v___y_1420_);
v___x_1422_ = l_Lean_mkAppB(v___y_1420_, v___y_1417_, v___y_1421_);
v___y_1391_ = v___y_1416_;
v___y_1392_ = v___y_1417_;
v___y_1393_ = v___y_1418_;
v___y_1394_ = v___y_1419_;
v___y_1395_ = v___x_1422_;
goto v___jp_1390_;
}
v___jp_1423_:
{
lean_object* v_lowerBound_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v_type_1428_; 
v_lowerBound_1425_ = lean_ctor_get(v_t_1368_, 0);
v___x_1426_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1427_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1428_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1425_) == 0)
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1391_ = v___x_1427_;
v___y_1392_ = v_type_1428_;
v___y_1393_ = v___x_1426_;
v___y_1394_ = v___y_1424_;
v___y_1395_ = v___x_1429_;
goto v___jp_1390_;
}
else
{
lean_object* v_val_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v_val_1430_ = lean_ctor_get(v_lowerBound_1425_, 0);
v___x_1431_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1432_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1433_ = lean_int_dec_le(v___x_1432_, v_val_1430_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1434_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1435_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1436_ = lean_int_neg(v_val_1430_);
v___x_1437_ = l_Int_toNat(v___x_1436_);
lean_dec(v___x_1436_);
v___x_1438_ = l_Lean_instToExprInt_mkNat(v___x_1437_);
v___x_1439_ = l_Lean_mkApp3(v___x_1434_, v_type_1428_, v___x_1435_, v___x_1438_);
v___y_1416_ = v___x_1427_;
v___y_1417_ = v_type_1428_;
v___y_1418_ = v___x_1426_;
v___y_1419_ = v___y_1424_;
v___y_1420_ = v___x_1431_;
v___y_1421_ = v___x_1439_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = l_Int_toNat(v_val_1430_);
v___x_1441_ = l_Lean_instToExprInt_mkNat(v___x_1440_);
v___y_1416_ = v___x_1427_;
v___y_1417_ = v_type_1428_;
v___y_1418_ = v___x_1426_;
v___y_1419_ = v___y_1424_;
v___y_1420_ = v___x_1431_;
v___y_1421_ = v___x_1441_;
goto v___jp_1415_;
}
}
}
v___jp_1446_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_inc_ref(v___y_1447_);
v___x_1450_ = l_Lean_mkAppB(v___y_1447_, v_type_1445_, v___y_1449_);
v___x_1451_ = l_Lean_Expr_app___override(v___y_1448_, v___x_1450_);
v___y_1424_ = v___x_1451_;
goto v___jp_1423_;
}
v___jp_1452_:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Expr_app___override(v___x_1444_, v___y_1453_);
if (lean_obj_tag(v_upperBound_1443_) == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1456_ = l_Lean_Expr_app___override(v___x_1454_, v___x_1455_);
v___y_1424_ = v___x_1456_;
goto v___jp_1423_;
}
else
{
lean_object* v_val_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v_val_1457_ = lean_ctor_get(v_upperBound_1443_, 0);
v___x_1458_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1459_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1460_ = lean_int_dec_le(v___x_1459_, v_val_1457_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1461_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1462_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1463_ = lean_int_neg(v_val_1457_);
v___x_1464_ = l_Int_toNat(v___x_1463_);
lean_dec(v___x_1463_);
v___x_1465_ = l_Lean_instToExprInt_mkNat(v___x_1464_);
v___x_1466_ = l_Lean_mkApp3(v___x_1461_, v_type_1445_, v___x_1462_, v___x_1465_);
v___y_1447_ = v___x_1458_;
v___y_1448_ = v___x_1454_;
v___y_1449_ = v___x_1466_;
goto v___jp_1446_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = l_Int_toNat(v_val_1457_);
v___x_1468_ = l_Lean_instToExprInt_mkNat(v___x_1467_);
v___y_1447_ = v___x_1458_;
v___y_1448_ = v___x_1454_;
v___y_1449_ = v___x_1468_;
goto v___jp_1446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___boxed(lean_object* v_s_1485_, lean_object* v_t_1486_, lean_object* v_x_1487_, lean_object* v_v_1488_, lean_object* v_ps_1489_, lean_object* v_pt_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1485_, v_t_1486_, v_x_1487_, v_v_1488_, v_ps_1489_, v_pt_1490_);
lean_dec(v_x_1487_);
lean_dec_ref(v_t_1486_);
lean_dec_ref(v_s_1485_);
return v_res_1491_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = lean_box(0);
v___x_1498_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1));
v___x_1499_ = l_Lean_Expr_const___override(v___x_1498_, v___x_1497_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof(lean_object* v_s_1500_, lean_object* v_t_1501_, lean_object* v_a_1502_, lean_object* v_x_1503_, lean_object* v_b_1504_, lean_object* v_y_1505_, lean_object* v_v_1506_, lean_object* v_px_1507_, lean_object* v_py_1508_){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1595_; lean_object* v_lowerBound_1613_; lean_object* v_upperBound_1614_; lean_object* v___x_1615_; lean_object* v_type_1616_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1624_; 
v___x_1509_ = lean_box(0);
v___x_1510_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2);
v_lowerBound_1613_ = lean_ctor_get(v_s_1500_, 0);
v_upperBound_1614_ = lean_ctor_get(v_s_1500_, 1);
v___x_1615_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1616_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1613_) == 0)
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1624_ = v___x_1640_;
goto v___jp_1623_;
}
else
{
lean_object* v_val_1641_; lean_object* v___x_1642_; lean_object* v___y_1644_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v_val_1641_ = lean_ctor_get(v_lowerBound_1613_, 0);
v___x_1642_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1646_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1647_ = lean_int_dec_le(v___x_1646_, v_val_1641_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1648_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1649_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1650_ = lean_int_neg(v_val_1641_);
v___x_1651_ = l_Int_toNat(v___x_1650_);
lean_dec(v___x_1650_);
v___x_1652_ = l_Lean_instToExprInt_mkNat(v___x_1651_);
v___x_1653_ = l_Lean_mkApp3(v___x_1648_, v_type_1616_, v___x_1649_, v___x_1652_);
v___y_1644_ = v___x_1653_;
goto v___jp_1643_;
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = l_Int_toNat(v_val_1641_);
v___x_1655_ = l_Lean_instToExprInt_mkNat(v___x_1654_);
v___y_1644_ = v___x_1655_;
goto v___jp_1643_;
}
v___jp_1643_:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_mkAppB(v___x_1642_, v_type_1616_, v___y_1644_);
v___y_1624_ = v___x_1645_;
goto v___jp_1623_;
}
}
v___jp_1511_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v___y_1517_, v___y_1513_, v_y_1505_);
v___x_1520_ = l_Lean_mkApp9(v___x_1510_, v___y_1516_, v___y_1515_, v___y_1512_, v___y_1514_, v___y_1518_, v___x_1519_, v_v_1506_, v_px_1507_, v_py_1508_);
return v___x_1520_;
}
v___jp_1521_:
{
lean_object* v_type_1525_; lean_object* v_nil_1526_; lean_object* v_cons_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v_type_1525_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_nil_1526_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1527_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1528_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1526_, v_cons_1527_, v_x_1503_);
v___x_1529_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1530_ = lean_int_dec_le(v___x_1529_, v_b_1504_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1531_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1532_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1533_ = lean_int_neg(v_b_1504_);
v___x_1534_ = l_Int_toNat(v___x_1533_);
lean_dec(v___x_1533_);
v___x_1535_ = l_Lean_instToExprInt_mkNat(v___x_1534_);
v___x_1536_ = l_Lean_mkApp3(v___x_1531_, v_type_1525_, v___x_1532_, v___x_1535_);
v___y_1512_ = v___y_1524_;
v___y_1513_ = v_cons_1527_;
v___y_1514_ = v___x_1528_;
v___y_1515_ = v___y_1523_;
v___y_1516_ = v___y_1522_;
v___y_1517_ = v_nil_1526_;
v___y_1518_ = v___x_1536_;
goto v___jp_1511_;
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = l_Int_toNat(v_b_1504_);
v___x_1538_ = l_Lean_instToExprInt_mkNat(v___x_1537_);
v___y_1512_ = v___y_1524_;
v___y_1513_ = v_cons_1527_;
v___y_1514_ = v___x_1528_;
v___y_1515_ = v___y_1523_;
v___y_1516_ = v___y_1522_;
v___y_1517_ = v_nil_1526_;
v___y_1518_ = v___x_1538_;
goto v___jp_1511_;
}
}
v___jp_1539_:
{
lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1542_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1543_ = lean_int_dec_le(v___x_1542_, v_a_1502_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1544_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1545_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1546_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1547_ = lean_int_neg(v_a_1502_);
v___x_1548_ = l_Int_toNat(v___x_1547_);
lean_dec(v___x_1547_);
v___x_1549_ = l_Lean_instToExprInt_mkNat(v___x_1548_);
v___x_1550_ = l_Lean_mkApp3(v___x_1544_, v___x_1545_, v___x_1546_, v___x_1549_);
v___y_1522_ = v___y_1540_;
v___y_1523_ = v___y_1541_;
v___y_1524_ = v___x_1550_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = l_Int_toNat(v_a_1502_);
v___x_1552_ = l_Lean_instToExprInt_mkNat(v___x_1551_);
v___y_1522_ = v___y_1540_;
v___y_1523_ = v___y_1541_;
v___y_1524_ = v___x_1552_;
goto v___jp_1521_;
}
}
v___jp_1553_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_inc_ref(v___y_1554_);
v___x_1559_ = l_Lean_mkAppB(v___y_1554_, v___y_1555_, v___y_1558_);
v___x_1560_ = l_Lean_Expr_app___override(v___y_1556_, v___x_1559_);
v___y_1540_ = v___y_1557_;
v___y_1541_ = v___x_1560_;
goto v___jp_1539_;
}
v___jp_1561_:
{
lean_object* v_upperBound_1567_; lean_object* v___x_1568_; 
v_upperBound_1567_ = lean_ctor_get(v_t_1501_, 1);
lean_inc_ref(v___y_1564_);
v___x_1568_ = l_Lean_Expr_app___override(v___y_1564_, v___y_1566_);
if (lean_obj_tag(v_upperBound_1567_) == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1570_ = l_Lean_Expr_app___override(v___x_1569_, v___y_1563_);
v___x_1571_ = l_Lean_Expr_app___override(v___x_1568_, v___x_1570_);
v___y_1540_ = v___y_1565_;
v___y_1541_ = v___x_1571_;
goto v___jp_1539_;
}
else
{
lean_object* v_val_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v_val_1572_ = lean_ctor_get(v_upperBound_1567_, 0);
v___x_1573_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1574_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1575_ = lean_int_dec_le(v___x_1574_, v_val_1572_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1576_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1577_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1562_);
v___x_1578_ = l_Lean_Name_mkStr2(v___y_1562_, v___x_1577_);
v___x_1579_ = l_Lean_Expr_const___override(v___x_1578_, v___x_1509_);
v___x_1580_ = lean_int_neg(v_val_1572_);
v___x_1581_ = l_Int_toNat(v___x_1580_);
lean_dec(v___x_1580_);
v___x_1582_ = l_Lean_instToExprInt_mkNat(v___x_1581_);
lean_inc_ref(v___y_1563_);
v___x_1583_ = l_Lean_mkApp3(v___x_1576_, v___y_1563_, v___x_1579_, v___x_1582_);
v___y_1554_ = v___x_1573_;
v___y_1555_ = v___y_1563_;
v___y_1556_ = v___x_1568_;
v___y_1557_ = v___y_1565_;
v___y_1558_ = v___x_1583_;
goto v___jp_1553_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = l_Int_toNat(v_val_1572_);
v___x_1585_ = l_Lean_instToExprInt_mkNat(v___x_1584_);
v___y_1554_ = v___x_1573_;
v___y_1555_ = v___y_1563_;
v___y_1556_ = v___x_1568_;
v___y_1557_ = v___y_1565_;
v___y_1558_ = v___x_1585_;
goto v___jp_1553_;
}
}
}
v___jp_1586_:
{
lean_object* v___x_1593_; 
lean_inc_ref(v___y_1589_);
lean_inc_ref(v___y_1587_);
v___x_1593_ = l_Lean_mkAppB(v___y_1587_, v___y_1589_, v___y_1592_);
v___y_1562_ = v___y_1588_;
v___y_1563_ = v___y_1589_;
v___y_1564_ = v___y_1590_;
v___y_1565_ = v___y_1591_;
v___y_1566_ = v___x_1593_;
goto v___jp_1561_;
}
v___jp_1594_:
{
lean_object* v_lowerBound_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v_type_1599_; 
v_lowerBound_1596_ = lean_ctor_get(v_t_1501_, 0);
v___x_1597_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1598_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1599_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1596_) == 0)
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1562_ = v___x_1598_;
v___y_1563_ = v_type_1599_;
v___y_1564_ = v___x_1597_;
v___y_1565_ = v___y_1595_;
v___y_1566_ = v___x_1600_;
goto v___jp_1561_;
}
else
{
lean_object* v_val_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v_val_1601_ = lean_ctor_get(v_lowerBound_1596_, 0);
v___x_1602_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1603_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1604_ = lean_int_dec_le(v___x_1603_, v_val_1601_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1605_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1606_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1607_ = lean_int_neg(v_val_1601_);
v___x_1608_ = l_Int_toNat(v___x_1607_);
lean_dec(v___x_1607_);
v___x_1609_ = l_Lean_instToExprInt_mkNat(v___x_1608_);
v___x_1610_ = l_Lean_mkApp3(v___x_1605_, v_type_1599_, v___x_1606_, v___x_1609_);
v___y_1587_ = v___x_1602_;
v___y_1588_ = v___x_1598_;
v___y_1589_ = v_type_1599_;
v___y_1590_ = v___x_1597_;
v___y_1591_ = v___y_1595_;
v___y_1592_ = v___x_1610_;
goto v___jp_1586_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = l_Int_toNat(v_val_1601_);
v___x_1612_ = l_Lean_instToExprInt_mkNat(v___x_1611_);
v___y_1587_ = v___x_1602_;
v___y_1588_ = v___x_1598_;
v___y_1589_ = v_type_1599_;
v___y_1590_ = v___x_1597_;
v___y_1591_ = v___y_1595_;
v___y_1592_ = v___x_1612_;
goto v___jp_1586_;
}
}
}
v___jp_1617_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_inc_ref(v___y_1619_);
v___x_1621_ = l_Lean_mkAppB(v___y_1619_, v_type_1616_, v___y_1620_);
v___x_1622_ = l_Lean_Expr_app___override(v___y_1618_, v___x_1621_);
v___y_1595_ = v___x_1622_;
goto v___jp_1594_;
}
v___jp_1623_:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Expr_app___override(v___x_1615_, v___y_1624_);
if (lean_obj_tag(v_upperBound_1614_) == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1627_ = l_Lean_Expr_app___override(v___x_1625_, v___x_1626_);
v___y_1595_ = v___x_1627_;
goto v___jp_1594_;
}
else
{
lean_object* v_val_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v_val_1628_ = lean_ctor_get(v_upperBound_1614_, 0);
v___x_1629_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1630_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1631_ = lean_int_dec_le(v___x_1630_, v_val_1628_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1632_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1633_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1634_ = lean_int_neg(v_val_1628_);
v___x_1635_ = l_Int_toNat(v___x_1634_);
lean_dec(v___x_1634_);
v___x_1636_ = l_Lean_instToExprInt_mkNat(v___x_1635_);
v___x_1637_ = l_Lean_mkApp3(v___x_1632_, v_type_1616_, v___x_1633_, v___x_1636_);
v___y_1618_ = v___x_1625_;
v___y_1619_ = v___x_1629_;
v___y_1620_ = v___x_1637_;
goto v___jp_1617_;
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = l_Int_toNat(v_val_1628_);
v___x_1639_ = l_Lean_instToExprInt_mkNat(v___x_1638_);
v___y_1618_ = v___x_1625_;
v___y_1619_ = v___x_1629_;
v___y_1620_ = v___x_1639_;
goto v___jp_1617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___boxed(lean_object* v_s_1656_, lean_object* v_t_1657_, lean_object* v_a_1658_, lean_object* v_x_1659_, lean_object* v_b_1660_, lean_object* v_y_1661_, lean_object* v_v_1662_, lean_object* v_px_1663_, lean_object* v_py_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1656_, v_t_1657_, v_a_1658_, v_x_1659_, v_b_1660_, v_y_1661_, v_v_1662_, v_px_1663_, v_py_1664_);
lean_dec(v_y_1661_);
lean_dec(v_b_1660_);
lean_dec(v_x_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_t_1657_);
lean_dec_ref(v_s_1656_);
return v_res_1665_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_1672_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2));
v___x_1673_ = l_Lean_Expr_const___override(v___x_1672_, v___x_1671_);
return v___x_1673_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_box(0);
v___x_1678_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5));
v___x_1679_ = l_Lean_Expr_const___override(v___x_1678_, v___x_1677_);
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = lean_box(0);
v___x_1684_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8));
v___x_1685_ = l_Lean_Expr_const___override(v___x_1684_, v___x_1683_);
return v___x_1685_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = lean_box(0);
v___x_1694_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12));
v___x_1695_ = l_Lean_Expr_const___override(v___x_1694_, v___x_1693_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_box(0);
v___x_1703_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15));
v___x_1704_ = l_Lean_Expr_const___override(v___x_1703_, v___x_1702_);
return v___x_1704_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = lean_box(0);
v___x_1711_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18));
v___x_1712_ = l_Lean_Expr_const___override(v___x_1711_, v___x_1710_);
return v___x_1712_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = lean_box(0);
v___x_1719_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21));
v___x_1720_ = l_Lean_Expr_const___override(v___x_1719_, v___x_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof(lean_object* v_m_1721_, lean_object* v_r_1722_, lean_object* v_i_1723_, lean_object* v_x_1724_, lean_object* v_v_1725_, lean_object* v_w_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_m_1732_; lean_object* v___y_1734_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v_m_1732_ = l_Lean_mkNatLit(v_m_1721_);
v___x_1762_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1763_ = lean_int_dec_le(v___x_1762_, v_r_1722_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1764_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1765_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1766_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1767_ = lean_int_neg(v_r_1722_);
v___x_1768_ = l_Int_toNat(v___x_1767_);
lean_dec(v___x_1767_);
v___x_1769_ = l_Lean_instToExprInt_mkNat(v___x_1768_);
v___x_1770_ = l_Lean_mkApp3(v___x_1764_, v___x_1765_, v___x_1766_, v___x_1769_);
v___y_1734_ = v___x_1770_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = l_Int_toNat(v_r_1722_);
v___x_1772_ = l_Lean_instToExprInt_mkNat(v___x_1771_);
v___y_1734_ = v___x_1772_;
goto v___jp_1733_;
}
v___jp_1733_:
{
lean_object* v_i_1735_; lean_object* v_nil_1736_; lean_object* v_cons_1737_; lean_object* v_x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_i_1735_ = l_Lean_mkNatLit(v_i_1723_);
v_nil_1736_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1737_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v_x_1738_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1736_, v_cons_1737_, v_x_1724_);
v___x_1739_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3);
v___x_1740_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6);
v___x_1741_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9);
v___x_1742_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13);
lean_inc_ref(v_x_1738_);
v___x_1743_ = l_Lean_Expr_app___override(v___x_1742_, v_x_1738_);
lean_inc_ref(v_i_1735_);
v___x_1744_ = l_Lean_mkApp4(v___x_1739_, v___x_1740_, v___x_1741_, v___x_1743_, v_i_1735_);
v___x_1745_ = l_Lean_Meta_mkDecideProof(v___x_1744_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref(v___x_1745_);
v___x_1747_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16);
lean_inc_ref(v_i_1735_);
lean_inc_ref_n(v_v_1725_, 2);
v___x_1748_ = l_Lean_mkAppB(v___x_1747_, v_v_1725_, v_i_1735_);
v___x_1749_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc_ref(v_x_1738_);
lean_inc_ref(v_m_1732_);
v___x_1750_ = l_Lean_mkApp3(v___x_1749_, v_m_1732_, v_x_1738_, v_v_1725_);
v___x_1751_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v___x_1748_, v___x_1750_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1761_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1761_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1761_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1756_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22);
v___x_1757_ = l_Lean_mkApp8(v___x_1756_, v_m_1732_, v___y_1734_, v_i_1735_, v_x_1738_, v_v_1725_, v_a_1746_, v_a_1752_, v_w_1726_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1757_);
v___x_1759_ = v___x_1754_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
else
{
lean_dec(v_a_1746_);
lean_dec_ref(v_x_1738_);
lean_dec_ref(v_i_1735_);
lean_dec_ref(v___y_1734_);
lean_dec_ref(v_m_1732_);
lean_dec_ref(v_w_1726_);
lean_dec_ref(v_v_1725_);
return v___x_1751_;
}
}
else
{
lean_dec_ref(v_x_1738_);
lean_dec_ref(v_i_1735_);
lean_dec_ref(v___y_1734_);
lean_dec_ref(v_m_1732_);
lean_dec_ref(v_w_1726_);
lean_dec_ref(v_v_1725_);
return v___x_1745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___boxed(lean_object* v_m_1773_, lean_object* v_r_1774_, lean_object* v_i_1775_, lean_object* v_x_1776_, lean_object* v_v_1777_, lean_object* v_w_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1773_, v_r_1774_, v_i_1775_, v_x_1776_, v_v_1777_, v_w_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_x_1776_);
lean_dec(v_r_1774_);
return v_res_1784_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0(void){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_instMonadEIO(lean_box(0));
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0);
v___x_1787_ = l_StateRefT_x27_instMonad___redArg(v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(lean_object* v_c_1792_, lean_object* v_v_1793_, lean_object* v_assumptions_1794_, lean_object* v_x_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, uint8_t v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___x_1806_; lean_object* v_toApplicative_1807_; lean_object* v_toFunctor_1808_; lean_object* v_toSeq_1809_; lean_object* v_toSeqLeft_1810_; lean_object* v_toSeqRight_1811_; lean_object* v___f_1812_; lean_object* v___f_1813_; lean_object* v___f_1814_; lean_object* v___f_1815_; lean_object* v___x_1816_; lean_object* v___f_1817_; lean_object* v___f_1818_; lean_object* v___f_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v_toApplicative_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1918_; 
v___x_1806_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1);
v_toApplicative_1807_ = lean_ctor_get(v___x_1806_, 0);
v_toFunctor_1808_ = lean_ctor_get(v_toApplicative_1807_, 0);
v_toSeq_1809_ = lean_ctor_get(v_toApplicative_1807_, 2);
v_toSeqLeft_1810_ = lean_ctor_get(v_toApplicative_1807_, 3);
v_toSeqRight_1811_ = lean_ctor_get(v_toApplicative_1807_, 4);
v___f_1812_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2));
v___f_1813_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1808_, 2);
v___f_1814_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1814_, 0, v_toFunctor_1808_);
v___f_1815_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1815_, 0, v_toFunctor_1808_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___f_1814_);
lean_ctor_set(v___x_1816_, 1, v___f_1815_);
lean_inc(v_toSeqRight_1811_);
v___f_1817_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1817_, 0, v_toSeqRight_1811_);
lean_inc(v_toSeqLeft_1810_);
v___f_1818_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1818_, 0, v_toSeqLeft_1810_);
lean_inc(v_toSeq_1809_);
v___f_1819_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1819_, 0, v_toSeq_1809_);
v___x_1820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1816_);
lean_ctor_set(v___x_1820_, 1, v___f_1812_);
lean_ctor_set(v___x_1820_, 2, v___f_1819_);
lean_ctor_set(v___x_1820_, 3, v___f_1818_);
lean_ctor_set(v___x_1820_, 4, v___f_1817_);
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
lean_ctor_set(v___x_1821_, 1, v___f_1813_);
v___x_1822_ = l_StateRefT_x27_instMonad___redArg(v___x_1821_);
v_toApplicative_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v___x_1822_, 1);
lean_dec(v_unused_1919_);
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1918_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_toApplicative_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1918_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_toFunctor_1827_; lean_object* v_toSeq_1828_; lean_object* v_toSeqLeft_1829_; lean_object* v_toSeqRight_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1916_; 
v_toFunctor_1827_ = lean_ctor_get(v_toApplicative_1823_, 0);
v_toSeq_1828_ = lean_ctor_get(v_toApplicative_1823_, 2);
v_toSeqLeft_1829_ = lean_ctor_get(v_toApplicative_1823_, 3);
v_toSeqRight_1830_ = lean_ctor_get(v_toApplicative_1823_, 4);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_toApplicative_1823_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; 
v_unused_1917_ = lean_ctor_get(v_toApplicative_1823_, 1);
lean_dec(v_unused_1917_);
v___x_1832_ = v_toApplicative_1823_;
v_isShared_1833_ = v_isSharedCheck_1916_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_toSeqRight_1830_);
lean_inc(v_toSeqLeft_1829_);
lean_inc(v_toSeq_1828_);
lean_inc(v_toFunctor_1827_);
lean_dec(v_toApplicative_1823_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1916_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___f_1834_; lean_object* v___f_1835_; lean_object* v___f_1836_; lean_object* v___f_1837_; lean_object* v___x_1838_; lean_object* v___f_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___x_1843_; 
v___f_1834_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4));
v___f_1835_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5));
lean_inc_ref(v_toFunctor_1827_);
v___f_1836_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1836_, 0, v_toFunctor_1827_);
v___f_1837_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1837_, 0, v_toFunctor_1827_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___f_1836_);
lean_ctor_set(v___x_1838_, 1, v___f_1837_);
v___f_1839_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1839_, 0, v_toSeqRight_1830_);
v___f_1840_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1840_, 0, v_toSeqLeft_1829_);
v___f_1841_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1841_, 0, v_toSeq_1828_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 4, v___f_1839_);
lean_ctor_set(v___x_1832_, 3, v___f_1840_);
lean_ctor_set(v___x_1832_, 2, v___f_1841_);
lean_ctor_set(v___x_1832_, 1, v___f_1834_);
lean_ctor_set(v___x_1832_, 0, v___x_1838_);
v___x_1843_ = v___x_1832_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___f_1834_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v___f_1841_);
lean_ctor_set(v_reuseFailAlloc_1915_, 3, v___f_1840_);
lean_ctor_set(v_reuseFailAlloc_1915_, 4, v___f_1839_);
v___x_1843_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 1, v___f_1835_);
lean_ctor_set(v___x_1825_, 0, v___x_1843_);
v___x_1845_ = v___x_1825_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___f_1835_);
v___x_1845_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1846_ = l_StateRefT_x27_instMonad___redArg(v___x_1845_);
v___x_1847_ = l_ReaderT_instMonad___redArg(v___x_1846_);
v___x_1848_ = l_ReaderT_instMonad___redArg(v___x_1847_);
v___x_1849_ = l_StateRefT_x27_instMonad___redArg(v___x_1848_);
v___x_1850_ = l_StateRefT_x27_instMonad___redArg(v___x_1849_);
switch(lean_obj_tag(v_x_1795_))
{
case 0:
{
lean_object* v_i_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_3965__overap_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec_ref(v_v_1793_);
v_i_1851_ = lean_ctor_get(v_x_1795_, 2);
lean_inc(v_i_1851_);
lean_dec_ref(v_x_1795_);
v___x_1852_ = l_Lean_instInhabitedExpr;
v___x_1853_ = l_instInhabitedOfMonad___redArg(v___x_1850_, v___x_1852_);
v___x_3965__overap_1854_ = lean_array_get(v___x_1853_, v_assumptions_1794_, v_i_1851_);
lean_dec(v_i_1851_);
lean_dec(v___x_1853_);
v___x_1855_ = lean_box(v_a_1799_);
lean_inc(v_a_1804_);
lean_inc_ref(v_a_1803_);
lean_inc(v_a_1802_);
lean_inc_ref(v_a_1801_);
lean_inc(v_a_1800_);
lean_inc_ref(v_a_1798_);
lean_inc(v_a_1797_);
lean_inc(v_a_1796_);
v___x_1856_ = lean_apply_10(v___x_3965__overap_1854_, v_a_1796_, v_a_1797_, v_a_1798_, v___x_1855_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, lean_box(0));
return v___x_1856_;
}
case 1:
{
lean_object* v_s_1857_; lean_object* v_c_1858_; lean_object* v_j_1859_; lean_object* v___x_1860_; 
lean_dec_ref(v___x_1850_);
v_s_1857_ = lean_ctor_get(v_x_1795_, 0);
lean_inc_ref(v_s_1857_);
v_c_1858_ = lean_ctor_get(v_x_1795_, 1);
lean_inc(v_c_1858_);
v_j_1859_ = lean_ctor_get(v_x_1795_, 2);
lean_inc_ref(v_j_1859_);
lean_dec_ref(v_x_1795_);
lean_inc_ref(v_v_1793_);
v___x_1860_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1858_, v_v_1793_, v_assumptions_1794_, v_j_1859_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1869_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1865_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1857_, v_c_1858_, v_v_1793_, v_a_1861_);
lean_dec(v_c_1858_);
lean_dec_ref(v_s_1857_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1865_);
v___x_1867_ = v___x_1863_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_dec(v_c_1858_);
lean_dec_ref(v_s_1857_);
lean_dec_ref(v_v_1793_);
return v___x_1860_;
}
}
case 2:
{
lean_object* v_s_1870_; lean_object* v_t_1871_; lean_object* v_j_1872_; lean_object* v_k_1873_; lean_object* v___x_1874_; 
lean_dec_ref(v___x_1850_);
v_s_1870_ = lean_ctor_get(v_x_1795_, 0);
lean_inc_ref(v_s_1870_);
v_t_1871_ = lean_ctor_get(v_x_1795_, 1);
lean_inc_ref(v_t_1871_);
v_j_1872_ = lean_ctor_get(v_x_1795_, 3);
lean_inc_ref(v_j_1872_);
v_k_1873_ = lean_ctor_get(v_x_1795_, 4);
lean_inc_ref(v_k_1873_);
lean_dec_ref(v_x_1795_);
lean_inc_ref(v_v_1793_);
v___x_1874_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1792_, v_v_1793_, v_assumptions_1794_, v_j_1872_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1876_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref(v___x_1874_);
lean_inc_ref(v_v_1793_);
v___x_1876_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1792_, v_v_1793_, v_assumptions_1794_, v_k_1873_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1885_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1881_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1870_, v_t_1871_, v_c_1792_, v_v_1793_, v_a_1875_, v_a_1877_);
lean_dec_ref(v_t_1871_);
lean_dec_ref(v_s_1870_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1881_);
v___x_1883_ = v___x_1879_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
else
{
lean_dec(v_a_1875_);
lean_dec_ref(v_t_1871_);
lean_dec_ref(v_s_1870_);
lean_dec_ref(v_v_1793_);
return v___x_1876_;
}
}
else
{
lean_dec_ref(v_k_1873_);
lean_dec_ref(v_t_1871_);
lean_dec_ref(v_s_1870_);
lean_dec_ref(v_v_1793_);
return v___x_1874_;
}
}
case 3:
{
lean_object* v_s_1886_; lean_object* v_t_1887_; lean_object* v_x_1888_; lean_object* v_y_1889_; lean_object* v_a_1890_; lean_object* v_j_1891_; lean_object* v_b_1892_; lean_object* v_k_1893_; lean_object* v___x_1894_; 
lean_dec_ref(v___x_1850_);
v_s_1886_ = lean_ctor_get(v_x_1795_, 0);
lean_inc_ref(v_s_1886_);
v_t_1887_ = lean_ctor_get(v_x_1795_, 1);
lean_inc_ref(v_t_1887_);
v_x_1888_ = lean_ctor_get(v_x_1795_, 2);
lean_inc(v_x_1888_);
v_y_1889_ = lean_ctor_get(v_x_1795_, 3);
lean_inc(v_y_1889_);
v_a_1890_ = lean_ctor_get(v_x_1795_, 4);
lean_inc(v_a_1890_);
v_j_1891_ = lean_ctor_get(v_x_1795_, 5);
lean_inc_ref(v_j_1891_);
v_b_1892_ = lean_ctor_get(v_x_1795_, 6);
lean_inc(v_b_1892_);
v_k_1893_ = lean_ctor_get(v_x_1795_, 7);
lean_inc_ref(v_k_1893_);
lean_dec_ref(v_x_1795_);
lean_inc_ref(v_v_1793_);
v___x_1894_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1888_, v_v_1793_, v_assumptions_1794_, v_j_1891_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1896_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref(v___x_1894_);
lean_inc_ref(v_v_1793_);
v___x_1896_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_y_1889_, v_v_1793_, v_assumptions_1794_, v_k_1893_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1905_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1886_, v_t_1887_, v_a_1890_, v_x_1888_, v_b_1892_, v_y_1889_, v_v_1793_, v_a_1895_, v_a_1897_);
lean_dec(v_y_1889_);
lean_dec(v_b_1892_);
lean_dec(v_x_1888_);
lean_dec(v_a_1890_);
lean_dec_ref(v_t_1887_);
lean_dec_ref(v_s_1886_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1901_);
v___x_1903_ = v___x_1899_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
else
{
lean_dec(v_a_1895_);
lean_dec(v_b_1892_);
lean_dec(v_a_1890_);
lean_dec(v_y_1889_);
lean_dec(v_x_1888_);
lean_dec_ref(v_t_1887_);
lean_dec_ref(v_s_1886_);
lean_dec_ref(v_v_1793_);
return v___x_1896_;
}
}
else
{
lean_dec_ref(v_k_1893_);
lean_dec(v_b_1892_);
lean_dec(v_a_1890_);
lean_dec(v_y_1889_);
lean_dec(v_x_1888_);
lean_dec_ref(v_t_1887_);
lean_dec_ref(v_s_1886_);
lean_dec_ref(v_v_1793_);
return v___x_1894_;
}
}
default: 
{
lean_object* v_m_1906_; lean_object* v_r_1907_; lean_object* v_i_1908_; lean_object* v_x_1909_; lean_object* v_j_1910_; lean_object* v___x_1911_; 
lean_dec_ref(v___x_1850_);
v_m_1906_ = lean_ctor_get(v_x_1795_, 0);
lean_inc(v_m_1906_);
v_r_1907_ = lean_ctor_get(v_x_1795_, 1);
lean_inc(v_r_1907_);
v_i_1908_ = lean_ctor_get(v_x_1795_, 2);
lean_inc(v_i_1908_);
v_x_1909_ = lean_ctor_get(v_x_1795_, 3);
lean_inc(v_x_1909_);
v_j_1910_ = lean_ctor_get(v_x_1795_, 4);
lean_inc_ref(v_j_1910_);
lean_dec_ref(v_x_1795_);
lean_inc_ref(v_v_1793_);
v___x_1911_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1909_, v_v_1793_, v_assumptions_1794_, v_j_1910_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
v___x_1913_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1906_, v_r_1907_, v_i_1908_, v_x_1909_, v_v_1793_, v_a_1912_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec(v_x_1909_);
lean_dec(v_r_1907_);
return v___x_1913_;
}
else
{
lean_dec(v_x_1909_);
lean_dec(v_i_1908_);
lean_dec(v_r_1907_);
lean_dec(v_m_1906_);
lean_dec_ref(v_v_1793_);
return v___x_1911_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___boxed(lean_object* v_c_1920_, lean_object* v_v_1921_, lean_object* v_assumptions_1922_, lean_object* v_x_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
uint8_t v_a_boxed_1934_; lean_object* v_res_1935_; 
v_a_boxed_1934_ = lean_unbox(v_a_1927_);
v_res_1935_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1920_, v_v_1921_, v_assumptions_1922_, v_x_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_boxed_1934_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1926_);
lean_dec(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec_ref(v_assumptions_1922_);
lean_dec(v_c_1920_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof(lean_object* v_s_1936_, lean_object* v_c_1937_, lean_object* v_v_1938_, lean_object* v_assumptions_1939_, lean_object* v_x_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, uint8_t v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1937_, v_v_1938_, v_assumptions_1939_, v_x_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___boxed(lean_object* v_s_1952_, lean_object* v_c_1953_, lean_object* v_v_1954_, lean_object* v_assumptions_1955_, lean_object* v_x_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
uint8_t v_a_boxed_1967_; lean_object* v_res_1968_; 
v_a_boxed_1967_ = lean_unbox(v_a_1960_);
v_res_1968_ = l_Lean_Elab_Tactic_Omega_Justification_proof(v_s_1952_, v_c_1953_, v_v_1954_, v_assumptions_1955_, v_x_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_boxed_1967_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1959_);
lean_dec(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec_ref(v_assumptions_1955_);
lean_dec(v_c_1953_);
lean_dec_ref(v_s_1952_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_instToString___lam__0(lean_object* v_f_1969_){
_start:
{
lean_object* v_coeffs_1970_; lean_object* v_constraint_1971_; lean_object* v_justification_1972_; lean_object* v___x_1973_; 
v_coeffs_1970_ = lean_ctor_get(v_f_1969_, 0);
lean_inc(v_coeffs_1970_);
v_constraint_1971_ = lean_ctor_get(v_f_1969_, 1);
lean_inc_ref(v_constraint_1971_);
v_justification_1972_ = lean_ctor_get(v_f_1969_, 2);
lean_inc_ref(v_justification_1972_);
lean_dec_ref(v_f_1969_);
v___x_1973_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_1971_, v_coeffs_1970_, v_justification_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_tidy(lean_object* v_f_1976_){
_start:
{
lean_object* v_coeffs_1977_; lean_object* v_constraint_1978_; lean_object* v_justification_1979_; lean_object* v___x_1980_; 
v_coeffs_1977_ = lean_ctor_get(v_f_1976_, 0);
v_constraint_1978_ = lean_ctor_get(v_f_1976_, 1);
v_justification_1979_ = lean_ctor_get(v_f_1976_, 2);
lean_inc_ref(v_justification_1979_);
lean_inc(v_coeffs_1977_);
lean_inc_ref(v_constraint_1978_);
v___x_1980_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(v_constraint_1978_, v_coeffs_1977_, v_justification_1979_);
if (lean_obj_tag(v___x_1980_) == 0)
{
return v_f_1976_;
}
else
{
lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1992_; 
v_isSharedCheck_1992_ = !lean_is_exclusive(v_f_1976_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; lean_object* v_unused_1994_; lean_object* v_unused_1995_; 
v_unused_1993_ = lean_ctor_get(v_f_1976_, 2);
lean_dec(v_unused_1993_);
v_unused_1994_ = lean_ctor_get(v_f_1976_, 1);
lean_dec(v_unused_1994_);
v_unused_1995_ = lean_ctor_get(v_f_1976_, 0);
lean_dec(v_unused_1995_);
v___x_1982_ = v_f_1976_;
v_isShared_1983_ = v_isSharedCheck_1992_;
goto v_resetjp_1981_;
}
else
{
lean_dec(v_f_1976_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1992_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v_val_1984_; lean_object* v_snd_1985_; lean_object* v_fst_1986_; lean_object* v_fst_1987_; lean_object* v_snd_1988_; lean_object* v___x_1990_; 
v_val_1984_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_val_1984_);
lean_dec_ref(v___x_1980_);
v_snd_1985_ = lean_ctor_get(v_val_1984_, 1);
lean_inc(v_snd_1985_);
v_fst_1986_ = lean_ctor_get(v_val_1984_, 0);
lean_inc(v_fst_1986_);
lean_dec(v_val_1984_);
v_fst_1987_ = lean_ctor_get(v_snd_1985_, 0);
lean_inc(v_fst_1987_);
v_snd_1988_ = lean_ctor_get(v_snd_1985_, 1);
lean_inc(v_snd_1988_);
lean_dec(v_snd_1985_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 2, v_snd_1988_);
lean_ctor_set(v___x_1982_, 1, v_fst_1986_);
lean_ctor_set(v___x_1982_, 0, v_fst_1987_);
v___x_1990_ = v___x_1982_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_fst_1987_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_fst_1986_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_snd_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_combo(lean_object* v_a_1996_, lean_object* v_f_1997_, lean_object* v_b_1998_, lean_object* v_g_1999_){
_start:
{
lean_object* v_coeffs_2000_; lean_object* v_constraint_2001_; lean_object* v_justification_2002_; lean_object* v_coeffs_2003_; lean_object* v_constraint_2004_; lean_object* v_justification_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2015_; 
v_coeffs_2000_ = lean_ctor_get(v_f_1997_, 0);
lean_inc(v_coeffs_2000_);
v_constraint_2001_ = lean_ctor_get(v_f_1997_, 1);
lean_inc_ref(v_constraint_2001_);
v_justification_2002_ = lean_ctor_get(v_f_1997_, 2);
lean_inc_ref(v_justification_2002_);
lean_dec_ref(v_f_1997_);
v_coeffs_2003_ = lean_ctor_get(v_g_1999_, 0);
v_constraint_2004_ = lean_ctor_get(v_g_1999_, 1);
v_justification_2005_ = lean_ctor_get(v_g_1999_, 2);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_g_1999_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2007_ = v_g_1999_;
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_justification_2005_);
lean_inc(v_constraint_2004_);
lean_inc(v_coeffs_2003_);
lean_dec(v_g_1999_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
lean_inc(v_coeffs_2003_);
lean_inc_n(v_b_1998_, 2);
lean_inc(v_coeffs_2000_);
lean_inc_n(v_a_1996_, 2);
v___x_2009_ = l_Lean_Omega_IntList_combo(v_a_1996_, v_coeffs_2000_, v_b_1998_, v_coeffs_2003_);
lean_inc_ref(v_constraint_2004_);
lean_inc_ref(v_constraint_2001_);
v___x_2010_ = l_Lean_Omega_Constraint_combo(v_a_1996_, v_constraint_2001_, v_b_1998_, v_constraint_2004_);
v___x_2011_ = lean_alloc_ctor(3, 8, 0);
lean_ctor_set(v___x_2011_, 0, v_constraint_2001_);
lean_ctor_set(v___x_2011_, 1, v_constraint_2004_);
lean_ctor_set(v___x_2011_, 2, v_coeffs_2000_);
lean_ctor_set(v___x_2011_, 3, v_coeffs_2003_);
lean_ctor_set(v___x_2011_, 4, v_a_1996_);
lean_ctor_set(v___x_2011_, 5, v_justification_2002_);
lean_ctor_set(v___x_2011_, 6, v_b_1998_);
lean_ctor_set(v___x_2011_, 7, v_justification_2005_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 2, v___x_2011_);
lean_ctor_set(v___x_2007_, 1, v___x_2010_);
lean_ctor_set(v___x_2007_, 0, v___x_2009_);
v___x_2013_ = v___x_2007_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__10));
v___x_2042_ = l_Lean_mkAtom(v___x_2041_);
return v___x_2042_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2043_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11);
v___x_2044_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2045_ = lean_array_push(v___x_2044_, v___x_2043_);
return v___x_2045_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2046_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12);
v___x_2047_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9));
v___x_2048_ = lean_box(2);
v___x_2049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v___x_2047_);
lean_ctor_set(v___x_2049_, 2, v___x_2046_);
return v___x_2049_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13);
v___x_2051_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2052_ = lean_array_push(v___x_2051_, v___x_2050_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2053_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14);
v___x_2054_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7));
v___x_2055_ = lean_box(2);
v___x_2056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v___x_2054_);
lean_ctor_set(v___x_2056_, 2, v___x_2053_);
return v___x_2056_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15);
v___x_2058_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2059_ = lean_array_push(v___x_2058_, v___x_2057_);
return v___x_2059_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2060_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16);
v___x_2061_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5));
v___x_2062_ = lean_box(2);
v___x_2063_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v___x_2061_);
lean_ctor_set(v___x_2063_, 2, v___x_2060_);
return v___x_2063_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17);
v___x_2065_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2066_ = lean_array_push(v___x_2065_, v___x_2064_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2067_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18);
v___x_2068_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2));
v___x_2069_ = lean_box(2);
v___x_2070_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v___x_2068_);
lean_ctor_set(v___x_2070_, 2, v___x_2067_);
return v___x_2070_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam(void){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19);
return v___x_2071_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_isEmpty(lean_object* v_p_2072_){
_start:
{
lean_object* v_constraints_2073_; lean_object* v_size_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v_constraints_2073_ = lean_ctor_get(v_p_2072_, 2);
v_size_2074_ = lean_ctor_get(v_constraints_2073_, 0);
v___x_2075_ = lean_unsigned_to_nat(0u);
v___x_2076_ = lean_nat_dec_eq(v_size_2074_, v___x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_isEmpty___boxed(lean_object* v_p_2077_){
_start:
{
uint8_t v_res_2078_; lean_object* v_r_2079_; 
v_res_2078_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2077_);
lean_dec_ref(v_p_2077_);
v_r_2079_ = lean_box(v_res_2078_);
return v_r_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object* v_x_2081_){
_start:
{
lean_object* v_snd_2082_; lean_object* v_constraint_2083_; lean_object* v_fst_2084_; lean_object* v_lowerBound_2085_; lean_object* v_upperBound_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___y_2092_; lean_object* v___y_2093_; 
v_snd_2082_ = lean_ctor_get(v_x_2081_, 1);
v_constraint_2083_ = lean_ctor_get(v_snd_2082_, 1);
lean_inc_ref(v_constraint_2083_);
v_fst_2084_ = lean_ctor_get(v_x_2081_, 0);
lean_inc(v_fst_2084_);
lean_dec_ref(v_x_2081_);
v_lowerBound_2085_ = lean_ctor_get(v_constraint_2083_, 0);
lean_inc(v_lowerBound_2085_);
v_upperBound_2086_ = lean_ctor_get(v_constraint_2083_, 1);
lean_inc(v_upperBound_2086_);
lean_dec_ref(v_constraint_2083_);
v___x_2087_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0___closed__0));
v___x_2088_ = l_List_toString___redArg(v___x_2087_, v_fst_2084_);
v___x_2089_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_2090_ = lean_string_append(v___x_2088_, v___x_2089_);
if (lean_obj_tag(v_lowerBound_2085_) == 0)
{
if (lean_obj_tag(v_upperBound_2086_) == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_2099_ = lean_string_append(v___x_2090_, v___x_2098_);
return v___x_2099_;
}
else
{
lean_object* v_val_2100_; lean_object* v___x_2101_; lean_object* v___y_2103_; lean_object* v_intZero_2108_; uint8_t v_isNeg_2109_; 
v_val_2100_ = lean_ctor_get(v_upperBound_2086_, 0);
lean_inc(v_val_2100_);
lean_dec_ref(v_upperBound_2086_);
v___x_2101_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_2108_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2109_ = lean_int_dec_lt(v_val_2100_, v_intZero_2108_);
if (v_isNeg_2109_ == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; 
v_a_2110_ = lean_nat_abs(v_val_2100_);
lean_dec(v_val_2100_);
v___x_2111_ = l_Nat_reprFast(v_a_2110_);
v___y_2103_ = v___x_2111_;
goto v___jp_2102_;
}
else
{
lean_object* v_abs_2112_; lean_object* v_one_2113_; lean_object* v_a_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_abs_2112_ = lean_nat_abs(v_val_2100_);
lean_dec(v_val_2100_);
v_one_2113_ = lean_unsigned_to_nat(1u);
v_a_2114_ = lean_nat_sub(v_abs_2112_, v_one_2113_);
lean_dec(v_abs_2112_);
v___x_2115_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2116_ = lean_nat_add(v_a_2114_, v_one_2113_);
lean_dec(v_a_2114_);
v___x_2117_ = l_Nat_reprFast(v___x_2116_);
v___x_2118_ = lean_string_append(v___x_2115_, v___x_2117_);
lean_dec_ref(v___x_2117_);
v___y_2103_ = v___x_2118_;
goto v___jp_2102_;
}
v___jp_2102_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2104_ = lean_string_append(v___x_2101_, v___y_2103_);
lean_dec_ref(v___y_2103_);
v___x_2105_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2106_ = lean_string_append(v___x_2104_, v___x_2105_);
v___x_2107_ = lean_string_append(v___x_2090_, v___x_2106_);
lean_dec_ref(v___x_2106_);
return v___x_2107_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_2086_) == 0)
{
lean_object* v_val_2119_; lean_object* v___x_2120_; lean_object* v___y_2122_; lean_object* v_intZero_2127_; uint8_t v_isNeg_2128_; 
v_val_2119_ = lean_ctor_get(v_lowerBound_2085_, 0);
lean_inc(v_val_2119_);
lean_dec_ref(v_lowerBound_2085_);
v___x_2120_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2127_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2128_ = lean_int_dec_lt(v_val_2119_, v_intZero_2127_);
if (v_isNeg_2128_ == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; 
v_a_2129_ = lean_nat_abs(v_val_2119_);
lean_dec(v_val_2119_);
v___x_2130_ = l_Nat_reprFast(v_a_2129_);
v___y_2122_ = v___x_2130_;
goto v___jp_2121_;
}
else
{
lean_object* v_abs_2131_; lean_object* v_one_2132_; lean_object* v_a_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_abs_2131_ = lean_nat_abs(v_val_2119_);
lean_dec(v_val_2119_);
v_one_2132_ = lean_unsigned_to_nat(1u);
v_a_2133_ = lean_nat_sub(v_abs_2131_, v_one_2132_);
lean_dec(v_abs_2131_);
v___x_2134_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2135_ = lean_nat_add(v_a_2133_, v_one_2132_);
lean_dec(v_a_2133_);
v___x_2136_ = l_Nat_reprFast(v___x_2135_);
v___x_2137_ = lean_string_append(v___x_2134_, v___x_2136_);
lean_dec_ref(v___x_2136_);
v___y_2122_ = v___x_2137_;
goto v___jp_2121_;
}
v___jp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2123_ = lean_string_append(v___x_2120_, v___y_2122_);
lean_dec_ref(v___y_2122_);
v___x_2124_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_2125_ = lean_string_append(v___x_2123_, v___x_2124_);
v___x_2126_ = lean_string_append(v___x_2090_, v___x_2125_);
lean_dec_ref(v___x_2125_);
return v___x_2126_;
}
}
else
{
lean_object* v_val_2138_; lean_object* v_val_2139_; uint8_t v___x_2140_; 
v_val_2138_ = lean_ctor_get(v_lowerBound_2085_, 0);
lean_inc(v_val_2138_);
lean_dec_ref(v_lowerBound_2085_);
v_val_2139_ = lean_ctor_get(v_upperBound_2086_, 0);
lean_inc(v_val_2139_);
lean_dec_ref(v_upperBound_2086_);
v___x_2140_ = lean_int_dec_lt(v_val_2139_, v_val_2138_);
if (v___x_2140_ == 0)
{
uint8_t v___x_2141_; 
v___x_2141_ = lean_int_dec_eq(v_val_2138_, v_val_2139_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___y_2144_; lean_object* v_intZero_2159_; uint8_t v_isNeg_2160_; 
v___x_2142_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2159_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2160_ = lean_int_dec_lt(v_val_2138_, v_intZero_2159_);
if (v_isNeg_2160_ == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; 
v_a_2161_ = lean_nat_abs(v_val_2138_);
lean_dec(v_val_2138_);
v___x_2162_ = l_Nat_reprFast(v_a_2161_);
v___y_2144_ = v___x_2162_;
goto v___jp_2143_;
}
else
{
lean_object* v_abs_2163_; lean_object* v_one_2164_; lean_object* v_a_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v_abs_2163_ = lean_nat_abs(v_val_2138_);
lean_dec(v_val_2138_);
v_one_2164_ = lean_unsigned_to_nat(1u);
v_a_2165_ = lean_nat_sub(v_abs_2163_, v_one_2164_);
lean_dec(v_abs_2163_);
v___x_2166_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2167_ = lean_nat_add(v_a_2165_, v_one_2164_);
lean_dec(v_a_2165_);
v___x_2168_ = l_Nat_reprFast(v___x_2167_);
v___x_2169_ = lean_string_append(v___x_2166_, v___x_2168_);
lean_dec_ref(v___x_2168_);
v___y_2144_ = v___x_2169_;
goto v___jp_2143_;
}
v___jp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v_intZero_2148_; uint8_t v_isNeg_2149_; 
v___x_2145_ = lean_string_append(v___x_2142_, v___y_2144_);
lean_dec_ref(v___y_2144_);
v___x_2146_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_2147_ = lean_string_append(v___x_2145_, v___x_2146_);
v_intZero_2148_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2149_ = lean_int_dec_lt(v_val_2139_, v_intZero_2148_);
if (v_isNeg_2149_ == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; 
v_a_2150_ = lean_nat_abs(v_val_2139_);
lean_dec(v_val_2139_);
v___x_2151_ = l_Nat_reprFast(v_a_2150_);
v___y_2092_ = v___x_2147_;
v___y_2093_ = v___x_2151_;
goto v___jp_2091_;
}
else
{
lean_object* v_abs_2152_; lean_object* v_one_2153_; lean_object* v_a_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_abs_2152_ = lean_nat_abs(v_val_2139_);
lean_dec(v_val_2139_);
v_one_2153_ = lean_unsigned_to_nat(1u);
v_a_2154_ = lean_nat_sub(v_abs_2152_, v_one_2153_);
lean_dec(v_abs_2152_);
v___x_2155_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2156_ = lean_nat_add(v_a_2154_, v_one_2153_);
lean_dec(v_a_2154_);
v___x_2157_ = l_Nat_reprFast(v___x_2156_);
v___x_2158_ = lean_string_append(v___x_2155_, v___x_2157_);
lean_dec_ref(v___x_2157_);
v___y_2092_ = v___x_2147_;
v___y_2093_ = v___x_2158_;
goto v___jp_2091_;
}
}
}
else
{
lean_object* v___x_2170_; lean_object* v___y_2172_; lean_object* v_intZero_2177_; uint8_t v_isNeg_2178_; 
lean_dec(v_val_2139_);
v___x_2170_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_2177_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2178_ = lean_int_dec_lt(v_val_2138_, v_intZero_2177_);
if (v_isNeg_2178_ == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; 
v_a_2179_ = lean_nat_abs(v_val_2138_);
lean_dec(v_val_2138_);
v___x_2180_ = l_Nat_reprFast(v_a_2179_);
v___y_2172_ = v___x_2180_;
goto v___jp_2171_;
}
else
{
lean_object* v_abs_2181_; lean_object* v_one_2182_; lean_object* v_a_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_abs_2181_ = lean_nat_abs(v_val_2138_);
lean_dec(v_val_2138_);
v_one_2182_ = lean_unsigned_to_nat(1u);
v_a_2183_ = lean_nat_sub(v_abs_2181_, v_one_2182_);
lean_dec(v_abs_2181_);
v___x_2184_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2185_ = lean_nat_add(v_a_2183_, v_one_2182_);
lean_dec(v_a_2183_);
v___x_2186_ = l_Nat_reprFast(v___x_2185_);
v___x_2187_ = lean_string_append(v___x_2184_, v___x_2186_);
lean_dec_ref(v___x_2186_);
v___y_2172_ = v___x_2187_;
goto v___jp_2171_;
}
v___jp_2171_:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2173_ = lean_string_append(v___x_2170_, v___y_2172_);
lean_dec_ref(v___y_2172_);
v___x_2174_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_2175_ = lean_string_append(v___x_2173_, v___x_2174_);
v___x_2176_ = lean_string_append(v___x_2090_, v___x_2175_);
lean_dec_ref(v___x_2175_);
return v___x_2176_;
}
}
}
else
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_dec(v_val_2139_);
lean_dec(v_val_2138_);
v___x_2188_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_2189_ = lean_string_append(v___x_2090_, v___x_2188_);
return v___x_2189_;
}
}
}
v___jp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2094_ = lean_string_append(v___y_2092_, v___y_2093_);
lean_dec_ref(v___y_2093_);
v___x_2095_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2096_ = lean_string_append(v___x_2094_, v___x_2095_);
v___x_2097_ = lean_string_append(v___x_2090_, v___x_2096_);
lean_dec_ref(v___x_2096_);
return v___x_2097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object* v_a_2190_, lean_object* v_b_2191_, lean_object* v_d_2192_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2193_, 0, v_a_2190_);
lean_ctor_set(v___x_2193_, 1, v_b_2191_);
v___x_2194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
lean_ctor_set(v___x_2194_, 1, v_d_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2(lean_object* v___x_2195_, lean_object* v___f_2196_, lean_object* v_l_2197_, lean_object* v_acc_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2195_, v___f_2196_, v_acc_2198_, v_l_2197_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3(lean_object* v___f_2221_, lean_object* v___f_2222_, lean_object* v_p_2223_){
_start:
{
uint8_t v_possible_2224_; 
v_possible_2224_ = lean_ctor_get_uint8(v_p_2223_, sizeof(void*)*7);
if (v_possible_2224_ == 0)
{
lean_object* v___x_2225_; 
lean_dec_ref(v_p_2223_);
lean_dec_ref(v___f_2222_);
lean_dec_ref(v___f_2221_);
v___x_2225_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
return v___x_2225_;
}
else
{
lean_object* v_constraints_2226_; uint8_t v___x_2227_; 
v_constraints_2226_ = lean_ctor_get(v_p_2223_, 2);
lean_inc_ref(v_constraints_2226_);
v___x_2227_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2223_);
lean_dec_ref(v_p_2223_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; lean_object* v_buckets_2229_; lean_object* v___x_2230_; lean_object* v___y_2232_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v___x_2228_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10));
v_buckets_2229_ = lean_ctor_get(v_constraints_2226_, 1);
lean_inc_ref(v_buckets_2229_);
lean_dec_ref(v_constraints_2226_);
v___x_2230_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_2236_ = lean_box(0);
v___x_2237_ = lean_array_get_size(v_buckets_2229_);
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = lean_nat_dec_lt(v___x_2238_, v___x_2237_);
if (v___x_2239_ == 0)
{
lean_dec_ref(v_buckets_2229_);
lean_dec_ref(v___f_2222_);
v___y_2232_ = v___x_2236_;
goto v___jp_2231_;
}
else
{
lean_object* v___f_2240_; size_t v___x_2241_; size_t v___x_2242_; lean_object* v___x_2243_; 
v___f_2240_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2), 4, 2);
lean_closure_set(v___f_2240_, 0, v___x_2228_);
lean_closure_set(v___f_2240_, 1, v___f_2222_);
v___x_2241_ = lean_usize_of_nat(v___x_2237_);
v___x_2242_ = ((size_t)0ULL);
v___x_2243_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2228_, v___f_2240_, v_buckets_2229_, v___x_2241_, v___x_2242_, v___x_2236_);
v___y_2232_ = v___x_2243_;
goto v___jp_2231_;
}
v___jp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = lean_box(0);
v___x_2234_ = l_List_mapTR_loop___redArg(v___f_2221_, v___y_2232_, v___x_2233_);
v___x_2235_ = l_String_intercalate(v___x_2230_, v___x_2234_);
return v___x_2235_;
}
}
else
{
lean_object* v___x_2244_; 
lean_dec_ref(v_constraints_2226_);
lean_dec_ref(v___f_2222_);
lean_dec_ref(v___f_2221_);
v___x_2244_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
return v___x_2244_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = lean_box(0);
v___x_2258_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1));
v___x_2259_ = l_Lean_Expr_const___override(v___x_2258_, v___x_2257_);
return v___x_2259_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2265_ = lean_box(0);
v___x_2266_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5));
v___x_2267_ = l_Lean_Expr_const___override(v___x_2266_, v___x_2265_);
return v___x_2267_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = lean_box(0);
v___x_2275_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8));
v___x_2276_ = l_Lean_Expr_const___override(v___x_2275_, v___x_2274_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse(lean_object* v_s_2277_, lean_object* v_x_2278_, lean_object* v_j_2279_, lean_object* v_assumptions_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, uint8_t v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2282_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2293_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc_n(v_a_2292_, 2);
lean_dec_ref(v___x_2291_);
v___x_2293_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_2278_, v_a_2292_, v_assumptions_2280_, v_j_2279_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2295_; lean_object* v_lowerBound_2296_; lean_object* v_upperBound_2297_; lean_object* v_nil_2298_; lean_object* v_cons_2299_; lean_object* v___x_2300_; lean_object* v___y_2302_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___x_2325_; lean_object* v___y_2327_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref(v___x_2293_);
v___x_2295_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_lowerBound_2296_ = lean_ctor_get(v_s_2277_, 0);
v_upperBound_2297_ = lean_ctor_get(v_s_2277_, 1);
v_nil_2298_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2299_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2300_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2298_, v_cons_2299_, v_x_2278_);
v___x_2325_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
if (lean_obj_tag(v_lowerBound_2296_) == 0)
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_2327_ = v___x_2343_;
goto v___jp_2326_;
}
else
{
lean_object* v_val_2344_; lean_object* v___x_2345_; lean_object* v___y_2347_; lean_object* v___x_2349_; uint8_t v___x_2350_; 
v_val_2344_ = lean_ctor_get(v_lowerBound_2296_, 0);
v___x_2345_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2349_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2350_ = lean_int_dec_le(v___x_2349_, v_val_2344_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2351_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2352_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2353_ = lean_int_neg(v_val_2344_);
v___x_2354_ = l_Int_toNat(v___x_2353_);
lean_dec(v___x_2353_);
v___x_2355_ = l_Lean_instToExprInt_mkNat(v___x_2354_);
v___x_2356_ = l_Lean_mkApp3(v___x_2351_, v___x_2295_, v___x_2352_, v___x_2355_);
v___y_2347_ = v___x_2356_;
goto v___jp_2346_;
}
else
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = l_Int_toNat(v_val_2344_);
v___x_2358_ = l_Lean_instToExprInt_mkNat(v___x_2357_);
v___y_2347_ = v___x_2358_;
goto v___jp_2346_;
}
v___jp_2346_:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_mkAppB(v___x_2345_, v___x_2295_, v___y_2347_);
v___y_2327_ = v___x_2348_;
goto v___jp_2326_;
}
}
v___jp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2303_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2);
lean_inc_ref(v___y_2302_);
v___x_2304_ = l_Lean_Expr_app___override(v___x_2303_, v___y_2302_);
v___x_2305_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6);
v___x_2306_ = l_Lean_Meta_mkEq(v___x_2304_, v___x_2305_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2308_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref(v___x_2306_);
v___x_2308_ = l_Lean_Meta_mkDecideProof(v_a_2307_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2318_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2311_ = v___x_2308_;
v_isShared_2312_ = v_isSharedCheck_2318_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2308_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2318_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2313_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9);
v___x_2314_ = l_Lean_mkApp5(v___x_2313_, v___y_2302_, v_a_2309_, v___x_2300_, v_a_2292_, v_a_2294_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v___x_2314_);
v___x_2316_ = v___x_2311_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
else
{
lean_dec_ref(v___y_2302_);
lean_dec_ref(v___x_2300_);
lean_dec(v_a_2294_);
lean_dec(v_a_2292_);
return v___x_2308_;
}
}
else
{
lean_dec_ref(v___y_2302_);
lean_dec_ref(v___x_2300_);
lean_dec(v_a_2294_);
lean_dec(v_a_2292_);
return v___x_2306_;
}
}
v___jp_2319_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_inc_ref(v___y_2320_);
v___x_2323_ = l_Lean_mkAppB(v___y_2320_, v___x_2295_, v___y_2322_);
v___x_2324_ = l_Lean_Expr_app___override(v___y_2321_, v___x_2323_);
v___y_2302_ = v___x_2324_;
goto v___jp_2301_;
}
v___jp_2326_:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_Expr_app___override(v___x_2325_, v___y_2327_);
if (lean_obj_tag(v_upperBound_2297_) == 0)
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_2330_ = l_Lean_Expr_app___override(v___x_2328_, v___x_2329_);
v___y_2302_ = v___x_2330_;
goto v___jp_2301_;
}
else
{
lean_object* v_val_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v_val_2331_ = lean_ctor_get(v_upperBound_2297_, 0);
v___x_2332_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2333_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2334_ = lean_int_dec_le(v___x_2333_, v_val_2331_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2335_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2336_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2337_ = lean_int_neg(v_val_2331_);
v___x_2338_ = l_Int_toNat(v___x_2337_);
lean_dec(v___x_2337_);
v___x_2339_ = l_Lean_instToExprInt_mkNat(v___x_2338_);
v___x_2340_ = l_Lean_mkApp3(v___x_2335_, v___x_2295_, v___x_2336_, v___x_2339_);
v___y_2320_ = v___x_2332_;
v___y_2321_ = v___x_2328_;
v___y_2322_ = v___x_2340_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = l_Int_toNat(v_val_2331_);
v___x_2342_ = l_Lean_instToExprInt_mkNat(v___x_2341_);
v___y_2320_ = v___x_2332_;
v___y_2321_ = v___x_2328_;
v___y_2322_ = v___x_2342_;
goto v___jp_2319_;
}
}
}
}
else
{
lean_dec(v_a_2292_);
return v___x_2293_;
}
}
else
{
lean_dec_ref(v_j_2279_);
return v___x_2291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed(lean_object* v_s_2359_, lean_object* v_x_2360_, lean_object* v_j_2361_, lean_object* v_assumptions_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
uint8_t v_a_boxed_2373_; lean_object* v_res_2374_; 
v_a_boxed_2373_ = lean_unbox(v_a_2366_);
v_res_2374_ = l_Lean_Elab_Tactic_Omega_Problem_proveFalse(v_s_2359_, v_x_2360_, v_j_2361_, v_assumptions_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_boxed_2373_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec(v_a_2363_);
lean_dec_ref(v_assumptions_2362_);
lean_dec(v_x_2360_);
lean_dec_ref(v_s_2359_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0(lean_object* v_constraint_2375_, lean_object* v_coeffs_2376_, lean_object* v_justification_2377_, lean_object* v_x_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_2375_, v_coeffs_2376_, v_justification_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(lean_object* v_a_2380_, lean_object* v_x_2381_){
_start:
{
if (lean_obj_tag(v_x_2381_) == 0)
{
uint8_t v___x_2382_; 
v___x_2382_ = 0;
return v___x_2382_;
}
else
{
lean_object* v_key_2383_; lean_object* v_tail_2384_; uint8_t v___x_2385_; 
v_key_2383_ = lean_ctor_get(v_x_2381_, 0);
v_tail_2384_ = lean_ctor_get(v_x_2381_, 2);
v___x_2385_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2383_, v_a_2380_);
if (v___x_2385_ == 0)
{
v_x_2381_ = v_tail_2384_;
goto _start;
}
else
{
return v___x_2385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg___boxed(lean_object* v_a_2387_, lean_object* v_x_2388_){
_start:
{
uint8_t v_res_2389_; lean_object* v_r_2390_; 
v_res_2389_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2387_, v_x_2388_);
lean_dec(v_x_2388_);
lean_dec(v_a_2387_);
v_r_2390_ = lean_box(v_res_2389_);
return v_r_2390_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(uint64_t v_x_2391_, lean_object* v_x_2392_){
_start:
{
if (lean_obj_tag(v_x_2392_) == 0)
{
return v_x_2391_;
}
else
{
lean_object* v_head_2393_; lean_object* v_tail_2394_; lean_object* v_intZero_2395_; uint8_t v_isNeg_2396_; 
v_head_2393_ = lean_ctor_get(v_x_2392_, 0);
v_tail_2394_ = lean_ctor_get(v_x_2392_, 1);
v_intZero_2395_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2396_ = lean_int_dec_lt(v_head_2393_, v_intZero_2395_);
if (v_isNeg_2396_ == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint64_t v___x_2400_; uint64_t v___x_2401_; 
v_a_2397_ = lean_nat_abs(v_head_2393_);
v___x_2398_ = lean_unsigned_to_nat(2u);
v___x_2399_ = lean_nat_mul(v___x_2398_, v_a_2397_);
lean_dec(v_a_2397_);
v___x_2400_ = lean_uint64_of_nat(v___x_2399_);
lean_dec(v___x_2399_);
v___x_2401_ = lean_uint64_mix_hash(v_x_2391_, v___x_2400_);
v_x_2391_ = v___x_2401_;
v_x_2392_ = v_tail_2394_;
goto _start;
}
else
{
lean_object* v_abs_2403_; lean_object* v_one_2404_; lean_object* v_a_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint64_t v___x_2409_; uint64_t v___x_2410_; 
v_abs_2403_ = lean_nat_abs(v_head_2393_);
v_one_2404_ = lean_unsigned_to_nat(1u);
v_a_2405_ = lean_nat_sub(v_abs_2403_, v_one_2404_);
lean_dec(v_abs_2403_);
v___x_2406_ = lean_unsigned_to_nat(2u);
v___x_2407_ = lean_nat_mul(v___x_2406_, v_a_2405_);
lean_dec(v_a_2405_);
v___x_2408_ = lean_nat_add(v___x_2407_, v_one_2404_);
lean_dec(v___x_2407_);
v___x_2409_ = lean_uint64_of_nat(v___x_2408_);
lean_dec(v___x_2408_);
v___x_2410_ = lean_uint64_mix_hash(v_x_2391_, v___x_2409_);
v_x_2391_ = v___x_2410_;
v_x_2392_ = v_tail_2394_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0___boxed(lean_object* v_x_2412_, lean_object* v_x_2413_){
_start:
{
uint64_t v_x_980__boxed_2414_; uint64_t v_res_2415_; lean_object* v_r_2416_; 
v_x_980__boxed_2414_ = lean_unbox_uint64(v_x_2412_);
lean_dec_ref(v_x_2412_);
v_res_2415_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v_x_980__boxed_2414_, v_x_2413_);
lean_dec(v_x_2413_);
v_r_2416_ = lean_box_uint64(v_res_2415_);
return v_r_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_2417_, lean_object* v_x_2418_){
_start:
{
if (lean_obj_tag(v_x_2418_) == 0)
{
return v_x_2417_;
}
else
{
lean_object* v_key_2419_; lean_object* v_value_2420_; lean_object* v_tail_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2445_; 
v_key_2419_ = lean_ctor_get(v_x_2418_, 0);
v_value_2420_ = lean_ctor_get(v_x_2418_, 1);
v_tail_2421_ = lean_ctor_get(v_x_2418_, 2);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_x_2418_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2423_ = v_x_2418_;
v_isShared_2424_ = v_isSharedCheck_2445_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_tail_2421_);
lean_inc(v_value_2420_);
lean_inc(v_key_2419_);
lean_dec(v_x_2418_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2445_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; uint64_t v___x_2426_; uint64_t v___x_2427_; uint64_t v___x_2428_; uint64_t v___x_2429_; uint64_t v_fold_2430_; uint64_t v___x_2431_; uint64_t v___x_2432_; uint64_t v___x_2433_; size_t v___x_2434_; size_t v___x_2435_; size_t v___x_2436_; size_t v___x_2437_; size_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2441_; 
v___x_2425_ = lean_array_get_size(v_x_2417_);
v___x_2426_ = 7ULL;
v___x_2427_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2426_, v_key_2419_);
v___x_2428_ = 32ULL;
v___x_2429_ = lean_uint64_shift_right(v___x_2427_, v___x_2428_);
v_fold_2430_ = lean_uint64_xor(v___x_2427_, v___x_2429_);
v___x_2431_ = 16ULL;
v___x_2432_ = lean_uint64_shift_right(v_fold_2430_, v___x_2431_);
v___x_2433_ = lean_uint64_xor(v_fold_2430_, v___x_2432_);
v___x_2434_ = lean_uint64_to_usize(v___x_2433_);
v___x_2435_ = lean_usize_of_nat(v___x_2425_);
v___x_2436_ = ((size_t)1ULL);
v___x_2437_ = lean_usize_sub(v___x_2435_, v___x_2436_);
v___x_2438_ = lean_usize_land(v___x_2434_, v___x_2437_);
v___x_2439_ = lean_array_uget_borrowed(v_x_2417_, v___x_2438_);
lean_inc(v___x_2439_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 2, v___x_2439_);
v___x_2441_ = v___x_2423_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_key_2419_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_value_2420_);
lean_ctor_set(v_reuseFailAlloc_2444_, 2, v___x_2439_);
v___x_2441_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_array_uset(v_x_2417_, v___x_2438_, v___x_2441_);
v_x_2417_ = v___x_2442_;
v_x_2418_ = v_tail_2421_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(lean_object* v_i_2446_, lean_object* v_source_2447_, lean_object* v_target_2448_){
_start:
{
lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2449_ = lean_array_get_size(v_source_2447_);
v___x_2450_ = lean_nat_dec_lt(v_i_2446_, v___x_2449_);
if (v___x_2450_ == 0)
{
lean_dec_ref(v_source_2447_);
lean_dec(v_i_2446_);
return v_target_2448_;
}
else
{
lean_object* v_es_2451_; lean_object* v___x_2452_; lean_object* v_source_2453_; lean_object* v_target_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v_es_2451_ = lean_array_fget(v_source_2447_, v_i_2446_);
v___x_2452_ = lean_box(0);
v_source_2453_ = lean_array_fset(v_source_2447_, v_i_2446_, v___x_2452_);
v_target_2454_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_target_2448_, v_es_2451_);
v___x_2455_ = lean_unsigned_to_nat(1u);
v___x_2456_ = lean_nat_add(v_i_2446_, v___x_2455_);
lean_dec(v_i_2446_);
v_i_2446_ = v___x_2456_;
v_source_2447_ = v_source_2453_;
v_target_2448_ = v_target_2454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(lean_object* v_data_2458_){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v_nbuckets_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2459_ = lean_array_get_size(v_data_2458_);
v___x_2460_ = lean_unsigned_to_nat(2u);
v_nbuckets_2461_ = lean_nat_mul(v___x_2459_, v___x_2460_);
v___x_2462_ = lean_unsigned_to_nat(0u);
v___x_2463_ = lean_box(0);
v___x_2464_ = lean_mk_array(v_nbuckets_2461_, v___x_2463_);
v___x_2465_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v___x_2462_, v_data_2458_, v___x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(lean_object* v_m_2466_, lean_object* v_a_2467_, lean_object* v_b_2468_){
_start:
{
lean_object* v_size_2469_; lean_object* v_buckets_2470_; lean_object* v___x_2471_; uint64_t v___x_2472_; uint64_t v___x_2473_; uint64_t v___x_2474_; uint64_t v___x_2475_; uint64_t v_fold_2476_; uint64_t v___x_2477_; uint64_t v___x_2478_; uint64_t v___x_2479_; size_t v___x_2480_; size_t v___x_2481_; size_t v___x_2482_; size_t v___x_2483_; size_t v___x_2484_; lean_object* v_bkt_2485_; uint8_t v___x_2486_; 
v_size_2469_ = lean_ctor_get(v_m_2466_, 0);
v_buckets_2470_ = lean_ctor_get(v_m_2466_, 1);
v___x_2471_ = lean_array_get_size(v_buckets_2470_);
v___x_2472_ = 7ULL;
v___x_2473_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2472_, v_a_2467_);
v___x_2474_ = 32ULL;
v___x_2475_ = lean_uint64_shift_right(v___x_2473_, v___x_2474_);
v_fold_2476_ = lean_uint64_xor(v___x_2473_, v___x_2475_);
v___x_2477_ = 16ULL;
v___x_2478_ = lean_uint64_shift_right(v_fold_2476_, v___x_2477_);
v___x_2479_ = lean_uint64_xor(v_fold_2476_, v___x_2478_);
v___x_2480_ = lean_uint64_to_usize(v___x_2479_);
v___x_2481_ = lean_usize_of_nat(v___x_2471_);
v___x_2482_ = ((size_t)1ULL);
v___x_2483_ = lean_usize_sub(v___x_2481_, v___x_2482_);
v___x_2484_ = lean_usize_land(v___x_2480_, v___x_2483_);
v_bkt_2485_ = lean_array_uget_borrowed(v_buckets_2470_, v___x_2484_);
v___x_2486_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2467_, v_bkt_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2507_; 
lean_inc_ref(v_buckets_2470_);
lean_inc(v_size_2469_);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_m_2466_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; lean_object* v_unused_2509_; 
v_unused_2508_ = lean_ctor_get(v_m_2466_, 1);
lean_dec(v_unused_2508_);
v_unused_2509_ = lean_ctor_get(v_m_2466_, 0);
lean_dec(v_unused_2509_);
v___x_2488_ = v_m_2466_;
v_isShared_2489_ = v_isSharedCheck_2507_;
goto v_resetjp_2487_;
}
else
{
lean_dec(v_m_2466_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2507_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; lean_object* v_size_x27_2491_; lean_object* v___x_2492_; lean_object* v_buckets_x27_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2490_ = lean_unsigned_to_nat(1u);
v_size_x27_2491_ = lean_nat_add(v_size_2469_, v___x_2490_);
lean_dec(v_size_2469_);
lean_inc(v_bkt_2485_);
v___x_2492_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2492_, 0, v_a_2467_);
lean_ctor_set(v___x_2492_, 1, v_b_2468_);
lean_ctor_set(v___x_2492_, 2, v_bkt_2485_);
v_buckets_x27_2493_ = lean_array_uset(v_buckets_2470_, v___x_2484_, v___x_2492_);
v___x_2494_ = lean_unsigned_to_nat(4u);
v___x_2495_ = lean_nat_mul(v_size_x27_2491_, v___x_2494_);
v___x_2496_ = lean_unsigned_to_nat(3u);
v___x_2497_ = lean_nat_div(v___x_2495_, v___x_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_array_get_size(v_buckets_x27_2493_);
v___x_2499_ = lean_nat_dec_le(v___x_2497_, v___x_2498_);
lean_dec(v___x_2497_);
if (v___x_2499_ == 0)
{
lean_object* v_val_2500_; lean_object* v___x_2502_; 
v_val_2500_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2493_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 1, v_val_2500_);
lean_ctor_set(v___x_2488_, 0, v_size_x27_2491_);
v___x_2502_ = v___x_2488_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_size_x27_2491_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_val_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
else
{
lean_object* v___x_2505_; 
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 1, v_buckets_x27_2493_);
lean_ctor_set(v___x_2488_, 0, v_size_x27_2491_);
v___x_2505_ = v___x_2488_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_size_x27_2491_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v_buckets_x27_2493_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_dec(v_b_2468_);
lean_dec(v_a_2467_);
return v_m_2466_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(lean_object* v_a_2510_, lean_object* v_b_2511_, lean_object* v_x_2512_){
_start:
{
if (lean_obj_tag(v_x_2512_) == 0)
{
lean_dec(v_b_2511_);
lean_dec(v_a_2510_);
return v_x_2512_;
}
else
{
lean_object* v_key_2513_; lean_object* v_value_2514_; lean_object* v_tail_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2527_; 
v_key_2513_ = lean_ctor_get(v_x_2512_, 0);
v_value_2514_ = lean_ctor_get(v_x_2512_, 1);
v_tail_2515_ = lean_ctor_get(v_x_2512_, 2);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_x_2512_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2517_ = v_x_2512_;
v_isShared_2518_ = v_isSharedCheck_2527_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_tail_2515_);
lean_inc(v_value_2514_);
lean_inc(v_key_2513_);
lean_dec(v_x_2512_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2527_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
uint8_t v___x_2519_; 
v___x_2519_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2513_, v_a_2510_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2520_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2510_, v_b_2511_, v_tail_2515_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 2, v___x_2520_);
v___x_2522_ = v___x_2517_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_key_2513_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_value_2514_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
else
{
lean_object* v___x_2525_; 
lean_dec(v_value_2514_);
lean_dec(v_key_2513_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 1, v_b_2511_);
lean_ctor_set(v___x_2517_, 0, v_a_2510_);
v___x_2525_ = v___x_2517_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2510_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_b_2511_);
lean_ctor_set(v_reuseFailAlloc_2526_, 2, v_tail_2515_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(lean_object* v_m_2528_, lean_object* v_a_2529_, lean_object* v_b_2530_){
_start:
{
lean_object* v_size_2531_; lean_object* v_buckets_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2576_; 
v_size_2531_ = lean_ctor_get(v_m_2528_, 0);
v_buckets_2532_ = lean_ctor_get(v_m_2528_, 1);
v_isSharedCheck_2576_ = !lean_is_exclusive(v_m_2528_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2534_ = v_m_2528_;
v_isShared_2535_ = v_isSharedCheck_2576_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_buckets_2532_);
lean_inc(v_size_2531_);
lean_dec(v_m_2528_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2576_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2536_; uint64_t v___x_2537_; uint64_t v___x_2538_; uint64_t v___x_2539_; uint64_t v___x_2540_; uint64_t v_fold_2541_; uint64_t v___x_2542_; uint64_t v___x_2543_; uint64_t v___x_2544_; size_t v___x_2545_; size_t v___x_2546_; size_t v___x_2547_; size_t v___x_2548_; size_t v___x_2549_; lean_object* v_bkt_2550_; uint8_t v___x_2551_; 
v___x_2536_ = lean_array_get_size(v_buckets_2532_);
v___x_2537_ = 7ULL;
v___x_2538_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2537_, v_a_2529_);
v___x_2539_ = 32ULL;
v___x_2540_ = lean_uint64_shift_right(v___x_2538_, v___x_2539_);
v_fold_2541_ = lean_uint64_xor(v___x_2538_, v___x_2540_);
v___x_2542_ = 16ULL;
v___x_2543_ = lean_uint64_shift_right(v_fold_2541_, v___x_2542_);
v___x_2544_ = lean_uint64_xor(v_fold_2541_, v___x_2543_);
v___x_2545_ = lean_uint64_to_usize(v___x_2544_);
v___x_2546_ = lean_usize_of_nat(v___x_2536_);
v___x_2547_ = ((size_t)1ULL);
v___x_2548_ = lean_usize_sub(v___x_2546_, v___x_2547_);
v___x_2549_ = lean_usize_land(v___x_2545_, v___x_2548_);
v_bkt_2550_ = lean_array_uget_borrowed(v_buckets_2532_, v___x_2549_);
v___x_2551_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2529_, v_bkt_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v_size_x27_2553_; lean_object* v___x_2554_; lean_object* v_buckets_x27_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2552_ = lean_unsigned_to_nat(1u);
v_size_x27_2553_ = lean_nat_add(v_size_2531_, v___x_2552_);
lean_dec(v_size_2531_);
lean_inc(v_bkt_2550_);
v___x_2554_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2554_, 0, v_a_2529_);
lean_ctor_set(v___x_2554_, 1, v_b_2530_);
lean_ctor_set(v___x_2554_, 2, v_bkt_2550_);
v_buckets_x27_2555_ = lean_array_uset(v_buckets_2532_, v___x_2549_, v___x_2554_);
v___x_2556_ = lean_unsigned_to_nat(4u);
v___x_2557_ = lean_nat_mul(v_size_x27_2553_, v___x_2556_);
v___x_2558_ = lean_unsigned_to_nat(3u);
v___x_2559_ = lean_nat_div(v___x_2557_, v___x_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_array_get_size(v_buckets_x27_2555_);
v___x_2561_ = lean_nat_dec_le(v___x_2559_, v___x_2560_);
lean_dec(v___x_2559_);
if (v___x_2561_ == 0)
{
lean_object* v_val_2562_; lean_object* v___x_2564_; 
v_val_2562_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2555_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 1, v_val_2562_);
lean_ctor_set(v___x_2534_, 0, v_size_x27_2553_);
v___x_2564_ = v___x_2534_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_size_x27_2553_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_val_2562_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
else
{
lean_object* v___x_2567_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 1, v_buckets_x27_2555_);
lean_ctor_set(v___x_2534_, 0, v_size_x27_2553_);
v___x_2567_ = v___x_2534_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_size_x27_2553_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_buckets_x27_2555_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
else
{
lean_object* v___x_2569_; lean_object* v_buckets_x27_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2574_; 
lean_inc(v_bkt_2550_);
v___x_2569_ = lean_box(0);
v_buckets_x27_2570_ = lean_array_uset(v_buckets_2532_, v___x_2549_, v___x_2569_);
v___x_2571_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2529_, v_b_2530_, v_bkt_2550_);
v___x_2572_ = lean_array_uset(v_buckets_x27_2570_, v___x_2549_, v___x_2571_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 1, v___x_2572_);
v___x_2574_ = v___x_2534_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_size_2531_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(lean_object* v_p_2577_, lean_object* v_x_2578_){
_start:
{
lean_object* v_coeffs_2579_; lean_object* v_constraint_2580_; lean_object* v_justification_2581_; uint8_t v___x_2582_; 
v_coeffs_2579_ = lean_ctor_get(v_x_2578_, 0);
lean_inc(v_coeffs_2579_);
v_constraint_2580_ = lean_ctor_get(v_x_2578_, 1);
lean_inc_ref(v_constraint_2580_);
v_justification_2581_ = lean_ctor_get(v_x_2578_, 2);
v___x_2582_ = l_Lean_Omega_Constraint_isImpossible(v_constraint_2580_);
if (v___x_2582_ == 0)
{
lean_object* v_assumptions_2583_; lean_object* v_numVars_2584_; lean_object* v_constraints_2585_; lean_object* v_equalities_2586_; lean_object* v_eliminations_2587_; uint8_t v_possible_2588_; lean_object* v_proveFalse_x3f_2589_; lean_object* v_explanation_x3f_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2608_; 
v_assumptions_2583_ = lean_ctor_get(v_p_2577_, 0);
v_numVars_2584_ = lean_ctor_get(v_p_2577_, 1);
v_constraints_2585_ = lean_ctor_get(v_p_2577_, 2);
v_equalities_2586_ = lean_ctor_get(v_p_2577_, 3);
v_eliminations_2587_ = lean_ctor_get(v_p_2577_, 4);
v_possible_2588_ = lean_ctor_get_uint8(v_p_2577_, sizeof(void*)*7);
v_proveFalse_x3f_2589_ = lean_ctor_get(v_p_2577_, 5);
v_explanation_x3f_2590_ = lean_ctor_get(v_p_2577_, 6);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_p_2577_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2592_ = v_p_2577_;
v_isShared_2593_ = v_isSharedCheck_2608_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_explanation_x3f_2590_);
lean_inc(v_proveFalse_x3f_2589_);
lean_inc(v_eliminations_2587_);
lean_inc(v_equalities_2586_);
lean_inc(v_constraints_2585_);
lean_inc(v_numVars_2584_);
lean_inc(v_assumptions_2583_);
lean_dec(v_p_2577_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2608_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___y_2595_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2606_ = l_List_lengthTR___redArg(v_coeffs_2579_);
v___x_2607_ = lean_nat_dec_le(v_numVars_2584_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_dec(v___x_2606_);
v___y_2595_ = v_numVars_2584_;
goto v___jp_2594_;
}
else
{
lean_dec(v_numVars_2584_);
v___y_2595_ = v___x_2606_;
goto v___jp_2594_;
}
v___jp_2594_:
{
lean_object* v___x_2596_; uint8_t v___x_2597_; 
lean_inc(v_coeffs_2579_);
v___x_2596_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_constraints_2585_, v_coeffs_2579_, v_x_2578_);
v___x_2597_ = l_Lean_Omega_Constraint_isExact(v_constraint_2580_);
lean_dec_ref(v_constraint_2580_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2599_; 
lean_dec(v_coeffs_2579_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 2, v___x_2596_);
lean_ctor_set(v___x_2592_, 1, v___y_2595_);
v___x_2599_ = v___x_2592_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_assumptions_2583_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___y_2595_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v_equalities_2586_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v_eliminations_2587_);
lean_ctor_set(v_reuseFailAlloc_2600_, 5, v_proveFalse_x3f_2589_);
lean_ctor_set(v_reuseFailAlloc_2600_, 6, v_explanation_x3f_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2600_, sizeof(void*)*7, v_possible_2588_);
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
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v___x_2601_ = lean_box(0);
v___x_2602_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_equalities_2586_, v_coeffs_2579_, v___x_2601_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 3, v___x_2602_);
lean_ctor_set(v___x_2592_, 2, v___x_2596_);
lean_ctor_set(v___x_2592_, 1, v___y_2595_);
v___x_2604_ = v___x_2592_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_assumptions_2583_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v___y_2595_);
lean_ctor_set(v_reuseFailAlloc_2605_, 2, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2605_, 3, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2605_, 4, v_eliminations_2587_);
lean_ctor_set(v_reuseFailAlloc_2605_, 5, v_proveFalse_x3f_2589_);
lean_ctor_set(v_reuseFailAlloc_2605_, 6, v_explanation_x3f_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2605_, sizeof(void*)*7, v_possible_2588_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
else
{
lean_object* v_assumptions_2609_; lean_object* v_numVars_2610_; lean_object* v_constraints_2611_; lean_object* v_equalities_2612_; lean_object* v_eliminations_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2625_; 
lean_inc_ref(v_justification_2581_);
lean_dec_ref(v_x_2578_);
v_assumptions_2609_ = lean_ctor_get(v_p_2577_, 0);
v_numVars_2610_ = lean_ctor_get(v_p_2577_, 1);
v_constraints_2611_ = lean_ctor_get(v_p_2577_, 2);
v_equalities_2612_ = lean_ctor_get(v_p_2577_, 3);
v_eliminations_2613_ = lean_ctor_get(v_p_2577_, 4);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_p_2577_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; lean_object* v_unused_2627_; 
v_unused_2626_ = lean_ctor_get(v_p_2577_, 6);
lean_dec(v_unused_2626_);
v_unused_2627_ = lean_ctor_get(v_p_2577_, 5);
lean_dec(v_unused_2627_);
v___x_2615_ = v_p_2577_;
v_isShared_2616_ = v_isSharedCheck_2625_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_eliminations_2613_);
lean_inc(v_equalities_2612_);
lean_inc(v_constraints_2611_);
lean_inc(v_numVars_2610_);
lean_inc(v_assumptions_2609_);
lean_dec(v_p_2577_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2625_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___f_2617_; uint8_t v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
lean_inc_ref(v_justification_2581_);
lean_inc(v_coeffs_2579_);
lean_inc_ref(v_constraint_2580_);
v___f_2617_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0), 4, 3);
lean_closure_set(v___f_2617_, 0, v_constraint_2580_);
lean_closure_set(v___f_2617_, 1, v_coeffs_2579_);
lean_closure_set(v___f_2617_, 2, v_justification_2581_);
v___x_2618_ = 0;
lean_inc_ref(v_assumptions_2609_);
v___x_2619_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed), 14, 4);
lean_closure_set(v___x_2619_, 0, v_constraint_2580_);
lean_closure_set(v___x_2619_, 1, v_coeffs_2579_);
lean_closure_set(v___x_2619_, 2, v_justification_2581_);
lean_closure_set(v___x_2619_, 3, v_assumptions_2609_);
v___x_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
v___x_2621_ = lean_mk_thunk(v___f_2617_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 6, v___x_2621_);
lean_ctor_set(v___x_2615_, 5, v___x_2620_);
v___x_2623_ = v___x_2615_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_assumptions_2609_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_numVars_2610_);
lean_ctor_set(v_reuseFailAlloc_2624_, 2, v_constraints_2611_);
lean_ctor_set(v_reuseFailAlloc_2624_, 3, v_equalities_2612_);
lean_ctor_set(v_reuseFailAlloc_2624_, 4, v_eliminations_2613_);
lean_ctor_set(v_reuseFailAlloc_2624_, 5, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2624_, 6, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_ctor_set_uint8(v___x_2623_, sizeof(void*)*7, v___x_2618_);
return v___x_2623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0(lean_object* v_00_u03b2_2628_, lean_object* v_m_2629_, lean_object* v_a_2630_, lean_object* v_b_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_m_2629_, v_a_2630_, v_b_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1(lean_object* v_00_u03b2_2633_, lean_object* v_m_2634_, lean_object* v_a_2635_, lean_object* v_b_2636_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_m_2634_, v_a_2635_, v_b_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_object* v_00_u03b2_2638_, lean_object* v_a_2639_, lean_object* v_x_2640_){
_start:
{
uint8_t v___x_2641_; 
v___x_2641_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2639_, v_x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2642_, lean_object* v_a_2643_, lean_object* v_x_2644_){
_start:
{
uint8_t v_res_2645_; lean_object* v_r_2646_; 
v_res_2645_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(v_00_u03b2_2642_, v_a_2643_, v_x_2644_);
lean_dec(v_x_2644_);
lean_dec(v_a_2643_);
v_r_2646_ = lean_box(v_res_2645_);
return v_r_2646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2(lean_object* v_00_u03b2_2647_, lean_object* v_data_2648_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_data_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3(lean_object* v_00_u03b2_2650_, lean_object* v_a_2651_, lean_object* v_b_2652_, lean_object* v_x_2653_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2651_, v_b_2652_, v_x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2655_, lean_object* v_i_2656_, lean_object* v_source_2657_, lean_object* v_target_2658_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v_i_2656_, v_source_2657_, v_target_2658_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2660_, lean_object* v_x_2661_, lean_object* v_x_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_x_2661_, v_x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(lean_object* v_a_2664_, lean_object* v_x_2665_){
_start:
{
if (lean_obj_tag(v_x_2665_) == 0)
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_box(0);
return v___x_2666_;
}
else
{
lean_object* v_key_2667_; lean_object* v_value_2668_; lean_object* v_tail_2669_; uint8_t v___x_2670_; 
v_key_2667_ = lean_ctor_get(v_x_2665_, 0);
v_value_2668_ = lean_ctor_get(v_x_2665_, 1);
v_tail_2669_ = lean_ctor_get(v_x_2665_, 2);
v___x_2670_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2667_, v_a_2664_);
if (v___x_2670_ == 0)
{
v_x_2665_ = v_tail_2669_;
goto _start;
}
else
{
lean_object* v___x_2672_; 
lean_inc(v_value_2668_);
v___x_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2672_, 0, v_value_2668_);
return v___x_2672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg___boxed(lean_object* v_a_2673_, lean_object* v_x_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2673_, v_x_2674_);
lean_dec(v_x_2674_);
lean_dec(v_a_2673_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(lean_object* v_m_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v_buckets_2678_; lean_object* v___x_2679_; uint64_t v___x_2680_; uint64_t v___x_2681_; uint64_t v___x_2682_; uint64_t v___x_2683_; uint64_t v_fold_2684_; uint64_t v___x_2685_; uint64_t v___x_2686_; uint64_t v___x_2687_; size_t v___x_2688_; size_t v___x_2689_; size_t v___x_2690_; size_t v___x_2691_; size_t v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v_buckets_2678_ = lean_ctor_get(v_m_2676_, 1);
v___x_2679_ = lean_array_get_size(v_buckets_2678_);
v___x_2680_ = 7ULL;
v___x_2681_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2680_, v_a_2677_);
v___x_2682_ = 32ULL;
v___x_2683_ = lean_uint64_shift_right(v___x_2681_, v___x_2682_);
v_fold_2684_ = lean_uint64_xor(v___x_2681_, v___x_2683_);
v___x_2685_ = 16ULL;
v___x_2686_ = lean_uint64_shift_right(v_fold_2684_, v___x_2685_);
v___x_2687_ = lean_uint64_xor(v_fold_2684_, v___x_2686_);
v___x_2688_ = lean_uint64_to_usize(v___x_2687_);
v___x_2689_ = lean_usize_of_nat(v___x_2679_);
v___x_2690_ = ((size_t)1ULL);
v___x_2691_ = lean_usize_sub(v___x_2689_, v___x_2690_);
v___x_2692_ = lean_usize_land(v___x_2688_, v___x_2691_);
v___x_2693_ = lean_array_uget_borrowed(v_buckets_2678_, v___x_2692_);
v___x_2694_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2677_, v___x_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg___boxed(lean_object* v_m_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2695_, v_a_2696_);
lean_dec(v_a_2696_);
lean_dec_ref(v_m_2695_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addConstraint(lean_object* v_p_2698_, lean_object* v_x_2699_){
_start:
{
uint8_t v_possible_2700_; 
v_possible_2700_ = lean_ctor_get_uint8(v_p_2698_, sizeof(void*)*7);
if (v_possible_2700_ == 0)
{
lean_dec_ref(v_x_2699_);
return v_p_2698_;
}
else
{
lean_object* v_coeffs_2701_; lean_object* v_constraint_2702_; lean_object* v_justification_2703_; lean_object* v_constraints_2704_; lean_object* v___x_2705_; 
v_coeffs_2701_ = lean_ctor_get(v_x_2699_, 0);
v_constraint_2702_ = lean_ctor_get(v_x_2699_, 1);
v_justification_2703_ = lean_ctor_get(v_x_2699_, 2);
v_constraints_2704_ = lean_ctor_get(v_p_2698_, 2);
v___x_2705_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2704_, v_coeffs_2701_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_lowerBound_2706_; 
v_lowerBound_2706_ = lean_ctor_get(v_constraint_2702_, 0);
if (lean_obj_tag(v_lowerBound_2706_) == 0)
{
lean_object* v_upperBound_2707_; 
v_upperBound_2707_ = lean_ctor_get(v_constraint_2702_, 1);
if (lean_obj_tag(v_upperBound_2707_) == 0)
{
lean_dec_ref(v_x_2699_);
return v_p_2698_;
}
else
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2698_, v_x_2699_);
return v___x_2708_;
}
}
else
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2698_, v_x_2699_);
return v___x_2709_;
}
}
else
{
lean_object* v_val_2710_; lean_object* v_coeffs_2711_; lean_object* v_constraint_2712_; lean_object* v_justification_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2728_; 
v_val_2710_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_val_2710_);
lean_dec_ref(v___x_2705_);
v_coeffs_2711_ = lean_ctor_get(v_val_2710_, 0);
v_constraint_2712_ = lean_ctor_get(v_val_2710_, 1);
v_justification_2713_ = lean_ctor_get(v_val_2710_, 2);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_val_2710_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2715_ = v_val_2710_;
v_isShared_2716_ = v_isSharedCheck_2728_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_justification_2713_);
lean_inc(v_constraint_2712_);
lean_inc(v_coeffs_2711_);
lean_dec(v_val_2710_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2728_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2717_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc(v_coeffs_2701_);
v___x_2718_ = l_instDecidableEqList___redArg(v___x_2717_, v_coeffs_2701_, v_coeffs_2711_);
if (v___x_2718_ == 0)
{
lean_del_object(v___x_2715_);
lean_dec_ref(v_justification_2713_);
lean_dec_ref(v_constraint_2712_);
lean_dec_ref(v_x_2699_);
return v_p_2698_;
}
else
{
lean_object* v_r_2719_; uint8_t v___x_2720_; 
lean_inc_ref_n(v_constraint_2712_, 2);
lean_inc_ref(v_constraint_2702_);
v_r_2719_ = l_Lean_Omega_Constraint_combine(v_constraint_2702_, v_constraint_2712_);
lean_inc_ref(v_r_2719_);
v___x_2720_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2719_, v_constraint_2712_);
if (v___x_2720_ == 0)
{
uint8_t v___x_2721_; 
lean_inc_ref(v_constraint_2702_);
lean_inc_ref(v_r_2719_);
v___x_2721_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2719_, v_constraint_2702_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2724_; 
lean_inc_ref(v_justification_2703_);
lean_inc_ref(v_constraint_2702_);
lean_inc_n(v_coeffs_2701_, 2);
lean_dec_ref(v_x_2699_);
v___x_2722_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_2722_, 0, v_constraint_2702_);
lean_ctor_set(v___x_2722_, 1, v_constraint_2712_);
lean_ctor_set(v___x_2722_, 2, v_coeffs_2701_);
lean_ctor_set(v___x_2722_, 3, v_justification_2703_);
lean_ctor_set(v___x_2722_, 4, v_justification_2713_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 2, v___x_2722_);
lean_ctor_set(v___x_2715_, 1, v_r_2719_);
lean_ctor_set(v___x_2715_, 0, v_coeffs_2701_);
v___x_2724_ = v___x_2715_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_coeffs_2701_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_r_2719_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2698_, v___x_2724_);
return v___x_2725_;
}
}
else
{
lean_object* v___x_2727_; 
lean_dec_ref(v_r_2719_);
lean_del_object(v___x_2715_);
lean_dec_ref(v_justification_2713_);
lean_dec_ref(v_constraint_2712_);
v___x_2727_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2698_, v_x_2699_);
return v___x_2727_;
}
}
else
{
lean_dec_ref(v_r_2719_);
lean_del_object(v___x_2715_);
lean_dec_ref(v_justification_2713_);
lean_dec_ref(v_constraint_2712_);
lean_dec_ref(v_x_2699_);
return v_p_2698_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(lean_object* v_00_u03b2_2729_, lean_object* v_m_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2730_, v_a_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___boxed(lean_object* v_00_u03b2_2733_, lean_object* v_m_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(v_00_u03b2_2733_, v_m_2734_, v_a_2735_);
lean_dec(v_a_2735_);
lean_dec_ref(v_m_2734_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(lean_object* v_00_u03b2_2737_, lean_object* v_a_2738_, lean_object* v_x_2739_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2738_, v_x_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2741_, lean_object* v_a_2742_, lean_object* v_x_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(v_00_u03b2_2741_, v_a_2742_, v_x_2743_);
lean_dec(v_x_2743_);
lean_dec(v_a_2742_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(lean_object* v_x_2745_, lean_object* v_x_2746_){
_start:
{
if (lean_obj_tag(v_x_2746_) == 0)
{
return v_x_2745_;
}
else
{
if (lean_obj_tag(v_x_2745_) == 0)
{
lean_object* v_key_2747_; lean_object* v_tail_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_key_2747_ = lean_ctor_get(v_x_2746_, 0);
lean_inc_n(v_key_2747_, 2);
v_tail_2748_ = lean_ctor_get(v_x_2746_, 2);
lean_inc(v_tail_2748_);
lean_dec_ref(v_x_2746_);
v___x_2749_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2747_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v_key_2747_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
v_x_2745_ = v___x_2751_;
v_x_2746_ = v_tail_2748_;
goto _start;
}
else
{
lean_object* v_val_2753_; lean_object* v_key_2754_; lean_object* v_tail_2755_; lean_object* v_fst_2756_; lean_object* v_snd_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2785_; 
v_val_2753_ = lean_ctor_get(v_x_2745_, 0);
lean_inc(v_val_2753_);
v_key_2754_ = lean_ctor_get(v_x_2746_, 0);
lean_inc(v_key_2754_);
v_tail_2755_ = lean_ctor_get(v_x_2746_, 2);
lean_inc(v_tail_2755_);
lean_dec_ref(v_x_2746_);
v_fst_2756_ = lean_ctor_get(v_val_2753_, 0);
v_snd_2757_ = lean_ctor_get(v_val_2753_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_val_2753_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2759_ = v_val_2753_;
v_isShared_2760_ = v_isSharedCheck_2785_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_snd_2757_);
lean_inc(v_fst_2756_);
lean_dec(v_val_2753_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2785_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2761_ = lean_unsigned_to_nat(2u);
v___x_2762_ = lean_nat_dec_le(v___x_2761_, v_snd_2757_);
if (v___x_2762_ == 0)
{
lean_del_object(v___x_2759_);
lean_dec(v_snd_2757_);
lean_dec(v_fst_2756_);
lean_dec(v_key_2754_);
v_x_2746_ = v_tail_2755_;
goto _start;
}
else
{
lean_object* v_m_x27_2764_; uint8_t v___y_2766_; uint8_t v___x_2780_; 
lean_inc(v_key_2754_);
v_m_x27_2764_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2754_);
v___x_2780_ = lean_nat_dec_lt(v_m_x27_2764_, v_snd_2757_);
if (v___x_2780_ == 0)
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_nat_dec_eq(v_m_x27_2764_, v_snd_2757_);
lean_dec(v_snd_2757_);
if (v___x_2781_ == 0)
{
lean_dec(v_fst_2756_);
v___y_2766_ = v___x_2781_;
goto v___jp_2765_;
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
lean_inc(v_key_2754_);
v___x_2782_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_key_2754_);
v___x_2783_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_fst_2756_);
v___x_2784_ = lean_nat_dec_lt(v___x_2782_, v___x_2783_);
lean_dec(v___x_2783_);
lean_dec(v___x_2782_);
v___y_2766_ = v___x_2784_;
goto v___jp_2765_;
}
}
else
{
lean_dec(v_snd_2757_);
lean_dec(v_fst_2756_);
v___y_2766_ = v___x_2780_;
goto v___jp_2765_;
}
v___jp_2765_:
{
if (v___y_2766_ == 0)
{
lean_dec(v_m_x27_2764_);
lean_del_object(v___x_2759_);
lean_dec(v_key_2754_);
v_x_2746_ = v_tail_2755_;
goto _start;
}
else
{
lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2778_; 
v_isSharedCheck_2778_ = !lean_is_exclusive(v_x_2745_);
if (v_isSharedCheck_2778_ == 0)
{
lean_object* v_unused_2779_; 
v_unused_2779_ = lean_ctor_get(v_x_2745_, 0);
lean_dec(v_unused_2779_);
v___x_2769_ = v_x_2745_;
v_isShared_2770_ = v_isSharedCheck_2778_;
goto v_resetjp_2768_;
}
else
{
lean_dec(v_x_2745_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2778_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 1, v_m_x27_2764_);
lean_ctor_set(v___x_2759_, 0, v_key_2754_);
v___x_2772_ = v___x_2759_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_key_2754_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_m_x27_2764_);
v___x_2772_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2774_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v___x_2772_);
v___x_2774_ = v___x_2769_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
v_x_2745_ = v___x_2774_;
v_x_2746_ = v_tail_2755_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(lean_object* v_as_2786_, size_t v_i_2787_, size_t v_stop_2788_, lean_object* v_b_2789_){
_start:
{
uint8_t v___x_2790_; 
v___x_2790_ = lean_usize_dec_eq(v_i_2787_, v_stop_2788_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; lean_object* v___x_2792_; size_t v___x_2793_; size_t v___x_2794_; 
v___x_2791_ = lean_array_uget_borrowed(v_as_2786_, v_i_2787_);
lean_inc(v___x_2791_);
v___x_2792_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(v_b_2789_, v___x_2791_);
v___x_2793_ = ((size_t)1ULL);
v___x_2794_ = lean_usize_add(v_i_2787_, v___x_2793_);
v_i_2787_ = v___x_2794_;
v_b_2789_ = v___x_2792_;
goto _start;
}
else
{
return v_b_2789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1___boxed(lean_object* v_as_2796_, lean_object* v_i_2797_, lean_object* v_stop_2798_, lean_object* v_b_2799_){
_start:
{
size_t v_i_boxed_2800_; size_t v_stop_boxed_2801_; lean_object* v_res_2802_; 
v_i_boxed_2800_ = lean_unbox_usize(v_i_2797_);
lean_dec(v_i_2797_);
v_stop_boxed_2801_ = lean_unbox_usize(v_stop_2798_);
lean_dec(v_stop_2798_);
v_res_2802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_as_2796_, v_i_boxed_2800_, v_stop_boxed_2801_, v_b_2799_);
lean_dec_ref(v_as_2796_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality(lean_object* v_p_2803_){
_start:
{
lean_object* v_equalities_2804_; lean_object* v_buckets_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v_equalities_2804_ = lean_ctor_get(v_p_2803_, 3);
v_buckets_2805_ = lean_ctor_get(v_equalities_2804_, 1);
v___x_2806_ = lean_box(0);
v___x_2807_ = lean_unsigned_to_nat(0u);
v___x_2808_ = lean_array_get_size(v_buckets_2805_);
v___x_2809_ = lean_nat_dec_lt(v___x_2807_, v___x_2808_);
if (v___x_2809_ == 0)
{
return v___x_2806_;
}
else
{
uint8_t v___x_2810_; 
v___x_2810_ = lean_nat_dec_le(v___x_2808_, v___x_2808_);
if (v___x_2810_ == 0)
{
if (v___x_2809_ == 0)
{
return v___x_2806_;
}
else
{
size_t v___x_2811_; size_t v___x_2812_; lean_object* v___x_2813_; 
v___x_2811_ = ((size_t)0ULL);
v___x_2812_ = lean_usize_of_nat(v___x_2808_);
v___x_2813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2805_, v___x_2811_, v___x_2812_, v___x_2806_);
return v___x_2813_;
}
}
else
{
size_t v___x_2814_; size_t v___x_2815_; lean_object* v___x_2816_; 
v___x_2814_ = ((size_t)0ULL);
v___x_2815_ = lean_usize_of_nat(v___x_2808_);
v___x_2816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2805_, v___x_2814_, v___x_2815_, v___x_2806_);
return v___x_2816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality___boxed(lean_object* v_p_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_2817_);
lean_dec_ref(v_p_2817_);
return v_res_2818_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_unsigned_to_nat(1u);
v___x_2820_ = lean_nat_to_int(v___x_2819_);
return v___x_2820_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2822_ = lean_int_neg(v___x_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(lean_object* v_as_2823_, size_t v_i_2824_, size_t v_stop_2825_, lean_object* v_b_2826_){
_start:
{
uint8_t v___x_2827_; 
v___x_2827_ = lean_usize_dec_eq(v_i_2824_, v_stop_2825_);
if (v___x_2827_ == 0)
{
size_t v___x_2828_; size_t v___x_2829_; lean_object* v___x_2830_; lean_object* v_snd_2831_; lean_object* v_fst_2832_; lean_object* v_fst_2833_; lean_object* v_snd_2834_; lean_object* v_coeffs_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2828_ = ((size_t)1ULL);
v___x_2829_ = lean_usize_sub(v_i_2824_, v___x_2828_);
v___x_2830_ = lean_array_uget_borrowed(v_as_2823_, v___x_2829_);
v_snd_2831_ = lean_ctor_get(v___x_2830_, 1);
v_fst_2832_ = lean_ctor_get(v___x_2830_, 0);
v_fst_2833_ = lean_ctor_get(v_snd_2831_, 0);
v_snd_2834_ = lean_ctor_get(v_snd_2831_, 1);
v_coeffs_2835_ = lean_ctor_get(v_b_2826_, 0);
lean_inc(v_fst_2833_);
v___x_2836_ = l_Lean_Omega_IntList_get(v_coeffs_2835_, v_fst_2833_);
v___x_2837_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2838_ = lean_int_dec_eq(v___x_2836_, v___x_2837_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2839_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2840_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2841_ = lean_int_mul(v___x_2840_, v_snd_2834_);
v___x_2842_ = lean_int_mul(v___x_2841_, v___x_2836_);
lean_dec(v___x_2836_);
lean_dec(v___x_2841_);
lean_inc(v_fst_2832_);
v___x_2843_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v___x_2842_, v_fst_2832_, v___x_2839_, v_b_2826_);
v_i_2824_ = v___x_2829_;
v_b_2826_ = v___x_2843_;
goto _start;
}
else
{
lean_dec(v___x_2836_);
v_i_2824_ = v___x_2829_;
goto _start;
}
}
else
{
return v_b_2826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___boxed(lean_object* v_as_2846_, lean_object* v_i_2847_, lean_object* v_stop_2848_, lean_object* v_b_2849_){
_start:
{
size_t v_i_boxed_2850_; size_t v_stop_boxed_2851_; lean_object* v_res_2852_; 
v_i_boxed_2850_ = lean_unbox_usize(v_i_2847_);
lean_dec(v_i_2847_);
v_stop_boxed_2851_ = lean_unbox_usize(v_stop_2848_);
lean_dec(v_stop_2848_);
v_res_2852_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v_as_2846_, v_i_boxed_2850_, v_stop_boxed_2851_, v_b_2849_);
lean_dec_ref(v_as_2846_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(lean_object* v_init_2853_, lean_object* v_l_2854_){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2855_ = lean_array_mk(v_l_2854_);
v___x_2856_ = lean_array_get_size(v___x_2855_);
v___x_2857_ = lean_unsigned_to_nat(0u);
v___x_2858_ = lean_nat_dec_lt(v___x_2857_, v___x_2856_);
if (v___x_2858_ == 0)
{
lean_dec_ref(v___x_2855_);
return v_init_2853_;
}
else
{
size_t v___x_2859_; size_t v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = lean_usize_of_nat(v___x_2856_);
v___x_2860_ = ((size_t)0ULL);
v___x_2861_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v___x_2855_, v___x_2859_, v___x_2860_, v_init_2853_);
lean_dec_ref(v___x_2855_);
return v___x_2861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(lean_object* v_p_2862_, lean_object* v_f_2863_){
_start:
{
lean_object* v_eliminations_2864_; lean_object* v___x_2865_; 
v_eliminations_2864_ = lean_ctor_get(v_p_2862_, 4);
lean_inc(v_eliminations_2864_);
lean_dec_ref(v_p_2862_);
v___x_2865_ = l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(v_f_2863_, v_eliminations_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__0(lean_object* v_x_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
return v___x_2867_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1(lean_object* v_x_2868_){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2869_ = lean_nat_abs(v_x_2868_);
v___x_2870_ = lean_unsigned_to_nat(1u);
v___x_2871_ = lean_nat_dec_eq(v___x_2869_, v___x_2870_);
lean_dec(v___x_2869_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1___boxed(lean_object* v_x_2872_){
_start:
{
uint8_t v_res_2873_; lean_object* v_r_2874_; 
v_res_2873_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1(v_x_2872_);
lean_dec(v_x_2872_);
v_r_2874_ = lean_box(v_res_2873_);
return v_r_2874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(lean_object* v___y_2875_, lean_object* v_sign_2876_, lean_object* v_val_2877_, lean_object* v_x_2878_, lean_object* v_x_2879_){
_start:
{
if (lean_obj_tag(v_x_2879_) == 0)
{
lean_dec_ref(v_val_2877_);
lean_dec(v___y_2875_);
return v_x_2878_;
}
else
{
lean_object* v_key_2880_; lean_object* v_value_2881_; lean_object* v_tail_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v_key_2880_ = lean_ctor_get(v_x_2879_, 0);
lean_inc(v_key_2880_);
v_value_2881_ = lean_ctor_get(v_x_2879_, 1);
lean_inc(v_value_2881_);
v_tail_2882_ = lean_ctor_get(v_x_2879_, 2);
lean_inc(v_tail_2882_);
lean_dec_ref(v_x_2879_);
lean_inc(v___y_2875_);
v___x_2883_ = l_Lean_Omega_IntList_get(v_key_2880_, v___y_2875_);
lean_dec(v_key_2880_);
v___x_2884_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2885_ = lean_int_dec_eq(v___x_2883_, v___x_2884_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v_k_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2886_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2887_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2888_ = lean_int_mul(v___x_2887_, v_sign_2876_);
v_k_2889_ = lean_int_mul(v___x_2888_, v___x_2883_);
lean_dec(v___x_2883_);
lean_dec(v___x_2888_);
lean_inc_ref(v_val_2877_);
v___x_2890_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_k_2889_, v_val_2877_, v___x_2886_, v_value_2881_);
v___x_2891_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_2890_);
v___x_2892_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2878_, v___x_2891_);
v_x_2878_ = v___x_2892_;
v_x_2879_ = v_tail_2882_;
goto _start;
}
else
{
lean_object* v___x_2894_; 
lean_dec(v___x_2883_);
v___x_2894_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2878_, v_value_2881_);
v_x_2878_ = v___x_2894_;
v_x_2879_ = v_tail_2882_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0___boxed(lean_object* v___y_2896_, lean_object* v_sign_2897_, lean_object* v_val_2898_, lean_object* v_x_2899_, lean_object* v_x_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2896_, v_sign_2897_, v_val_2898_, v_x_2899_, v_x_2900_);
lean_dec(v_sign_2897_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object* v___y_2902_, lean_object* v_sign_2903_, lean_object* v_val_2904_, lean_object* v_as_2905_, size_t v_i_2906_, size_t v_stop_2907_, lean_object* v_b_2908_){
_start:
{
uint8_t v___x_2909_; 
v___x_2909_ = lean_usize_dec_eq(v_i_2906_, v_stop_2907_);
if (v___x_2909_ == 0)
{
lean_object* v___x_2910_; lean_object* v___x_2911_; size_t v___x_2912_; size_t v___x_2913_; 
v___x_2910_ = lean_array_uget_borrowed(v_as_2905_, v_i_2906_);
lean_inc(v___x_2910_);
lean_inc_ref(v_val_2904_);
lean_inc(v___y_2902_);
v___x_2911_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2902_, v_sign_2903_, v_val_2904_, v_b_2908_, v___x_2910_);
v___x_2912_ = ((size_t)1ULL);
v___x_2913_ = lean_usize_add(v_i_2906_, v___x_2912_);
v_i_2906_ = v___x_2913_;
v_b_2908_ = v___x_2911_;
goto _start;
}
else
{
lean_dec_ref(v_val_2904_);
lean_dec(v___y_2902_);
return v_b_2908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1___boxed(lean_object* v___y_2915_, lean_object* v_sign_2916_, lean_object* v_val_2917_, lean_object* v_as_2918_, lean_object* v_i_2919_, lean_object* v_stop_2920_, lean_object* v_b_2921_){
_start:
{
size_t v_i_boxed_2922_; size_t v_stop_boxed_2923_; lean_object* v_res_2924_; 
v_i_boxed_2922_ = lean_unbox_usize(v_i_2919_);
lean_dec(v_i_2919_);
v_stop_boxed_2923_ = lean_unbox_usize(v_stop_2920_);
lean_dec(v_stop_2920_);
v_res_2924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2915_, v_sign_2916_, v_val_2917_, v_as_2918_, v_i_boxed_2922_, v_stop_boxed_2923_, v_b_2921_);
lean_dec_ref(v_as_2918_);
lean_dec(v_sign_2916_);
return v_res_2924_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1(void){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2926_ = lean_box(0);
v___x_2927_ = lean_unsigned_to_nat(16u);
v___x_2928_ = lean_mk_array(v___x_2927_, v___x_2926_);
return v___x_2928_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2(void){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2929_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1);
v___x_2930_ = lean_unsigned_to_nat(0u);
v___x_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
lean_ctor_set(v___x_2931_, 1, v___x_2929_);
return v___x_2931_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3(void){
_start:
{
lean_object* v___f_2932_; lean_object* v___x_2933_; 
v___f_2932_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0));
v___x_2933_ = lean_mk_thunk(v___f_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(lean_object* v_p_2935_, lean_object* v_c_2936_){
_start:
{
lean_object* v___y_2938_; lean_object* v___f_2985_; lean_object* v___x_2986_; 
v___f_2985_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__4));
lean_inc(v_c_2936_);
v___x_2986_ = l_List_findIdx_x3f___redArg(v___f_2985_, v_c_2936_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_unsigned_to_nat(0u);
v___y_2938_ = v___x_2987_;
goto v___jp_2937_;
}
else
{
lean_object* v_val_2988_; 
v_val_2988_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_val_2988_);
lean_dec_ref(v___x_2986_);
v___y_2938_ = v_val_2988_;
goto v___jp_2937_;
}
v___jp_2937_:
{
lean_object* v_assumptions_2939_; lean_object* v_constraints_2940_; lean_object* v_eliminations_2941_; lean_object* v___x_2942_; 
v_assumptions_2939_ = lean_ctor_get(v_p_2935_, 0);
v_constraints_2940_ = lean_ctor_get(v_p_2935_, 2);
lean_inc_ref(v_constraints_2940_);
v_eliminations_2941_ = lean_ctor_get(v_p_2935_, 4);
v___x_2942_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2940_, v_c_2936_);
if (lean_obj_tag(v___x_2942_) == 1)
{
lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2977_; 
lean_inc(v_eliminations_2941_);
lean_inc_ref(v_assumptions_2939_);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_p_2935_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; lean_object* v_unused_2979_; lean_object* v_unused_2980_; lean_object* v_unused_2981_; lean_object* v_unused_2982_; lean_object* v_unused_2983_; lean_object* v_unused_2984_; 
v_unused_2978_ = lean_ctor_get(v_p_2935_, 6);
lean_dec(v_unused_2978_);
v_unused_2979_ = lean_ctor_get(v_p_2935_, 5);
lean_dec(v_unused_2979_);
v_unused_2980_ = lean_ctor_get(v_p_2935_, 4);
lean_dec(v_unused_2980_);
v_unused_2981_ = lean_ctor_get(v_p_2935_, 3);
lean_dec(v_unused_2981_);
v_unused_2982_ = lean_ctor_get(v_p_2935_, 2);
lean_dec(v_unused_2982_);
v_unused_2983_ = lean_ctor_get(v_p_2935_, 1);
lean_dec(v_unused_2983_);
v_unused_2984_ = lean_ctor_get(v_p_2935_, 0);
lean_dec(v_unused_2984_);
v___x_2944_ = v_p_2935_;
v_isShared_2945_ = v_isSharedCheck_2977_;
goto v_resetjp_2943_;
}
else
{
lean_dec(v_p_2935_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2977_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v_val_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v_buckets_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2975_; 
v_val_2946_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_val_2946_);
lean_dec_ref(v___x_2942_);
v___x_2947_ = lean_unsigned_to_nat(0u);
v___x_2948_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v_buckets_2949_ = lean_ctor_get(v_constraints_2940_, 1);
v_isSharedCheck_2975_ = !lean_is_exclusive(v_constraints_2940_);
if (v_isSharedCheck_2975_ == 0)
{
lean_object* v_unused_2976_; 
v_unused_2976_ = lean_ctor_get(v_constraints_2940_, 0);
lean_dec(v_unused_2976_);
v___x_2951_ = v_constraints_2940_;
v_isShared_2952_ = v_isSharedCheck_2975_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_buckets_2949_);
lean_dec(v_constraints_2940_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2975_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v_sign_2954_; lean_object* v___x_2956_; 
lean_inc_n(v___y_2938_, 2);
v___x_2953_ = l_Lean_Omega_IntList_get(v_c_2936_, v___y_2938_);
lean_dec(v_c_2936_);
v_sign_2954_ = l_Int_sign(v___x_2953_);
lean_dec(v___x_2953_);
lean_inc(v_sign_2954_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v_sign_2954_);
lean_ctor_set(v___x_2951_, 0, v___y_2938_);
v___x_2956_ = v___x_2951_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___y_2938_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_sign_2954_);
v___x_2956_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; uint8_t v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v_init_2963_; 
lean_inc(v_val_2946_);
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v_val_2946_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
lean_ctor_set(v___x_2958_, 1, v_eliminations_2941_);
v___x_2959_ = 1;
v___x_2960_ = lean_box(0);
v___x_2961_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 6, v___x_2961_);
lean_ctor_set(v___x_2944_, 5, v___x_2960_);
lean_ctor_set(v___x_2944_, 4, v___x_2958_);
lean_ctor_set(v___x_2944_, 3, v___x_2948_);
lean_ctor_set(v___x_2944_, 2, v___x_2948_);
lean_ctor_set(v___x_2944_, 1, v___x_2947_);
v_init_2963_ = v___x_2944_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_assumptions_2939_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_2973_, 2, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2973_, 3, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2973_, 4, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_2973_, 5, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_2973_, 6, v___x_2961_);
v_init_2963_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; uint8_t v___x_2965_; 
lean_ctor_set_uint8(v_init_2963_, sizeof(void*)*7, v___x_2959_);
v___x_2964_ = lean_array_get_size(v_buckets_2949_);
v___x_2965_ = lean_nat_dec_lt(v___x_2947_, v___x_2964_);
if (v___x_2965_ == 0)
{
lean_dec(v_sign_2954_);
lean_dec_ref(v_buckets_2949_);
lean_dec(v_val_2946_);
lean_dec(v___y_2938_);
return v_init_2963_;
}
else
{
uint8_t v___x_2966_; 
v___x_2966_ = lean_nat_dec_le(v___x_2964_, v___x_2964_);
if (v___x_2966_ == 0)
{
if (v___x_2965_ == 0)
{
lean_dec(v_sign_2954_);
lean_dec_ref(v_buckets_2949_);
lean_dec(v_val_2946_);
lean_dec(v___y_2938_);
return v_init_2963_;
}
else
{
size_t v___x_2967_; size_t v___x_2968_; lean_object* v___x_2969_; 
v___x_2967_ = ((size_t)0ULL);
v___x_2968_ = lean_usize_of_nat(v___x_2964_);
v___x_2969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2938_, v_sign_2954_, v_val_2946_, v_buckets_2949_, v___x_2967_, v___x_2968_, v_init_2963_);
lean_dec_ref(v_buckets_2949_);
lean_dec(v_sign_2954_);
return v___x_2969_;
}
}
else
{
size_t v___x_2970_; size_t v___x_2971_; lean_object* v___x_2972_; 
v___x_2970_ = ((size_t)0ULL);
v___x_2971_ = lean_usize_of_nat(v___x_2964_);
v___x_2972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2938_, v_sign_2954_, v_val_2946_, v_buckets_2949_, v___x_2970_, v___x_2971_, v_init_2963_);
lean_dec_ref(v_buckets_2949_);
lean_dec(v_sign_2954_);
return v___x_2972_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2942_);
lean_dec_ref(v_constraints_2940_);
lean_dec(v___y_2938_);
lean_dec(v_c_2936_);
return v_p_2935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(lean_object* v_msgData_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v___x_2995_; lean_object* v_env_2996_; lean_object* v___x_2997_; lean_object* v_mctx_2998_; lean_object* v_lctx_2999_; lean_object* v_options_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_2995_ = lean_st_ref_get(v___y_2993_);
v_env_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc_ref(v_env_2996_);
lean_dec(v___x_2995_);
v___x_2997_ = lean_st_ref_get(v___y_2991_);
v_mctx_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc_ref(v_mctx_2998_);
lean_dec(v___x_2997_);
v_lctx_2999_ = lean_ctor_get(v___y_2990_, 2);
v_options_3000_ = lean_ctor_get(v___y_2992_, 2);
lean_inc_ref(v_options_3000_);
lean_inc_ref(v_lctx_2999_);
v___x_3001_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3001_, 0, v_env_2996_);
lean_ctor_set(v___x_3001_, 1, v_mctx_2998_);
lean_ctor_set(v___x_3001_, 2, v_lctx_2999_);
lean_ctor_set(v___x_3001_, 3, v_options_3000_);
v___x_3002_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
lean_ctor_set(v___x_3002_, 1, v_msgData_2989_);
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0___boxed(lean_object* v_msgData_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msgData_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(lean_object* v_msg_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v_ref_3017_; lean_object* v___x_3018_; lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3027_; 
v_ref_3017_ = lean_ctor_get(v___y_3014_, 5);
v___x_3018_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3021_ = v___x_3018_;
v_isShared_3022_ = v_isSharedCheck_3027_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3018_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3027_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
lean_inc(v_ref_3017_);
v___x_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3023_, 0, v_ref_3017_);
lean_ctor_set(v___x_3023_, 1, v_a_3019_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set_tag(v___x_3021_, 1);
lean_ctor_set(v___x_3021_, 0, v___x_3023_);
v___x_3025_ = v___x_3021_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg___boxed(lean_object* v_msg_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
return v_res_3034_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0));
v___x_3037_ = l_Lean_stringToMessageData(v___x_3036_);
return v___x_3037_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3(void){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2));
v___x_3040_ = l_Lean_stringToMessageData(v___x_3039_);
return v___x_3040_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4));
v___x_3043_ = l_Lean_stringToMessageData(v___x_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(lean_object* v_p_3044_, lean_object* v_c_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, uint8_t v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v_constraints_3056_; lean_object* v___x_3057_; 
v_constraints_3056_ = lean_ctor_get(v_p_3044_, 2);
v___x_3057_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_3056_, v_c_3045_);
if (lean_obj_tag(v___x_3057_) == 1)
{
lean_object* v_val_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3157_; 
v_val_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3157_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_val_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3157_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v_constraint_3062_; lean_object* v_lowerBound_3063_; 
v_constraint_3062_ = lean_ctor_get(v_val_3058_, 1);
v_lowerBound_3063_ = lean_ctor_get(v_constraint_3062_, 0);
lean_inc(v_lowerBound_3063_);
if (lean_obj_tag(v_lowerBound_3063_) == 1)
{
lean_object* v_upperBound_3064_; 
lean_del_object(v___x_3060_);
v_upperBound_3064_ = lean_ctor_get(v_constraint_3062_, 1);
lean_inc(v_upperBound_3064_);
if (lean_obj_tag(v_upperBound_3064_) == 1)
{
lean_object* v_coeffs_3065_; lean_object* v_justification_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3144_; 
v_coeffs_3065_ = lean_ctor_get(v_val_3058_, 0);
v_justification_3066_ = lean_ctor_get(v_val_3058_, 2);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_val_3058_);
if (v_isSharedCheck_3144_ == 0)
{
lean_object* v_unused_3145_; 
v_unused_3145_ = lean_ctor_get(v_val_3058_, 1);
lean_dec(v_unused_3145_);
v___x_3068_ = v_val_3058_;
v_isShared_3069_ = v_isSharedCheck_3144_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_justification_3066_);
lean_inc(v_coeffs_3065_);
lean_dec(v_val_3058_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3144_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v_val_3070_; lean_object* v_val_3071_; lean_object* v___x_3072_; 
v_val_3070_ = lean_ctor_get(v_lowerBound_3063_, 0);
lean_inc(v_val_3070_);
lean_dec_ref(v_lowerBound_3063_);
v_val_3071_ = lean_ctor_get(v_upperBound_3064_, 0);
lean_inc(v_val_3071_);
lean_dec_ref(v_upperBound_3064_);
v___x_3072_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3047_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v_m_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v_nil_3079_; lean_object* v_cons_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref(v___x_3072_);
lean_inc(v_c_3045_);
v___x_3074_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_c_3045_);
v___x_3075_ = lean_unsigned_to_nat(1u);
v_m_3076_ = lean_nat_add(v___x_3074_, v___x_3075_);
lean_dec(v___x_3074_);
v___x_3077_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc(v_m_3076_);
v___x_3078_ = l_Lean_mkNatLit(v_m_3076_);
v_nil_3079_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3080_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3081_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3079_, v_cons_3080_, v_c_3045_);
lean_dec(v_c_3045_);
v___x_3082_ = l_Lean_mkApp3(v___x_3077_, v___x_3078_, v___x_3081_, v_a_3073_);
v___x_3083_ = l_Lean_Elab_Tactic_Omega_lookup(v___x_3082_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3127_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3127_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3127_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v_fst_3088_; lean_object* v_snd_3089_; uint8_t v___x_3102_; 
v_fst_3088_ = lean_ctor_get(v_a_3084_, 0);
lean_inc(v_fst_3088_);
v_snd_3089_ = lean_ctor_get(v_a_3084_, 1);
lean_inc(v_snd_3089_);
lean_dec(v_a_3084_);
v___x_3102_ = lean_int_dec_eq(v_val_3071_, v_val_3070_);
lean_dec(v_val_3071_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
lean_dec(v_snd_3089_);
lean_dec(v_fst_3088_);
lean_del_object(v___x_3086_);
lean_dec(v_m_3076_);
lean_dec(v_val_3070_);
lean_del_object(v___x_3068_);
lean_dec_ref(v_justification_3066_);
lean_dec(v_coeffs_3065_);
lean_dec_ref(v_p_3044_);
v___x_3103_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1);
v___x_3104_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3103_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_);
return v___x_3104_;
}
else
{
if (lean_obj_tag(v_snd_3089_) == 0)
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec(v_fst_3088_);
lean_del_object(v___x_3086_);
lean_dec(v_m_3076_);
lean_dec(v_val_3070_);
lean_del_object(v___x_3068_);
lean_dec_ref(v_justification_3066_);
lean_dec(v_coeffs_3065_);
lean_dec_ref(v_p_3044_);
v___x_3105_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3);
v___x_3106_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3105_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_);
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
else
{
lean_object* v_val_3115_; uint8_t v___x_3116_; 
v_val_3115_ = lean_ctor_get(v_snd_3089_, 0);
lean_inc(v_val_3115_);
lean_dec_ref(v_snd_3089_);
v___x_3116_ = l_List_isEmpty___redArg(v_val_3115_);
lean_dec(v_val_3115_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v_fst_3088_);
lean_del_object(v___x_3086_);
lean_dec(v_m_3076_);
lean_dec(v_val_3070_);
lean_del_object(v___x_3068_);
lean_dec_ref(v_justification_3066_);
lean_dec(v_coeffs_3065_);
lean_dec_ref(v_p_3044_);
v___x_3117_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5);
v___x_3118_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3117_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_);
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
else
{
goto v___jp_3090_;
}
}
}
v___jp_3090_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
lean_inc(v_coeffs_3065_);
lean_inc_n(v_m_3076_, 2);
v___x_3091_ = l_Lean_Omega_bmod__coeffs(v_m_3076_, v_fst_3088_, v_coeffs_3065_);
v___x_3092_ = l_Int_bmod(v_val_3070_, v_m_3076_);
v___x_3093_ = l_Lean_Omega_Constraint_exact(v___x_3092_);
v___x_3094_ = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(v___x_3094_, 0, v_m_3076_);
lean_ctor_set(v___x_3094_, 1, v_val_3070_);
lean_ctor_set(v___x_3094_, 2, v_fst_3088_);
lean_ctor_set(v___x_3094_, 3, v_coeffs_3065_);
lean_ctor_set(v___x_3094_, 4, v_justification_3066_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 2, v___x_3094_);
lean_ctor_set(v___x_3068_, 1, v___x_3093_);
lean_ctor_set(v___x_3068_, 0, v___x_3091_);
v___x_3096_ = v___x_3068_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3097_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_3044_, v___x_3096_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v___x_3097_);
v___x_3099_ = v___x_3086_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec(v_m_3076_);
lean_dec(v_val_3071_);
lean_dec(v_val_3070_);
lean_del_object(v___x_3068_);
lean_dec_ref(v_justification_3066_);
lean_dec(v_coeffs_3065_);
lean_dec_ref(v_p_3044_);
v_a_3128_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3083_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3083_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec(v_val_3071_);
lean_dec(v_val_3070_);
lean_del_object(v___x_3068_);
lean_dec_ref(v_justification_3066_);
lean_dec(v_coeffs_3065_);
lean_dec(v_c_3045_);
lean_dec_ref(v_p_3044_);
v_a_3136_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3072_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3072_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
else
{
lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec(v_upperBound_3064_);
lean_dec(v_val_3058_);
lean_dec(v_c_3045_);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_lowerBound_3063_);
if (v_isSharedCheck_3152_ == 0)
{
lean_object* v_unused_3153_; 
v_unused_3153_ = lean_ctor_get(v_lowerBound_3063_, 0);
lean_dec(v_unused_3153_);
v___x_3147_ = v_lowerBound_3063_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_dec(v_lowerBound_3063_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set_tag(v___x_3147_, 0);
lean_ctor_set(v___x_3147_, 0, v_p_3044_);
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_p_3044_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
else
{
lean_object* v___x_3155_; 
lean_dec(v_lowerBound_3063_);
lean_dec(v_val_3058_);
lean_dec(v_c_3045_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set_tag(v___x_3060_, 0);
lean_ctor_set(v___x_3060_, 0, v_p_3044_);
v___x_3155_ = v___x_3060_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_p_3044_);
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
lean_object* v___x_3158_; 
lean_dec(v___x_3057_);
lean_dec(v_c_3045_);
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v_p_3044_);
return v___x_3158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___boxed(lean_object* v_p_3159_, lean_object* v_c_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
uint8_t v_a_boxed_3171_; lean_object* v_res_3172_; 
v_a_boxed_3171_ = lean_unbox(v_a_3164_);
v_res_3172_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3159_, v_c_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_boxed_3171_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
lean_dec(v_a_3169_);
lean_dec_ref(v_a_3168_);
lean_dec(v_a_3167_);
lean_dec_ref(v_a_3166_);
lean_dec(v_a_3165_);
lean_dec_ref(v_a_3163_);
lean_dec(v_a_3162_);
lean_dec(v_a_3161_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_object* v_00_u03b1_3173_, lean_object* v_msg_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, uint8_t v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3174_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___boxed(lean_object* v_00_u03b1_3186_, lean_object* v_msg_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
uint8_t v___y_14890__boxed_3198_; lean_object* v_res_3199_; 
v___y_14890__boxed_3198_ = lean_unbox(v___y_3191_);
v_res_3199_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(v_00_u03b1_3186_, v_msg_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_14890__boxed_3198_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality(lean_object* v_p_3200_, lean_object* v_c_3201_, lean_object* v_m_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, uint8_t v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v___x_3213_; uint8_t v___x_3214_; 
v___x_3213_ = lean_unsigned_to_nat(1u);
v___x_3214_ = lean_nat_dec_eq(v_m_3202_, v___x_3213_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; 
v___x_3215_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3200_, v_c_3201_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
return v___x_3215_;
}
else
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_3200_, v_c_3201_);
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
return v___x_3217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality___boxed(lean_object* v_p_3218_, lean_object* v_c_3219_, lean_object* v_m_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_){
_start:
{
uint8_t v_a_boxed_3231_; lean_object* v_res_3232_; 
v_a_boxed_3231_ = lean_unbox(v_a_3224_);
v_res_3232_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3218_, v_c_3219_, v_m_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_boxed_3231_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_);
lean_dec(v_a_3229_);
lean_dec_ref(v_a_3228_);
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3223_);
lean_dec(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec(v_m_3220_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(lean_object* v_p_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, uint8_t v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
uint8_t v_possible_3244_; 
v_possible_3244_ = lean_ctor_get_uint8(v_p_3233_, sizeof(void*)*7);
if (v_possible_3244_ == 0)
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3245_, 0, v_p_3233_);
return v___x_3245_;
}
else
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_3233_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3247_, 0, v_p_3233_);
return v___x_3247_;
}
else
{
lean_object* v_val_3248_; lean_object* v_fst_3249_; lean_object* v_snd_3250_; lean_object* v___x_3251_; 
v_val_3248_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_val_3248_);
lean_dec_ref(v___x_3246_);
v_fst_3249_ = lean_ctor_get(v_val_3248_, 0);
lean_inc(v_fst_3249_);
v_snd_3250_ = lean_ctor_get(v_val_3248_, 1);
lean_inc(v_snd_3250_);
lean_dec(v_val_3248_);
v___x_3251_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3233_, v_fst_3249_, v_snd_3250_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
lean_dec(v_snd_3250_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref(v___x_3251_);
v_p_3233_ = v_a_3252_;
goto _start;
}
else
{
return v___x_3251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities___boxed(lean_object* v_p_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
uint8_t v_a_boxed_3265_; lean_object* v_res_3266_; 
v_a_boxed_3265_ = lean_unbox(v_a_3258_);
v_res_3266_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_boxed_3265_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
lean_dec(v_a_3259_);
lean_dec_ref(v_a_3257_);
lean_dec(v_a_3256_);
lean_dec(v_a_3255_);
return v_res_3266_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = lean_box(0);
v___x_3274_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1));
v___x_3275_ = l_Lean_Expr_const___override(v___x_3274_, v___x_3273_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object* v_c_3276_, lean_object* v_x_3277_, lean_object* v_p_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, uint8_t v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3280_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_a_3290_);
lean_dec_ref(v___x_3289_);
v___x_3291_ = lean_box(v_a_3282_);
lean_inc(v_a_3287_);
lean_inc_ref(v_a_3286_);
lean_inc(v_a_3285_);
lean_inc_ref(v_a_3284_);
lean_inc(v_a_3283_);
lean_inc_ref(v_a_3281_);
lean_inc(v_a_3280_);
lean_inc(v_a_3279_);
v___x_3292_ = lean_apply_10(v_p_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v___x_3291_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, lean_box(0));
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3318_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3295_ = v___x_3292_;
v_isShared_3296_ = v_isSharedCheck_3318_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3292_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3318_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; lean_object* v___y_3299_; lean_object* v___x_3307_; uint8_t v___x_3308_; 
v___x_3297_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2);
v___x_3307_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3308_ = lean_int_dec_le(v___x_3307_, v_c_3276_);
if (v___x_3308_ == 0)
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3309_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3310_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3311_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3312_ = lean_int_neg(v_c_3276_);
v___x_3313_ = l_Int_toNat(v___x_3312_);
lean_dec(v___x_3312_);
v___x_3314_ = l_Lean_instToExprInt_mkNat(v___x_3313_);
v___x_3315_ = l_Lean_mkApp3(v___x_3309_, v___x_3310_, v___x_3311_, v___x_3314_);
v___y_3299_ = v___x_3315_;
goto v___jp_3298_;
}
else
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = l_Int_toNat(v_c_3276_);
v___x_3317_ = l_Lean_instToExprInt_mkNat(v___x_3316_);
v___y_3299_ = v___x_3317_;
goto v___jp_3298_;
}
v___jp_3298_:
{
lean_object* v_nil_3300_; lean_object* v_cons_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3305_; 
v_nil_3300_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3301_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3302_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3300_, v_cons_3301_, v_x_3277_);
v___x_3303_ = l_Lean_mkApp4(v___x_3297_, v___y_3299_, v___x_3302_, v_a_3290_, v_a_3293_);
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 0, v___x_3303_);
v___x_3305_ = v___x_3295_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
else
{
lean_dec(v_a_3290_);
return v___x_3292_;
}
}
else
{
lean_dec_ref(v_p_3278_);
return v___x_3289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object* v_c_3319_, lean_object* v_x_3320_, lean_object* v_p_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_){
_start:
{
uint8_t v_a_boxed_3332_; lean_object* v_res_3333_; 
v_a_boxed_3332_ = lean_unbox(v_a_3325_);
v_res_3333_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(v_c_3319_, v_x_3320_, v_p_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_boxed_3332_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_);
lean_dec(v_a_3330_);
lean_dec_ref(v_a_3329_);
lean_dec(v_a_3328_);
lean_dec_ref(v_a_3327_);
lean_dec(v_a_3326_);
lean_dec_ref(v_a_3324_);
lean_dec(v_a_3323_);
lean_dec(v_a_3322_);
lean_dec(v_x_3320_);
lean_dec(v_c_3319_);
return v_res_3333_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3340_ = lean_box(0);
v___x_3341_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1));
v___x_3342_ = l_Lean_Expr_const___override(v___x_3341_, v___x_3340_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(lean_object* v_c_3343_, lean_object* v_x_3344_, lean_object* v_p_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, uint8_t v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3347_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref(v___x_3356_);
v___x_3358_ = lean_box(v_a_3349_);
lean_inc(v_a_3354_);
lean_inc_ref(v_a_3353_);
lean_inc(v_a_3352_);
lean_inc_ref(v_a_3351_);
lean_inc(v_a_3350_);
lean_inc_ref(v_a_3348_);
lean_inc(v_a_3347_);
lean_inc(v_a_3346_);
v___x_3359_ = lean_apply_10(v_p_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v___x_3358_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, lean_box(0));
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3385_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3362_ = v___x_3359_;
v_isShared_3363_ = v_isSharedCheck_3385_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3385_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3364_; lean_object* v___y_3366_; lean_object* v___x_3374_; uint8_t v___x_3375_; 
v___x_3364_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2);
v___x_3374_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3375_ = lean_int_dec_le(v___x_3374_, v_c_3343_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3376_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3377_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3378_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3379_ = lean_int_neg(v_c_3343_);
v___x_3380_ = l_Int_toNat(v___x_3379_);
lean_dec(v___x_3379_);
v___x_3381_ = l_Lean_instToExprInt_mkNat(v___x_3380_);
v___x_3382_ = l_Lean_mkApp3(v___x_3376_, v___x_3377_, v___x_3378_, v___x_3381_);
v___y_3366_ = v___x_3382_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3383_ = l_Int_toNat(v_c_3343_);
v___x_3384_ = l_Lean_instToExprInt_mkNat(v___x_3383_);
v___y_3366_ = v___x_3384_;
goto v___jp_3365_;
}
v___jp_3365_:
{
lean_object* v_nil_3367_; lean_object* v_cons_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3372_; 
v_nil_3367_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3368_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3369_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3367_, v_cons_3368_, v_x_3344_);
v___x_3370_ = l_Lean_mkApp4(v___x_3364_, v___y_3366_, v___x_3369_, v_a_3357_, v_a_3360_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 0, v___x_3370_);
v___x_3372_ = v___x_3362_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
else
{
lean_dec(v_a_3357_);
return v___x_3359_;
}
}
else
{
lean_dec_ref(v_p_3345_);
return v___x_3356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed(lean_object* v_c_3386_, lean_object* v_x_3387_, lean_object* v_p_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
uint8_t v_a_boxed_3399_; lean_object* v_res_3400_; 
v_a_boxed_3399_ = lean_unbox(v_a_3392_);
v_res_3400_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(v_c_3386_, v_x_3387_, v_p_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_boxed_3399_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3391_);
lean_dec(v_a_3390_);
lean_dec(v_a_3389_);
lean_dec(v_x_3387_);
lean_dec(v_c_3386_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(lean_object* v_prf_x3f_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, uint8_t v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
if (lean_obj_tag(v_prf_x3f_3401_) == 0)
{
lean_object* v___x_3412_; uint8_t v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3412_ = lean_box(0);
v___x_3413_ = 0;
v___x_3414_ = lean_box(0);
v___x_3415_ = l_Lean_Meta_mkFreshExprMVar(v___x_3412_, v___x_3413_, v___x_3414_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; uint8_t v___x_3417_; lean_object* v___x_3418_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3416_);
lean_dec_ref(v___x_3415_);
v___x_3417_ = 0;
v___x_3418_ = l_Lean_Meta_mkSorry(v_a_3416_, v___x_3417_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
return v___x_3418_;
}
else
{
return v___x_3415_;
}
}
else
{
lean_object* v_val_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v_val_3419_ = lean_ctor_get(v_prf_x3f_3401_, 0);
lean_inc(v_val_3419_);
lean_dec_ref(v_prf_x3f_3401_);
v___x_3420_ = lean_box(v___y_3405_);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
lean_inc(v___y_3408_);
lean_inc_ref(v___y_3407_);
lean_inc(v___y_3406_);
lean_inc_ref(v___y_3404_);
lean_inc(v___y_3403_);
lean_inc(v___y_3402_);
v___x_3421_ = lean_apply_10(v_val_3419_, v___y_3402_, v___y_3403_, v___y_3404_, v___x_3420_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, lean_box(0));
return v___x_3421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed(lean_object* v_prf_x3f_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
uint8_t v___y_833__boxed_3433_; lean_object* v_res_3434_; 
v___y_833__boxed_3433_ = lean_unbox(v___y_3426_);
v_res_3434_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(v_prf_x3f_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_833__boxed_3433_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec(v___y_3423_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality(lean_object* v_p_3435_, lean_object* v_const_3436_, lean_object* v_coeffs_3437_, lean_object* v_prf_x3f_3438_){
_start:
{
lean_object* v_assumptions_3439_; lean_object* v_numVars_3440_; lean_object* v_constraints_3441_; lean_object* v_equalities_3442_; lean_object* v_eliminations_3443_; uint8_t v_possible_3444_; lean_object* v_proveFalse_x3f_3445_; lean_object* v_explanation_x3f_3446_; lean_object* v_prf_3447_; lean_object* v_i_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v_p_x27_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v_f_3457_; lean_object* v_f_3458_; lean_object* v_f_3459_; lean_object* v___x_3460_; 
v_assumptions_3439_ = lean_ctor_get(v_p_3435_, 0);
v_numVars_3440_ = lean_ctor_get(v_p_3435_, 1);
v_constraints_3441_ = lean_ctor_get(v_p_3435_, 2);
v_equalities_3442_ = lean_ctor_get(v_p_3435_, 3);
v_eliminations_3443_ = lean_ctor_get(v_p_3435_, 4);
v_possible_3444_ = lean_ctor_get_uint8(v_p_3435_, sizeof(void*)*7);
v_proveFalse_x3f_3445_ = lean_ctor_get(v_p_3435_, 5);
v_explanation_x3f_3446_ = lean_ctor_get(v_p_3435_, 6);
v_prf_3447_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3447_, 0, v_prf_x3f_3438_);
v_i_3448_ = lean_array_get_size(v_assumptions_3439_);
lean_inc_n(v_coeffs_3437_, 2);
lean_inc(v_const_3436_);
v___x_3449_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed), 13, 3);
lean_closure_set(v___x_3449_, 0, v_const_3436_);
lean_closure_set(v___x_3449_, 1, v_coeffs_3437_);
lean_closure_set(v___x_3449_, 2, v_prf_3447_);
lean_inc_ref(v_assumptions_3439_);
v___x_3450_ = lean_array_push(v_assumptions_3439_, v___x_3449_);
lean_inc_ref(v_explanation_x3f_3446_);
lean_inc(v_proveFalse_x3f_3445_);
lean_inc(v_eliminations_3443_);
lean_inc_ref(v_equalities_3442_);
lean_inc_ref(v_constraints_3441_);
lean_inc(v_numVars_3440_);
v_p_x27_3451_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3451_, 0, v___x_3450_);
lean_ctor_set(v_p_x27_3451_, 1, v_numVars_3440_);
lean_ctor_set(v_p_x27_3451_, 2, v_constraints_3441_);
lean_ctor_set(v_p_x27_3451_, 3, v_equalities_3442_);
lean_ctor_set(v_p_x27_3451_, 4, v_eliminations_3443_);
lean_ctor_set(v_p_x27_3451_, 5, v_proveFalse_x3f_3445_);
lean_ctor_set(v_p_x27_3451_, 6, v_explanation_x3f_3446_);
lean_ctor_set_uint8(v_p_x27_3451_, sizeof(void*)*7, v_possible_3444_);
v___x_3452_ = lean_int_neg(v_const_3436_);
lean_dec(v_const_3436_);
v___x_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
v___x_3454_ = lean_box(0);
v___x_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3453_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
lean_inc_ref(v___x_3455_);
v___x_3456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3455_);
lean_ctor_set(v___x_3456_, 1, v_coeffs_3437_);
lean_ctor_set(v___x_3456_, 2, v_i_3448_);
v_f_3457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3457_, 0, v_coeffs_3437_);
lean_ctor_set(v_f_3457_, 1, v___x_3455_);
lean_ctor_set(v_f_3457_, 2, v___x_3456_);
v_f_3458_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3435_, v_f_3457_);
v_f_3459_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3458_);
v___x_3460_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3451_, v_f_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality(lean_object* v_p_3461_, lean_object* v_const_3462_, lean_object* v_coeffs_3463_, lean_object* v_prf_x3f_3464_){
_start:
{
lean_object* v_assumptions_3465_; lean_object* v_numVars_3466_; lean_object* v_constraints_3467_; lean_object* v_equalities_3468_; lean_object* v_eliminations_3469_; uint8_t v_possible_3470_; lean_object* v_proveFalse_x3f_3471_; lean_object* v_explanation_x3f_3472_; lean_object* v_prf_3473_; lean_object* v_i_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v_p_x27_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v_f_3482_; lean_object* v_f_3483_; lean_object* v_f_3484_; lean_object* v___x_3485_; 
v_assumptions_3465_ = lean_ctor_get(v_p_3461_, 0);
v_numVars_3466_ = lean_ctor_get(v_p_3461_, 1);
v_constraints_3467_ = lean_ctor_get(v_p_3461_, 2);
v_equalities_3468_ = lean_ctor_get(v_p_3461_, 3);
v_eliminations_3469_ = lean_ctor_get(v_p_3461_, 4);
v_possible_3470_ = lean_ctor_get_uint8(v_p_3461_, sizeof(void*)*7);
v_proveFalse_x3f_3471_ = lean_ctor_get(v_p_3461_, 5);
v_explanation_x3f_3472_ = lean_ctor_get(v_p_3461_, 6);
v_prf_3473_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3473_, 0, v_prf_x3f_3464_);
v_i_3474_ = lean_array_get_size(v_assumptions_3465_);
lean_inc_n(v_coeffs_3463_, 2);
lean_inc(v_const_3462_);
v___x_3475_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed), 13, 3);
lean_closure_set(v___x_3475_, 0, v_const_3462_);
lean_closure_set(v___x_3475_, 1, v_coeffs_3463_);
lean_closure_set(v___x_3475_, 2, v_prf_3473_);
lean_inc_ref(v_assumptions_3465_);
v___x_3476_ = lean_array_push(v_assumptions_3465_, v___x_3475_);
lean_inc_ref(v_explanation_x3f_3472_);
lean_inc(v_proveFalse_x3f_3471_);
lean_inc(v_eliminations_3469_);
lean_inc_ref(v_equalities_3468_);
lean_inc_ref(v_constraints_3467_);
lean_inc(v_numVars_3466_);
v_p_x27_3477_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3477_, 0, v___x_3476_);
lean_ctor_set(v_p_x27_3477_, 1, v_numVars_3466_);
lean_ctor_set(v_p_x27_3477_, 2, v_constraints_3467_);
lean_ctor_set(v_p_x27_3477_, 3, v_equalities_3468_);
lean_ctor_set(v_p_x27_3477_, 4, v_eliminations_3469_);
lean_ctor_set(v_p_x27_3477_, 5, v_proveFalse_x3f_3471_);
lean_ctor_set(v_p_x27_3477_, 6, v_explanation_x3f_3472_);
lean_ctor_set_uint8(v_p_x27_3477_, sizeof(void*)*7, v_possible_3470_);
v___x_3478_ = lean_int_neg(v_const_3462_);
lean_dec(v_const_3462_);
v___x_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
lean_inc_ref(v___x_3479_);
v___x_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
lean_inc_ref(v___x_3480_);
v___x_3481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
lean_ctor_set(v___x_3481_, 1, v_coeffs_3463_);
lean_ctor_set(v___x_3481_, 2, v_i_3474_);
v_f_3482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3482_, 0, v_coeffs_3463_);
lean_ctor_set(v_f_3482_, 1, v___x_3480_);
lean_ctor_set(v_f_3482_, 2, v___x_3481_);
v_f_3483_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3461_, v_f_3482_);
v_f_3484_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3483_);
v___x_3485_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3477_, v_f_3484_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(lean_object* v_x_3486_, lean_object* v_x_3487_){
_start:
{
if (lean_obj_tag(v_x_3487_) == 0)
{
return v_x_3486_;
}
else
{
lean_object* v_head_3488_; lean_object* v_snd_3489_; lean_object* v_tail_3490_; lean_object* v_fst_3491_; lean_object* v_fst_3492_; lean_object* v_snd_3493_; lean_object* v___x_3494_; 
v_head_3488_ = lean_ctor_get(v_x_3487_, 0);
lean_inc(v_head_3488_);
v_snd_3489_ = lean_ctor_get(v_head_3488_, 1);
lean_inc(v_snd_3489_);
v_tail_3490_ = lean_ctor_get(v_x_3487_, 1);
lean_inc(v_tail_3490_);
lean_dec_ref(v_x_3487_);
v_fst_3491_ = lean_ctor_get(v_head_3488_, 0);
lean_inc(v_fst_3491_);
lean_dec(v_head_3488_);
v_fst_3492_ = lean_ctor_get(v_snd_3489_, 0);
lean_inc(v_fst_3492_);
v_snd_3493_ = lean_ctor_get(v_snd_3489_, 1);
lean_inc(v_snd_3493_);
lean_dec(v_snd_3489_);
v___x_3494_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality(v_x_3486_, v_fst_3491_, v_fst_3492_, v_snd_3493_);
v_x_3486_ = v___x_3494_;
v_x_3487_ = v_tail_3490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequalities(lean_object* v_p_3496_, lean_object* v_ineqs_3497_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(v_p_3496_, v_ineqs_3497_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(lean_object* v_x_3499_, lean_object* v_x_3500_){
_start:
{
if (lean_obj_tag(v_x_3500_) == 0)
{
return v_x_3499_;
}
else
{
lean_object* v_head_3501_; lean_object* v_snd_3502_; lean_object* v_tail_3503_; lean_object* v_fst_3504_; lean_object* v_fst_3505_; lean_object* v_snd_3506_; lean_object* v___x_3507_; 
v_head_3501_ = lean_ctor_get(v_x_3500_, 0);
lean_inc(v_head_3501_);
v_snd_3502_ = lean_ctor_get(v_head_3501_, 1);
lean_inc(v_snd_3502_);
v_tail_3503_ = lean_ctor_get(v_x_3500_, 1);
lean_inc(v_tail_3503_);
lean_dec_ref(v_x_3500_);
v_fst_3504_ = lean_ctor_get(v_head_3501_, 0);
lean_inc(v_fst_3504_);
lean_dec(v_head_3501_);
v_fst_3505_ = lean_ctor_get(v_snd_3502_, 0);
lean_inc(v_fst_3505_);
v_snd_3506_ = lean_ctor_get(v_snd_3502_, 1);
lean_inc(v_snd_3506_);
lean_dec(v_snd_3502_);
v___x_3507_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality(v_x_3499_, v_fst_3504_, v_fst_3505_, v_snd_3506_);
v_x_3499_ = v___x_3507_;
v_x_3500_ = v_tail_3503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEqualities(lean_object* v_p_3509_, lean_object* v_eqs_3510_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(v_p_3509_, v_eqs_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0(lean_object* v___x_3518_, lean_object* v_x_3519_){
_start:
{
lean_object* v_constraint_3520_; lean_object* v_coeffs_3521_; lean_object* v_lowerBound_3522_; lean_object* v_upperBound_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___y_3528_; lean_object* v___y_3529_; 
v_constraint_3520_ = lean_ctor_get(v_x_3519_, 1);
lean_inc_ref(v_constraint_3520_);
v_coeffs_3521_ = lean_ctor_get(v_x_3519_, 0);
lean_inc(v_coeffs_3521_);
lean_dec_ref(v_x_3519_);
v_lowerBound_3522_ = lean_ctor_get(v_constraint_3520_, 0);
lean_inc(v_lowerBound_3522_);
v_upperBound_3523_ = lean_ctor_get(v_constraint_3520_, 1);
lean_inc(v_upperBound_3523_);
lean_dec_ref(v_constraint_3520_);
v___x_3524_ = l_List_toString___redArg(v___x_3518_, v_coeffs_3521_);
v___x_3525_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3526_ = lean_string_append(v___x_3524_, v___x_3525_);
if (lean_obj_tag(v_lowerBound_3522_) == 0)
{
if (lean_obj_tag(v_upperBound_3523_) == 0)
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3535_ = lean_string_append(v___x_3526_, v___x_3534_);
return v___x_3535_;
}
else
{
lean_object* v_val_3536_; lean_object* v___x_3537_; lean_object* v___y_3539_; lean_object* v_intZero_3544_; uint8_t v_isNeg_3545_; 
v_val_3536_ = lean_ctor_get(v_upperBound_3523_, 0);
lean_inc(v_val_3536_);
lean_dec_ref(v_upperBound_3523_);
v___x_3537_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3544_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3545_ = lean_int_dec_lt(v_val_3536_, v_intZero_3544_);
if (v_isNeg_3545_ == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3547_; 
v_a_3546_ = lean_nat_abs(v_val_3536_);
lean_dec(v_val_3536_);
v___x_3547_ = l_Nat_reprFast(v_a_3546_);
v___y_3539_ = v___x_3547_;
goto v___jp_3538_;
}
else
{
lean_object* v_abs_3548_; lean_object* v_one_3549_; lean_object* v_a_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v_abs_3548_ = lean_nat_abs(v_val_3536_);
lean_dec(v_val_3536_);
v_one_3549_ = lean_unsigned_to_nat(1u);
v_a_3550_ = lean_nat_sub(v_abs_3548_, v_one_3549_);
lean_dec(v_abs_3548_);
v___x_3551_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3552_ = lean_nat_add(v_a_3550_, v_one_3549_);
lean_dec(v_a_3550_);
v___x_3553_ = l_Nat_reprFast(v___x_3552_);
v___x_3554_ = lean_string_append(v___x_3551_, v___x_3553_);
lean_dec_ref(v___x_3553_);
v___y_3539_ = v___x_3554_;
goto v___jp_3538_;
}
v___jp_3538_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3540_ = lean_string_append(v___x_3537_, v___y_3539_);
lean_dec_ref(v___y_3539_);
v___x_3541_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3542_ = lean_string_append(v___x_3540_, v___x_3541_);
v___x_3543_ = lean_string_append(v___x_3526_, v___x_3542_);
lean_dec_ref(v___x_3542_);
return v___x_3543_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3523_) == 0)
{
lean_object* v_val_3555_; lean_object* v___x_3556_; lean_object* v___y_3558_; lean_object* v_intZero_3563_; uint8_t v_isNeg_3564_; 
v_val_3555_ = lean_ctor_get(v_lowerBound_3522_, 0);
lean_inc(v_val_3555_);
lean_dec_ref(v_lowerBound_3522_);
v___x_3556_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
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
v___x_3560_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3561_ = lean_string_append(v___x_3559_, v___x_3560_);
v___x_3562_ = lean_string_append(v___x_3526_, v___x_3561_);
lean_dec_ref(v___x_3561_);
return v___x_3562_;
}
}
else
{
lean_object* v_val_3574_; lean_object* v_val_3575_; uint8_t v___x_3576_; 
v_val_3574_ = lean_ctor_get(v_lowerBound_3522_, 0);
lean_inc(v_val_3574_);
lean_dec_ref(v_lowerBound_3522_);
v_val_3575_ = lean_ctor_get(v_upperBound_3523_, 0);
lean_inc(v_val_3575_);
lean_dec_ref(v_upperBound_3523_);
v___x_3576_ = lean_int_dec_lt(v_val_3575_, v_val_3574_);
if (v___x_3576_ == 0)
{
uint8_t v___x_3577_; 
v___x_3577_ = lean_int_dec_eq(v_val_3574_, v_val_3575_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v___y_3580_; lean_object* v_intZero_3595_; uint8_t v_isNeg_3596_; 
v___x_3578_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3595_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3596_ = lean_int_dec_lt(v_val_3574_, v_intZero_3595_);
if (v_isNeg_3596_ == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3598_; 
v_a_3597_ = lean_nat_abs(v_val_3574_);
lean_dec(v_val_3574_);
v___x_3598_ = l_Nat_reprFast(v_a_3597_);
v___y_3580_ = v___x_3598_;
goto v___jp_3579_;
}
else
{
lean_object* v_abs_3599_; lean_object* v_one_3600_; lean_object* v_a_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v_abs_3599_ = lean_nat_abs(v_val_3574_);
lean_dec(v_val_3574_);
v_one_3600_ = lean_unsigned_to_nat(1u);
v_a_3601_ = lean_nat_sub(v_abs_3599_, v_one_3600_);
lean_dec(v_abs_3599_);
v___x_3602_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3603_ = lean_nat_add(v_a_3601_, v_one_3600_);
lean_dec(v_a_3601_);
v___x_3604_ = l_Nat_reprFast(v___x_3603_);
v___x_3605_ = lean_string_append(v___x_3602_, v___x_3604_);
lean_dec_ref(v___x_3604_);
v___y_3580_ = v___x_3605_;
goto v___jp_3579_;
}
v___jp_3579_:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v_intZero_3584_; uint8_t v_isNeg_3585_; 
v___x_3581_ = lean_string_append(v___x_3578_, v___y_3580_);
lean_dec_ref(v___y_3580_);
v___x_3582_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3583_ = lean_string_append(v___x_3581_, v___x_3582_);
v_intZero_3584_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3585_ = lean_int_dec_lt(v_val_3575_, v_intZero_3584_);
if (v_isNeg_3585_ == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3587_; 
v_a_3586_ = lean_nat_abs(v_val_3575_);
lean_dec(v_val_3575_);
v___x_3587_ = l_Nat_reprFast(v_a_3586_);
v___y_3528_ = v___x_3583_;
v___y_3529_ = v___x_3587_;
goto v___jp_3527_;
}
else
{
lean_object* v_abs_3588_; lean_object* v_one_3589_; lean_object* v_a_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v_abs_3588_ = lean_nat_abs(v_val_3575_);
lean_dec(v_val_3575_);
v_one_3589_ = lean_unsigned_to_nat(1u);
v_a_3590_ = lean_nat_sub(v_abs_3588_, v_one_3589_);
lean_dec(v_abs_3588_);
v___x_3591_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3592_ = lean_nat_add(v_a_3590_, v_one_3589_);
lean_dec(v_a_3590_);
v___x_3593_ = l_Nat_reprFast(v___x_3592_);
v___x_3594_ = lean_string_append(v___x_3591_, v___x_3593_);
lean_dec_ref(v___x_3593_);
v___y_3528_ = v___x_3583_;
v___y_3529_ = v___x_3594_;
goto v___jp_3527_;
}
}
}
else
{
lean_object* v___x_3606_; lean_object* v___y_3608_; lean_object* v_intZero_3613_; uint8_t v_isNeg_3614_; 
lean_dec(v_val_3575_);
v___x_3606_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3613_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3614_ = lean_int_dec_lt(v_val_3574_, v_intZero_3613_);
if (v_isNeg_3614_ == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3616_; 
v_a_3615_ = lean_nat_abs(v_val_3574_);
lean_dec(v_val_3574_);
v___x_3616_ = l_Nat_reprFast(v_a_3615_);
v___y_3608_ = v___x_3616_;
goto v___jp_3607_;
}
else
{
lean_object* v_abs_3617_; lean_object* v_one_3618_; lean_object* v_a_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v_abs_3617_ = lean_nat_abs(v_val_3574_);
lean_dec(v_val_3574_);
v_one_3618_ = lean_unsigned_to_nat(1u);
v_a_3619_ = lean_nat_sub(v_abs_3617_, v_one_3618_);
lean_dec(v_abs_3617_);
v___x_3620_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3621_ = lean_nat_add(v_a_3619_, v_one_3618_);
lean_dec(v_a_3619_);
v___x_3622_ = l_Nat_reprFast(v___x_3621_);
v___x_3623_ = lean_string_append(v___x_3620_, v___x_3622_);
lean_dec_ref(v___x_3622_);
v___y_3608_ = v___x_3623_;
goto v___jp_3607_;
}
v___jp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3609_ = lean_string_append(v___x_3606_, v___y_3608_);
lean_dec_ref(v___y_3608_);
v___x_3610_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3611_ = lean_string_append(v___x_3609_, v___x_3610_);
v___x_3612_ = lean_string_append(v___x_3526_, v___x_3611_);
lean_dec_ref(v___x_3611_);
return v___x_3612_;
}
}
}
else
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
lean_dec(v_val_3575_);
lean_dec(v_val_3574_);
v___x_3624_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3625_ = lean_string_append(v___x_3526_, v___x_3624_);
return v___x_3625_;
}
}
}
v___jp_3527_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3530_ = lean_string_append(v___y_3528_, v___y_3529_);
lean_dec_ref(v___y_3529_);
v___x_3531_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3532_ = lean_string_append(v___x_3530_, v___x_3531_);
v___x_3533_ = lean_string_append(v___x_3526_, v___x_3532_);
lean_dec_ref(v___x_3532_);
return v___x_3533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1(lean_object* v___x_3626_, lean_object* v_x_3627_){
_start:
{
lean_object* v_fst_3628_; lean_object* v_constraint_3629_; lean_object* v_coeffs_3630_; lean_object* v_lowerBound_3631_; lean_object* v_upperBound_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___y_3637_; lean_object* v___y_3638_; 
v_fst_3628_ = lean_ctor_get(v_x_3627_, 0);
lean_inc(v_fst_3628_);
lean_dec_ref(v_x_3627_);
v_constraint_3629_ = lean_ctor_get(v_fst_3628_, 1);
lean_inc_ref(v_constraint_3629_);
v_coeffs_3630_ = lean_ctor_get(v_fst_3628_, 0);
lean_inc(v_coeffs_3630_);
lean_dec(v_fst_3628_);
v_lowerBound_3631_ = lean_ctor_get(v_constraint_3629_, 0);
lean_inc(v_lowerBound_3631_);
v_upperBound_3632_ = lean_ctor_get(v_constraint_3629_, 1);
lean_inc(v_upperBound_3632_);
lean_dec_ref(v_constraint_3629_);
v___x_3633_ = l_List_toString___redArg(v___x_3626_, v_coeffs_3630_);
v___x_3634_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3635_ = lean_string_append(v___x_3633_, v___x_3634_);
if (lean_obj_tag(v_lowerBound_3631_) == 0)
{
if (lean_obj_tag(v_upperBound_3632_) == 0)
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3644_ = lean_string_append(v___x_3635_, v___x_3643_);
return v___x_3644_;
}
else
{
lean_object* v_val_3645_; lean_object* v___x_3646_; lean_object* v___y_3648_; lean_object* v_intZero_3653_; uint8_t v_isNeg_3654_; 
v_val_3645_ = lean_ctor_get(v_upperBound_3632_, 0);
lean_inc(v_val_3645_);
lean_dec_ref(v_upperBound_3632_);
v___x_3646_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3653_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3654_ = lean_int_dec_lt(v_val_3645_, v_intZero_3653_);
if (v_isNeg_3654_ == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3656_; 
v_a_3655_ = lean_nat_abs(v_val_3645_);
lean_dec(v_val_3645_);
v___x_3656_ = l_Nat_reprFast(v_a_3655_);
v___y_3648_ = v___x_3656_;
goto v___jp_3647_;
}
else
{
lean_object* v_abs_3657_; lean_object* v_one_3658_; lean_object* v_a_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_abs_3657_ = lean_nat_abs(v_val_3645_);
lean_dec(v_val_3645_);
v_one_3658_ = lean_unsigned_to_nat(1u);
v_a_3659_ = lean_nat_sub(v_abs_3657_, v_one_3658_);
lean_dec(v_abs_3657_);
v___x_3660_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3661_ = lean_nat_add(v_a_3659_, v_one_3658_);
lean_dec(v_a_3659_);
v___x_3662_ = l_Nat_reprFast(v___x_3661_);
v___x_3663_ = lean_string_append(v___x_3660_, v___x_3662_);
lean_dec_ref(v___x_3662_);
v___y_3648_ = v___x_3663_;
goto v___jp_3647_;
}
v___jp_3647_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3649_ = lean_string_append(v___x_3646_, v___y_3648_);
lean_dec_ref(v___y_3648_);
v___x_3650_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3651_ = lean_string_append(v___x_3649_, v___x_3650_);
v___x_3652_ = lean_string_append(v___x_3635_, v___x_3651_);
lean_dec_ref(v___x_3651_);
return v___x_3652_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3632_) == 0)
{
lean_object* v_val_3664_; lean_object* v___x_3665_; lean_object* v___y_3667_; lean_object* v_intZero_3672_; uint8_t v_isNeg_3673_; 
v_val_3664_ = lean_ctor_get(v_lowerBound_3631_, 0);
lean_inc(v_val_3664_);
lean_dec_ref(v_lowerBound_3631_);
v___x_3665_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
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
v___x_3669_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3670_ = lean_string_append(v___x_3668_, v___x_3669_);
v___x_3671_ = lean_string_append(v___x_3635_, v___x_3670_);
lean_dec_ref(v___x_3670_);
return v___x_3671_;
}
}
else
{
lean_object* v_val_3683_; lean_object* v_val_3684_; uint8_t v___x_3685_; 
v_val_3683_ = lean_ctor_get(v_lowerBound_3631_, 0);
lean_inc(v_val_3683_);
lean_dec_ref(v_lowerBound_3631_);
v_val_3684_ = lean_ctor_get(v_upperBound_3632_, 0);
lean_inc(v_val_3684_);
lean_dec_ref(v_upperBound_3632_);
v___x_3685_ = lean_int_dec_lt(v_val_3684_, v_val_3683_);
if (v___x_3685_ == 0)
{
uint8_t v___x_3686_; 
v___x_3686_ = lean_int_dec_eq(v_val_3683_, v_val_3684_);
if (v___x_3686_ == 0)
{
lean_object* v___x_3687_; lean_object* v___y_3689_; lean_object* v_intZero_3704_; uint8_t v_isNeg_3705_; 
v___x_3687_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3704_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3705_ = lean_int_dec_lt(v_val_3683_, v_intZero_3704_);
if (v_isNeg_3705_ == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3707_; 
v_a_3706_ = lean_nat_abs(v_val_3683_);
lean_dec(v_val_3683_);
v___x_3707_ = l_Nat_reprFast(v_a_3706_);
v___y_3689_ = v___x_3707_;
goto v___jp_3688_;
}
else
{
lean_object* v_abs_3708_; lean_object* v_one_3709_; lean_object* v_a_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v_abs_3708_ = lean_nat_abs(v_val_3683_);
lean_dec(v_val_3683_);
v_one_3709_ = lean_unsigned_to_nat(1u);
v_a_3710_ = lean_nat_sub(v_abs_3708_, v_one_3709_);
lean_dec(v_abs_3708_);
v___x_3711_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3712_ = lean_nat_add(v_a_3710_, v_one_3709_);
lean_dec(v_a_3710_);
v___x_3713_ = l_Nat_reprFast(v___x_3712_);
v___x_3714_ = lean_string_append(v___x_3711_, v___x_3713_);
lean_dec_ref(v___x_3713_);
v___y_3689_ = v___x_3714_;
goto v___jp_3688_;
}
v___jp_3688_:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v_intZero_3693_; uint8_t v_isNeg_3694_; 
v___x_3690_ = lean_string_append(v___x_3687_, v___y_3689_);
lean_dec_ref(v___y_3689_);
v___x_3691_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3692_ = lean_string_append(v___x_3690_, v___x_3691_);
v_intZero_3693_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3694_ = lean_int_dec_lt(v_val_3684_, v_intZero_3693_);
if (v_isNeg_3694_ == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3696_; 
v_a_3695_ = lean_nat_abs(v_val_3684_);
lean_dec(v_val_3684_);
v___x_3696_ = l_Nat_reprFast(v_a_3695_);
v___y_3637_ = v___x_3692_;
v___y_3638_ = v___x_3696_;
goto v___jp_3636_;
}
else
{
lean_object* v_abs_3697_; lean_object* v_one_3698_; lean_object* v_a_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v_abs_3697_ = lean_nat_abs(v_val_3684_);
lean_dec(v_val_3684_);
v_one_3698_ = lean_unsigned_to_nat(1u);
v_a_3699_ = lean_nat_sub(v_abs_3697_, v_one_3698_);
lean_dec(v_abs_3697_);
v___x_3700_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3701_ = lean_nat_add(v_a_3699_, v_one_3698_);
lean_dec(v_a_3699_);
v___x_3702_ = l_Nat_reprFast(v___x_3701_);
v___x_3703_ = lean_string_append(v___x_3700_, v___x_3702_);
lean_dec_ref(v___x_3702_);
v___y_3637_ = v___x_3692_;
v___y_3638_ = v___x_3703_;
goto v___jp_3636_;
}
}
}
else
{
lean_object* v___x_3715_; lean_object* v___y_3717_; lean_object* v_intZero_3722_; uint8_t v_isNeg_3723_; 
lean_dec(v_val_3684_);
v___x_3715_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3722_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3723_ = lean_int_dec_lt(v_val_3683_, v_intZero_3722_);
if (v_isNeg_3723_ == 0)
{
lean_object* v_a_3724_; lean_object* v___x_3725_; 
v_a_3724_ = lean_nat_abs(v_val_3683_);
lean_dec(v_val_3683_);
v___x_3725_ = l_Nat_reprFast(v_a_3724_);
v___y_3717_ = v___x_3725_;
goto v___jp_3716_;
}
else
{
lean_object* v_abs_3726_; lean_object* v_one_3727_; lean_object* v_a_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v_abs_3726_ = lean_nat_abs(v_val_3683_);
lean_dec(v_val_3683_);
v_one_3727_ = lean_unsigned_to_nat(1u);
v_a_3728_ = lean_nat_sub(v_abs_3726_, v_one_3727_);
lean_dec(v_abs_3726_);
v___x_3729_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3730_ = lean_nat_add(v_a_3728_, v_one_3727_);
lean_dec(v_a_3728_);
v___x_3731_ = l_Nat_reprFast(v___x_3730_);
v___x_3732_ = lean_string_append(v___x_3729_, v___x_3731_);
lean_dec_ref(v___x_3731_);
v___y_3717_ = v___x_3732_;
goto v___jp_3716_;
}
v___jp_3716_:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3718_ = lean_string_append(v___x_3715_, v___y_3717_);
lean_dec_ref(v___y_3717_);
v___x_3719_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3720_ = lean_string_append(v___x_3718_, v___x_3719_);
v___x_3721_ = lean_string_append(v___x_3635_, v___x_3720_);
lean_dec_ref(v___x_3720_);
return v___x_3721_;
}
}
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_dec(v_val_3684_);
lean_dec(v_val_3683_);
v___x_3733_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3734_ = lean_string_append(v___x_3635_, v___x_3733_);
return v___x_3734_;
}
}
}
v___jp_3636_:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3639_ = lean_string_append(v___y_3637_, v___y_3638_);
lean_dec_ref(v___y_3638_);
v___x_3640_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3641_ = lean_string_append(v___x_3639_, v___x_3640_);
v___x_3642_ = lean_string_append(v___x_3635_, v___x_3641_);
lean_dec_ref(v___x_3641_);
return v___x_3642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2(lean_object* v___f_3739_, lean_object* v___f_3740_, lean_object* v___f_3741_, lean_object* v_d_3742_){
_start:
{
lean_object* v_var_3743_; lean_object* v_irrelevant_3744_; lean_object* v_lowerBounds_3745_; lean_object* v_upperBounds_3746_; lean_object* v___x_3747_; lean_object* v_irrelevant_3748_; lean_object* v_lowerBounds_3749_; lean_object* v_upperBounds_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v_var_3743_ = lean_ctor_get(v_d_3742_, 0);
lean_inc(v_var_3743_);
v_irrelevant_3744_ = lean_ctor_get(v_d_3742_, 1);
lean_inc(v_irrelevant_3744_);
v_lowerBounds_3745_ = lean_ctor_get(v_d_3742_, 2);
lean_inc(v_lowerBounds_3745_);
v_upperBounds_3746_ = lean_ctor_get(v_d_3742_, 3);
lean_inc(v_upperBounds_3746_);
lean_dec_ref(v_d_3742_);
v___x_3747_ = lean_box(0);
v_irrelevant_3748_ = l_List_mapTR_loop___redArg(v___f_3739_, v_irrelevant_3744_, v___x_3747_);
lean_inc_ref(v___f_3740_);
v_lowerBounds_3749_ = l_List_mapTR_loop___redArg(v___f_3740_, v_lowerBounds_3745_, v___x_3747_);
v_upperBounds_3750_ = l_List_mapTR_loop___redArg(v___f_3740_, v_upperBounds_3746_, v___x_3747_);
v___x_3751_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0));
v___x_3752_ = l_Nat_reprFast(v_var_3743_);
v___x_3753_ = lean_string_append(v___x_3751_, v___x_3752_);
lean_dec_ref(v___x_3752_);
v___x_3754_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_3755_ = lean_string_append(v___x_3753_, v___x_3754_);
v___x_3756_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1));
lean_inc_ref_n(v___f_3741_, 2);
v___x_3757_ = l_List_toString___redArg(v___f_3741_, v_irrelevant_3748_);
v___x_3758_ = lean_string_append(v___x_3756_, v___x_3757_);
lean_dec_ref(v___x_3757_);
v___x_3759_ = lean_string_append(v___x_3758_, v___x_3754_);
v___x_3760_ = lean_string_append(v___x_3755_, v___x_3759_);
lean_dec_ref(v___x_3759_);
v___x_3761_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2));
v___x_3762_ = l_List_toString___redArg(v___f_3741_, v_lowerBounds_3749_);
v___x_3763_ = lean_string_append(v___x_3761_, v___x_3762_);
lean_dec_ref(v___x_3762_);
v___x_3764_ = lean_string_append(v___x_3763_, v___x_3754_);
v___x_3765_ = lean_string_append(v___x_3760_, v___x_3764_);
lean_dec_ref(v___x_3764_);
v___x_3766_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3));
v___x_3767_ = l_List_toString___redArg(v___f_3741_, v_upperBounds_3750_);
v___x_3768_ = lean_string_append(v___x_3766_, v___x_3767_);
lean_dec_ref(v___x_3767_);
v___x_3769_ = lean_string_append(v___x_3765_, v___x_3768_);
lean_dec_ref(v___x_3768_);
return v___x_3769_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(lean_object* v_d_3780_){
_start:
{
lean_object* v_lowerBounds_3781_; lean_object* v_upperBounds_3782_; uint8_t v___x_3783_; 
v_lowerBounds_3781_ = lean_ctor_get(v_d_3780_, 2);
v_upperBounds_3782_ = lean_ctor_get(v_d_3780_, 3);
v___x_3783_ = l_List_isEmpty___redArg(v_lowerBounds_3781_);
if (v___x_3783_ == 0)
{
return v___x_3783_;
}
else
{
uint8_t v___x_3784_; 
v___x_3784_ = l_List_isEmpty___redArg(v_upperBounds_3782_);
return v___x_3784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty___boxed(lean_object* v_d_3785_){
_start:
{
uint8_t v_res_3786_; lean_object* v_r_3787_; 
v_res_3786_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v_d_3785_);
lean_dec_ref(v_d_3785_);
v_r_3787_ = lean_box(v_res_3786_);
return v_r_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(lean_object* v_d_3788_){
_start:
{
lean_object* v_lowerBounds_3789_; lean_object* v_upperBounds_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v_lowerBounds_3789_ = lean_ctor_get(v_d_3788_, 2);
v_upperBounds_3790_ = lean_ctor_get(v_d_3788_, 3);
v___x_3791_ = l_List_lengthTR___redArg(v_lowerBounds_3789_);
v___x_3792_ = l_List_lengthTR___redArg(v_upperBounds_3790_);
v___x_3793_ = lean_nat_mul(v___x_3791_, v___x_3792_);
lean_dec(v___x_3792_);
lean_dec(v___x_3791_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size___boxed(lean_object* v_d_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_d_3794_);
lean_dec_ref(v_d_3794_);
return v_res_3795_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(lean_object* v_d_3796_){
_start:
{
uint8_t v_lowerExact_3797_; 
v_lowerExact_3797_ = lean_ctor_get_uint8(v_d_3796_, sizeof(void*)*4);
if (v_lowerExact_3797_ == 0)
{
uint8_t v_upperExact_3798_; 
v_upperExact_3798_ = lean_ctor_get_uint8(v_d_3796_, sizeof(void*)*4 + 1);
return v_upperExact_3798_;
}
else
{
return v_lowerExact_3797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact___boxed(lean_object* v_d_3799_){
_start:
{
uint8_t v_res_3800_; lean_object* v_r_3801_; 
v_res_3800_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_d_3799_);
lean_dec_ref(v_d_3799_);
v_r_3801_ = lean_box(v_res_3800_);
return v_r_3801_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(lean_object* v_x_3802_, lean_object* v_x_3803_){
_start:
{
if (lean_obj_tag(v_x_3803_) == 0)
{
return v_x_3802_;
}
else
{
lean_object* v_head_3804_; lean_object* v_tail_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v_head_3804_ = lean_ctor_get(v_x_3803_, 0);
v_tail_3805_ = lean_ctor_get(v_x_3803_, 1);
v___x_3806_ = lean_box(0);
v___x_3807_ = 1;
lean_inc(v_head_3804_);
v___x_3808_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3808_, 0, v_head_3804_);
lean_ctor_set(v___x_3808_, 1, v___x_3806_);
lean_ctor_set(v___x_3808_, 2, v___x_3806_);
lean_ctor_set(v___x_3808_, 3, v___x_3806_);
lean_ctor_set_uint8(v___x_3808_, sizeof(void*)*4, v___x_3807_);
lean_ctor_set_uint8(v___x_3808_, sizeof(void*)*4 + 1, v___x_3807_);
v___x_3809_ = lean_array_push(v_x_3802_, v___x_3808_);
v_x_3802_ = v___x_3809_;
v_x_3803_ = v_tail_3805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2___boxed(lean_object* v_x_3811_, lean_object* v_x_3812_){
_start:
{
lean_object* v_res_3813_; 
v_res_3813_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v_x_3811_, v_x_3812_);
lean_dec(v_x_3812_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object* v___x_3814_, lean_object* v_b_3815_, lean_object* v___x_3816_, lean_object* v_____r_3817_, lean_object* v_d_x27_3818_){
_start:
{
lean_object* v_upperBound_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3846_; 
v_upperBound_3819_ = lean_ctor_get(v___x_3814_, 1);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3846_ == 0)
{
lean_object* v_unused_3847_; 
v_unused_3847_ = lean_ctor_get(v___x_3814_, 0);
lean_dec(v_unused_3847_);
v___x_3821_ = v___x_3814_;
v_isShared_3822_ = v_isSharedCheck_3846_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_upperBound_3819_);
lean_dec(v___x_3814_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3846_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
if (lean_obj_tag(v_upperBound_3819_) == 0)
{
lean_del_object(v___x_3821_);
lean_dec(v___x_3816_);
lean_dec_ref(v_b_3815_);
return v_d_x27_3818_;
}
else
{
lean_object* v_var_3823_; lean_object* v_irrelevant_3824_; lean_object* v_lowerBounds_3825_; lean_object* v_upperBounds_3826_; uint8_t v_lowerExact_3827_; uint8_t v_upperExact_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3845_; 
lean_dec_ref(v_upperBound_3819_);
v_var_3823_ = lean_ctor_get(v_d_x27_3818_, 0);
v_irrelevant_3824_ = lean_ctor_get(v_d_x27_3818_, 1);
v_lowerBounds_3825_ = lean_ctor_get(v_d_x27_3818_, 2);
v_upperBounds_3826_ = lean_ctor_get(v_d_x27_3818_, 3);
v_lowerExact_3827_ = lean_ctor_get_uint8(v_d_x27_3818_, sizeof(void*)*4);
v_upperExact_3828_ = lean_ctor_get_uint8(v_d_x27_3818_, sizeof(void*)*4 + 1);
v_isSharedCheck_3845_ = !lean_is_exclusive(v_d_x27_3818_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3830_ = v_d_x27_3818_;
v_isShared_3831_ = v_isSharedCheck_3845_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_upperBounds_3826_);
lean_inc(v_lowerBounds_3825_);
lean_inc(v_irrelevant_3824_);
lean_inc(v_var_3823_);
lean_dec(v_d_x27_3818_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3845_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
lean_inc(v___x_3816_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 1, v___x_3816_);
lean_ctor_set(v___x_3821_, 0, v_b_3815_);
v___x_3833_ = v___x_3821_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_b_3815_);
lean_ctor_set(v_reuseFailAlloc_3844_, 1, v___x_3816_);
v___x_3833_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3834_; 
v___x_3834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
lean_ctor_set(v___x_3834_, 1, v_upperBounds_3826_);
if (v_upperExact_3828_ == 0)
{
lean_object* v___x_3836_; 
lean_dec(v___x_3816_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 3, v___x_3834_);
v___x_3836_ = v___x_3830_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_var_3823_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v_irrelevant_3824_);
lean_ctor_set(v_reuseFailAlloc_3837_, 2, v_lowerBounds_3825_);
lean_ctor_set(v_reuseFailAlloc_3837_, 3, v___x_3834_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, sizeof(void*)*4, v_lowerExact_3827_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, sizeof(void*)*4 + 1, v_upperExact_3828_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
else
{
lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; lean_object* v___x_3842_; 
v___x_3838_ = lean_nat_abs(v___x_3816_);
lean_dec(v___x_3816_);
v___x_3839_ = lean_unsigned_to_nat(1u);
v___x_3840_ = lean_nat_dec_eq(v___x_3838_, v___x_3839_);
lean_dec(v___x_3838_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 3, v___x_3834_);
v___x_3842_ = v___x_3830_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_var_3823_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_irrelevant_3824_);
lean_ctor_set(v_reuseFailAlloc_3843_, 2, v_lowerBounds_3825_);
lean_ctor_set(v_reuseFailAlloc_3843_, 3, v___x_3834_);
lean_ctor_set_uint8(v_reuseFailAlloc_3843_, sizeof(void*)*4, v_lowerExact_3827_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_ctor_set_uint8(v___x_3842_, sizeof(void*)*4 + 1, v___x_3840_);
return v___x_3842_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(lean_object* v_upperBound_3848_, lean_object* v_coeffs_3849_, lean_object* v_constraint_3850_, lean_object* v_b_3851_, lean_object* v_a_3852_, lean_object* v_b_3853_){
_start:
{
lean_object* v_a_3855_; uint8_t v___x_3859_; 
v___x_3859_ = lean_nat_dec_lt(v_a_3852_, v_upperBound_3848_);
if (v___x_3859_ == 0)
{
lean_dec(v_a_3852_);
lean_dec_ref(v_b_3851_);
lean_dec_ref(v_constraint_3850_);
return v_b_3853_;
}
else
{
lean_object* v___x_3860_; uint8_t v___x_3861_; 
v___x_3860_ = lean_array_get_size(v_b_3853_);
v___x_3861_ = lean_nat_dec_lt(v_a_3852_, v___x_3860_);
if (v___x_3861_ == 0)
{
v_a_3855_ = v_b_3853_;
goto v___jp_3854_;
}
else
{
lean_object* v___x_3862_; lean_object* v_v_3863_; lean_object* v___x_3864_; lean_object* v_xs_x27_3865_; lean_object* v___y_3867_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
lean_inc(v_a_3852_);
v___x_3862_ = l_Lean_Omega_IntList_get(v_coeffs_3849_, v_a_3852_);
v_v_3863_ = lean_array_fget(v_b_3853_, v_a_3852_);
v___x_3864_ = lean_box(0);
v_xs_x27_3865_ = lean_array_fset(v_b_3853_, v_a_3852_, v___x_3864_);
v___x_3869_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3870_ = lean_int_dec_eq(v___x_3862_, v___x_3869_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; lean_object* v_lowerBound_3872_; 
lean_inc_ref(v_constraint_3850_);
lean_inc(v___x_3862_);
v___x_3871_ = l_Lean_Omega_Constraint_scale(v___x_3862_, v_constraint_3850_);
v_lowerBound_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_lowerBound_3872_);
if (lean_obj_tag(v_lowerBound_3872_) == 0)
{
lean_object* v___x_3873_; 
lean_inc_ref(v_b_3851_);
v___x_3873_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3871_, v_b_3851_, v___x_3862_, v___x_3864_, v_v_3863_);
v___y_3867_ = v___x_3873_;
goto v___jp_3866_;
}
else
{
lean_object* v_var_3874_; lean_object* v_irrelevant_3875_; lean_object* v_lowerBounds_3876_; lean_object* v_upperBounds_3877_; uint8_t v_lowerExact_3878_; uint8_t v_upperExact_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3894_; 
lean_dec_ref(v_lowerBound_3872_);
v_var_3874_ = lean_ctor_get(v_v_3863_, 0);
v_irrelevant_3875_ = lean_ctor_get(v_v_3863_, 1);
v_lowerBounds_3876_ = lean_ctor_get(v_v_3863_, 2);
v_upperBounds_3877_ = lean_ctor_get(v_v_3863_, 3);
v_lowerExact_3878_ = lean_ctor_get_uint8(v_v_3863_, sizeof(void*)*4);
v_upperExact_3879_ = lean_ctor_get_uint8(v_v_3863_, sizeof(void*)*4 + 1);
v_isSharedCheck_3894_ = !lean_is_exclusive(v_v_3863_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3881_ = v_v_3863_;
v_isShared_3882_ = v_isSharedCheck_3894_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_upperBounds_3877_);
lean_inc(v_lowerBounds_3876_);
lean_inc(v_irrelevant_3875_);
lean_inc(v_var_3874_);
lean_dec(v_v_3863_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3894_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; uint8_t v___y_3886_; 
lean_inc(v___x_3862_);
lean_inc_ref(v_b_3851_);
v___x_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3883_, 0, v_b_3851_);
lean_ctor_set(v___x_3883_, 1, v___x_3862_);
v___x_3884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
lean_ctor_set(v___x_3884_, 1, v_lowerBounds_3876_);
if (v_lowerExact_3878_ == 0)
{
v___y_3886_ = v_lowerExact_3878_;
goto v___jp_3885_;
}
else
{
lean_object* v___x_3891_; lean_object* v___x_3892_; uint8_t v___x_3893_; 
v___x_3891_ = lean_nat_abs(v___x_3862_);
v___x_3892_ = lean_unsigned_to_nat(1u);
v___x_3893_ = lean_nat_dec_eq(v___x_3891_, v___x_3892_);
lean_dec(v___x_3891_);
v___y_3886_ = v___x_3893_;
goto v___jp_3885_;
}
v___jp_3885_:
{
lean_object* v___x_3888_; 
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 2, v___x_3884_);
v___x_3888_ = v___x_3881_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_var_3874_);
lean_ctor_set(v_reuseFailAlloc_3890_, 1, v_irrelevant_3875_);
lean_ctor_set(v_reuseFailAlloc_3890_, 2, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3890_, 3, v_upperBounds_3877_);
lean_ctor_set_uint8(v_reuseFailAlloc_3890_, sizeof(void*)*4 + 1, v_upperExact_3879_);
v___x_3888_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3889_; 
lean_ctor_set_uint8(v___x_3888_, sizeof(void*)*4, v___y_3886_);
lean_inc_ref(v_b_3851_);
v___x_3889_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3871_, v_b_3851_, v___x_3862_, v___x_3864_, v___x_3888_);
v___y_3867_ = v___x_3889_;
goto v___jp_3866_;
}
}
}
}
}
else
{
lean_object* v_var_3895_; lean_object* v_irrelevant_3896_; lean_object* v_lowerBounds_3897_; lean_object* v_upperBounds_3898_; uint8_t v_lowerExact_3899_; uint8_t v_upperExact_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3908_; 
lean_dec(v___x_3862_);
v_var_3895_ = lean_ctor_get(v_v_3863_, 0);
v_irrelevant_3896_ = lean_ctor_get(v_v_3863_, 1);
v_lowerBounds_3897_ = lean_ctor_get(v_v_3863_, 2);
v_upperBounds_3898_ = lean_ctor_get(v_v_3863_, 3);
v_lowerExact_3899_ = lean_ctor_get_uint8(v_v_3863_, sizeof(void*)*4);
v_upperExact_3900_ = lean_ctor_get_uint8(v_v_3863_, sizeof(void*)*4 + 1);
v_isSharedCheck_3908_ = !lean_is_exclusive(v_v_3863_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3902_ = v_v_3863_;
v_isShared_3903_ = v_isSharedCheck_3908_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_upperBounds_3898_);
lean_inc(v_lowerBounds_3897_);
lean_inc(v_irrelevant_3896_);
lean_inc(v_var_3895_);
lean_dec(v_v_3863_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3908_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3904_; lean_object* v___x_3906_; 
lean_inc_ref(v_b_3851_);
v___x_3904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3904_, 0, v_b_3851_);
lean_ctor_set(v___x_3904_, 1, v_irrelevant_3896_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 1, v___x_3904_);
v___x_3906_ = v___x_3902_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_var_3895_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3907_, 2, v_lowerBounds_3897_);
lean_ctor_set(v_reuseFailAlloc_3907_, 3, v_upperBounds_3898_);
lean_ctor_set_uint8(v_reuseFailAlloc_3907_, sizeof(void*)*4, v_lowerExact_3899_);
lean_ctor_set_uint8(v_reuseFailAlloc_3907_, sizeof(void*)*4 + 1, v_upperExact_3900_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
v___y_3867_ = v___x_3906_;
goto v___jp_3866_;
}
}
}
v___jp_3866_:
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_array_fset(v_xs_x27_3865_, v_a_3852_, v___y_3867_);
v_a_3855_ = v___x_3868_;
goto v___jp_3854_;
}
}
}
v___jp_3854_:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3856_ = lean_unsigned_to_nat(1u);
v___x_3857_ = lean_nat_add(v_a_3852_, v___x_3856_);
lean_dec(v_a_3852_);
v_a_3852_ = v___x_3857_;
v_b_3853_ = v_a_3855_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___boxed(lean_object* v_upperBound_3909_, lean_object* v_coeffs_3910_, lean_object* v_constraint_3911_, lean_object* v_b_3912_, lean_object* v_a_3913_, lean_object* v_b_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3909_, v_coeffs_3910_, v_constraint_3911_, v_b_3912_, v_a_3913_, v_b_3914_);
lean_dec(v_coeffs_3910_);
lean_dec(v_upperBound_3909_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(lean_object* v_n_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_){
_start:
{
if (lean_obj_tag(v_a_3917_) == 0)
{
lean_object* v___x_3919_; 
v___x_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3919_, 0, v_a_3918_);
return v___x_3919_;
}
else
{
lean_object* v_value_3920_; lean_object* v_tail_3921_; lean_object* v_coeffs_3922_; lean_object* v_constraint_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v_value_3920_ = lean_ctor_get(v_a_3917_, 1);
lean_inc(v_value_3920_);
v_tail_3921_ = lean_ctor_get(v_a_3917_, 2);
lean_inc(v_tail_3921_);
lean_dec_ref(v_a_3917_);
v_coeffs_3922_ = lean_ctor_get(v_value_3920_, 0);
lean_inc(v_coeffs_3922_);
v_constraint_3923_ = lean_ctor_get(v_value_3920_, 1);
lean_inc_ref(v_constraint_3923_);
v___x_3924_ = lean_unsigned_to_nat(0u);
v___x_3925_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_n_3916_, v_coeffs_3922_, v_constraint_3923_, v_value_3920_, v___x_3924_, v_a_3918_);
lean_dec(v_coeffs_3922_);
v_a_3917_ = v_tail_3921_;
v_a_3918_ = v___x_3925_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1___boxed(lean_object* v_n_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3927_, v_a_3928_, v_a_3929_);
lean_dec(v_n_3927_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(lean_object* v_n_3931_, lean_object* v_as_3932_, size_t v_sz_3933_, size_t v_i_3934_, lean_object* v_b_3935_){
_start:
{
uint8_t v___x_3936_; 
v___x_3936_ = lean_usize_dec_lt(v_i_3934_, v_sz_3933_);
if (v___x_3936_ == 0)
{
return v_b_3935_;
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3938_; 
v_a_3937_ = lean_array_uget_borrowed(v_as_3932_, v_i_3934_);
lean_inc(v_a_3937_);
v___x_3938_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3931_, v_a_3937_, v_b_3935_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_a_3939_);
lean_dec_ref(v___x_3938_);
return v_a_3939_;
}
else
{
lean_object* v_a_3940_; size_t v___x_3941_; size_t v___x_3942_; 
v_a_3940_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_a_3940_);
lean_dec_ref(v___x_3938_);
v___x_3941_ = ((size_t)1ULL);
v___x_3942_ = lean_usize_add(v_i_3934_, v___x_3941_);
v_i_3934_ = v___x_3942_;
v_b_3935_ = v_a_3940_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3___boxed(lean_object* v_n_3944_, lean_object* v_as_3945_, lean_object* v_sz_3946_, lean_object* v_i_3947_, lean_object* v_b_3948_){
_start:
{
size_t v_sz_boxed_3949_; size_t v_i_boxed_3950_; lean_object* v_res_3951_; 
v_sz_boxed_3949_ = lean_unbox_usize(v_sz_3946_);
lean_dec(v_sz_3946_);
v_i_boxed_3950_ = lean_unbox_usize(v_i_3947_);
lean_dec(v_i_3947_);
v_res_3951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_n_3944_, v_as_3945_, v_sz_boxed_3949_, v_i_boxed_3950_, v_b_3948_);
lean_dec_ref(v_as_3945_);
lean_dec(v_n_3944_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(lean_object* v_p_3954_){
_start:
{
lean_object* v_constraints_3955_; lean_object* v_numVars_3956_; lean_object* v_buckets_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v_data_3960_; size_t v_sz_3961_; size_t v___x_3962_; lean_object* v___x_3963_; 
v_constraints_3955_ = lean_ctor_get(v_p_3954_, 2);
lean_inc_ref(v_constraints_3955_);
v_numVars_3956_ = lean_ctor_get(v_p_3954_, 1);
lean_inc_n(v_numVars_3956_, 2);
lean_dec_ref(v_p_3954_);
v_buckets_3957_ = lean_ctor_get(v_constraints_3955_, 1);
lean_inc_ref(v_buckets_3957_);
lean_dec_ref(v_constraints_3955_);
v___x_3958_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_3959_ = l_List_range(v_numVars_3956_);
v_data_3960_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v___x_3958_, v___x_3959_);
lean_dec(v___x_3959_);
v_sz_3961_ = lean_array_size(v_buckets_3957_);
v___x_3962_ = ((size_t)0ULL);
v___x_3963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_numVars_3956_, v_buckets_3957_, v_sz_3961_, v___x_3962_, v_data_3960_);
lean_dec_ref(v_buckets_3957_);
lean_dec(v_numVars_3956_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(lean_object* v_upperBound_3964_, lean_object* v_coeffs_3965_, lean_object* v_constraint_3966_, lean_object* v_b_3967_, lean_object* v_inst_3968_, lean_object* v_R_3969_, lean_object* v_a_3970_, lean_object* v_b_3971_, lean_object* v_c_3972_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3964_, v_coeffs_3965_, v_constraint_3966_, v_b_3967_, v_a_3970_, v_b_3971_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___boxed(lean_object* v_upperBound_3974_, lean_object* v_coeffs_3975_, lean_object* v_constraint_3976_, lean_object* v_b_3977_, lean_object* v_inst_3978_, lean_object* v_R_3979_, lean_object* v_a_3980_, lean_object* v_b_3981_, lean_object* v_c_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(v_upperBound_3974_, v_coeffs_3975_, v_constraint_3976_, v_b_3977_, v_inst_3978_, v_R_3979_, v_a_3980_, v_b_3981_, v_c_3982_);
lean_dec(v_coeffs_3975_);
lean_dec(v_upperBound_3974_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(lean_object* v_cls_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v_options_3993_; uint8_t v_hasTrace_3994_; 
v_options_3993_ = lean_ctor_get(v___y_3990_, 2);
v_hasTrace_3994_ = lean_ctor_get_uint8(v_options_3993_, sizeof(void*)*1);
if (v_hasTrace_3994_ == 0)
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
lean_dec(v_cls_3987_);
v___x_3995_ = lean_box(v_hasTrace_3994_);
v___x_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
return v___x_3996_;
}
else
{
lean_object* v_inheritedTraceOptions_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; uint8_t v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v_inheritedTraceOptions_3997_ = lean_ctor_get(v___y_3990_, 13);
v___x_3998_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_3999_ = l_Lean_Name_append(v___x_3998_, v_cls_3987_);
v___x_4000_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3997_, v_options_3993_, v___x_3999_);
lean_dec(v___x_3999_);
v___x_4001_ = lean_box(v___x_4000_);
v___x_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
return v___x_4002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___boxed(lean_object* v_cls_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(lean_object* v___x_4010_, lean_object* v_fst_4011_, lean_object* v_snd_4012_, lean_object* v_fst_4013_, lean_object* v_____r_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4010_);
v___x_4021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4021_, 0, v_fst_4011_);
lean_ctor_set(v___x_4021_, 1, v_snd_4012_);
v___x_4022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4022_, 0, v_fst_4013_);
lean_ctor_set(v___x_4022_, 1, v___x_4021_);
v___x_4023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4020_);
lean_ctor_set(v___x_4023_, 1, v___x_4022_);
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
v___x_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0___boxed(lean_object* v___x_4026_, lean_object* v_fst_4027_, lean_object* v_snd_4028_, lean_object* v_fst_4029_, lean_object* v_____r_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4026_, v_fst_4027_, v_snd_4028_, v_fst_4029_, v_____r_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
return v_res_4036_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4037_; double v___x_4038_; 
v___x_4037_ = lean_unsigned_to_nat(0u);
v___x_4038_ = lean_float_of_nat(v___x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(lean_object* v_cls_4041_, lean_object* v_msg_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v_ref_4048_; lean_object* v___x_4049_; lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4094_; 
v_ref_4048_ = lean_ctor_get(v___y_4045_, 5);
v___x_4049_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4052_ = v___x_4049_;
v_isShared_4053_ = v_isSharedCheck_4094_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4049_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4094_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4054_; lean_object* v_traceState_4055_; lean_object* v_env_4056_; lean_object* v_nextMacroScope_4057_; lean_object* v_ngen_4058_; lean_object* v_auxDeclNGen_4059_; lean_object* v_cache_4060_; lean_object* v_messages_4061_; lean_object* v_infoState_4062_; lean_object* v_snapshotTasks_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4093_; 
v___x_4054_ = lean_st_ref_take(v___y_4046_);
v_traceState_4055_ = lean_ctor_get(v___x_4054_, 4);
v_env_4056_ = lean_ctor_get(v___x_4054_, 0);
v_nextMacroScope_4057_ = lean_ctor_get(v___x_4054_, 1);
v_ngen_4058_ = lean_ctor_get(v___x_4054_, 2);
v_auxDeclNGen_4059_ = lean_ctor_get(v___x_4054_, 3);
v_cache_4060_ = lean_ctor_get(v___x_4054_, 5);
v_messages_4061_ = lean_ctor_get(v___x_4054_, 6);
v_infoState_4062_ = lean_ctor_get(v___x_4054_, 7);
v_snapshotTasks_4063_ = lean_ctor_get(v___x_4054_, 8);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4065_ = v___x_4054_;
v_isShared_4066_ = v_isSharedCheck_4093_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_snapshotTasks_4063_);
lean_inc(v_infoState_4062_);
lean_inc(v_messages_4061_);
lean_inc(v_cache_4060_);
lean_inc(v_traceState_4055_);
lean_inc(v_auxDeclNGen_4059_);
lean_inc(v_ngen_4058_);
lean_inc(v_nextMacroScope_4057_);
lean_inc(v_env_4056_);
lean_dec(v___x_4054_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4093_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
uint64_t v_tid_4067_; lean_object* v_traces_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4092_; 
v_tid_4067_ = lean_ctor_get_uint64(v_traceState_4055_, sizeof(void*)*1);
v_traces_4068_ = lean_ctor_get(v_traceState_4055_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_traceState_4055_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4070_ = v_traceState_4055_;
v_isShared_4071_ = v_isSharedCheck_4092_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_traces_4068_);
lean_dec(v_traceState_4055_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4092_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4072_; double v___x_4073_; uint8_t v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4082_; 
v___x_4072_ = lean_box(0);
v___x_4073_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4074_ = 0;
v___x_4075_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4076_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4076_, 0, v_cls_4041_);
lean_ctor_set(v___x_4076_, 1, v___x_4072_);
lean_ctor_set(v___x_4076_, 2, v___x_4075_);
lean_ctor_set_float(v___x_4076_, sizeof(void*)*3, v___x_4073_);
lean_ctor_set_float(v___x_4076_, sizeof(void*)*3 + 8, v___x_4073_);
lean_ctor_set_uint8(v___x_4076_, sizeof(void*)*3 + 16, v___x_4074_);
v___x_4077_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4078_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4076_);
lean_ctor_set(v___x_4078_, 1, v_a_4050_);
lean_ctor_set(v___x_4078_, 2, v___x_4077_);
lean_inc(v_ref_4048_);
v___x_4079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4079_, 0, v_ref_4048_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
v___x_4080_ = l_Lean_PersistentArray_push___redArg(v_traces_4068_, v___x_4079_);
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 0, v___x_4080_);
v___x_4082_ = v___x_4070_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4080_);
lean_ctor_set_uint64(v_reuseFailAlloc_4091_, sizeof(void*)*1, v_tid_4067_);
v___x_4082_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
lean_object* v___x_4084_; 
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 4, v___x_4082_);
v___x_4084_ = v___x_4065_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_env_4056_);
lean_ctor_set(v_reuseFailAlloc_4090_, 1, v_nextMacroScope_4057_);
lean_ctor_set(v_reuseFailAlloc_4090_, 2, v_ngen_4058_);
lean_ctor_set(v_reuseFailAlloc_4090_, 3, v_auxDeclNGen_4059_);
lean_ctor_set(v_reuseFailAlloc_4090_, 4, v___x_4082_);
lean_ctor_set(v_reuseFailAlloc_4090_, 5, v_cache_4060_);
lean_ctor_set(v_reuseFailAlloc_4090_, 6, v_messages_4061_);
lean_ctor_set(v_reuseFailAlloc_4090_, 7, v_infoState_4062_);
lean_ctor_set(v_reuseFailAlloc_4090_, 8, v_snapshotTasks_4063_);
v___x_4084_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4088_; 
v___x_4085_ = lean_st_ref_set(v___y_4046_, v___x_4084_);
v___x_4086_ = lean_box(0);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v___x_4086_);
v___x_4088_ = v___x_4052_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4086_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___boxed(lean_object* v_cls_4095_, lean_object* v_msg_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4095_, v_msg_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
return v_res_4102_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v_cls_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v_cls_4103_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4104_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4105_ = l_Lean_Name_append(v___x_4104_, v_cls_4103_);
return v___x_4105_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4107_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__1));
v___x_4108_ = l_Lean_stringToMessageData(v___x_4107_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(lean_object* v_upperBound_4109_, lean_object* v___y_4110_, lean_object* v_a_4111_, lean_object* v_b_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
lean_object* v_a_4119_; lean_object* v___y_4124_; uint8_t v___x_4143_; 
v___x_4143_ = lean_nat_dec_lt(v_a_4111_, v_upperBound_4109_);
if (v___x_4143_ == 0)
{
lean_object* v___x_4144_; 
lean_dec(v_a_4111_);
v___x_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4144_, 0, v_b_4112_);
return v___x_4144_;
}
else
{
lean_object* v_snd_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4215_; 
v_snd_4145_ = lean_ctor_get(v_b_4112_, 1);
v_isSharedCheck_4215_ = !lean_is_exclusive(v_b_4112_);
if (v_isSharedCheck_4215_ == 0)
{
lean_object* v_unused_4216_; 
v_unused_4216_ = lean_ctor_get(v_b_4112_, 0);
lean_dec(v_unused_4216_);
v___x_4147_ = v_b_4112_;
v_isShared_4148_ = v_isSharedCheck_4215_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_snd_4145_);
lean_dec(v_b_4112_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4215_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v_snd_4149_; lean_object* v_fst_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4214_; 
v_snd_4149_ = lean_ctor_get(v_snd_4145_, 1);
v_fst_4150_ = lean_ctor_get(v_snd_4145_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v_snd_4145_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4152_ = v_snd_4145_;
v_isShared_4153_ = v_isSharedCheck_4214_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_snd_4149_);
lean_inc(v_fst_4150_);
lean_dec(v_snd_4145_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4214_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v_fst_4154_; lean_object* v_snd_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4213_; 
v_fst_4154_ = lean_ctor_get(v_snd_4149_, 0);
v_snd_4155_ = lean_ctor_get(v_snd_4149_, 1);
v_isSharedCheck_4213_ = !lean_is_exclusive(v_snd_4149_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4157_ = v_snd_4149_;
v_isShared_4158_ = v_isSharedCheck_4213_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_snd_4155_);
lean_inc(v_fst_4154_);
lean_dec(v_snd_4149_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4213_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v_bestIdx_4159_; lean_object* v___x_4160_; lean_object* v_cls_4171_; lean_object* v___x_4172_; uint8_t v___x_4176_; lean_object* v___x_4177_; uint8_t v___x_4178_; uint8_t v___y_4207_; uint8_t v___y_4210_; 
v_bestIdx_4159_ = lean_unsigned_to_nat(0u);
v___x_4160_ = lean_box(0);
v_cls_4171_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4172_ = lean_array_fget_borrowed(v___y_4110_, v_a_4111_);
v___x_4176_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4172_);
v___x_4177_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4172_);
v___x_4178_ = lean_nat_dec_eq(v___x_4177_, v_bestIdx_4159_);
if (v___x_4178_ == 0)
{
uint8_t v___x_4212_; 
v___x_4212_ = lean_unbox(v_snd_4155_);
if (v___x_4212_ == 0)
{
v___y_4210_ = v___x_4176_;
goto v___jp_4209_;
}
else
{
if (v___x_4178_ == 0)
{
v___y_4210_ = v___x_4178_;
goto v___jp_4209_;
}
else
{
v___y_4210_ = v___x_4176_;
goto v___jp_4209_;
}
}
}
else
{
v___y_4210_ = v___x_4178_;
goto v___jp_4209_;
}
v___jp_4161_:
{
lean_object* v___x_4163_; 
if (v_isShared_4158_ == 0)
{
v___x_4163_ = v___x_4157_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_fst_4154_);
lean_ctor_set(v_reuseFailAlloc_4170_, 1, v_snd_4155_);
v___x_4163_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
lean_object* v___x_4165_; 
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 1, v___x_4163_);
v___x_4165_ = v___x_4152_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_fst_4150_);
lean_ctor_set(v_reuseFailAlloc_4169_, 1, v___x_4163_);
v___x_4165_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
lean_object* v___x_4167_; 
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 1, v___x_4165_);
lean_ctor_set(v___x_4147_, 0, v___x_4160_);
v___x_4167_ = v___x_4147_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4160_);
lean_ctor_set(v_reuseFailAlloc_4168_, 1, v___x_4165_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
v_a_4119_ = v___x_4167_;
goto v___jp_4118_;
}
}
}
}
v___jp_4173_:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4174_ = lean_box(0);
lean_inc(v___x_4172_);
v___x_4175_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4172_, v_fst_4154_, v_snd_4155_, v_fst_4150_, v___x_4174_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
v___y_4124_ = v___x_4175_;
goto v___jp_4123_;
}
v___jp_4179_:
{
if (v___x_4178_ == 0)
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
lean_dec(v_snd_4155_);
lean_dec(v_fst_4154_);
lean_dec(v_fst_4150_);
v___x_4180_ = lean_box(v___x_4176_);
v___x_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4177_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
lean_inc(v_a_4111_);
v___x_4182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4182_, 0, v_a_4111_);
lean_ctor_set(v___x_4182_, 1, v___x_4181_);
v___x_4183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4160_);
lean_ctor_set(v___x_4183_, 1, v___x_4182_);
v_a_4119_ = v___x_4183_;
goto v___jp_4118_;
}
else
{
lean_object* v_options_4184_; uint8_t v_hasTrace_4185_; 
lean_dec(v___x_4177_);
v_options_4184_ = lean_ctor_get(v___y_4115_, 2);
v_hasTrace_4185_ = lean_ctor_get_uint8(v_options_4184_, sizeof(void*)*1);
if (v_hasTrace_4185_ == 0)
{
goto v___jp_4173_;
}
else
{
lean_object* v_inheritedTraceOptions_4186_; lean_object* v___x_4187_; uint8_t v___x_4188_; 
v_inheritedTraceOptions_4186_ = lean_ctor_get(v___y_4115_, 13);
v___x_4187_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_4188_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4186_, v_options_4184_, v___x_4187_);
if (v___x_4188_ == 0)
{
goto v___jp_4173_;
}
else
{
lean_object* v_var_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v_var_4189_ = lean_ctor_get(v___x_4172_, 0);
v___x_4190_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4189_);
v___x_4191_ = l_Nat_reprFast(v_var_4189_);
v___x_4192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
v___x_4193_ = l_Lean_MessageData_ofFormat(v___x_4192_);
v___x_4194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4190_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
v___x_4195_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4171_, v___x_4194_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4197_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4196_);
lean_dec_ref(v___x_4195_);
lean_inc(v___x_4172_);
v___x_4197_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4172_, v_fst_4154_, v_snd_4155_, v_fst_4150_, v_a_4196_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
v___y_4124_ = v___x_4197_;
goto v___jp_4123_;
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_dec(v_snd_4155_);
lean_dec(v_fst_4154_);
lean_dec(v_fst_4150_);
lean_dec(v_a_4111_);
v_a_4198_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4195_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4195_);
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
}
v___jp_4206_:
{
if (v___y_4207_ == 0)
{
lean_dec(v___x_4177_);
goto v___jp_4161_;
}
else
{
uint8_t v___x_4208_; 
v___x_4208_ = lean_nat_dec_lt(v___x_4177_, v_fst_4154_);
if (v___x_4208_ == 0)
{
lean_dec(v___x_4177_);
goto v___jp_4161_;
}
else
{
lean_del_object(v___x_4157_);
lean_del_object(v___x_4152_);
lean_del_object(v___x_4147_);
goto v___jp_4179_;
}
}
}
v___jp_4209_:
{
if (v___y_4210_ == 0)
{
uint8_t v___x_4211_; 
v___x_4211_ = lean_unbox(v_snd_4155_);
if (v___x_4211_ == 0)
{
if (v___x_4176_ == 0)
{
v___y_4207_ = v___x_4143_;
goto v___jp_4206_;
}
else
{
lean_dec(v___x_4177_);
goto v___jp_4161_;
}
}
else
{
v___y_4207_ = v___x_4176_;
goto v___jp_4206_;
}
}
else
{
lean_del_object(v___x_4157_);
lean_del_object(v___x_4152_);
lean_del_object(v___x_4147_);
goto v___jp_4179_;
}
}
}
}
}
}
v___jp_4118_:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4120_ = lean_unsigned_to_nat(1u);
v___x_4121_ = lean_nat_add(v_a_4111_, v___x_4120_);
lean_dec(v_a_4111_);
v_a_4111_ = v___x_4121_;
v_b_4112_ = v_a_4119_;
goto _start;
}
v___jp_4123_:
{
if (lean_obj_tag(v___y_4124_) == 0)
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4134_; 
v_a_4125_ = lean_ctor_get(v___y_4124_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___y_4124_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4127_ = v___y_4124_;
v_isShared_4128_ = v_isSharedCheck_4134_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___y_4124_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4134_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
if (lean_obj_tag(v_a_4125_) == 0)
{
lean_object* v_a_4129_; lean_object* v___x_4131_; 
lean_dec(v_a_4111_);
v_a_4129_ = lean_ctor_get(v_a_4125_, 0);
lean_inc(v_a_4129_);
lean_dec_ref(v_a_4125_);
if (v_isShared_4128_ == 0)
{
lean_ctor_set(v___x_4127_, 0, v_a_4129_);
v___x_4131_ = v___x_4127_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4129_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
else
{
lean_object* v_a_4133_; 
lean_del_object(v___x_4127_);
v_a_4133_ = lean_ctor_get(v_a_4125_, 0);
lean_inc(v_a_4133_);
lean_dec_ref(v_a_4125_);
v_a_4119_ = v_a_4133_;
goto v___jp_4118_;
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec(v_a_4111_);
v_a_4135_ = lean_ctor_get(v___y_4124_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___y_4124_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___y_4124_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___y_4124_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___boxed(lean_object* v_upperBound_4217_, lean_object* v___y_4218_, lean_object* v_a_4219_, lean_object* v_b_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4217_, v___y_4218_, v_a_4219_, v_b_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec_ref(v___y_4218_);
lean_dec(v_upperBound_4217_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(lean_object* v_as_4227_, size_t v_i_4228_, size_t v_stop_4229_, lean_object* v_b_4230_){
_start:
{
lean_object* v___y_4232_; uint8_t v___x_4236_; 
v___x_4236_ = lean_usize_dec_eq(v_i_4228_, v_stop_4229_);
if (v___x_4236_ == 0)
{
lean_object* v___x_4237_; uint8_t v___x_4240_; 
v___x_4237_ = lean_array_uget_borrowed(v_as_4227_, v_i_4228_);
v___x_4240_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v___x_4237_);
if (v___x_4240_ == 0)
{
goto v___jp_4238_;
}
else
{
if (v___x_4236_ == 0)
{
v___y_4232_ = v_b_4230_;
goto v___jp_4231_;
}
else
{
goto v___jp_4238_;
}
}
v___jp_4238_:
{
lean_object* v___x_4239_; 
lean_inc(v___x_4237_);
v___x_4239_ = lean_array_push(v_b_4230_, v___x_4237_);
v___y_4232_ = v___x_4239_;
goto v___jp_4231_;
}
}
else
{
return v_b_4230_;
}
v___jp_4231_:
{
size_t v___x_4233_; size_t v___x_4234_; 
v___x_4233_ = ((size_t)1ULL);
v___x_4234_ = lean_usize_add(v_i_4228_, v___x_4233_);
v_i_4228_ = v___x_4234_;
v_b_4230_ = v___y_4232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___boxed(lean_object* v_as_4241_, lean_object* v_i_4242_, lean_object* v_stop_4243_, lean_object* v_b_4244_){
_start:
{
size_t v_i_boxed_4245_; size_t v_stop_boxed_4246_; lean_object* v_res_4247_; 
v_i_boxed_4245_ = lean_unbox_usize(v_i_4242_);
lean_dec(v_i_4242_);
v_stop_boxed_4246_ = lean_unbox_usize(v_stop_4243_);
lean_dec(v_stop_4243_);
v_res_4247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_as_4241_, v_i_boxed_4245_, v_stop_boxed_4246_, v_b_4244_);
lean_dec_ref(v_as_4241_);
return v_res_4247_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2(void){
_start:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4251_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__1));
v___x_4252_ = l_Lean_MessageData_ofFormat(v___x_4251_);
return v___x_4252_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4253_ = lean_box(1);
v___x_4254_ = l_Lean_MessageData_ofFormat(v___x_4253_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(lean_object* v_a_4256_, lean_object* v_a_4257_){
_start:
{
if (lean_obj_tag(v_a_4256_) == 0)
{
lean_object* v___x_4258_; 
v___x_4258_ = l_List_reverse___redArg(v_a_4257_);
return v___x_4258_;
}
else
{
lean_object* v_head_4259_; lean_object* v_snd_4260_; lean_object* v_tail_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4308_; 
v_head_4259_ = lean_ctor_get(v_a_4256_, 0);
lean_inc(v_head_4259_);
v_snd_4260_ = lean_ctor_get(v_head_4259_, 1);
lean_inc(v_snd_4260_);
v_tail_4261_ = lean_ctor_get(v_a_4256_, 1);
v_isSharedCheck_4308_ = !lean_is_exclusive(v_a_4256_);
if (v_isSharedCheck_4308_ == 0)
{
lean_object* v_unused_4309_; 
v_unused_4309_ = lean_ctor_get(v_a_4256_, 0);
lean_dec(v_unused_4309_);
v___x_4263_ = v_a_4256_;
v_isShared_4264_ = v_isSharedCheck_4308_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_tail_4261_);
lean_dec(v_a_4256_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4308_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v_fst_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4306_; 
v_fst_4265_ = lean_ctor_get(v_head_4259_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v_head_4259_);
if (v_isSharedCheck_4306_ == 0)
{
lean_object* v_unused_4307_; 
v_unused_4307_ = lean_ctor_get(v_head_4259_, 1);
lean_dec(v_unused_4307_);
v___x_4267_ = v_head_4259_;
v_isShared_4268_ = v_isSharedCheck_4306_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_fst_4265_);
lean_dec(v_head_4259_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4306_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v_fst_4269_; lean_object* v_snd_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4305_; 
v_fst_4269_ = lean_ctor_get(v_snd_4260_, 0);
v_snd_4270_ = lean_ctor_get(v_snd_4260_, 1);
v_isSharedCheck_4305_ = !lean_is_exclusive(v_snd_4260_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4272_ = v_snd_4260_;
v_isShared_4273_ = v_isSharedCheck_4305_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_snd_4270_);
lean_inc(v_fst_4269_);
lean_dec(v_snd_4260_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4305_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4279_; 
v___x_4274_ = l_Nat_reprFast(v_fst_4265_);
v___x_4275_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
v___x_4276_ = l_Lean_MessageData_ofFormat(v___x_4275_);
v___x_4277_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2);
if (v_isShared_4273_ == 0)
{
lean_ctor_set_tag(v___x_4272_, 7);
lean_ctor_set(v___x_4272_, 1, v___x_4277_);
lean_ctor_set(v___x_4272_, 0, v___x_4276_);
v___x_4279_ = v___x_4272_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v___x_4276_);
lean_ctor_set(v_reuseFailAlloc_4304_, 1, v___x_4277_);
v___x_4279_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
lean_object* v___x_4280_; lean_object* v___x_4282_; 
v___x_4280_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3);
if (v_isShared_4268_ == 0)
{
lean_ctor_set_tag(v___x_4267_, 7);
lean_ctor_set(v___x_4267_, 1, v___x_4280_);
lean_ctor_set(v___x_4267_, 0, v___x_4279_);
v___x_4282_ = v___x_4267_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v___x_4279_);
lean_ctor_set(v_reuseFailAlloc_4303_, 1, v___x_4280_);
v___x_4282_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___y_4289_; uint8_t v___x_4300_; 
v___x_4283_ = l_Nat_reprFast(v_fst_4269_);
v___x_4284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4284_, 0, v___x_4283_);
v___x_4285_ = l_Lean_MessageData_ofFormat(v___x_4284_);
v___x_4286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4285_);
lean_ctor_set(v___x_4286_, 1, v___x_4277_);
v___x_4287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
lean_ctor_set(v___x_4287_, 1, v___x_4280_);
v___x_4300_ = lean_unbox(v_snd_4270_);
lean_dec(v_snd_4270_);
if (v___x_4300_ == 0)
{
lean_object* v___x_4301_; 
v___x_4301_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__4));
v___y_4289_ = v___x_4301_;
goto v___jp_4288_;
}
else
{
lean_object* v___x_4302_; 
v___x_4302_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4));
v___y_4289_ = v___x_4302_;
goto v___jp_4288_;
}
v___jp_4288_:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4297_; 
lean_inc_ref(v___y_4289_);
v___x_4290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4290_, 0, v___y_4289_);
v___x_4291_ = l_Lean_MessageData_ofFormat(v___x_4290_);
v___x_4292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4287_);
lean_ctor_set(v___x_4292_, 1, v___x_4291_);
v___x_4293_ = l_Lean_MessageData_paren(v___x_4292_);
v___x_4294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4282_);
lean_ctor_set(v___x_4294_, 1, v___x_4293_);
v___x_4295_ = l_Lean_MessageData_paren(v___x_4294_);
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 1, v_a_4257_);
lean_ctor_set(v___x_4263_, 0, v___x_4295_);
v___x_4297_ = v___x_4263_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v___x_4295_);
lean_ctor_set(v_reuseFailAlloc_4299_, 1, v_a_4257_);
v___x_4297_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
v_a_4256_ = v_tail_4261_;
v_a_4257_ = v___x_4297_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(size_t v_sz_4310_, size_t v_i_4311_, lean_object* v_bs_4312_){
_start:
{
uint8_t v___x_4313_; 
v___x_4313_ = lean_usize_dec_lt(v_i_4311_, v_sz_4310_);
if (v___x_4313_ == 0)
{
return v_bs_4312_;
}
else
{
lean_object* v_v_4314_; lean_object* v_var_4315_; lean_object* v___x_4316_; lean_object* v_bs_x27_4317_; lean_object* v___x_4318_; uint8_t v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; size_t v___x_4323_; size_t v___x_4324_; lean_object* v___x_4325_; 
v_v_4314_ = lean_array_uget(v_bs_4312_, v_i_4311_);
v_var_4315_ = lean_ctor_get(v_v_4314_, 0);
lean_inc(v_var_4315_);
v___x_4316_ = lean_unsigned_to_nat(0u);
v_bs_x27_4317_ = lean_array_uset(v_bs_4312_, v_i_4311_, v___x_4316_);
v___x_4318_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_v_4314_);
v___x_4319_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_v_4314_);
lean_dec(v_v_4314_);
v___x_4320_ = lean_box(v___x_4319_);
v___x_4321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4318_);
lean_ctor_set(v___x_4321_, 1, v___x_4320_);
v___x_4322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4322_, 0, v_var_4315_);
lean_ctor_set(v___x_4322_, 1, v___x_4321_);
v___x_4323_ = ((size_t)1ULL);
v___x_4324_ = lean_usize_add(v_i_4311_, v___x_4323_);
v___x_4325_ = lean_array_uset(v_bs_x27_4317_, v_i_4311_, v___x_4322_);
v_i_4311_ = v___x_4324_;
v_bs_4312_ = v___x_4325_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___boxed(lean_object* v_sz_4327_, lean_object* v_i_4328_, lean_object* v_bs_4329_){
_start:
{
size_t v_sz_boxed_4330_; size_t v_i_boxed_4331_; lean_object* v_res_4332_; 
v_sz_boxed_4330_ = lean_unbox_usize(v_sz_4327_);
lean_dec(v_sz_4327_);
v_i_boxed_4331_ = lean_unbox_usize(v_i_4328_);
lean_dec(v_i_4328_);
v_res_4332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_boxed_4330_, v_i_boxed_4331_, v_bs_4329_);
return v_res_4332_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1(void){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4334_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0));
v___x_4335_ = l_Lean_stringToMessageData(v___x_4334_);
return v___x_4335_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4(void){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4339_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3));
v___x_4340_ = l_Lean_stringToMessageData(v___x_4339_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(lean_object* v_data_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v___x_4347_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v_bestIdx_4353_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4482_; lean_object* v___x_4506_; lean_object* v___x_4507_; uint8_t v___x_4508_; 
v___x_4347_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default));
v_bestIdx_4353_ = lean_unsigned_to_nat(0u);
v___x_4506_ = lean_array_get_size(v_data_4341_);
v___x_4507_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_4508_ = lean_nat_dec_lt(v_bestIdx_4353_, v___x_4506_);
if (v___x_4508_ == 0)
{
v___y_4482_ = v___x_4507_;
goto v___jp_4481_;
}
else
{
uint8_t v___x_4509_; 
v___x_4509_ = lean_nat_dec_le(v___x_4506_, v___x_4506_);
if (v___x_4509_ == 0)
{
if (v___x_4508_ == 0)
{
v___y_4482_ = v___x_4507_;
goto v___jp_4481_;
}
else
{
size_t v___x_4510_; size_t v___x_4511_; lean_object* v___x_4512_; 
v___x_4510_ = ((size_t)0ULL);
v___x_4511_ = lean_usize_of_nat(v___x_4506_);
v___x_4512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4341_, v___x_4510_, v___x_4511_, v___x_4507_);
v___y_4482_ = v___x_4512_;
goto v___jp_4481_;
}
}
else
{
size_t v___x_4513_; size_t v___x_4514_; lean_object* v___x_4515_; 
v___x_4513_ = ((size_t)0ULL);
v___x_4514_ = lean_usize_of_nat(v___x_4506_);
v___x_4515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4341_, v___x_4513_, v___x_4514_, v___x_4507_);
v___y_4482_ = v___x_4515_;
goto v___jp_4481_;
}
}
v___jp_4348_:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4351_ = lean_array_get(v___x_4347_, v___y_4350_, v___y_4349_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4350_);
v___x_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4351_);
return v___x_4352_;
}
v___jp_4354_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; uint8_t v___x_4364_; 
v___x_4362_ = lean_array_get_borrowed(v___x_4347_, v___y_4356_, v_bestIdx_4353_);
v___x_4363_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4362_);
v___x_4364_ = lean_nat_dec_eq(v___x_4363_, v_bestIdx_4353_);
if (v___x_4364_ == 0)
{
lean_object* v___x_4365_; lean_object* v___x_4366_; uint8_t v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4365_ = lean_unsigned_to_nat(1u);
v___x_4366_ = lean_array_get_size(v___y_4356_);
v___x_4367_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4362_);
v___x_4368_ = lean_box(0);
v___x_4369_ = lean_box(v___x_4367_);
v___x_4370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4363_);
lean_ctor_set(v___x_4370_, 1, v___x_4369_);
v___x_4371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4371_, 0, v_bestIdx_4353_);
lean_ctor_set(v___x_4371_, 1, v___x_4370_);
v___x_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4368_);
lean_ctor_set(v___x_4372_, 1, v___x_4371_);
v___x_4373_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v___x_4366_, v___y_4356_, v___x_4365_, v___x_4372_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4429_; 
v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4376_ = v___x_4373_;
v_isShared_4377_ = v_isSharedCheck_4429_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4373_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4429_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v_fst_4378_; 
v_fst_4378_ = lean_ctor_get(v_a_4374_, 0);
if (lean_obj_tag(v_fst_4378_) == 0)
{
lean_object* v_snd_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4423_; 
lean_del_object(v___x_4376_);
v_snd_4379_ = lean_ctor_get(v_a_4374_, 1);
v_isSharedCheck_4423_ = !lean_is_exclusive(v_a_4374_);
if (v_isSharedCheck_4423_ == 0)
{
lean_object* v_unused_4424_; 
v_unused_4424_ = lean_ctor_get(v_a_4374_, 0);
lean_dec(v_unused_4424_);
v___x_4381_ = v_a_4374_;
v_isShared_4382_ = v_isSharedCheck_4423_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_snd_4379_);
lean_dec(v_a_4374_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4423_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4383_; 
lean_inc_ref(v___y_4357_);
lean_inc(v___y_4361_);
lean_inc_ref(v___y_4360_);
lean_inc(v___y_4359_);
lean_inc_ref(v___y_4358_);
v___x_4383_ = lean_apply_5(v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, lean_box(0));
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; uint8_t v___x_4385_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
lean_inc(v_a_4384_);
lean_dec_ref(v___x_4383_);
v___x_4385_ = lean_unbox(v_a_4384_);
lean_dec(v_a_4384_);
if (v___x_4385_ == 0)
{
lean_object* v_fst_4386_; 
lean_del_object(v___x_4381_);
lean_dec(v___y_4355_);
v_fst_4386_ = lean_ctor_get(v_snd_4379_, 0);
lean_inc(v_fst_4386_);
lean_dec(v_snd_4379_);
v___y_4349_ = v_fst_4386_;
v___y_4350_ = v___y_4356_;
goto v___jp_4348_;
}
else
{
lean_object* v_fst_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4413_; 
v_fst_4387_ = lean_ctor_get(v_snd_4379_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v_snd_4379_);
if (v_isSharedCheck_4413_ == 0)
{
lean_object* v_unused_4414_; 
v_unused_4414_ = lean_ctor_get(v_snd_4379_, 1);
lean_dec(v_unused_4414_);
v___x_4389_ = v_snd_4379_;
v_isShared_4390_ = v_isSharedCheck_4413_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_fst_4387_);
lean_dec(v_snd_4379_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4413_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4391_; lean_object* v_var_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4398_; 
v___x_4391_ = lean_array_get_borrowed(v___x_4347_, v___y_4356_, v_fst_4387_);
v_var_4392_ = lean_ctor_get(v___x_4391_, 0);
v___x_4393_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4392_);
v___x_4394_ = l_Nat_reprFast(v_var_4392_);
v___x_4395_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4394_);
v___x_4396_ = l_Lean_MessageData_ofFormat(v___x_4395_);
if (v_isShared_4390_ == 0)
{
lean_ctor_set_tag(v___x_4389_, 7);
lean_ctor_set(v___x_4389_, 1, v___x_4396_);
lean_ctor_set(v___x_4389_, 0, v___x_4393_);
v___x_4398_ = v___x_4389_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4393_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v___x_4396_);
v___x_4398_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
lean_object* v___x_4399_; lean_object* v___x_4401_; 
v___x_4399_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
if (v_isShared_4382_ == 0)
{
lean_ctor_set_tag(v___x_4381_, 7);
lean_ctor_set(v___x_4381_, 1, v___x_4399_);
lean_ctor_set(v___x_4381_, 0, v___x_4398_);
v___x_4401_ = v___x_4381_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4398_);
lean_ctor_set(v_reuseFailAlloc_4411_, 1, v___x_4399_);
v___x_4401_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
lean_object* v___x_4402_; 
v___x_4402_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4355_, v___x_4401_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_dec_ref(v___x_4402_);
v___y_4349_ = v_fst_4387_;
v___y_4350_ = v___y_4356_;
goto v___jp_4348_;
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v_fst_4387_);
lean_dec_ref(v___y_4356_);
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4402_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4402_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
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
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_del_object(v___x_4381_);
lean_dec(v_snd_4379_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
v_a_4415_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4383_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4383_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
else
{
lean_object* v_val_4425_; lean_object* v___x_4427_; 
lean_inc_ref(v_fst_4378_);
lean_dec(v_a_4374_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
v_val_4425_ = lean_ctor_get(v_fst_4378_, 0);
lean_inc(v_val_4425_);
lean_dec_ref(v_fst_4378_);
if (v_isShared_4377_ == 0)
{
lean_ctor_set(v___x_4376_, 0, v_val_4425_);
v___x_4427_ = v___x_4376_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_val_4425_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
v_a_4430_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4373_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4373_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
else
{
lean_object* v___x_4438_; 
lean_inc(v___x_4362_);
lean_dec(v___x_4363_);
lean_dec_ref(v___y_4356_);
lean_inc_ref(v___y_4357_);
lean_inc(v___y_4361_);
lean_inc_ref(v___y_4360_);
lean_inc(v___y_4359_);
lean_inc_ref(v___y_4358_);
v___x_4438_ = lean_apply_5(v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, lean_box(0));
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4472_; 
v_a_4439_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4441_ = v___x_4438_;
v_isShared_4442_ = v_isSharedCheck_4472_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4438_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4472_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
uint8_t v___x_4443_; 
v___x_4443_ = lean_unbox(v_a_4439_);
lean_dec(v_a_4439_);
if (v___x_4443_ == 0)
{
lean_object* v___x_4445_; 
lean_dec(v___y_4355_);
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 0, v___x_4362_);
v___x_4445_ = v___x_4441_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4362_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
else
{
lean_object* v_var_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
lean_del_object(v___x_4441_);
v_var_4447_ = lean_ctor_get(v___x_4362_, 0);
v___x_4448_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4447_);
v___x_4449_ = l_Nat_reprFast(v_var_4447_);
v___x_4450_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4449_);
v___x_4451_ = l_Lean_MessageData_ofFormat(v___x_4450_);
v___x_4452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4448_);
lean_ctor_set(v___x_4452_, 1, v___x_4451_);
v___x_4453_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
v___x_4454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4452_);
lean_ctor_set(v___x_4454_, 1, v___x_4453_);
v___x_4455_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4355_, v___x_4454_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4462_ == 0)
{
lean_object* v_unused_4463_; 
v_unused_4463_ = lean_ctor_get(v___x_4455_, 0);
lean_dec(v_unused_4463_);
v___x_4457_ = v___x_4455_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_dec(v___x_4455_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 0, v___x_4362_);
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4362_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
else
{
lean_object* v_a_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4471_; 
lean_dec(v___x_4362_);
v_a_4464_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4471_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4466_ = v___x_4455_;
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_a_4464_);
lean_dec(v___x_4455_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v___x_4469_; 
if (v_isShared_4467_ == 0)
{
v___x_4469_ = v___x_4466_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_a_4464_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
}
}
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_dec(v___x_4362_);
lean_dec(v___y_4355_);
v_a_4473_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4438_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4438_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
}
v___jp_4481_:
{
lean_object* v_cls_4483_; lean_object* v___f_4484_; lean_object* v___x_4485_; lean_object* v_a_4486_; uint8_t v___x_4487_; 
v_cls_4483_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___f_4484_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2));
v___x_4485_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4483_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref(v___x_4485_);
v___x_4487_ = lean_unbox(v_a_4486_);
lean_dec(v_a_4486_);
if (v___x_4487_ == 0)
{
v___y_4355_ = v_cls_4483_;
v___y_4356_ = v___y_4482_;
v___y_4357_ = v___f_4484_;
v___y_4358_ = v_a_4342_;
v___y_4359_ = v_a_4343_;
v___y_4360_ = v_a_4344_;
v___y_4361_ = v_a_4345_;
goto v___jp_4354_;
}
else
{
lean_object* v___x_4488_; size_t v_sz_4489_; size_t v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4488_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4);
v_sz_4489_ = lean_array_size(v___y_4482_);
v___x_4490_ = ((size_t)0ULL);
lean_inc_ref(v___y_4482_);
v___x_4491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_4489_, v___x_4490_, v___y_4482_);
v___x_4492_ = lean_array_to_list(v___x_4491_);
v___x_4493_ = lean_box(0);
v___x_4494_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v___x_4492_, v___x_4493_);
v___x_4495_ = l_Lean_MessageData_ofList(v___x_4494_);
v___x_4496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4488_);
lean_ctor_set(v___x_4496_, 1, v___x_4495_);
v___x_4497_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4483_, v___x_4496_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_dec_ref(v___x_4497_);
v___y_4355_ = v_cls_4483_;
v___y_4356_ = v___y_4482_;
v___y_4357_ = v___f_4484_;
v___y_4358_ = v_a_4342_;
v___y_4359_ = v_a_4343_;
v___y_4360_ = v_a_4344_;
v___y_4361_ = v_a_4345_;
goto v___jp_4354_;
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4505_; 
lean_dec_ref(v___y_4482_);
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4500_ = v___x_4497_;
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4497_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object* v_data_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec_ref(v_data_4516_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object* v_upperBound_4523_, lean_object* v___y_4524_, lean_object* v_inst_4525_, lean_object* v_R_4526_, lean_object* v_a_4527_, lean_object* v_b_4528_, lean_object* v_c_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4523_, v___y_4524_, v_a_4527_, v_b_4528_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object* v_upperBound_4536_, lean_object* v___y_4537_, lean_object* v_inst_4538_, lean_object* v_R_4539_, lean_object* v_a_4540_, lean_object* v_b_4541_, lean_object* v_c_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_upperBound_4536_, v___y_4537_, v_inst_4538_, v_R_4539_, v_a_4540_, v_b_4541_, v_c_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec_ref(v___y_4537_);
lean_dec(v_upperBound_4536_);
return v_res_4548_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(lean_object* v_snd_4549_, lean_object* v_fst_4550_, lean_object* v_as_x27_4551_, lean_object* v_b_4552_){
_start:
{
if (lean_obj_tag(v_as_x27_4551_) == 0)
{
lean_object* v___x_4554_; 
lean_dec_ref(v_fst_4550_);
v___x_4554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4554_, 0, v_b_4552_);
return v___x_4554_;
}
else
{
lean_object* v_head_4555_; lean_object* v_tail_4556_; lean_object* v_fst_4557_; lean_object* v_snd_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v_head_4555_ = lean_ctor_get(v_as_x27_4551_, 0);
lean_inc(v_head_4555_);
v_tail_4556_ = lean_ctor_get(v_as_x27_4551_, 1);
lean_inc(v_tail_4556_);
lean_dec_ref(v_as_x27_4551_);
v_fst_4557_ = lean_ctor_get(v_head_4555_, 0);
lean_inc(v_fst_4557_);
v_snd_4558_ = lean_ctor_get(v_head_4555_, 1);
lean_inc(v_snd_4558_);
lean_dec(v_head_4555_);
v___x_4559_ = lean_int_neg(v_snd_4549_);
lean_inc_ref(v_fst_4550_);
v___x_4560_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_snd_4558_, v_fst_4550_, v___x_4559_, v_fst_4557_);
v___x_4561_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_4560_);
v___x_4562_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_b_4552_, v___x_4561_);
v_as_x27_4551_ = v_tail_4556_;
v_b_4552_ = v___x_4562_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg___boxed(lean_object* v_snd_4564_, lean_object* v_fst_4565_, lean_object* v_as_x27_4566_, lean_object* v_b_4567_, lean_object* v___y_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4564_, v_fst_4565_, v_as_x27_4566_, v_b_4567_);
lean_dec(v_snd_4564_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(lean_object* v_upperBounds_4570_, lean_object* v_as_x27_4571_, lean_object* v_b_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
if (lean_obj_tag(v_as_x27_4571_) == 0)
{
lean_object* v___x_4578_; 
lean_dec(v_upperBounds_4570_);
v___x_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4578_, 0, v_b_4572_);
return v___x_4578_;
}
else
{
lean_object* v_head_4579_; lean_object* v_tail_4580_; lean_object* v_fst_4581_; lean_object* v_snd_4582_; lean_object* v___x_4583_; lean_object* v_a_4584_; 
v_head_4579_ = lean_ctor_get(v_as_x27_4571_, 0);
lean_inc(v_head_4579_);
v_tail_4580_ = lean_ctor_get(v_as_x27_4571_, 1);
lean_inc(v_tail_4580_);
lean_dec_ref(v_as_x27_4571_);
v_fst_4581_ = lean_ctor_get(v_head_4579_, 0);
lean_inc(v_fst_4581_);
v_snd_4582_ = lean_ctor_get(v_head_4579_, 1);
lean_inc(v_snd_4582_);
lean_dec(v_head_4579_);
lean_inc(v_upperBounds_4570_);
v___x_4583_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4582_, v_fst_4581_, v_upperBounds_4570_, v_b_4572_);
lean_dec(v_snd_4582_);
v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
lean_inc(v_a_4584_);
lean_dec_ref(v___x_4583_);
v_as_x27_4571_ = v_tail_4580_;
v_b_4572_ = v_a_4584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg___boxed(lean_object* v_upperBounds_4586_, lean_object* v_as_x27_4587_, lean_object* v_b_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4586_, v_as_x27_4587_, v_b_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(lean_object* v_as_x27_4595_, lean_object* v_b_4596_){
_start:
{
if (lean_obj_tag(v_as_x27_4595_) == 0)
{
lean_object* v___x_4598_; 
v___x_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4598_, 0, v_b_4596_);
return v___x_4598_;
}
else
{
lean_object* v_head_4599_; lean_object* v_tail_4600_; lean_object* v___x_4601_; 
v_head_4599_ = lean_ctor_get(v_as_x27_4595_, 0);
lean_inc(v_head_4599_);
v_tail_4600_ = lean_ctor_get(v_as_x27_4595_, 1);
lean_inc(v_tail_4600_);
lean_dec_ref(v_as_x27_4595_);
v___x_4601_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_b_4596_, v_head_4599_);
v_as_x27_4595_ = v_tail_4600_;
v_b_4596_ = v___x_4601_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg___boxed(lean_object* v_as_x27_4603_, lean_object* v_b_4604_, lean_object* v___y_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4603_, v_b_4604_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(lean_object* v_p_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
lean_object* v_data_4613_; lean_object* v___x_4614_; 
lean_inc_ref(v_p_4607_);
v_data_4613_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(v_p_4607_);
v___x_4614_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4613_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
lean_dec_ref(v_data_4613_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v_irrelevant_4616_; lean_object* v_lowerBounds_4617_; lean_object* v_upperBounds_4618_; lean_object* v_assumptions_4619_; lean_object* v_eliminations_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4635_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
lean_inc(v_a_4615_);
lean_dec_ref(v___x_4614_);
v_irrelevant_4616_ = lean_ctor_get(v_a_4615_, 1);
lean_inc(v_irrelevant_4616_);
v_lowerBounds_4617_ = lean_ctor_get(v_a_4615_, 2);
lean_inc(v_lowerBounds_4617_);
v_upperBounds_4618_ = lean_ctor_get(v_a_4615_, 3);
lean_inc(v_upperBounds_4618_);
lean_dec(v_a_4615_);
v_assumptions_4619_ = lean_ctor_get(v_p_4607_, 0);
v_eliminations_4620_ = lean_ctor_get(v_p_4607_, 4);
v_isSharedCheck_4635_ = !lean_is_exclusive(v_p_4607_);
if (v_isSharedCheck_4635_ == 0)
{
lean_object* v_unused_4636_; lean_object* v_unused_4637_; lean_object* v_unused_4638_; lean_object* v_unused_4639_; lean_object* v_unused_4640_; 
v_unused_4636_ = lean_ctor_get(v_p_4607_, 6);
lean_dec(v_unused_4636_);
v_unused_4637_ = lean_ctor_get(v_p_4607_, 5);
lean_dec(v_unused_4637_);
v_unused_4638_ = lean_ctor_get(v_p_4607_, 3);
lean_dec(v_unused_4638_);
v_unused_4639_ = lean_ctor_get(v_p_4607_, 2);
lean_dec(v_unused_4639_);
v_unused_4640_ = lean_ctor_get(v_p_4607_, 1);
lean_dec(v_unused_4640_);
v___x_4622_ = v_p_4607_;
v_isShared_4623_ = v_isSharedCheck_4635_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_eliminations_4620_);
lean_inc(v_assumptions_4619_);
lean_dec(v_p_4607_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4635_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; uint8_t v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4630_; 
v___x_4624_ = lean_unsigned_to_nat(0u);
v___x_4625_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v___x_4626_ = 1;
v___x_4627_ = lean_box(0);
v___x_4628_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_4623_ == 0)
{
lean_ctor_set(v___x_4622_, 6, v___x_4628_);
lean_ctor_set(v___x_4622_, 5, v___x_4627_);
lean_ctor_set(v___x_4622_, 3, v___x_4625_);
lean_ctor_set(v___x_4622_, 2, v___x_4625_);
lean_ctor_set(v___x_4622_, 1, v___x_4624_);
v___x_4630_ = v___x_4622_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_assumptions_4619_);
lean_ctor_set(v_reuseFailAlloc_4634_, 1, v___x_4624_);
lean_ctor_set(v_reuseFailAlloc_4634_, 2, v___x_4625_);
lean_ctor_set(v_reuseFailAlloc_4634_, 3, v___x_4625_);
lean_ctor_set(v_reuseFailAlloc_4634_, 4, v_eliminations_4620_);
lean_ctor_set(v_reuseFailAlloc_4634_, 5, v___x_4627_);
lean_ctor_set(v_reuseFailAlloc_4634_, 6, v___x_4628_);
v___x_4630_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
lean_object* v___x_4631_; lean_object* v_a_4632_; lean_object* v___x_4633_; 
lean_ctor_set_uint8(v___x_4630_, sizeof(void*)*7, v___x_4626_);
v___x_4631_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_irrelevant_4616_, v___x_4630_);
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc(v_a_4632_);
lean_dec_ref(v___x_4631_);
v___x_4633_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4618_, v_lowerBounds_4617_, v_a_4632_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
return v___x_4633_;
}
}
}
else
{
lean_object* v_a_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4648_; 
lean_dec_ref(v_p_4607_);
v_a_4641_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4643_ = v___x_4614_;
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_a_4641_);
lean_dec(v___x_4614_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4646_; 
if (v_isShared_4644_ == 0)
{
v___x_4646_ = v___x_4643_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4641_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin___boxed(lean_object* v_p_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
lean_dec(v_a_4653_);
lean_dec_ref(v_a_4652_);
lean_dec(v_a_4651_);
lean_dec_ref(v_a_4650_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(lean_object* v_snd_4656_, lean_object* v_fst_4657_, lean_object* v_as_4658_, lean_object* v_as_x27_4659_, lean_object* v_b_4660_, lean_object* v_a_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
lean_object* v___x_4667_; 
v___x_4667_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4656_, v_fst_4657_, v_as_x27_4659_, v_b_4660_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___boxed(lean_object* v_snd_4668_, lean_object* v_fst_4669_, lean_object* v_as_4670_, lean_object* v_as_x27_4671_, lean_object* v_b_4672_, lean_object* v_a_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(v_snd_4668_, v_fst_4669_, v_as_4670_, v_as_x27_4671_, v_b_4672_, v_a_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v_as_4670_);
lean_dec(v_snd_4668_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(lean_object* v_as_4680_, lean_object* v_as_x27_4681_, lean_object* v_b_4682_, lean_object* v_a_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_){
_start:
{
lean_object* v___x_4689_; 
v___x_4689_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4681_, v_b_4682_);
return v___x_4689_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___boxed(lean_object* v_as_4690_, lean_object* v_as_x27_4691_, lean_object* v_b_4692_, lean_object* v_a_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v_res_4699_; 
v_res_4699_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(v_as_4690_, v_as_x27_4691_, v_b_4692_, v_a_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v_as_4690_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(lean_object* v_upperBounds_4700_, lean_object* v_as_4701_, lean_object* v_as_x27_4702_, lean_object* v_b_4703_, lean_object* v_a_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v___x_4710_; 
v___x_4710_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4700_, v_as_x27_4702_, v_b_4703_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___boxed(lean_object* v_upperBounds_4711_, lean_object* v_as_4712_, lean_object* v_as_x27_4713_, lean_object* v_b_4714_, lean_object* v_a_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(v_upperBounds_4711_, v_as_4712_, v_as_x27_4713_, v_b_4714_, v_a_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v_as_4712_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object* v_x_4722_, lean_object* v_x_4723_){
_start:
{
if (lean_obj_tag(v_x_4723_) == 0)
{
lean_inc(v_x_4722_);
return v_x_4722_;
}
else
{
lean_object* v_key_4724_; lean_object* v_value_4725_; lean_object* v_tail_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
v_key_4724_ = lean_ctor_get(v_x_4723_, 0);
v_value_4725_ = lean_ctor_get(v_x_4723_, 1);
v_tail_4726_ = lean_ctor_get(v_x_4723_, 2);
v___x_4727_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4722_, v_tail_4726_);
lean_inc(v_value_4725_);
lean_inc(v_key_4724_);
v___x_4728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4728_, 0, v_key_4724_);
lean_ctor_set(v___x_4728_, 1, v_value_4725_);
v___x_4729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4729_, 0, v___x_4728_);
lean_ctor_set(v___x_4729_, 1, v___x_4727_);
return v___x_4729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2___boxed(lean_object* v_x_4730_, lean_object* v_x_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4730_, v_x_4731_);
lean_dec(v_x_4731_);
lean_dec(v_x_4730_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object* v_as_4733_, size_t v_i_4734_, size_t v_stop_4735_, lean_object* v_b_4736_){
_start:
{
uint8_t v___x_4737_; 
v___x_4737_ = lean_usize_dec_eq(v_i_4734_, v_stop_4735_);
if (v___x_4737_ == 0)
{
size_t v___x_4738_; size_t v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4738_ = ((size_t)1ULL);
v___x_4739_ = lean_usize_sub(v_i_4734_, v___x_4738_);
v___x_4740_ = lean_array_uget_borrowed(v_as_4733_, v___x_4739_);
v___x_4741_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_b_4736_, v___x_4740_);
lean_dec(v_b_4736_);
v_i_4734_ = v___x_4739_;
v_b_4736_ = v___x_4741_;
goto _start;
}
else
{
return v_b_4736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object* v_as_4743_, lean_object* v_i_4744_, lean_object* v_stop_4745_, lean_object* v_b_4746_){
_start:
{
size_t v_i_boxed_4747_; size_t v_stop_boxed_4748_; lean_object* v_res_4749_; 
v_i_boxed_4747_ = lean_unbox_usize(v_i_4744_);
lean_dec(v_i_4744_);
v_stop_boxed_4748_ = lean_unbox_usize(v_stop_4745_);
lean_dec(v_stop_4745_);
v_res_4749_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_as_4743_, v_i_boxed_4747_, v_stop_boxed_4748_, v_b_4746_);
lean_dec_ref(v_as_4743_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object* v_a_4750_, lean_object* v_a_4751_){
_start:
{
if (lean_obj_tag(v_a_4750_) == 0)
{
lean_object* v___x_4752_; 
v___x_4752_ = l_List_reverse___redArg(v_a_4751_);
return v___x_4752_;
}
else
{
lean_object* v_head_4753_; lean_object* v_tail_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4871_; 
v_head_4753_ = lean_ctor_get(v_a_4750_, 0);
v_tail_4754_ = lean_ctor_get(v_a_4750_, 1);
v_isSharedCheck_4871_ = !lean_is_exclusive(v_a_4750_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4756_ = v_a_4750_;
v_isShared_4757_ = v_isSharedCheck_4871_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_tail_4754_);
lean_inc(v_head_4753_);
lean_dec(v_a_4750_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4871_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___y_4759_; lean_object* v_snd_4764_; lean_object* v_constraint_4765_; lean_object* v_fst_4766_; lean_object* v_lowerBound_4767_; lean_object* v_upperBound_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___y_4773_; lean_object* v___y_4774_; 
v_snd_4764_ = lean_ctor_get(v_head_4753_, 1);
v_constraint_4765_ = lean_ctor_get(v_snd_4764_, 1);
lean_inc_ref(v_constraint_4765_);
v_fst_4766_ = lean_ctor_get(v_head_4753_, 0);
lean_inc(v_fst_4766_);
lean_dec(v_head_4753_);
v_lowerBound_4767_ = lean_ctor_get(v_constraint_4765_, 0);
lean_inc(v_lowerBound_4767_);
v_upperBound_4768_ = lean_ctor_get(v_constraint_4765_, 1);
lean_inc(v_upperBound_4768_);
lean_dec_ref(v_constraint_4765_);
v___x_4769_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_fst_4766_);
lean_dec(v_fst_4766_);
v___x_4770_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_4771_ = lean_string_append(v___x_4769_, v___x_4770_);
if (lean_obj_tag(v_lowerBound_4767_) == 0)
{
if (lean_obj_tag(v_upperBound_4768_) == 0)
{
lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4779_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_4780_ = lean_string_append(v___x_4771_, v___x_4779_);
v___y_4759_ = v___x_4780_;
goto v___jp_4758_;
}
else
{
lean_object* v_val_4781_; lean_object* v___x_4782_; lean_object* v___y_4784_; lean_object* v_intZero_4789_; uint8_t v_isNeg_4790_; 
v_val_4781_ = lean_ctor_get(v_upperBound_4768_, 0);
lean_inc(v_val_4781_);
lean_dec_ref(v_upperBound_4768_);
v___x_4782_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_4789_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4790_ = lean_int_dec_lt(v_val_4781_, v_intZero_4789_);
if (v_isNeg_4790_ == 0)
{
lean_object* v_a_4791_; lean_object* v___x_4792_; 
v_a_4791_ = lean_nat_abs(v_val_4781_);
lean_dec(v_val_4781_);
v___x_4792_ = l_Nat_reprFast(v_a_4791_);
v___y_4784_ = v___x_4792_;
goto v___jp_4783_;
}
else
{
lean_object* v_abs_4793_; lean_object* v_one_4794_; lean_object* v_a_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
v_abs_4793_ = lean_nat_abs(v_val_4781_);
lean_dec(v_val_4781_);
v_one_4794_ = lean_unsigned_to_nat(1u);
v_a_4795_ = lean_nat_sub(v_abs_4793_, v_one_4794_);
lean_dec(v_abs_4793_);
v___x_4796_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4797_ = lean_nat_add(v_a_4795_, v_one_4794_);
lean_dec(v_a_4795_);
v___x_4798_ = l_Nat_reprFast(v___x_4797_);
v___x_4799_ = lean_string_append(v___x_4796_, v___x_4798_);
lean_dec_ref(v___x_4798_);
v___y_4784_ = v___x_4799_;
goto v___jp_4783_;
}
v___jp_4783_:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4785_ = lean_string_append(v___x_4782_, v___y_4784_);
lean_dec_ref(v___y_4784_);
v___x_4786_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4787_ = lean_string_append(v___x_4785_, v___x_4786_);
v___x_4788_ = lean_string_append(v___x_4771_, v___x_4787_);
lean_dec_ref(v___x_4787_);
v___y_4759_ = v___x_4788_;
goto v___jp_4758_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_4768_) == 0)
{
lean_object* v_val_4800_; lean_object* v___x_4801_; lean_object* v___y_4803_; lean_object* v_intZero_4808_; uint8_t v_isNeg_4809_; 
v_val_4800_ = lean_ctor_get(v_lowerBound_4767_, 0);
lean_inc(v_val_4800_);
lean_dec_ref(v_lowerBound_4767_);
v___x_4801_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4808_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4809_ = lean_int_dec_lt(v_val_4800_, v_intZero_4808_);
if (v_isNeg_4809_ == 0)
{
lean_object* v_a_4810_; lean_object* v___x_4811_; 
v_a_4810_ = lean_nat_abs(v_val_4800_);
lean_dec(v_val_4800_);
v___x_4811_ = l_Nat_reprFast(v_a_4810_);
v___y_4803_ = v___x_4811_;
goto v___jp_4802_;
}
else
{
lean_object* v_abs_4812_; lean_object* v_one_4813_; lean_object* v_a_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
v_abs_4812_ = lean_nat_abs(v_val_4800_);
lean_dec(v_val_4800_);
v_one_4813_ = lean_unsigned_to_nat(1u);
v_a_4814_ = lean_nat_sub(v_abs_4812_, v_one_4813_);
lean_dec(v_abs_4812_);
v___x_4815_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4816_ = lean_nat_add(v_a_4814_, v_one_4813_);
lean_dec(v_a_4814_);
v___x_4817_ = l_Nat_reprFast(v___x_4816_);
v___x_4818_ = lean_string_append(v___x_4815_, v___x_4817_);
lean_dec_ref(v___x_4817_);
v___y_4803_ = v___x_4818_;
goto v___jp_4802_;
}
v___jp_4802_:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4804_ = lean_string_append(v___x_4801_, v___y_4803_);
lean_dec_ref(v___y_4803_);
v___x_4805_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_4806_ = lean_string_append(v___x_4804_, v___x_4805_);
v___x_4807_ = lean_string_append(v___x_4771_, v___x_4806_);
lean_dec_ref(v___x_4806_);
v___y_4759_ = v___x_4807_;
goto v___jp_4758_;
}
}
else
{
lean_object* v_val_4819_; lean_object* v_val_4820_; uint8_t v___x_4821_; 
v_val_4819_ = lean_ctor_get(v_lowerBound_4767_, 0);
lean_inc(v_val_4819_);
lean_dec_ref(v_lowerBound_4767_);
v_val_4820_ = lean_ctor_get(v_upperBound_4768_, 0);
lean_inc(v_val_4820_);
lean_dec_ref(v_upperBound_4768_);
v___x_4821_ = lean_int_dec_lt(v_val_4820_, v_val_4819_);
if (v___x_4821_ == 0)
{
uint8_t v___x_4822_; 
v___x_4822_ = lean_int_dec_eq(v_val_4819_, v_val_4820_);
if (v___x_4822_ == 0)
{
lean_object* v___x_4823_; lean_object* v___y_4825_; lean_object* v_intZero_4840_; uint8_t v_isNeg_4841_; 
v___x_4823_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4840_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4841_ = lean_int_dec_lt(v_val_4819_, v_intZero_4840_);
if (v_isNeg_4841_ == 0)
{
lean_object* v_a_4842_; lean_object* v___x_4843_; 
v_a_4842_ = lean_nat_abs(v_val_4819_);
lean_dec(v_val_4819_);
v___x_4843_ = l_Nat_reprFast(v_a_4842_);
v___y_4825_ = v___x_4843_;
goto v___jp_4824_;
}
else
{
lean_object* v_abs_4844_; lean_object* v_one_4845_; lean_object* v_a_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
v_abs_4844_ = lean_nat_abs(v_val_4819_);
lean_dec(v_val_4819_);
v_one_4845_ = lean_unsigned_to_nat(1u);
v_a_4846_ = lean_nat_sub(v_abs_4844_, v_one_4845_);
lean_dec(v_abs_4844_);
v___x_4847_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4848_ = lean_nat_add(v_a_4846_, v_one_4845_);
lean_dec(v_a_4846_);
v___x_4849_ = l_Nat_reprFast(v___x_4848_);
v___x_4850_ = lean_string_append(v___x_4847_, v___x_4849_);
lean_dec_ref(v___x_4849_);
v___y_4825_ = v___x_4850_;
goto v___jp_4824_;
}
v___jp_4824_:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v_intZero_4829_; uint8_t v_isNeg_4830_; 
v___x_4826_ = lean_string_append(v___x_4823_, v___y_4825_);
lean_dec_ref(v___y_4825_);
v___x_4827_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_4828_ = lean_string_append(v___x_4826_, v___x_4827_);
v_intZero_4829_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4830_ = lean_int_dec_lt(v_val_4820_, v_intZero_4829_);
if (v_isNeg_4830_ == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4832_; 
v_a_4831_ = lean_nat_abs(v_val_4820_);
lean_dec(v_val_4820_);
v___x_4832_ = l_Nat_reprFast(v_a_4831_);
v___y_4773_ = v___x_4828_;
v___y_4774_ = v___x_4832_;
goto v___jp_4772_;
}
else
{
lean_object* v_abs_4833_; lean_object* v_one_4834_; lean_object* v_a_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v_abs_4833_ = lean_nat_abs(v_val_4820_);
lean_dec(v_val_4820_);
v_one_4834_ = lean_unsigned_to_nat(1u);
v_a_4835_ = lean_nat_sub(v_abs_4833_, v_one_4834_);
lean_dec(v_abs_4833_);
v___x_4836_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4837_ = lean_nat_add(v_a_4835_, v_one_4834_);
lean_dec(v_a_4835_);
v___x_4838_ = l_Nat_reprFast(v___x_4837_);
v___x_4839_ = lean_string_append(v___x_4836_, v___x_4838_);
lean_dec_ref(v___x_4838_);
v___y_4773_ = v___x_4828_;
v___y_4774_ = v___x_4839_;
goto v___jp_4772_;
}
}
}
else
{
lean_object* v___x_4851_; lean_object* v___y_4853_; lean_object* v_intZero_4858_; uint8_t v_isNeg_4859_; 
lean_dec(v_val_4820_);
v___x_4851_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_4858_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4859_ = lean_int_dec_lt(v_val_4819_, v_intZero_4858_);
if (v_isNeg_4859_ == 0)
{
lean_object* v_a_4860_; lean_object* v___x_4861_; 
v_a_4860_ = lean_nat_abs(v_val_4819_);
lean_dec(v_val_4819_);
v___x_4861_ = l_Nat_reprFast(v_a_4860_);
v___y_4853_ = v___x_4861_;
goto v___jp_4852_;
}
else
{
lean_object* v_abs_4862_; lean_object* v_one_4863_; lean_object* v_a_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; 
v_abs_4862_ = lean_nat_abs(v_val_4819_);
lean_dec(v_val_4819_);
v_one_4863_ = lean_unsigned_to_nat(1u);
v_a_4864_ = lean_nat_sub(v_abs_4862_, v_one_4863_);
lean_dec(v_abs_4862_);
v___x_4865_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4866_ = lean_nat_add(v_a_4864_, v_one_4863_);
lean_dec(v_a_4864_);
v___x_4867_ = l_Nat_reprFast(v___x_4866_);
v___x_4868_ = lean_string_append(v___x_4865_, v___x_4867_);
lean_dec_ref(v___x_4867_);
v___y_4853_ = v___x_4868_;
goto v___jp_4852_;
}
v___jp_4852_:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4854_ = lean_string_append(v___x_4851_, v___y_4853_);
lean_dec_ref(v___y_4853_);
v___x_4855_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_4856_ = lean_string_append(v___x_4854_, v___x_4855_);
v___x_4857_ = lean_string_append(v___x_4771_, v___x_4856_);
lean_dec_ref(v___x_4856_);
v___y_4759_ = v___x_4857_;
goto v___jp_4758_;
}
}
}
else
{
lean_object* v___x_4869_; lean_object* v___x_4870_; 
lean_dec(v_val_4820_);
lean_dec(v_val_4819_);
v___x_4869_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_4870_ = lean_string_append(v___x_4771_, v___x_4869_);
v___y_4759_ = v___x_4870_;
goto v___jp_4758_;
}
}
}
v___jp_4758_:
{
lean_object* v___x_4761_; 
if (v_isShared_4757_ == 0)
{
lean_ctor_set(v___x_4756_, 1, v_a_4751_);
lean_ctor_set(v___x_4756_, 0, v___y_4759_);
v___x_4761_ = v___x_4756_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v___y_4759_);
lean_ctor_set(v_reuseFailAlloc_4763_, 1, v_a_4751_);
v___x_4761_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
v_a_4750_ = v_tail_4754_;
v_a_4751_ = v___x_4761_;
goto _start;
}
}
v___jp_4772_:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4775_ = lean_string_append(v___y_4773_, v___y_4774_);
lean_dec_ref(v___y_4774_);
v___x_4776_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4777_ = lean_string_append(v___x_4775_, v___x_4776_);
v___x_4778_ = lean_string_append(v___x_4771_, v___x_4777_);
lean_dec_ref(v___x_4777_);
v___y_4759_ = v___x_4778_;
goto v___jp_4758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object* v_cls_4872_, lean_object* v_msg_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
lean_object* v_ref_4879_; lean_object* v___x_4880_; lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4925_; 
v_ref_4879_ = lean_ctor_get(v___y_4876_, 5);
v___x_4880_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4883_ = v___x_4880_;
v_isShared_4884_ = v_isSharedCheck_4925_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4880_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4925_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4885_; lean_object* v_traceState_4886_; lean_object* v_env_4887_; lean_object* v_nextMacroScope_4888_; lean_object* v_ngen_4889_; lean_object* v_auxDeclNGen_4890_; lean_object* v_cache_4891_; lean_object* v_messages_4892_; lean_object* v_infoState_4893_; lean_object* v_snapshotTasks_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4924_; 
v___x_4885_ = lean_st_ref_take(v___y_4877_);
v_traceState_4886_ = lean_ctor_get(v___x_4885_, 4);
v_env_4887_ = lean_ctor_get(v___x_4885_, 0);
v_nextMacroScope_4888_ = lean_ctor_get(v___x_4885_, 1);
v_ngen_4889_ = lean_ctor_get(v___x_4885_, 2);
v_auxDeclNGen_4890_ = lean_ctor_get(v___x_4885_, 3);
v_cache_4891_ = lean_ctor_get(v___x_4885_, 5);
v_messages_4892_ = lean_ctor_get(v___x_4885_, 6);
v_infoState_4893_ = lean_ctor_get(v___x_4885_, 7);
v_snapshotTasks_4894_ = lean_ctor_get(v___x_4885_, 8);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4896_ = v___x_4885_;
v_isShared_4897_ = v_isSharedCheck_4924_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_snapshotTasks_4894_);
lean_inc(v_infoState_4893_);
lean_inc(v_messages_4892_);
lean_inc(v_cache_4891_);
lean_inc(v_traceState_4886_);
lean_inc(v_auxDeclNGen_4890_);
lean_inc(v_ngen_4889_);
lean_inc(v_nextMacroScope_4888_);
lean_inc(v_env_4887_);
lean_dec(v___x_4885_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4924_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
uint64_t v_tid_4898_; lean_object* v_traces_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4923_; 
v_tid_4898_ = lean_ctor_get_uint64(v_traceState_4886_, sizeof(void*)*1);
v_traces_4899_ = lean_ctor_get(v_traceState_4886_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v_traceState_4886_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4901_ = v_traceState_4886_;
v_isShared_4902_ = v_isSharedCheck_4923_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_traces_4899_);
lean_dec(v_traceState_4886_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4923_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4903_; double v___x_4904_; uint8_t v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4913_; 
v___x_4903_ = lean_box(0);
v___x_4904_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4905_ = 0;
v___x_4906_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4907_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4907_, 0, v_cls_4872_);
lean_ctor_set(v___x_4907_, 1, v___x_4903_);
lean_ctor_set(v___x_4907_, 2, v___x_4906_);
lean_ctor_set_float(v___x_4907_, sizeof(void*)*3, v___x_4904_);
lean_ctor_set_float(v___x_4907_, sizeof(void*)*3 + 8, v___x_4904_);
lean_ctor_set_uint8(v___x_4907_, sizeof(void*)*3 + 16, v___x_4905_);
v___x_4908_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4909_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4909_, 0, v___x_4907_);
lean_ctor_set(v___x_4909_, 1, v_a_4881_);
lean_ctor_set(v___x_4909_, 2, v___x_4908_);
lean_inc(v_ref_4879_);
v___x_4910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4910_, 0, v_ref_4879_);
lean_ctor_set(v___x_4910_, 1, v___x_4909_);
v___x_4911_ = l_Lean_PersistentArray_push___redArg(v_traces_4899_, v___x_4910_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 0, v___x_4911_);
v___x_4913_ = v___x_4901_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v___x_4911_);
lean_ctor_set_uint64(v_reuseFailAlloc_4922_, sizeof(void*)*1, v_tid_4898_);
v___x_4913_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
lean_object* v___x_4915_; 
if (v_isShared_4897_ == 0)
{
lean_ctor_set(v___x_4896_, 4, v___x_4913_);
v___x_4915_ = v___x_4896_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_env_4887_);
lean_ctor_set(v_reuseFailAlloc_4921_, 1, v_nextMacroScope_4888_);
lean_ctor_set(v_reuseFailAlloc_4921_, 2, v_ngen_4889_);
lean_ctor_set(v_reuseFailAlloc_4921_, 3, v_auxDeclNGen_4890_);
lean_ctor_set(v_reuseFailAlloc_4921_, 4, v___x_4913_);
lean_ctor_set(v_reuseFailAlloc_4921_, 5, v_cache_4891_);
lean_ctor_set(v_reuseFailAlloc_4921_, 6, v_messages_4892_);
lean_ctor_set(v_reuseFailAlloc_4921_, 7, v_infoState_4893_);
lean_ctor_set(v_reuseFailAlloc_4921_, 8, v_snapshotTasks_4894_);
v___x_4915_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4919_; 
v___x_4916_ = lean_st_ref_set(v___y_4877_, v___x_4915_);
v___x_4917_ = lean_box(0);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 0, v___x_4917_);
v___x_4919_ = v___x_4883_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v___x_4917_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg___boxed(lean_object* v_cls_4926_, lean_object* v_msg_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4926_, v_msg_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
return v_res_4933_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1(void){
_start:
{
lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4935_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__0));
v___x_4936_ = l_Lean_stringToMessageData(v___x_4935_);
return v___x_4936_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1(void){
_start:
{
lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4938_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__0));
v___x_4939_ = l_Lean_stringToMessageData(v___x_4938_);
return v___x_4939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega(lean_object* v_p_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, uint8_t v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_){
_start:
{
lean_object* v___y_4952_; lean_object* v___y_4953_; lean_object* v___y_4954_; uint8_t v___y_4955_; lean_object* v___y_4956_; lean_object* v___y_4957_; lean_object* v___y_4958_; lean_object* v___y_4959_; lean_object* v___y_4960_; lean_object* v_options_4966_; uint8_t v_hasTrace_4967_; 
v_options_4966_ = lean_ctor_get(v_a_4948_, 2);
v_hasTrace_4967_ = lean_ctor_get_uint8(v_options_4966_, sizeof(void*)*1);
if (v_hasTrace_4967_ == 0)
{
v___y_4952_ = v_a_4941_;
v___y_4953_ = v_a_4942_;
v___y_4954_ = v_a_4943_;
v___y_4955_ = v_a_4944_;
v___y_4956_ = v_a_4945_;
v___y_4957_ = v_a_4946_;
v___y_4958_ = v_a_4947_;
v___y_4959_ = v_a_4948_;
v___y_4960_ = v_a_4949_;
goto v___jp_4951_;
}
else
{
lean_object* v_inheritedTraceOptions_4968_; lean_object* v_cls_4969_; lean_object* v___x_4970_; uint8_t v___x_4971_; 
v_inheritedTraceOptions_4968_ = lean_ctor_get(v_a_4948_, 13);
v_cls_4969_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4970_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_4971_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4968_, v_options_4966_, v___x_4970_);
if (v___x_4971_ == 0)
{
v___y_4952_ = v_a_4941_;
v___y_4953_ = v_a_4942_;
v___y_4954_ = v_a_4943_;
v___y_4955_ = v_a_4944_;
v___y_4956_ = v_a_4945_;
v___y_4957_ = v_a_4946_;
v___y_4958_ = v_a_4947_;
v___y_4959_ = v_a_4948_;
v___y_4960_ = v_a_4949_;
goto v___jp_4951_;
}
else
{
lean_object* v_constraints_4972_; uint8_t v_possible_4973_; lean_object* v___x_4974_; lean_object* v___y_4976_; 
v_constraints_4972_ = lean_ctor_get(v_p_4940_, 2);
v_possible_4973_ = lean_ctor_get_uint8(v_p_4940_, sizeof(void*)*7);
v___x_4974_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1);
if (v_possible_4973_ == 0)
{
lean_object* v___x_4989_; 
v___x_4989_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
v___y_4976_ = v___x_4989_;
goto v___jp_4975_;
}
else
{
uint8_t v___x_4990_; 
v___x_4990_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_4940_);
if (v___x_4990_ == 0)
{
lean_object* v_buckets_4991_; lean_object* v___x_4992_; lean_object* v___y_4994_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; uint8_t v___x_5001_; 
v_buckets_4991_ = lean_ctor_get(v_constraints_4972_, 1);
v___x_4992_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_4998_ = lean_box(0);
v___x_4999_ = lean_array_get_size(v_buckets_4991_);
v___x_5000_ = lean_unsigned_to_nat(0u);
v___x_5001_ = lean_nat_dec_lt(v___x_5000_, v___x_4999_);
if (v___x_5001_ == 0)
{
v___y_4994_ = v___x_4998_;
goto v___jp_4993_;
}
else
{
size_t v___x_5002_; size_t v___x_5003_; lean_object* v___x_5004_; 
v___x_5002_ = lean_usize_of_nat(v___x_4999_);
v___x_5003_ = ((size_t)0ULL);
v___x_5004_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_4991_, v___x_5002_, v___x_5003_, v___x_4998_);
v___y_4994_ = v___x_5004_;
goto v___jp_4993_;
}
v___jp_4993_:
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; 
v___x_4995_ = lean_box(0);
v___x_4996_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_4994_, v___x_4995_);
v___x_4997_ = l_String_intercalate(v___x_4992_, v___x_4996_);
v___y_4976_ = v___x_4997_;
goto v___jp_4975_;
}
}
else
{
lean_object* v___x_5005_; 
v___x_5005_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_4976_ = v___x_5005_;
goto v___jp_4975_;
}
}
v___jp_4975_:
{
lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4977_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4977_, 0, v___y_4976_);
v___x_4978_ = l_Lean_MessageData_ofFormat(v___x_4977_);
v___x_4979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4974_);
lean_ctor_set(v___x_4979_, 1, v___x_4978_);
v___x_4980_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4969_, v___x_4979_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_);
if (lean_obj_tag(v___x_4980_) == 0)
{
lean_dec_ref(v___x_4980_);
v___y_4952_ = v_a_4941_;
v___y_4953_ = v_a_4942_;
v___y_4954_ = v_a_4943_;
v___y_4955_ = v_a_4944_;
v___y_4956_ = v_a_4945_;
v___y_4957_ = v_a_4946_;
v___y_4958_ = v_a_4947_;
v___y_4959_ = v_a_4948_;
v___y_4960_ = v_a_4949_;
goto v___jp_4951_;
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
lean_dec_ref(v_p_4940_);
v_a_4981_ = lean_ctor_get(v___x_4980_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4980_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4980_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
}
}
}
v___jp_4951_:
{
uint8_t v_possible_4961_; 
v_possible_4961_ = lean_ctor_get_uint8(v_p_4940_, sizeof(void*)*7);
if (v_possible_4961_ == 0)
{
lean_object* v___x_4962_; 
v___x_4962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4962_, 0, v_p_4940_);
return v___x_4962_;
}
else
{
lean_object* v___x_4963_; 
v___x_4963_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_4940_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v___x_4965_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc(v_a_4964_);
lean_dec_ref(v___x_4963_);
v___x_4965_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_a_4964_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_);
return v___x_4965_;
}
else
{
return v___x_4963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination(lean_object* v_p_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, uint8_t v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_){
_start:
{
lean_object* v___y_5018_; lean_object* v___y_5019_; lean_object* v___y_5020_; uint8_t v___y_5021_; lean_object* v___y_5022_; lean_object* v___y_5023_; lean_object* v___y_5024_; lean_object* v___y_5025_; lean_object* v___y_5026_; uint8_t v_possible_5030_; 
v_possible_5030_ = lean_ctor_get_uint8(v_p_5006_, sizeof(void*)*7);
if (v_possible_5030_ == 0)
{
lean_object* v___x_5031_; 
v___x_5031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5031_, 0, v_p_5006_);
return v___x_5031_;
}
else
{
lean_object* v_constraints_5032_; uint8_t v___x_5033_; 
v_constraints_5032_ = lean_ctor_get(v_p_5006_, 2);
v___x_5033_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_5006_);
if (v___x_5033_ == 0)
{
lean_object* v_options_5034_; uint8_t v_hasTrace_5035_; 
v_options_5034_ = lean_ctor_get(v_a_5014_, 2);
v_hasTrace_5035_ = lean_ctor_get_uint8(v_options_5034_, sizeof(void*)*1);
if (v_hasTrace_5035_ == 0)
{
v___y_5018_ = v_a_5007_;
v___y_5019_ = v_a_5008_;
v___y_5020_ = v_a_5009_;
v___y_5021_ = v_a_5010_;
v___y_5022_ = v_a_5011_;
v___y_5023_ = v_a_5012_;
v___y_5024_ = v_a_5013_;
v___y_5025_ = v_a_5014_;
v___y_5026_ = v_a_5015_;
goto v___jp_5017_;
}
else
{
lean_object* v_inheritedTraceOptions_5036_; lean_object* v_cls_5037_; lean_object* v___x_5038_; uint8_t v___x_5039_; 
v_inheritedTraceOptions_5036_ = lean_ctor_get(v_a_5014_, 13);
v_cls_5037_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_5038_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_5039_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5036_, v_options_5034_, v___x_5038_);
if (v___x_5039_ == 0)
{
v___y_5018_ = v_a_5007_;
v___y_5019_ = v_a_5008_;
v___y_5020_ = v_a_5009_;
v___y_5021_ = v_a_5010_;
v___y_5022_ = v_a_5011_;
v___y_5023_ = v_a_5012_;
v___y_5024_ = v_a_5013_;
v___y_5025_ = v_a_5014_;
v___y_5026_ = v_a_5015_;
goto v___jp_5017_;
}
else
{
lean_object* v___x_5040_; lean_object* v___y_5042_; 
v___x_5040_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1);
if (v___x_5033_ == 0)
{
lean_object* v_buckets_5055_; lean_object* v___x_5056_; lean_object* v___y_5058_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; uint8_t v___x_5065_; 
v_buckets_5055_ = lean_ctor_get(v_constraints_5032_, 1);
v___x_5056_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5062_ = lean_box(0);
v___x_5063_ = lean_array_get_size(v_buckets_5055_);
v___x_5064_ = lean_unsigned_to_nat(0u);
v___x_5065_ = lean_nat_dec_lt(v___x_5064_, v___x_5063_);
if (v___x_5065_ == 0)
{
v___y_5058_ = v___x_5062_;
goto v___jp_5057_;
}
else
{
size_t v___x_5066_; size_t v___x_5067_; lean_object* v___x_5068_; 
v___x_5066_ = lean_usize_of_nat(v___x_5063_);
v___x_5067_ = ((size_t)0ULL);
v___x_5068_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5055_, v___x_5066_, v___x_5067_, v___x_5062_);
v___y_5058_ = v___x_5068_;
goto v___jp_5057_;
}
v___jp_5057_:
{
lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; 
v___x_5059_ = lean_box(0);
v___x_5060_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5058_, v___x_5059_);
v___x_5061_ = l_String_intercalate(v___x_5056_, v___x_5060_);
v___y_5042_ = v___x_5061_;
goto v___jp_5041_;
}
}
else
{
lean_object* v___x_5069_; 
v___x_5069_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_5042_ = v___x_5069_;
goto v___jp_5041_;
}
v___jp_5041_:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
v___x_5043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5043_, 0, v___y_5042_);
v___x_5044_ = l_Lean_MessageData_ofFormat(v___x_5043_);
v___x_5045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5045_, 0, v___x_5040_);
lean_ctor_set(v___x_5045_, 1, v___x_5044_);
v___x_5046_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5037_, v___x_5045_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_);
if (lean_obj_tag(v___x_5046_) == 0)
{
lean_dec_ref(v___x_5046_);
v___y_5018_ = v_a_5007_;
v___y_5019_ = v_a_5008_;
v___y_5020_ = v_a_5009_;
v___y_5021_ = v_a_5010_;
v___y_5022_ = v_a_5011_;
v___y_5023_ = v_a_5012_;
v___y_5024_ = v_a_5013_;
v___y_5025_ = v_a_5014_;
v___y_5026_ = v_a_5015_;
goto v___jp_5017_;
}
else
{
lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5054_; 
lean_dec_ref(v_p_5006_);
v_a_5047_ = lean_ctor_get(v___x_5046_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5046_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5049_ = v___x_5046_;
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v___x_5046_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5052_; 
if (v_isShared_5050_ == 0)
{
v___x_5052_ = v___x_5049_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5070_; 
v___x_5070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5070_, 0, v_p_5006_);
return v___x_5070_;
}
}
v___jp_5017_:
{
lean_object* v___x_5027_; 
v___x_5027_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_5006_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_object* v_a_5028_; lean_object* v___x_5029_; 
v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_a_5028_);
lean_dec_ref(v___x_5027_);
v___x_5029_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_a_5028_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
return v___x_5029_;
}
else
{
return v___x_5027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___boxed(lean_object* v_p_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_){
_start:
{
uint8_t v_a_boxed_5082_; lean_object* v_res_5083_; 
v_a_boxed_5082_ = lean_unbox(v_a_5075_);
v_res_5083_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_p_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_boxed_5082_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
lean_dec(v_a_5080_);
lean_dec_ref(v_a_5079_);
lean_dec(v_a_5078_);
lean_dec_ref(v_a_5077_);
lean_dec(v_a_5076_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec(v_a_5072_);
return v_res_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___boxed(lean_object* v_p_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_){
_start:
{
uint8_t v_a_boxed_5095_; lean_object* v_res_5096_; 
v_a_boxed_5095_ = lean_unbox(v_a_5088_);
v_res_5096_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_p_5084_, v_a_5085_, v_a_5086_, v_a_5087_, v_a_boxed_5095_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_);
lean_dec(v_a_5093_);
lean_dec_ref(v_a_5092_);
lean_dec(v_a_5091_);
lean_dec_ref(v_a_5090_);
lean_dec(v_a_5089_);
lean_dec_ref(v_a_5087_);
lean_dec(v_a_5086_);
lean_dec(v_a_5085_);
return v_res_5096_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(lean_object* v_cls_5097_, lean_object* v_msg_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, uint8_t v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_){
_start:
{
lean_object* v___x_5109_; 
v___x_5109_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5097_, v_msg_5098_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
return v___x_5109_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___boxed(lean_object* v_cls_5110_, lean_object* v_msg_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
uint8_t v___y_22338__boxed_5122_; lean_object* v_res_5123_; 
v___y_22338__boxed_5122_ = lean_unbox(v___y_5115_);
v_res_5123_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(v_cls_5110_, v_msg_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_22338__boxed_5122_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
lean_dec(v___y_5118_);
lean_dec_ref(v___y_5117_);
lean_dec(v___y_5116_);
lean_dec_ref(v___y_5114_);
lean_dec(v___y_5113_);
lean_dec(v___y_5112_);
return v_res_5123_;
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
