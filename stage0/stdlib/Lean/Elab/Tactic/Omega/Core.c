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
v___x_807_ = lean_string_append(v___y_804_, v___y_806_);
lean_dec_ref(v___y_806_);
v___x_808_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_809_ = lean_string_append(v___x_807_, v___x_808_);
v___y_781_ = v___y_805_;
v___y_782_ = v___x_809_;
goto v___jp_780_;
}
v___jp_810_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_intZero_818_; uint8_t v_isNeg_819_; 
v___x_815_ = lean_string_append(v___y_811_, v___y_814_);
lean_dec_ref(v___y_814_);
v___x_816_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_817_ = lean_string_append(v___x_815_, v___x_816_);
v_intZero_818_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_819_ = lean_int_dec_lt(v___y_812_, v_intZero_818_);
if (v_isNeg_819_ == 0)
{
lean_object* v_a_820_; lean_object* v___x_821_; 
v_a_820_ = lean_nat_abs(v___y_812_);
lean_dec(v___y_812_);
v___x_821_ = l_Nat_reprFast(v_a_820_);
v___y_804_ = v___x_817_;
v___y_805_ = v___y_813_;
v___y_806_ = v___x_821_;
goto v___jp_803_;
}
else
{
lean_object* v_abs_822_; lean_object* v_one_823_; lean_object* v_a_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_abs_822_ = lean_nat_abs(v___y_812_);
lean_dec(v___y_812_);
v_one_823_ = lean_unsigned_to_nat(1u);
v_a_824_ = lean_nat_sub(v_abs_822_, v_one_823_);
lean_dec(v_abs_822_);
v___x_825_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_826_ = lean_nat_add(v_a_824_, v_one_823_);
lean_dec(v_a_824_);
v___x_827_ = l_Nat_reprFast(v___x_826_);
v___x_828_ = lean_string_append(v___x_825_, v___x_827_);
lean_dec_ref(v___x_827_);
v___y_804_ = v___x_817_;
v___y_805_ = v___y_813_;
v___y_806_ = v___x_828_;
goto v___jp_803_;
}
}
v___jp_829_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = lean_string_append(v___y_830_, v___y_832_);
lean_dec_ref(v___y_832_);
v___x_834_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_835_ = lean_string_append(v___x_833_, v___x_834_);
v___y_781_ = v___y_831_;
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
v___y_811_ = v___x_874_;
v___y_812_ = v_val_871_;
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
v___y_811_ = v___x_874_;
v___y_812_ = v_val_871_;
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
v___y_830_ = v___x_886_;
v___y_831_ = v___x_842_;
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
v___y_830_ = v___x_886_;
v___y_831_ = v___x_842_;
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
v___x_1318_ = l_Lean_mkAppB(v___y_1316_, v_type_1313_, v___y_1317_);
v___x_1319_ = l_Lean_Expr_app___override(v___y_1315_, v___x_1318_);
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
v___y_1315_ = v___x_1322_;
v___y_1316_ = v___x_1326_;
v___y_1317_ = v___x_1334_;
goto v___jp_1314_;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = l_Int_toNat(v_val_1325_);
v___x_1336_ = l_Lean_instToExprInt_mkNat(v___x_1335_);
v___y_1315_ = v___x_1322_;
v___y_1316_ = v___x_1326_;
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
v___x_1388_ = l_Lean_mkAppB(v___y_1386_, v___y_1385_, v___y_1387_);
v___x_1389_ = l_Lean_Expr_app___override(v___y_1383_, v___x_1388_);
v___y_1376_ = v___y_1384_;
v___y_1377_ = v___x_1389_;
goto v___jp_1375_;
}
v___jp_1390_:
{
lean_object* v_upperBound_1396_; lean_object* v___x_1397_; 
v_upperBound_1396_ = lean_ctor_get(v_t_1368_, 1);
v___x_1397_ = l_Lean_Expr_app___override(v___y_1391_, v___y_1395_);
if (lean_obj_tag(v_upperBound_1396_) == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec_ref(v___y_1394_);
v___x_1398_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1399_ = l_Lean_Expr_app___override(v___x_1398_, v___y_1393_);
v___x_1400_ = l_Lean_Expr_app___override(v___x_1397_, v___x_1399_);
v___y_1376_ = v___y_1392_;
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
v___x_1407_ = l_Lean_Name_mkStr2(v___y_1394_, v___x_1406_);
v___x_1408_ = l_Lean_Expr_const___override(v___x_1407_, v___x_1373_);
v___x_1409_ = lean_int_neg(v_val_1401_);
v___x_1410_ = l_Int_toNat(v___x_1409_);
lean_dec(v___x_1409_);
v___x_1411_ = l_Lean_instToExprInt_mkNat(v___x_1410_);
lean_inc_ref(v___y_1393_);
v___x_1412_ = l_Lean_mkApp3(v___x_1405_, v___y_1393_, v___x_1408_, v___x_1411_);
v___y_1383_ = v___x_1397_;
v___y_1384_ = v___y_1392_;
v___y_1385_ = v___y_1393_;
v___y_1386_ = v___x_1402_;
v___y_1387_ = v___x_1412_;
goto v___jp_1382_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_dec_ref(v___y_1394_);
v___x_1413_ = l_Int_toNat(v_val_1401_);
v___x_1414_ = l_Lean_instToExprInt_mkNat(v___x_1413_);
v___y_1383_ = v___x_1397_;
v___y_1384_ = v___y_1392_;
v___y_1385_ = v___y_1393_;
v___y_1386_ = v___x_1402_;
v___y_1387_ = v___x_1414_;
goto v___jp_1382_;
}
}
}
v___jp_1415_:
{
lean_object* v___x_1422_; 
lean_inc_ref(v___y_1419_);
v___x_1422_ = l_Lean_mkAppB(v___y_1417_, v___y_1419_, v___y_1421_);
v___y_1391_ = v___y_1416_;
v___y_1392_ = v___y_1418_;
v___y_1393_ = v___y_1419_;
v___y_1394_ = v___y_1420_;
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
v___y_1391_ = v___x_1426_;
v___y_1392_ = v___y_1424_;
v___y_1393_ = v_type_1428_;
v___y_1394_ = v___x_1427_;
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
v___y_1416_ = v___x_1426_;
v___y_1417_ = v___x_1431_;
v___y_1418_ = v___y_1424_;
v___y_1419_ = v_type_1428_;
v___y_1420_ = v___x_1427_;
v___y_1421_ = v___x_1439_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = l_Int_toNat(v_val_1430_);
v___x_1441_ = l_Lean_instToExprInt_mkNat(v___x_1440_);
v___y_1416_ = v___x_1426_;
v___y_1417_ = v___x_1431_;
v___y_1418_ = v___y_1424_;
v___y_1419_ = v_type_1428_;
v___y_1420_ = v___x_1427_;
v___y_1421_ = v___x_1441_;
goto v___jp_1415_;
}
}
}
v___jp_1446_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = l_Lean_mkAppB(v___y_1448_, v_type_1445_, v___y_1449_);
v___x_1451_ = l_Lean_Expr_app___override(v___y_1447_, v___x_1450_);
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
v___y_1447_ = v___x_1454_;
v___y_1448_ = v___x_1458_;
v___y_1449_ = v___x_1466_;
goto v___jp_1446_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = l_Int_toNat(v_val_1457_);
v___x_1468_ = l_Lean_instToExprInt_mkNat(v___x_1467_);
v___y_1447_ = v___x_1454_;
v___y_1448_ = v___x_1458_;
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
v___x_1519_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v___y_1516_, v___y_1513_, v_y_1505_);
lean_dec_ref(v___y_1516_);
v___x_1520_ = l_Lean_mkApp9(v___x_1510_, v___y_1512_, v___y_1515_, v___y_1517_, v___y_1514_, v___y_1518_, v___x_1519_, v_v_1506_, v_px_1507_, v_py_1508_);
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
v___y_1512_ = v___y_1522_;
v___y_1513_ = v_cons_1527_;
v___y_1514_ = v___x_1528_;
v___y_1515_ = v___y_1523_;
v___y_1516_ = v_nil_1526_;
v___y_1517_ = v___y_1524_;
v___y_1518_ = v___x_1536_;
goto v___jp_1511_;
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = l_Int_toNat(v_b_1504_);
v___x_1538_ = l_Lean_instToExprInt_mkNat(v___x_1537_);
v___y_1512_ = v___y_1522_;
v___y_1513_ = v_cons_1527_;
v___y_1514_ = v___x_1528_;
v___y_1515_ = v___y_1523_;
v___y_1516_ = v_nil_1526_;
v___y_1517_ = v___y_1524_;
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
v___x_1559_ = l_Lean_mkAppB(v___y_1556_, v___y_1555_, v___y_1558_);
v___x_1560_ = l_Lean_Expr_app___override(v___y_1557_, v___x_1559_);
v___y_1540_ = v___y_1554_;
v___y_1541_ = v___x_1560_;
goto v___jp_1539_;
}
v___jp_1561_:
{
lean_object* v_upperBound_1567_; lean_object* v___x_1568_; 
v_upperBound_1567_ = lean_ctor_get(v_t_1501_, 1);
v___x_1568_ = l_Lean_Expr_app___override(v___y_1562_, v___y_1566_);
if (lean_obj_tag(v_upperBound_1567_) == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec_ref(v___y_1565_);
v___x_1569_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1570_ = l_Lean_Expr_app___override(v___x_1569_, v___y_1564_);
v___x_1571_ = l_Lean_Expr_app___override(v___x_1568_, v___x_1570_);
v___y_1540_ = v___y_1563_;
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
v___x_1578_ = l_Lean_Name_mkStr2(v___y_1565_, v___x_1577_);
v___x_1579_ = l_Lean_Expr_const___override(v___x_1578_, v___x_1509_);
v___x_1580_ = lean_int_neg(v_val_1572_);
v___x_1581_ = l_Int_toNat(v___x_1580_);
lean_dec(v___x_1580_);
v___x_1582_ = l_Lean_instToExprInt_mkNat(v___x_1581_);
lean_inc_ref(v___y_1564_);
v___x_1583_ = l_Lean_mkApp3(v___x_1576_, v___y_1564_, v___x_1579_, v___x_1582_);
v___y_1554_ = v___y_1563_;
v___y_1555_ = v___y_1564_;
v___y_1556_ = v___x_1573_;
v___y_1557_ = v___x_1568_;
v___y_1558_ = v___x_1583_;
goto v___jp_1553_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec_ref(v___y_1565_);
v___x_1584_ = l_Int_toNat(v_val_1572_);
v___x_1585_ = l_Lean_instToExprInt_mkNat(v___x_1584_);
v___y_1554_ = v___y_1563_;
v___y_1555_ = v___y_1564_;
v___y_1556_ = v___x_1573_;
v___y_1557_ = v___x_1568_;
v___y_1558_ = v___x_1585_;
goto v___jp_1553_;
}
}
}
v___jp_1586_:
{
lean_object* v___x_1593_; 
lean_inc_ref(v___y_1589_);
v___x_1593_ = l_Lean_mkAppB(v___y_1590_, v___y_1589_, v___y_1592_);
v___y_1562_ = v___y_1587_;
v___y_1563_ = v___y_1588_;
v___y_1564_ = v___y_1589_;
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
v___y_1562_ = v___x_1597_;
v___y_1563_ = v___y_1595_;
v___y_1564_ = v_type_1599_;
v___y_1565_ = v___x_1598_;
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
v___y_1587_ = v___x_1597_;
v___y_1588_ = v___y_1595_;
v___y_1589_ = v_type_1599_;
v___y_1590_ = v___x_1602_;
v___y_1591_ = v___x_1598_;
v___y_1592_ = v___x_1610_;
goto v___jp_1586_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = l_Int_toNat(v_val_1601_);
v___x_1612_ = l_Lean_instToExprInt_mkNat(v___x_1611_);
v___y_1587_ = v___x_1597_;
v___y_1588_ = v___y_1595_;
v___y_1589_ = v_type_1599_;
v___y_1590_ = v___x_1602_;
v___y_1591_ = v___x_1598_;
v___y_1592_ = v___x_1612_;
goto v___jp_1586_;
}
}
}
v___jp_1617_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
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
lean_inc_ref(v_v_1725_);
v___x_1748_ = l_Lean_mkAppB(v___x_1747_, v_v_1725_, v_i_1735_);
v___x_1749_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc_ref(v_v_1725_);
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
lean_object* v___x_1806_; lean_object* v_toApplicative_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1932_; 
v___x_1806_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1);
v_toApplicative_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v___x_1806_, 1);
lean_dec(v_unused_1933_);
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1932_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_toApplicative_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1932_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v_toFunctor_1811_; lean_object* v_toSeq_1812_; lean_object* v_toSeqLeft_1813_; lean_object* v_toSeqRight_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1930_; 
v_toFunctor_1811_ = lean_ctor_get(v_toApplicative_1807_, 0);
v_toSeq_1812_ = lean_ctor_get(v_toApplicative_1807_, 2);
v_toSeqLeft_1813_ = lean_ctor_get(v_toApplicative_1807_, 3);
v_toSeqRight_1814_ = lean_ctor_get(v_toApplicative_1807_, 4);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_toApplicative_1807_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v_toApplicative_1807_, 1);
lean_dec(v_unused_1931_);
v___x_1816_ = v_toApplicative_1807_;
v_isShared_1817_ = v_isSharedCheck_1930_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_toSeqRight_1814_);
lean_inc(v_toSeqLeft_1813_);
lean_inc(v_toSeq_1812_);
lean_inc(v_toFunctor_1811_);
lean_dec(v_toApplicative_1807_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1930_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___f_1818_; lean_object* v___f_1819_; lean_object* v___f_1820_; lean_object* v___f_1821_; lean_object* v___x_1822_; lean_object* v___f_1823_; lean_object* v___f_1824_; lean_object* v___f_1825_; lean_object* v___x_1827_; 
v___f_1818_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2));
v___f_1819_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3));
lean_inc_ref(v_toFunctor_1811_);
v___f_1820_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1820_, 0, v_toFunctor_1811_);
v___f_1821_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1821_, 0, v_toFunctor_1811_);
v___x_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___f_1820_);
lean_ctor_set(v___x_1822_, 1, v___f_1821_);
v___f_1823_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1823_, 0, v_toSeqRight_1814_);
v___f_1824_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1824_, 0, v_toSeqLeft_1813_);
v___f_1825_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1825_, 0, v_toSeq_1812_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 4, v___f_1823_);
lean_ctor_set(v___x_1816_, 3, v___f_1824_);
lean_ctor_set(v___x_1816_, 2, v___f_1825_);
lean_ctor_set(v___x_1816_, 1, v___f_1818_);
lean_ctor_set(v___x_1816_, 0, v___x_1822_);
v___x_1827_ = v___x_1816_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1822_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___f_1818_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v___f_1825_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v___f_1824_);
lean_ctor_set(v_reuseFailAlloc_1929_, 4, v___f_1823_);
v___x_1827_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1829_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v___f_1819_);
lean_ctor_set(v___x_1809_, 0, v___x_1827_);
v___x_1829_ = v___x_1809_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v___f_1819_);
v___x_1829_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1830_; lean_object* v_toApplicative_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1926_; 
v___x_1830_ = l_StateRefT_x27_instMonad___redArg(v___x_1829_);
v_toApplicative_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v___x_1830_, 1);
lean_dec(v_unused_1927_);
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1926_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_toApplicative_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1926_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_toFunctor_1835_; lean_object* v_toSeq_1836_; lean_object* v_toSeqLeft_1837_; lean_object* v_toSeqRight_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1924_; 
v_toFunctor_1835_ = lean_ctor_get(v_toApplicative_1831_, 0);
v_toSeq_1836_ = lean_ctor_get(v_toApplicative_1831_, 2);
v_toSeqLeft_1837_ = lean_ctor_get(v_toApplicative_1831_, 3);
v_toSeqRight_1838_ = lean_ctor_get(v_toApplicative_1831_, 4);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_toApplicative_1831_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v_toApplicative_1831_, 1);
lean_dec(v_unused_1925_);
v___x_1840_ = v_toApplicative_1831_;
v_isShared_1841_ = v_isSharedCheck_1924_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_toSeqRight_1838_);
lean_inc(v_toSeqLeft_1837_);
lean_inc(v_toSeq_1836_);
lean_inc(v_toFunctor_1835_);
lean_dec(v_toApplicative_1831_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1924_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___f_1842_; lean_object* v___f_1843_; lean_object* v___f_1844_; lean_object* v___f_1845_; lean_object* v___x_1846_; lean_object* v___f_1847_; lean_object* v___f_1848_; lean_object* v___f_1849_; lean_object* v___x_1851_; 
v___f_1842_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4));
v___f_1843_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5));
lean_inc_ref(v_toFunctor_1835_);
v___f_1844_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1844_, 0, v_toFunctor_1835_);
v___f_1845_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1845_, 0, v_toFunctor_1835_);
v___x_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___f_1844_);
lean_ctor_set(v___x_1846_, 1, v___f_1845_);
v___f_1847_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1847_, 0, v_toSeqRight_1838_);
v___f_1848_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1848_, 0, v_toSeqLeft_1837_);
v___f_1849_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1849_, 0, v_toSeq_1836_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 4, v___f_1847_);
lean_ctor_set(v___x_1840_, 3, v___f_1848_);
lean_ctor_set(v___x_1840_, 2, v___f_1849_);
lean_ctor_set(v___x_1840_, 1, v___f_1842_);
lean_ctor_set(v___x_1840_, 0, v___x_1846_);
v___x_1851_ = v___x_1840_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v___f_1842_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v___f_1849_);
lean_ctor_set(v_reuseFailAlloc_1923_, 3, v___f_1848_);
lean_ctor_set(v_reuseFailAlloc_1923_, 4, v___f_1847_);
v___x_1851_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___f_1843_);
lean_ctor_set(v___x_1833_, 0, v___x_1851_);
v___x_1853_ = v___x_1833_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v___f_1843_);
v___x_1853_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1854_ = l_StateRefT_x27_instMonad___redArg(v___x_1853_);
v___x_1855_ = l_ReaderT_instMonad___redArg(v___x_1854_);
v___x_1856_ = l_ReaderT_instMonad___redArg(v___x_1855_);
v___x_1857_ = l_StateRefT_x27_instMonad___redArg(v___x_1856_);
v___x_1858_ = l_StateRefT_x27_instMonad___redArg(v___x_1857_);
switch(lean_obj_tag(v_x_1795_))
{
case 0:
{
lean_object* v_i_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_3965__overap_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec_ref(v_v_1793_);
v_i_1859_ = lean_ctor_get(v_x_1795_, 2);
lean_inc(v_i_1859_);
lean_dec_ref(v_x_1795_);
v___x_1860_ = l_Lean_instInhabitedExpr;
v___x_1861_ = l_instInhabitedOfMonad___redArg(v___x_1858_, v___x_1860_);
v___x_3965__overap_1862_ = lean_array_get_borrowed(v___x_1861_, v_assumptions_1794_, v_i_1859_);
lean_dec(v_i_1859_);
v___x_1863_ = lean_box(v_a_1799_);
lean_inc(v___x_3965__overap_1862_);
lean_inc(v_a_1804_);
lean_inc_ref(v_a_1803_);
lean_inc(v_a_1802_);
lean_inc_ref(v_a_1801_);
lean_inc(v_a_1800_);
lean_inc_ref(v_a_1798_);
lean_inc(v_a_1797_);
lean_inc(v_a_1796_);
v___x_1864_ = lean_apply_10(v___x_3965__overap_1862_, v_a_1796_, v_a_1797_, v_a_1798_, v___x_1863_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, lean_box(0));
return v___x_1864_;
}
case 1:
{
lean_object* v_s_1865_; lean_object* v_c_1866_; lean_object* v_j_1867_; lean_object* v___x_1868_; 
lean_dec_ref(v___x_1858_);
v_s_1865_ = lean_ctor_get(v_x_1795_, 0);
lean_inc_ref(v_s_1865_);
v_c_1866_ = lean_ctor_get(v_x_1795_, 1);
lean_inc(v_c_1866_);
v_j_1867_ = lean_ctor_get(v_x_1795_, 2);
lean_inc_ref(v_j_1867_);
lean_dec_ref(v_x_1795_);
lean_inc_ref(v_v_1793_);
v___x_1868_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1866_, v_v_1793_, v_assumptions_1794_, v_j_1867_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1877_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1865_, v_c_1866_, v_v_1793_, v_a_1869_);
lean_dec(v_c_1866_);
lean_dec_ref(v_s_1865_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1873_);
v___x_1875_ = v___x_1871_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
else
{
lean_dec(v_c_1866_);
lean_dec_ref(v_s_1865_);
lean_dec_ref(v_v_1793_);
return v___x_1868_;
}
}
case 2:
{
lean_object* v_s_1878_; lean_object* v_t_1879_; lean_object* v_j_1880_; lean_object* v_k_1881_; lean_object* v___x_1882_; 
lean_dec_ref(v___x_1858_);
v_s_1878_ = lean_ctor_get(v_x_1795_, 0);
lean_inc_ref(v_s_1878_);
v_t_1879_ = lean_ctor_get(v_x_1795_, 1);
lean_inc_ref(v_t_1879_);
v_j_1880_ = lean_ctor_get(v_x_1795_, 3);
lean_inc_ref(v_j_1880_);
v_k_1881_ = lean_ctor_get(v_x_1795_, 4);
lean_inc_ref(v_k_1881_);
lean_dec_ref(v_x_1795_);
lean_inc_ref(v_v_1793_);
v___x_1882_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1792_, v_v_1793_, v_assumptions_1794_, v_j_1880_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1884_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
lean_inc_ref(v_v_1793_);
v___x_1884_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1792_, v_v_1793_, v_assumptions_1794_, v_k_1881_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
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
v___x_1889_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1878_, v_t_1879_, v_c_1792_, v_v_1793_, v_a_1883_, v_a_1885_);
lean_dec_ref(v_t_1879_);
lean_dec_ref(v_s_1878_);
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
lean_dec(v_a_1883_);
lean_dec_ref(v_t_1879_);
lean_dec_ref(v_s_1878_);
lean_dec_ref(v_v_1793_);
return v___x_1884_;
}
}
else
{
lean_dec_ref(v_k_1881_);
lean_dec_ref(v_t_1879_);
lean_dec_ref(v_s_1878_);
lean_dec_ref(v_v_1793_);
return v___x_1882_;
}
}
case 3:
{
lean_object* v_s_1894_; lean_object* v_t_1895_; lean_object* v_x_1896_; lean_object* v_y_1897_; lean_object* v_a_1898_; lean_object* v_j_1899_; lean_object* v_b_1900_; lean_object* v_k_1901_; lean_object* v___x_1902_; 
lean_dec_ref(v___x_1858_);
v_s_1894_ = lean_ctor_get(v_x_1795_, 0);
lean_inc_ref(v_s_1894_);
v_t_1895_ = lean_ctor_get(v_x_1795_, 1);
lean_inc_ref(v_t_1895_);
v_x_1896_ = lean_ctor_get(v_x_1795_, 2);
lean_inc(v_x_1896_);
v_y_1897_ = lean_ctor_get(v_x_1795_, 3);
lean_inc(v_y_1897_);
v_a_1898_ = lean_ctor_get(v_x_1795_, 4);
lean_inc(v_a_1898_);
v_j_1899_ = lean_ctor_get(v_x_1795_, 5);
lean_inc_ref(v_j_1899_);
v_b_1900_ = lean_ctor_get(v_x_1795_, 6);
lean_inc(v_b_1900_);
v_k_1901_ = lean_ctor_get(v_x_1795_, 7);
lean_inc_ref(v_k_1901_);
lean_dec_ref(v_x_1795_);
lean_inc_ref(v_v_1793_);
v___x_1902_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1896_, v_v_1793_, v_assumptions_1794_, v_j_1899_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref(v___x_1902_);
lean_inc_ref(v_v_1793_);
v___x_1904_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_y_1897_, v_v_1793_, v_assumptions_1794_, v_k_1901_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1913_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1894_, v_t_1895_, v_a_1898_, v_x_1896_, v_b_1900_, v_y_1897_, v_v_1793_, v_a_1903_, v_a_1905_);
lean_dec(v_y_1897_);
lean_dec(v_b_1900_);
lean_dec(v_x_1896_);
lean_dec(v_a_1898_);
lean_dec_ref(v_t_1895_);
lean_dec_ref(v_s_1894_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
else
{
lean_dec(v_a_1903_);
lean_dec(v_b_1900_);
lean_dec(v_a_1898_);
lean_dec(v_y_1897_);
lean_dec(v_x_1896_);
lean_dec_ref(v_t_1895_);
lean_dec_ref(v_s_1894_);
lean_dec_ref(v_v_1793_);
return v___x_1904_;
}
}
else
{
lean_dec_ref(v_k_1901_);
lean_dec(v_b_1900_);
lean_dec(v_a_1898_);
lean_dec(v_y_1897_);
lean_dec(v_x_1896_);
lean_dec_ref(v_t_1895_);
lean_dec_ref(v_s_1894_);
lean_dec_ref(v_v_1793_);
return v___x_1902_;
}
}
default: 
{
lean_object* v_m_1914_; lean_object* v_r_1915_; lean_object* v_i_1916_; lean_object* v_x_1917_; lean_object* v_j_1918_; lean_object* v___x_1919_; 
lean_dec_ref(v___x_1858_);
v_m_1914_ = lean_ctor_get(v_x_1795_, 0);
lean_inc(v_m_1914_);
v_r_1915_ = lean_ctor_get(v_x_1795_, 1);
lean_inc(v_r_1915_);
v_i_1916_ = lean_ctor_get(v_x_1795_, 2);
lean_inc(v_i_1916_);
v_x_1917_ = lean_ctor_get(v_x_1795_, 3);
lean_inc(v_x_1917_);
v_j_1918_ = lean_ctor_get(v_x_1795_, 4);
lean_inc_ref(v_j_1918_);
lean_dec_ref(v_x_1795_);
lean_inc_ref(v_v_1793_);
v___x_1919_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1917_, v_v_1793_, v_assumptions_1794_, v_j_1918_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref(v___x_1919_);
v___x_1921_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1914_, v_r_1915_, v_i_1916_, v_x_1917_, v_v_1793_, v_a_1920_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec(v_x_1917_);
lean_dec(v_r_1915_);
return v___x_1921_;
}
else
{
lean_dec(v_x_1917_);
lean_dec(v_i_1916_);
lean_dec(v_r_1915_);
lean_dec(v_m_1914_);
lean_dec_ref(v_v_1793_);
return v___x_1919_;
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
lean_dec_ref(v___x_1994_);
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
lean_inc(v_b_2012_);
lean_inc(v_coeffs_2014_);
lean_inc(v_a_2010_);
v___x_2023_ = l_Lean_Omega_IntList_combo(v_a_2010_, v_coeffs_2014_, v_b_2012_, v_coeffs_2017_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object* v_x_2095_){
_start:
{
lean_object* v_snd_2096_; lean_object* v_constraint_2097_; lean_object* v_fst_2098_; lean_object* v_lowerBound_2099_; lean_object* v_upperBound_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___y_2106_; lean_object* v___y_2107_; 
v_snd_2096_ = lean_ctor_get(v_x_2095_, 1);
v_constraint_2097_ = lean_ctor_get(v_snd_2096_, 1);
lean_inc_ref(v_constraint_2097_);
v_fst_2098_ = lean_ctor_get(v_x_2095_, 0);
lean_inc(v_fst_2098_);
lean_dec_ref(v_x_2095_);
v_lowerBound_2099_ = lean_ctor_get(v_constraint_2097_, 0);
lean_inc(v_lowerBound_2099_);
v_upperBound_2100_ = lean_ctor_get(v_constraint_2097_, 1);
lean_inc(v_upperBound_2100_);
lean_dec_ref(v_constraint_2097_);
v___x_2101_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0___closed__0));
v___x_2102_ = l_List_toString___redArg(v___x_2101_, v_fst_2098_);
v___x_2103_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_2104_ = lean_string_append(v___x_2102_, v___x_2103_);
if (lean_obj_tag(v_lowerBound_2099_) == 0)
{
if (lean_obj_tag(v_upperBound_2100_) == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_2113_ = lean_string_append(v___x_2104_, v___x_2112_);
return v___x_2113_;
}
else
{
lean_object* v_val_2114_; lean_object* v___x_2115_; lean_object* v___y_2117_; lean_object* v_intZero_2122_; uint8_t v_isNeg_2123_; 
v_val_2114_ = lean_ctor_get(v_upperBound_2100_, 0);
lean_inc(v_val_2114_);
lean_dec_ref(v_upperBound_2100_);
v___x_2115_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_2122_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2123_ = lean_int_dec_lt(v_val_2114_, v_intZero_2122_);
if (v_isNeg_2123_ == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2125_; 
v_a_2124_ = lean_nat_abs(v_val_2114_);
lean_dec(v_val_2114_);
v___x_2125_ = l_Nat_reprFast(v_a_2124_);
v___y_2117_ = v___x_2125_;
goto v___jp_2116_;
}
else
{
lean_object* v_abs_2126_; lean_object* v_one_2127_; lean_object* v_a_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_abs_2126_ = lean_nat_abs(v_val_2114_);
lean_dec(v_val_2114_);
v_one_2127_ = lean_unsigned_to_nat(1u);
v_a_2128_ = lean_nat_sub(v_abs_2126_, v_one_2127_);
lean_dec(v_abs_2126_);
v___x_2129_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2130_ = lean_nat_add(v_a_2128_, v_one_2127_);
lean_dec(v_a_2128_);
v___x_2131_ = l_Nat_reprFast(v___x_2130_);
v___x_2132_ = lean_string_append(v___x_2129_, v___x_2131_);
lean_dec_ref(v___x_2131_);
v___y_2117_ = v___x_2132_;
goto v___jp_2116_;
}
v___jp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2118_ = lean_string_append(v___x_2115_, v___y_2117_);
lean_dec_ref(v___y_2117_);
v___x_2119_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2120_ = lean_string_append(v___x_2118_, v___x_2119_);
v___x_2121_ = lean_string_append(v___x_2104_, v___x_2120_);
lean_dec_ref(v___x_2120_);
return v___x_2121_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_2100_) == 0)
{
lean_object* v_val_2133_; lean_object* v___x_2134_; lean_object* v___y_2136_; lean_object* v_intZero_2141_; uint8_t v_isNeg_2142_; 
v_val_2133_ = lean_ctor_get(v_lowerBound_2099_, 0);
lean_inc(v_val_2133_);
lean_dec_ref(v_lowerBound_2099_);
v___x_2134_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2141_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2142_ = lean_int_dec_lt(v_val_2133_, v_intZero_2141_);
if (v_isNeg_2142_ == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; 
v_a_2143_ = lean_nat_abs(v_val_2133_);
lean_dec(v_val_2133_);
v___x_2144_ = l_Nat_reprFast(v_a_2143_);
v___y_2136_ = v___x_2144_;
goto v___jp_2135_;
}
else
{
lean_object* v_abs_2145_; lean_object* v_one_2146_; lean_object* v_a_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_abs_2145_ = lean_nat_abs(v_val_2133_);
lean_dec(v_val_2133_);
v_one_2146_ = lean_unsigned_to_nat(1u);
v_a_2147_ = lean_nat_sub(v_abs_2145_, v_one_2146_);
lean_dec(v_abs_2145_);
v___x_2148_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2149_ = lean_nat_add(v_a_2147_, v_one_2146_);
lean_dec(v_a_2147_);
v___x_2150_ = l_Nat_reprFast(v___x_2149_);
v___x_2151_ = lean_string_append(v___x_2148_, v___x_2150_);
lean_dec_ref(v___x_2150_);
v___y_2136_ = v___x_2151_;
goto v___jp_2135_;
}
v___jp_2135_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2137_ = lean_string_append(v___x_2134_, v___y_2136_);
lean_dec_ref(v___y_2136_);
v___x_2138_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_2139_ = lean_string_append(v___x_2137_, v___x_2138_);
v___x_2140_ = lean_string_append(v___x_2104_, v___x_2139_);
lean_dec_ref(v___x_2139_);
return v___x_2140_;
}
}
else
{
lean_object* v_val_2152_; lean_object* v_val_2153_; uint8_t v___x_2154_; 
v_val_2152_ = lean_ctor_get(v_lowerBound_2099_, 0);
lean_inc(v_val_2152_);
lean_dec_ref(v_lowerBound_2099_);
v_val_2153_ = lean_ctor_get(v_upperBound_2100_, 0);
lean_inc(v_val_2153_);
lean_dec_ref(v_upperBound_2100_);
v___x_2154_ = lean_int_dec_lt(v_val_2153_, v_val_2152_);
if (v___x_2154_ == 0)
{
uint8_t v___x_2155_; 
v___x_2155_ = lean_int_dec_eq(v_val_2152_, v_val_2153_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___y_2158_; lean_object* v_intZero_2173_; uint8_t v_isNeg_2174_; 
v___x_2156_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2173_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2174_ = lean_int_dec_lt(v_val_2152_, v_intZero_2173_);
if (v_isNeg_2174_ == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; 
v_a_2175_ = lean_nat_abs(v_val_2152_);
lean_dec(v_val_2152_);
v___x_2176_ = l_Nat_reprFast(v_a_2175_);
v___y_2158_ = v___x_2176_;
goto v___jp_2157_;
}
else
{
lean_object* v_abs_2177_; lean_object* v_one_2178_; lean_object* v_a_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_abs_2177_ = lean_nat_abs(v_val_2152_);
lean_dec(v_val_2152_);
v_one_2178_ = lean_unsigned_to_nat(1u);
v_a_2179_ = lean_nat_sub(v_abs_2177_, v_one_2178_);
lean_dec(v_abs_2177_);
v___x_2180_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2181_ = lean_nat_add(v_a_2179_, v_one_2178_);
lean_dec(v_a_2179_);
v___x_2182_ = l_Nat_reprFast(v___x_2181_);
v___x_2183_ = lean_string_append(v___x_2180_, v___x_2182_);
lean_dec_ref(v___x_2182_);
v___y_2158_ = v___x_2183_;
goto v___jp_2157_;
}
v___jp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v_intZero_2162_; uint8_t v_isNeg_2163_; 
v___x_2159_ = lean_string_append(v___x_2156_, v___y_2158_);
lean_dec_ref(v___y_2158_);
v___x_2160_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_2161_ = lean_string_append(v___x_2159_, v___x_2160_);
v_intZero_2162_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2163_ = lean_int_dec_lt(v_val_2153_, v_intZero_2162_);
if (v_isNeg_2163_ == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2165_; 
v_a_2164_ = lean_nat_abs(v_val_2153_);
lean_dec(v_val_2153_);
v___x_2165_ = l_Nat_reprFast(v_a_2164_);
v___y_2106_ = v___x_2161_;
v___y_2107_ = v___x_2165_;
goto v___jp_2105_;
}
else
{
lean_object* v_abs_2166_; lean_object* v_one_2167_; lean_object* v_a_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_abs_2166_ = lean_nat_abs(v_val_2153_);
lean_dec(v_val_2153_);
v_one_2167_ = lean_unsigned_to_nat(1u);
v_a_2168_ = lean_nat_sub(v_abs_2166_, v_one_2167_);
lean_dec(v_abs_2166_);
v___x_2169_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2170_ = lean_nat_add(v_a_2168_, v_one_2167_);
lean_dec(v_a_2168_);
v___x_2171_ = l_Nat_reprFast(v___x_2170_);
v___x_2172_ = lean_string_append(v___x_2169_, v___x_2171_);
lean_dec_ref(v___x_2171_);
v___y_2106_ = v___x_2161_;
v___y_2107_ = v___x_2172_;
goto v___jp_2105_;
}
}
}
else
{
lean_object* v___x_2184_; lean_object* v___y_2186_; lean_object* v_intZero_2191_; uint8_t v_isNeg_2192_; 
lean_dec(v_val_2153_);
v___x_2184_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_2191_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2192_ = lean_int_dec_lt(v_val_2152_, v_intZero_2191_);
if (v_isNeg_2192_ == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; 
v_a_2193_ = lean_nat_abs(v_val_2152_);
lean_dec(v_val_2152_);
v___x_2194_ = l_Nat_reprFast(v_a_2193_);
v___y_2186_ = v___x_2194_;
goto v___jp_2185_;
}
else
{
lean_object* v_abs_2195_; lean_object* v_one_2196_; lean_object* v_a_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_abs_2195_ = lean_nat_abs(v_val_2152_);
lean_dec(v_val_2152_);
v_one_2196_ = lean_unsigned_to_nat(1u);
v_a_2197_ = lean_nat_sub(v_abs_2195_, v_one_2196_);
lean_dec(v_abs_2195_);
v___x_2198_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2199_ = lean_nat_add(v_a_2197_, v_one_2196_);
lean_dec(v_a_2197_);
v___x_2200_ = l_Nat_reprFast(v___x_2199_);
v___x_2201_ = lean_string_append(v___x_2198_, v___x_2200_);
lean_dec_ref(v___x_2200_);
v___y_2186_ = v___x_2201_;
goto v___jp_2185_;
}
v___jp_2185_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2187_ = lean_string_append(v___x_2184_, v___y_2186_);
lean_dec_ref(v___y_2186_);
v___x_2188_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_2189_ = lean_string_append(v___x_2187_, v___x_2188_);
v___x_2190_ = lean_string_append(v___x_2104_, v___x_2189_);
lean_dec_ref(v___x_2189_);
return v___x_2190_;
}
}
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_dec(v_val_2153_);
lean_dec(v_val_2152_);
v___x_2202_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_2203_ = lean_string_append(v___x_2104_, v___x_2202_);
return v___x_2203_;
}
}
}
v___jp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2108_ = lean_string_append(v___y_2106_, v___y_2107_);
lean_dec_ref(v___y_2107_);
v___x_2109_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2110_ = lean_string_append(v___x_2108_, v___x_2109_);
v___x_2111_ = lean_string_append(v___x_2104_, v___x_2110_);
lean_dec_ref(v___x_2110_);
return v___x_2111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object* v_a_2204_, lean_object* v_b_2205_, lean_object* v_d_2206_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_a_2204_);
lean_ctor_set(v___x_2207_, 1, v_b_2205_);
v___x_2208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v_d_2206_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2(lean_object* v___x_2209_, lean_object* v___f_2210_, lean_object* v_l_2211_, lean_object* v_acc_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2209_, v___f_2210_, v_acc_2212_, v_l_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3(lean_object* v___f_2235_, lean_object* v___f_2236_, lean_object* v_p_2237_){
_start:
{
uint8_t v_possible_2238_; 
v_possible_2238_ = lean_ctor_get_uint8(v_p_2237_, sizeof(void*)*7);
if (v_possible_2238_ == 0)
{
lean_object* v___x_2239_; 
lean_dec_ref(v_p_2237_);
lean_dec_ref(v___f_2236_);
lean_dec_ref(v___f_2235_);
v___x_2239_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
return v___x_2239_;
}
else
{
lean_object* v_constraints_2240_; uint8_t v___x_2241_; 
v_constraints_2240_ = lean_ctor_get(v_p_2237_, 2);
lean_inc_ref(v_constraints_2240_);
v___x_2241_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2237_);
lean_dec_ref(v_p_2237_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; lean_object* v_buckets_2243_; lean_object* v___x_2244_; lean_object* v___y_2246_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; uint8_t v___x_2253_; 
v___x_2242_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10));
v_buckets_2243_ = lean_ctor_get(v_constraints_2240_, 1);
lean_inc_ref(v_buckets_2243_);
lean_dec_ref(v_constraints_2240_);
v___x_2244_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_2250_ = lean_box(0);
v___x_2251_ = lean_array_get_size(v_buckets_2243_);
v___x_2252_ = lean_unsigned_to_nat(0u);
v___x_2253_ = lean_nat_dec_lt(v___x_2252_, v___x_2251_);
if (v___x_2253_ == 0)
{
lean_dec_ref(v_buckets_2243_);
lean_dec_ref(v___f_2236_);
v___y_2246_ = v___x_2250_;
goto v___jp_2245_;
}
else
{
lean_object* v___f_2254_; size_t v___x_2255_; size_t v___x_2256_; lean_object* v___x_2257_; 
v___f_2254_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2), 4, 2);
lean_closure_set(v___f_2254_, 0, v___x_2242_);
lean_closure_set(v___f_2254_, 1, v___f_2236_);
v___x_2255_ = lean_usize_of_nat(v___x_2251_);
v___x_2256_ = ((size_t)0ULL);
v___x_2257_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2242_, v___f_2254_, v_buckets_2243_, v___x_2255_, v___x_2256_, v___x_2250_);
v___y_2246_ = v___x_2257_;
goto v___jp_2245_;
}
v___jp_2245_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = lean_box(0);
v___x_2248_ = l_List_mapTR_loop___redArg(v___f_2235_, v___y_2246_, v___x_2247_);
v___x_2249_ = l_String_intercalate(v___x_2244_, v___x_2248_);
return v___x_2249_;
}
}
else
{
lean_object* v___x_2258_; 
lean_dec_ref(v_constraints_2240_);
lean_dec_ref(v___f_2236_);
lean_dec_ref(v___f_2235_);
v___x_2258_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
return v___x_2258_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = lean_box(0);
v___x_2272_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1));
v___x_2273_ = l_Lean_Expr_const___override(v___x_2272_, v___x_2271_);
return v___x_2273_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_box(0);
v___x_2280_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5));
v___x_2281_ = l_Lean_Expr_const___override(v___x_2280_, v___x_2279_);
return v___x_2281_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = lean_box(0);
v___x_2289_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8));
v___x_2290_ = l_Lean_Expr_const___override(v___x_2289_, v___x_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse(lean_object* v_s_2291_, lean_object* v_x_2292_, lean_object* v_j_2293_, lean_object* v_assumptions_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, uint8_t v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2296_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref(v___x_2305_);
lean_inc(v_a_2306_);
v___x_2307_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_2292_, v_a_2306_, v_assumptions_2294_, v_j_2293_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2309_; lean_object* v_lowerBound_2310_; lean_object* v_upperBound_2311_; lean_object* v_nil_2312_; lean_object* v_cons_2313_; lean_object* v___x_2314_; lean_object* v___y_2316_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___x_2339_; lean_object* v___y_2341_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref(v___x_2307_);
v___x_2309_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_lowerBound_2310_ = lean_ctor_get(v_s_2291_, 0);
v_upperBound_2311_ = lean_ctor_get(v_s_2291_, 1);
v_nil_2312_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2313_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2314_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2312_, v_cons_2313_, v_x_2292_);
v___x_2339_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
if (lean_obj_tag(v_lowerBound_2310_) == 0)
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_2341_ = v___x_2357_;
goto v___jp_2340_;
}
else
{
lean_object* v_val_2358_; lean_object* v___x_2359_; lean_object* v___y_2361_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v_val_2358_ = lean_ctor_get(v_lowerBound_2310_, 0);
v___x_2359_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2363_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2364_ = lean_int_dec_le(v___x_2363_, v_val_2358_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2365_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2366_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2367_ = lean_int_neg(v_val_2358_);
v___x_2368_ = l_Int_toNat(v___x_2367_);
lean_dec(v___x_2367_);
v___x_2369_ = l_Lean_instToExprInt_mkNat(v___x_2368_);
v___x_2370_ = l_Lean_mkApp3(v___x_2365_, v___x_2309_, v___x_2366_, v___x_2369_);
v___y_2361_ = v___x_2370_;
goto v___jp_2360_;
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = l_Int_toNat(v_val_2358_);
v___x_2372_ = l_Lean_instToExprInt_mkNat(v___x_2371_);
v___y_2361_ = v___x_2372_;
goto v___jp_2360_;
}
v___jp_2360_:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_mkAppB(v___x_2359_, v___x_2309_, v___y_2361_);
v___y_2341_ = v___x_2362_;
goto v___jp_2340_;
}
}
v___jp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2317_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2);
lean_inc_ref(v___y_2316_);
v___x_2318_ = l_Lean_Expr_app___override(v___x_2317_, v___y_2316_);
v___x_2319_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6);
v___x_2320_ = l_Lean_Meta_mkEq(v___x_2318_, v___x_2319_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2322_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref(v___x_2320_);
v___x_2322_ = l_Lean_Meta_mkDecideProof(v_a_2321_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2332_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2332_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2332_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2327_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9);
v___x_2328_ = l_Lean_mkApp5(v___x_2327_, v___y_2316_, v_a_2323_, v___x_2314_, v_a_2306_, v_a_2308_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2328_);
v___x_2330_ = v___x_2325_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
else
{
lean_dec_ref(v___y_2316_);
lean_dec_ref(v___x_2314_);
lean_dec(v_a_2308_);
lean_dec(v_a_2306_);
return v___x_2322_;
}
}
else
{
lean_dec_ref(v___y_2316_);
lean_dec_ref(v___x_2314_);
lean_dec(v_a_2308_);
lean_dec(v_a_2306_);
return v___x_2320_;
}
}
v___jp_2333_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = l_Lean_mkAppB(v___y_2334_, v___x_2309_, v___y_2336_);
v___x_2338_ = l_Lean_Expr_app___override(v___y_2335_, v___x_2337_);
v___y_2316_ = v___x_2338_;
goto v___jp_2315_;
}
v___jp_2340_:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_Expr_app___override(v___x_2339_, v___y_2341_);
if (lean_obj_tag(v_upperBound_2311_) == 0)
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_2344_ = l_Lean_Expr_app___override(v___x_2342_, v___x_2343_);
v___y_2316_ = v___x_2344_;
goto v___jp_2315_;
}
else
{
lean_object* v_val_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v_val_2345_ = lean_ctor_get(v_upperBound_2311_, 0);
v___x_2346_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2347_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2348_ = lean_int_dec_le(v___x_2347_, v_val_2345_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2349_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2350_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2351_ = lean_int_neg(v_val_2345_);
v___x_2352_ = l_Int_toNat(v___x_2351_);
lean_dec(v___x_2351_);
v___x_2353_ = l_Lean_instToExprInt_mkNat(v___x_2352_);
v___x_2354_ = l_Lean_mkApp3(v___x_2349_, v___x_2309_, v___x_2350_, v___x_2353_);
v___y_2334_ = v___x_2346_;
v___y_2335_ = v___x_2342_;
v___y_2336_ = v___x_2354_;
goto v___jp_2333_;
}
else
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = l_Int_toNat(v_val_2345_);
v___x_2356_ = l_Lean_instToExprInt_mkNat(v___x_2355_);
v___y_2334_ = v___x_2346_;
v___y_2335_ = v___x_2342_;
v___y_2336_ = v___x_2356_;
goto v___jp_2333_;
}
}
}
}
else
{
lean_dec(v_a_2306_);
return v___x_2307_;
}
}
else
{
lean_dec_ref(v_j_2293_);
return v___x_2305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed(lean_object* v_s_2373_, lean_object* v_x_2374_, lean_object* v_j_2375_, lean_object* v_assumptions_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
uint8_t v_a_boxed_2387_; lean_object* v_res_2388_; 
v_a_boxed_2387_ = lean_unbox(v_a_2380_);
v_res_2388_ = l_Lean_Elab_Tactic_Omega_Problem_proveFalse(v_s_2373_, v_x_2374_, v_j_2375_, v_assumptions_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_boxed_2387_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_assumptions_2376_);
lean_dec(v_x_2374_);
lean_dec_ref(v_s_2373_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0(lean_object* v_constraint_2389_, lean_object* v_coeffs_2390_, lean_object* v_justification_2391_, lean_object* v_x_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_2389_, v_coeffs_2390_, v_justification_2391_);
return v___x_2393_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(lean_object* v_a_2394_, lean_object* v_x_2395_){
_start:
{
if (lean_obj_tag(v_x_2395_) == 0)
{
uint8_t v___x_2396_; 
v___x_2396_ = 0;
return v___x_2396_;
}
else
{
lean_object* v_key_2397_; lean_object* v_tail_2398_; uint8_t v___x_2399_; 
v_key_2397_ = lean_ctor_get(v_x_2395_, 0);
v_tail_2398_ = lean_ctor_get(v_x_2395_, 2);
v___x_2399_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2397_, v_a_2394_);
if (v___x_2399_ == 0)
{
v_x_2395_ = v_tail_2398_;
goto _start;
}
else
{
return v___x_2399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg___boxed(lean_object* v_a_2401_, lean_object* v_x_2402_){
_start:
{
uint8_t v_res_2403_; lean_object* v_r_2404_; 
v_res_2403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2401_, v_x_2402_);
lean_dec(v_x_2402_);
lean_dec(v_a_2401_);
v_r_2404_ = lean_box(v_res_2403_);
return v_r_2404_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(uint64_t v_x_2405_, lean_object* v_x_2406_){
_start:
{
if (lean_obj_tag(v_x_2406_) == 0)
{
return v_x_2405_;
}
else
{
lean_object* v_head_2407_; lean_object* v_tail_2408_; lean_object* v_intZero_2409_; uint8_t v_isNeg_2410_; 
v_head_2407_ = lean_ctor_get(v_x_2406_, 0);
v_tail_2408_ = lean_ctor_get(v_x_2406_, 1);
v_intZero_2409_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2410_ = lean_int_dec_lt(v_head_2407_, v_intZero_2409_);
if (v_isNeg_2410_ == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; uint64_t v___x_2414_; uint64_t v___x_2415_; 
v_a_2411_ = lean_nat_abs(v_head_2407_);
v___x_2412_ = lean_unsigned_to_nat(2u);
v___x_2413_ = lean_nat_mul(v___x_2412_, v_a_2411_);
lean_dec(v_a_2411_);
v___x_2414_ = lean_uint64_of_nat(v___x_2413_);
lean_dec(v___x_2413_);
v___x_2415_ = lean_uint64_mix_hash(v_x_2405_, v___x_2414_);
v_x_2405_ = v___x_2415_;
v_x_2406_ = v_tail_2408_;
goto _start;
}
else
{
lean_object* v_abs_2417_; lean_object* v_one_2418_; lean_object* v_a_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; uint64_t v___x_2423_; uint64_t v___x_2424_; 
v_abs_2417_ = lean_nat_abs(v_head_2407_);
v_one_2418_ = lean_unsigned_to_nat(1u);
v_a_2419_ = lean_nat_sub(v_abs_2417_, v_one_2418_);
lean_dec(v_abs_2417_);
v___x_2420_ = lean_unsigned_to_nat(2u);
v___x_2421_ = lean_nat_mul(v___x_2420_, v_a_2419_);
lean_dec(v_a_2419_);
v___x_2422_ = lean_nat_add(v___x_2421_, v_one_2418_);
lean_dec(v___x_2421_);
v___x_2423_ = lean_uint64_of_nat(v___x_2422_);
lean_dec(v___x_2422_);
v___x_2424_ = lean_uint64_mix_hash(v_x_2405_, v___x_2423_);
v_x_2405_ = v___x_2424_;
v_x_2406_ = v_tail_2408_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0___boxed(lean_object* v_x_2426_, lean_object* v_x_2427_){
_start:
{
uint64_t v_x_980__boxed_2428_; uint64_t v_res_2429_; lean_object* v_r_2430_; 
v_x_980__boxed_2428_ = lean_unbox_uint64(v_x_2426_);
lean_dec_ref(v_x_2426_);
v_res_2429_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v_x_980__boxed_2428_, v_x_2427_);
lean_dec(v_x_2427_);
v_r_2430_ = lean_box_uint64(v_res_2429_);
return v_r_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_2431_, lean_object* v_x_2432_){
_start:
{
if (lean_obj_tag(v_x_2432_) == 0)
{
return v_x_2431_;
}
else
{
lean_object* v_key_2433_; lean_object* v_value_2434_; lean_object* v_tail_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2459_; 
v_key_2433_ = lean_ctor_get(v_x_2432_, 0);
v_value_2434_ = lean_ctor_get(v_x_2432_, 1);
v_tail_2435_ = lean_ctor_get(v_x_2432_, 2);
v_isSharedCheck_2459_ = !lean_is_exclusive(v_x_2432_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2437_ = v_x_2432_;
v_isShared_2438_ = v_isSharedCheck_2459_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_tail_2435_);
lean_inc(v_value_2434_);
lean_inc(v_key_2433_);
lean_dec(v_x_2432_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2459_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; uint64_t v___x_2440_; uint64_t v___x_2441_; uint64_t v___x_2442_; uint64_t v___x_2443_; uint64_t v_fold_2444_; uint64_t v___x_2445_; uint64_t v___x_2446_; uint64_t v___x_2447_; size_t v___x_2448_; size_t v___x_2449_; size_t v___x_2450_; size_t v___x_2451_; size_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2439_ = lean_array_get_size(v_x_2431_);
v___x_2440_ = 7ULL;
v___x_2441_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2440_, v_key_2433_);
v___x_2442_ = 32ULL;
v___x_2443_ = lean_uint64_shift_right(v___x_2441_, v___x_2442_);
v_fold_2444_ = lean_uint64_xor(v___x_2441_, v___x_2443_);
v___x_2445_ = 16ULL;
v___x_2446_ = lean_uint64_shift_right(v_fold_2444_, v___x_2445_);
v___x_2447_ = lean_uint64_xor(v_fold_2444_, v___x_2446_);
v___x_2448_ = lean_uint64_to_usize(v___x_2447_);
v___x_2449_ = lean_usize_of_nat(v___x_2439_);
v___x_2450_ = ((size_t)1ULL);
v___x_2451_ = lean_usize_sub(v___x_2449_, v___x_2450_);
v___x_2452_ = lean_usize_land(v___x_2448_, v___x_2451_);
v___x_2453_ = lean_array_uget_borrowed(v_x_2431_, v___x_2452_);
lean_inc(v___x_2453_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 2, v___x_2453_);
v___x_2455_ = v___x_2437_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_key_2433_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_value_2434_);
lean_ctor_set(v_reuseFailAlloc_2458_, 2, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_array_uset(v_x_2431_, v___x_2452_, v___x_2455_);
v_x_2431_ = v___x_2456_;
v_x_2432_ = v_tail_2435_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(lean_object* v_i_2460_, lean_object* v_source_2461_, lean_object* v_target_2462_){
_start:
{
lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2463_ = lean_array_get_size(v_source_2461_);
v___x_2464_ = lean_nat_dec_lt(v_i_2460_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_dec_ref(v_source_2461_);
lean_dec(v_i_2460_);
return v_target_2462_;
}
else
{
lean_object* v_es_2465_; lean_object* v___x_2466_; lean_object* v_source_2467_; lean_object* v_target_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_es_2465_ = lean_array_fget(v_source_2461_, v_i_2460_);
v___x_2466_ = lean_box(0);
v_source_2467_ = lean_array_fset(v_source_2461_, v_i_2460_, v___x_2466_);
v_target_2468_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_target_2462_, v_es_2465_);
v___x_2469_ = lean_unsigned_to_nat(1u);
v___x_2470_ = lean_nat_add(v_i_2460_, v___x_2469_);
lean_dec(v_i_2460_);
v_i_2460_ = v___x_2470_;
v_source_2461_ = v_source_2467_;
v_target_2462_ = v_target_2468_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(lean_object* v_data_2472_){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v_nbuckets_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2473_ = lean_array_get_size(v_data_2472_);
v___x_2474_ = lean_unsigned_to_nat(2u);
v_nbuckets_2475_ = lean_nat_mul(v___x_2473_, v___x_2474_);
v___x_2476_ = lean_unsigned_to_nat(0u);
v___x_2477_ = lean_box(0);
v___x_2478_ = lean_mk_array(v_nbuckets_2475_, v___x_2477_);
v___x_2479_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v___x_2476_, v_data_2472_, v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(lean_object* v_m_2480_, lean_object* v_a_2481_, lean_object* v_b_2482_){
_start:
{
lean_object* v_size_2483_; lean_object* v_buckets_2484_; lean_object* v___x_2485_; uint64_t v___x_2486_; uint64_t v___x_2487_; uint64_t v___x_2488_; uint64_t v___x_2489_; uint64_t v_fold_2490_; uint64_t v___x_2491_; uint64_t v___x_2492_; uint64_t v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; size_t v___x_2497_; size_t v___x_2498_; lean_object* v_bkt_2499_; uint8_t v___x_2500_; 
v_size_2483_ = lean_ctor_get(v_m_2480_, 0);
v_buckets_2484_ = lean_ctor_get(v_m_2480_, 1);
v___x_2485_ = lean_array_get_size(v_buckets_2484_);
v___x_2486_ = 7ULL;
v___x_2487_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2486_, v_a_2481_);
v___x_2488_ = 32ULL;
v___x_2489_ = lean_uint64_shift_right(v___x_2487_, v___x_2488_);
v_fold_2490_ = lean_uint64_xor(v___x_2487_, v___x_2489_);
v___x_2491_ = 16ULL;
v___x_2492_ = lean_uint64_shift_right(v_fold_2490_, v___x_2491_);
v___x_2493_ = lean_uint64_xor(v_fold_2490_, v___x_2492_);
v___x_2494_ = lean_uint64_to_usize(v___x_2493_);
v___x_2495_ = lean_usize_of_nat(v___x_2485_);
v___x_2496_ = ((size_t)1ULL);
v___x_2497_ = lean_usize_sub(v___x_2495_, v___x_2496_);
v___x_2498_ = lean_usize_land(v___x_2494_, v___x_2497_);
v_bkt_2499_ = lean_array_uget_borrowed(v_buckets_2484_, v___x_2498_);
v___x_2500_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2481_, v_bkt_2499_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2521_; 
lean_inc_ref(v_buckets_2484_);
lean_inc(v_size_2483_);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_m_2480_);
if (v_isSharedCheck_2521_ == 0)
{
lean_object* v_unused_2522_; lean_object* v_unused_2523_; 
v_unused_2522_ = lean_ctor_get(v_m_2480_, 1);
lean_dec(v_unused_2522_);
v_unused_2523_ = lean_ctor_get(v_m_2480_, 0);
lean_dec(v_unused_2523_);
v___x_2502_ = v_m_2480_;
v_isShared_2503_ = v_isSharedCheck_2521_;
goto v_resetjp_2501_;
}
else
{
lean_dec(v_m_2480_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2521_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2504_; lean_object* v_size_x27_2505_; lean_object* v___x_2506_; lean_object* v_buckets_x27_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v___x_2504_ = lean_unsigned_to_nat(1u);
v_size_x27_2505_ = lean_nat_add(v_size_2483_, v___x_2504_);
lean_dec(v_size_2483_);
lean_inc(v_bkt_2499_);
v___x_2506_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2506_, 0, v_a_2481_);
lean_ctor_set(v___x_2506_, 1, v_b_2482_);
lean_ctor_set(v___x_2506_, 2, v_bkt_2499_);
v_buckets_x27_2507_ = lean_array_uset(v_buckets_2484_, v___x_2498_, v___x_2506_);
v___x_2508_ = lean_unsigned_to_nat(4u);
v___x_2509_ = lean_nat_mul(v_size_x27_2505_, v___x_2508_);
v___x_2510_ = lean_unsigned_to_nat(3u);
v___x_2511_ = lean_nat_div(v___x_2509_, v___x_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_array_get_size(v_buckets_x27_2507_);
v___x_2513_ = lean_nat_dec_le(v___x_2511_, v___x_2512_);
lean_dec(v___x_2511_);
if (v___x_2513_ == 0)
{
lean_object* v_val_2514_; lean_object* v___x_2516_; 
v_val_2514_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2507_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 1, v_val_2514_);
lean_ctor_set(v___x_2502_, 0, v_size_x27_2505_);
v___x_2516_ = v___x_2502_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_size_x27_2505_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_val_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
else
{
lean_object* v___x_2519_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 1, v_buckets_x27_2507_);
lean_ctor_set(v___x_2502_, 0, v_size_x27_2505_);
v___x_2519_ = v___x_2502_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_size_x27_2505_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_buckets_x27_2507_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
else
{
lean_dec(v_b_2482_);
lean_dec(v_a_2481_);
return v_m_2480_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(lean_object* v_a_2524_, lean_object* v_b_2525_, lean_object* v_x_2526_){
_start:
{
if (lean_obj_tag(v_x_2526_) == 0)
{
lean_dec(v_b_2525_);
lean_dec(v_a_2524_);
return v_x_2526_;
}
else
{
lean_object* v_key_2527_; lean_object* v_value_2528_; lean_object* v_tail_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2541_; 
v_key_2527_ = lean_ctor_get(v_x_2526_, 0);
v_value_2528_ = lean_ctor_get(v_x_2526_, 1);
v_tail_2529_ = lean_ctor_get(v_x_2526_, 2);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_x_2526_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2531_ = v_x_2526_;
v_isShared_2532_ = v_isSharedCheck_2541_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_tail_2529_);
lean_inc(v_value_2528_);
lean_inc(v_key_2527_);
lean_dec(v_x_2526_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2541_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
uint8_t v___x_2533_; 
v___x_2533_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2527_, v_a_2524_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2536_; 
v___x_2534_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2524_, v_b_2525_, v_tail_2529_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 2, v___x_2534_);
v___x_2536_ = v___x_2531_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_key_2527_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_value_2528_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
else
{
lean_object* v___x_2539_; 
lean_dec(v_value_2528_);
lean_dec(v_key_2527_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 1, v_b_2525_);
lean_ctor_set(v___x_2531_, 0, v_a_2524_);
v___x_2539_ = v___x_2531_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2524_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_b_2525_);
lean_ctor_set(v_reuseFailAlloc_2540_, 2, v_tail_2529_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(lean_object* v_m_2542_, lean_object* v_a_2543_, lean_object* v_b_2544_){
_start:
{
lean_object* v_size_2545_; lean_object* v_buckets_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2590_; 
v_size_2545_ = lean_ctor_get(v_m_2542_, 0);
v_buckets_2546_ = lean_ctor_get(v_m_2542_, 1);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_m_2542_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2548_ = v_m_2542_;
v_isShared_2549_ = v_isSharedCheck_2590_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_buckets_2546_);
lean_inc(v_size_2545_);
lean_dec(v_m_2542_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2590_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2550_; uint64_t v___x_2551_; uint64_t v___x_2552_; uint64_t v___x_2553_; uint64_t v___x_2554_; uint64_t v_fold_2555_; uint64_t v___x_2556_; uint64_t v___x_2557_; uint64_t v___x_2558_; size_t v___x_2559_; size_t v___x_2560_; size_t v___x_2561_; size_t v___x_2562_; size_t v___x_2563_; lean_object* v_bkt_2564_; uint8_t v___x_2565_; 
v___x_2550_ = lean_array_get_size(v_buckets_2546_);
v___x_2551_ = 7ULL;
v___x_2552_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2551_, v_a_2543_);
v___x_2553_ = 32ULL;
v___x_2554_ = lean_uint64_shift_right(v___x_2552_, v___x_2553_);
v_fold_2555_ = lean_uint64_xor(v___x_2552_, v___x_2554_);
v___x_2556_ = 16ULL;
v___x_2557_ = lean_uint64_shift_right(v_fold_2555_, v___x_2556_);
v___x_2558_ = lean_uint64_xor(v_fold_2555_, v___x_2557_);
v___x_2559_ = lean_uint64_to_usize(v___x_2558_);
v___x_2560_ = lean_usize_of_nat(v___x_2550_);
v___x_2561_ = ((size_t)1ULL);
v___x_2562_ = lean_usize_sub(v___x_2560_, v___x_2561_);
v___x_2563_ = lean_usize_land(v___x_2559_, v___x_2562_);
v_bkt_2564_ = lean_array_uget_borrowed(v_buckets_2546_, v___x_2563_);
v___x_2565_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2543_, v_bkt_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; lean_object* v_size_x27_2567_; lean_object* v___x_2568_; lean_object* v_buckets_x27_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2566_ = lean_unsigned_to_nat(1u);
v_size_x27_2567_ = lean_nat_add(v_size_2545_, v___x_2566_);
lean_dec(v_size_2545_);
lean_inc(v_bkt_2564_);
v___x_2568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2568_, 0, v_a_2543_);
lean_ctor_set(v___x_2568_, 1, v_b_2544_);
lean_ctor_set(v___x_2568_, 2, v_bkt_2564_);
v_buckets_x27_2569_ = lean_array_uset(v_buckets_2546_, v___x_2563_, v___x_2568_);
v___x_2570_ = lean_unsigned_to_nat(4u);
v___x_2571_ = lean_nat_mul(v_size_x27_2567_, v___x_2570_);
v___x_2572_ = lean_unsigned_to_nat(3u);
v___x_2573_ = lean_nat_div(v___x_2571_, v___x_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_array_get_size(v_buckets_x27_2569_);
v___x_2575_ = lean_nat_dec_le(v___x_2573_, v___x_2574_);
lean_dec(v___x_2573_);
if (v___x_2575_ == 0)
{
lean_object* v_val_2576_; lean_object* v___x_2578_; 
v_val_2576_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2569_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 1, v_val_2576_);
lean_ctor_set(v___x_2548_, 0, v_size_x27_2567_);
v___x_2578_ = v___x_2548_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_size_x27_2567_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_val_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
else
{
lean_object* v___x_2581_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 1, v_buckets_x27_2569_);
lean_ctor_set(v___x_2548_, 0, v_size_x27_2567_);
v___x_2581_ = v___x_2548_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_size_x27_2567_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_buckets_x27_2569_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
else
{
lean_object* v___x_2583_; lean_object* v_buckets_x27_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2588_; 
lean_inc(v_bkt_2564_);
v___x_2583_ = lean_box(0);
v_buckets_x27_2584_ = lean_array_uset(v_buckets_2546_, v___x_2563_, v___x_2583_);
v___x_2585_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2543_, v_b_2544_, v_bkt_2564_);
v___x_2586_ = lean_array_uset(v_buckets_x27_2584_, v___x_2563_, v___x_2585_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 1, v___x_2586_);
v___x_2588_ = v___x_2548_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_size_2545_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(lean_object* v_p_2591_, lean_object* v_x_2592_){
_start:
{
lean_object* v_coeffs_2593_; lean_object* v_constraint_2594_; lean_object* v_justification_2595_; uint8_t v___x_2596_; 
v_coeffs_2593_ = lean_ctor_get(v_x_2592_, 0);
lean_inc(v_coeffs_2593_);
v_constraint_2594_ = lean_ctor_get(v_x_2592_, 1);
lean_inc_ref(v_constraint_2594_);
v_justification_2595_ = lean_ctor_get(v_x_2592_, 2);
v___x_2596_ = l_Lean_Omega_Constraint_isImpossible(v_constraint_2594_);
if (v___x_2596_ == 0)
{
lean_object* v_assumptions_2597_; lean_object* v_numVars_2598_; lean_object* v_constraints_2599_; lean_object* v_equalities_2600_; lean_object* v_eliminations_2601_; uint8_t v_possible_2602_; lean_object* v_proveFalse_x3f_2603_; lean_object* v_explanation_x3f_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2622_; 
v_assumptions_2597_ = lean_ctor_get(v_p_2591_, 0);
v_numVars_2598_ = lean_ctor_get(v_p_2591_, 1);
v_constraints_2599_ = lean_ctor_get(v_p_2591_, 2);
v_equalities_2600_ = lean_ctor_get(v_p_2591_, 3);
v_eliminations_2601_ = lean_ctor_get(v_p_2591_, 4);
v_possible_2602_ = lean_ctor_get_uint8(v_p_2591_, sizeof(void*)*7);
v_proveFalse_x3f_2603_ = lean_ctor_get(v_p_2591_, 5);
v_explanation_x3f_2604_ = lean_ctor_get(v_p_2591_, 6);
v_isSharedCheck_2622_ = !lean_is_exclusive(v_p_2591_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2606_ = v_p_2591_;
v_isShared_2607_ = v_isSharedCheck_2622_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_explanation_x3f_2604_);
lean_inc(v_proveFalse_x3f_2603_);
lean_inc(v_eliminations_2601_);
lean_inc(v_equalities_2600_);
lean_inc(v_constraints_2599_);
lean_inc(v_numVars_2598_);
lean_inc(v_assumptions_2597_);
lean_dec(v_p_2591_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2622_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___y_2609_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2620_ = l_List_lengthTR___redArg(v_coeffs_2593_);
v___x_2621_ = lean_nat_dec_le(v_numVars_2598_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_dec(v___x_2620_);
v___y_2609_ = v_numVars_2598_;
goto v___jp_2608_;
}
else
{
lean_dec(v_numVars_2598_);
v___y_2609_ = v___x_2620_;
goto v___jp_2608_;
}
v___jp_2608_:
{
lean_object* v___x_2610_; uint8_t v___x_2611_; 
lean_inc(v_coeffs_2593_);
v___x_2610_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_constraints_2599_, v_coeffs_2593_, v_x_2592_);
v___x_2611_ = l_Lean_Omega_Constraint_isExact(v_constraint_2594_);
lean_dec_ref(v_constraint_2594_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2613_; 
lean_dec(v_coeffs_2593_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 2, v___x_2610_);
lean_ctor_set(v___x_2606_, 1, v___y_2609_);
v___x_2613_ = v___x_2606_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_assumptions_2597_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v___y_2609_);
lean_ctor_set(v_reuseFailAlloc_2614_, 2, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2614_, 3, v_equalities_2600_);
lean_ctor_set(v_reuseFailAlloc_2614_, 4, v_eliminations_2601_);
lean_ctor_set(v_reuseFailAlloc_2614_, 5, v_proveFalse_x3f_2603_);
lean_ctor_set(v_reuseFailAlloc_2614_, 6, v_explanation_x3f_2604_);
lean_ctor_set_uint8(v_reuseFailAlloc_2614_, sizeof(void*)*7, v_possible_2602_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
v___x_2615_ = lean_box(0);
v___x_2616_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_equalities_2600_, v_coeffs_2593_, v___x_2615_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 3, v___x_2616_);
lean_ctor_set(v___x_2606_, 2, v___x_2610_);
lean_ctor_set(v___x_2606_, 1, v___y_2609_);
v___x_2618_ = v___x_2606_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_assumptions_2597_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v___y_2609_);
lean_ctor_set(v_reuseFailAlloc_2619_, 2, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2619_, 3, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2619_, 4, v_eliminations_2601_);
lean_ctor_set(v_reuseFailAlloc_2619_, 5, v_proveFalse_x3f_2603_);
lean_ctor_set(v_reuseFailAlloc_2619_, 6, v_explanation_x3f_2604_);
lean_ctor_set_uint8(v_reuseFailAlloc_2619_, sizeof(void*)*7, v_possible_2602_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
else
{
lean_object* v_assumptions_2623_; lean_object* v_numVars_2624_; lean_object* v_constraints_2625_; lean_object* v_equalities_2626_; lean_object* v_eliminations_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2639_; 
lean_inc_ref(v_justification_2595_);
lean_dec_ref(v_x_2592_);
v_assumptions_2623_ = lean_ctor_get(v_p_2591_, 0);
v_numVars_2624_ = lean_ctor_get(v_p_2591_, 1);
v_constraints_2625_ = lean_ctor_get(v_p_2591_, 2);
v_equalities_2626_ = lean_ctor_get(v_p_2591_, 3);
v_eliminations_2627_ = lean_ctor_get(v_p_2591_, 4);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_p_2591_);
if (v_isSharedCheck_2639_ == 0)
{
lean_object* v_unused_2640_; lean_object* v_unused_2641_; 
v_unused_2640_ = lean_ctor_get(v_p_2591_, 6);
lean_dec(v_unused_2640_);
v_unused_2641_ = lean_ctor_get(v_p_2591_, 5);
lean_dec(v_unused_2641_);
v___x_2629_ = v_p_2591_;
v_isShared_2630_ = v_isSharedCheck_2639_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_eliminations_2627_);
lean_inc(v_equalities_2626_);
lean_inc(v_constraints_2625_);
lean_inc(v_numVars_2624_);
lean_inc(v_assumptions_2623_);
lean_dec(v_p_2591_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2639_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___f_2631_; uint8_t v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; 
lean_inc_ref(v_justification_2595_);
lean_inc(v_coeffs_2593_);
lean_inc_ref(v_constraint_2594_);
v___f_2631_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0), 4, 3);
lean_closure_set(v___f_2631_, 0, v_constraint_2594_);
lean_closure_set(v___f_2631_, 1, v_coeffs_2593_);
lean_closure_set(v___f_2631_, 2, v_justification_2595_);
v___x_2632_ = 0;
lean_inc_ref(v_assumptions_2623_);
v___x_2633_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed), 14, 4);
lean_closure_set(v___x_2633_, 0, v_constraint_2594_);
lean_closure_set(v___x_2633_, 1, v_coeffs_2593_);
lean_closure_set(v___x_2633_, 2, v_justification_2595_);
lean_closure_set(v___x_2633_, 3, v_assumptions_2623_);
v___x_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
v___x_2635_ = lean_mk_thunk(v___f_2631_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 6, v___x_2635_);
lean_ctor_set(v___x_2629_, 5, v___x_2634_);
v___x_2637_ = v___x_2629_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_assumptions_2623_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_numVars_2624_);
lean_ctor_set(v_reuseFailAlloc_2638_, 2, v_constraints_2625_);
lean_ctor_set(v_reuseFailAlloc_2638_, 3, v_equalities_2626_);
lean_ctor_set(v_reuseFailAlloc_2638_, 4, v_eliminations_2627_);
lean_ctor_set(v_reuseFailAlloc_2638_, 5, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2638_, 6, v___x_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
lean_ctor_set_uint8(v___x_2637_, sizeof(void*)*7, v___x_2632_);
return v___x_2637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0(lean_object* v_00_u03b2_2642_, lean_object* v_m_2643_, lean_object* v_a_2644_, lean_object* v_b_2645_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_m_2643_, v_a_2644_, v_b_2645_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1(lean_object* v_00_u03b2_2647_, lean_object* v_m_2648_, lean_object* v_a_2649_, lean_object* v_b_2650_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_m_2648_, v_a_2649_, v_b_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_object* v_00_u03b2_2652_, lean_object* v_a_2653_, lean_object* v_x_2654_){
_start:
{
uint8_t v___x_2655_; 
v___x_2655_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2653_, v_x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2656_, lean_object* v_a_2657_, lean_object* v_x_2658_){
_start:
{
uint8_t v_res_2659_; lean_object* v_r_2660_; 
v_res_2659_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(v_00_u03b2_2656_, v_a_2657_, v_x_2658_);
lean_dec(v_x_2658_);
lean_dec(v_a_2657_);
v_r_2660_ = lean_box(v_res_2659_);
return v_r_2660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2(lean_object* v_00_u03b2_2661_, lean_object* v_data_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_data_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3(lean_object* v_00_u03b2_2664_, lean_object* v_a_2665_, lean_object* v_b_2666_, lean_object* v_x_2667_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2665_, v_b_2666_, v_x_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2669_, lean_object* v_i_2670_, lean_object* v_source_2671_, lean_object* v_target_2672_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v_i_2670_, v_source_2671_, v_target_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2674_, lean_object* v_x_2675_, lean_object* v_x_2676_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_x_2675_, v_x_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(lean_object* v_a_2678_, lean_object* v_x_2679_){
_start:
{
if (lean_obj_tag(v_x_2679_) == 0)
{
lean_object* v___x_2680_; 
v___x_2680_ = lean_box(0);
return v___x_2680_;
}
else
{
lean_object* v_key_2681_; lean_object* v_value_2682_; lean_object* v_tail_2683_; uint8_t v___x_2684_; 
v_key_2681_ = lean_ctor_get(v_x_2679_, 0);
v_value_2682_ = lean_ctor_get(v_x_2679_, 1);
v_tail_2683_ = lean_ctor_get(v_x_2679_, 2);
v___x_2684_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2681_, v_a_2678_);
if (v___x_2684_ == 0)
{
v_x_2679_ = v_tail_2683_;
goto _start;
}
else
{
lean_object* v___x_2686_; 
lean_inc(v_value_2682_);
v___x_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2686_, 0, v_value_2682_);
return v___x_2686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg___boxed(lean_object* v_a_2687_, lean_object* v_x_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2687_, v_x_2688_);
lean_dec(v_x_2688_);
lean_dec(v_a_2687_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(lean_object* v_m_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v_buckets_2692_; lean_object* v___x_2693_; uint64_t v___x_2694_; uint64_t v___x_2695_; uint64_t v___x_2696_; uint64_t v___x_2697_; uint64_t v_fold_2698_; uint64_t v___x_2699_; uint64_t v___x_2700_; uint64_t v___x_2701_; size_t v___x_2702_; size_t v___x_2703_; size_t v___x_2704_; size_t v___x_2705_; size_t v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_buckets_2692_ = lean_ctor_get(v_m_2690_, 1);
v___x_2693_ = lean_array_get_size(v_buckets_2692_);
v___x_2694_ = 7ULL;
v___x_2695_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2694_, v_a_2691_);
v___x_2696_ = 32ULL;
v___x_2697_ = lean_uint64_shift_right(v___x_2695_, v___x_2696_);
v_fold_2698_ = lean_uint64_xor(v___x_2695_, v___x_2697_);
v___x_2699_ = 16ULL;
v___x_2700_ = lean_uint64_shift_right(v_fold_2698_, v___x_2699_);
v___x_2701_ = lean_uint64_xor(v_fold_2698_, v___x_2700_);
v___x_2702_ = lean_uint64_to_usize(v___x_2701_);
v___x_2703_ = lean_usize_of_nat(v___x_2693_);
v___x_2704_ = ((size_t)1ULL);
v___x_2705_ = lean_usize_sub(v___x_2703_, v___x_2704_);
v___x_2706_ = lean_usize_land(v___x_2702_, v___x_2705_);
v___x_2707_ = lean_array_uget_borrowed(v_buckets_2692_, v___x_2706_);
v___x_2708_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2691_, v___x_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg___boxed(lean_object* v_m_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2709_, v_a_2710_);
lean_dec(v_a_2710_);
lean_dec_ref(v_m_2709_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addConstraint(lean_object* v_p_2712_, lean_object* v_x_2713_){
_start:
{
uint8_t v_possible_2714_; 
v_possible_2714_ = lean_ctor_get_uint8(v_p_2712_, sizeof(void*)*7);
if (v_possible_2714_ == 0)
{
lean_dec_ref(v_x_2713_);
return v_p_2712_;
}
else
{
lean_object* v_coeffs_2715_; lean_object* v_constraint_2716_; lean_object* v_justification_2717_; lean_object* v_constraints_2718_; lean_object* v___x_2719_; 
v_coeffs_2715_ = lean_ctor_get(v_x_2713_, 0);
v_constraint_2716_ = lean_ctor_get(v_x_2713_, 1);
v_justification_2717_ = lean_ctor_get(v_x_2713_, 2);
v_constraints_2718_ = lean_ctor_get(v_p_2712_, 2);
v___x_2719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2718_, v_coeffs_2715_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_lowerBound_2720_; 
v_lowerBound_2720_ = lean_ctor_get(v_constraint_2716_, 0);
if (lean_obj_tag(v_lowerBound_2720_) == 0)
{
lean_object* v_upperBound_2721_; 
v_upperBound_2721_ = lean_ctor_get(v_constraint_2716_, 1);
if (lean_obj_tag(v_upperBound_2721_) == 0)
{
lean_dec_ref(v_x_2713_);
return v_p_2712_;
}
else
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2712_, v_x_2713_);
return v___x_2722_;
}
}
else
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2712_, v_x_2713_);
return v___x_2723_;
}
}
else
{
lean_object* v_val_2724_; lean_object* v_coeffs_2725_; lean_object* v_constraint_2726_; lean_object* v_justification_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2742_; 
v_val_2724_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_val_2724_);
lean_dec_ref(v___x_2719_);
v_coeffs_2725_ = lean_ctor_get(v_val_2724_, 0);
v_constraint_2726_ = lean_ctor_get(v_val_2724_, 1);
v_justification_2727_ = lean_ctor_get(v_val_2724_, 2);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_val_2724_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2729_ = v_val_2724_;
v_isShared_2730_ = v_isSharedCheck_2742_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_justification_2727_);
lean_inc(v_constraint_2726_);
lean_inc(v_coeffs_2725_);
lean_dec(v_val_2724_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2742_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2731_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc(v_coeffs_2715_);
v___x_2732_ = l_instDecidableEqList___redArg(v___x_2731_, v_coeffs_2715_, v_coeffs_2725_);
if (v___x_2732_ == 0)
{
lean_del_object(v___x_2729_);
lean_dec_ref(v_justification_2727_);
lean_dec_ref(v_constraint_2726_);
lean_dec_ref(v_x_2713_);
return v_p_2712_;
}
else
{
lean_object* v_r_2733_; uint8_t v___x_2734_; 
lean_inc_ref(v_constraint_2726_);
lean_inc_ref(v_constraint_2716_);
v_r_2733_ = l_Lean_Omega_Constraint_combine(v_constraint_2716_, v_constraint_2726_);
lean_inc_ref(v_constraint_2726_);
lean_inc_ref(v_r_2733_);
v___x_2734_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2733_, v_constraint_2726_);
if (v___x_2734_ == 0)
{
uint8_t v___x_2735_; 
lean_inc_ref(v_constraint_2716_);
lean_inc_ref(v_r_2733_);
v___x_2735_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2733_, v_constraint_2716_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_inc_ref(v_justification_2717_);
lean_inc_ref(v_constraint_2716_);
lean_inc(v_coeffs_2715_);
lean_dec_ref(v_x_2713_);
lean_inc(v_coeffs_2715_);
v___x_2736_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_2736_, 0, v_constraint_2716_);
lean_ctor_set(v___x_2736_, 1, v_constraint_2726_);
lean_ctor_set(v___x_2736_, 2, v_coeffs_2715_);
lean_ctor_set(v___x_2736_, 3, v_justification_2717_);
lean_ctor_set(v___x_2736_, 4, v_justification_2727_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 2, v___x_2736_);
lean_ctor_set(v___x_2729_, 1, v_r_2733_);
lean_ctor_set(v___x_2729_, 0, v_coeffs_2715_);
v___x_2738_ = v___x_2729_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_coeffs_2715_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_r_2733_);
lean_ctor_set(v_reuseFailAlloc_2740_, 2, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2712_, v___x_2738_);
return v___x_2739_;
}
}
else
{
lean_object* v___x_2741_; 
lean_dec_ref(v_r_2733_);
lean_del_object(v___x_2729_);
lean_dec_ref(v_justification_2727_);
lean_dec_ref(v_constraint_2726_);
v___x_2741_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2712_, v_x_2713_);
return v___x_2741_;
}
}
else
{
lean_dec_ref(v_r_2733_);
lean_del_object(v___x_2729_);
lean_dec_ref(v_justification_2727_);
lean_dec_ref(v_constraint_2726_);
lean_dec_ref(v_x_2713_);
return v_p_2712_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(lean_object* v_00_u03b2_2743_, lean_object* v_m_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2744_, v_a_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___boxed(lean_object* v_00_u03b2_2747_, lean_object* v_m_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(v_00_u03b2_2747_, v_m_2748_, v_a_2749_);
lean_dec(v_a_2749_);
lean_dec_ref(v_m_2748_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(lean_object* v_00_u03b2_2751_, lean_object* v_a_2752_, lean_object* v_x_2753_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2752_, v_x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2755_, lean_object* v_a_2756_, lean_object* v_x_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(v_00_u03b2_2755_, v_a_2756_, v_x_2757_);
lean_dec(v_x_2757_);
lean_dec(v_a_2756_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(lean_object* v_x_2759_, lean_object* v_x_2760_){
_start:
{
if (lean_obj_tag(v_x_2760_) == 0)
{
return v_x_2759_;
}
else
{
if (lean_obj_tag(v_x_2759_) == 0)
{
lean_object* v_key_2761_; lean_object* v_tail_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v_key_2761_ = lean_ctor_get(v_x_2760_, 0);
lean_inc(v_key_2761_);
v_tail_2762_ = lean_ctor_get(v_x_2760_, 2);
lean_inc(v_tail_2762_);
lean_dec_ref(v_x_2760_);
lean_inc(v_key_2761_);
v___x_2763_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2761_);
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v_key_2761_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2764_);
v_x_2759_ = v___x_2765_;
v_x_2760_ = v_tail_2762_;
goto _start;
}
else
{
lean_object* v_val_2767_; lean_object* v_key_2768_; lean_object* v_tail_2769_; lean_object* v_fst_2770_; lean_object* v_snd_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2799_; 
v_val_2767_ = lean_ctor_get(v_x_2759_, 0);
lean_inc(v_val_2767_);
v_key_2768_ = lean_ctor_get(v_x_2760_, 0);
lean_inc(v_key_2768_);
v_tail_2769_ = lean_ctor_get(v_x_2760_, 2);
lean_inc(v_tail_2769_);
lean_dec_ref(v_x_2760_);
v_fst_2770_ = lean_ctor_get(v_val_2767_, 0);
v_snd_2771_ = lean_ctor_get(v_val_2767_, 1);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_val_2767_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2773_ = v_val_2767_;
v_isShared_2774_ = v_isSharedCheck_2799_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_snd_2771_);
lean_inc(v_fst_2770_);
lean_dec(v_val_2767_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2799_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; uint8_t v___x_2776_; 
v___x_2775_ = lean_unsigned_to_nat(2u);
v___x_2776_ = lean_nat_dec_le(v___x_2775_, v_snd_2771_);
if (v___x_2776_ == 0)
{
lean_del_object(v___x_2773_);
lean_dec(v_snd_2771_);
lean_dec(v_fst_2770_);
lean_dec(v_key_2768_);
v_x_2760_ = v_tail_2769_;
goto _start;
}
else
{
lean_object* v_m_x27_2778_; uint8_t v___y_2780_; uint8_t v___x_2794_; 
lean_inc(v_key_2768_);
v_m_x27_2778_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2768_);
v___x_2794_ = lean_nat_dec_lt(v_m_x27_2778_, v_snd_2771_);
if (v___x_2794_ == 0)
{
uint8_t v___x_2795_; 
v___x_2795_ = lean_nat_dec_eq(v_m_x27_2778_, v_snd_2771_);
lean_dec(v_snd_2771_);
if (v___x_2795_ == 0)
{
lean_dec(v_fst_2770_);
v___y_2780_ = v___x_2795_;
goto v___jp_2779_;
}
else
{
lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
lean_inc(v_key_2768_);
v___x_2796_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_key_2768_);
v___x_2797_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_fst_2770_);
v___x_2798_ = lean_nat_dec_lt(v___x_2796_, v___x_2797_);
lean_dec(v___x_2797_);
lean_dec(v___x_2796_);
v___y_2780_ = v___x_2798_;
goto v___jp_2779_;
}
}
else
{
lean_dec(v_snd_2771_);
lean_dec(v_fst_2770_);
v___y_2780_ = v___x_2794_;
goto v___jp_2779_;
}
v___jp_2779_:
{
if (v___y_2780_ == 0)
{
lean_dec(v_m_x27_2778_);
lean_del_object(v___x_2773_);
lean_dec(v_key_2768_);
v_x_2760_ = v_tail_2769_;
goto _start;
}
else
{
lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2792_; 
v_isSharedCheck_2792_ = !lean_is_exclusive(v_x_2759_);
if (v_isSharedCheck_2792_ == 0)
{
lean_object* v_unused_2793_; 
v_unused_2793_ = lean_ctor_get(v_x_2759_, 0);
lean_dec(v_unused_2793_);
v___x_2783_ = v_x_2759_;
v_isShared_2784_ = v_isSharedCheck_2792_;
goto v_resetjp_2782_;
}
else
{
lean_dec(v_x_2759_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2792_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v_m_x27_2778_);
lean_ctor_set(v___x_2773_, 0, v_key_2768_);
v___x_2786_ = v___x_2773_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_key_2768_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_m_x27_2778_);
v___x_2786_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2788_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2786_);
v___x_2788_ = v___x_2783_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
v_x_2759_ = v___x_2788_;
v_x_2760_ = v_tail_2769_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(lean_object* v_as_2800_, size_t v_i_2801_, size_t v_stop_2802_, lean_object* v_b_2803_){
_start:
{
uint8_t v___x_2804_; 
v___x_2804_ = lean_usize_dec_eq(v_i_2801_, v_stop_2802_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; lean_object* v___x_2806_; size_t v___x_2807_; size_t v___x_2808_; 
v___x_2805_ = lean_array_uget_borrowed(v_as_2800_, v_i_2801_);
lean_inc(v___x_2805_);
v___x_2806_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(v_b_2803_, v___x_2805_);
v___x_2807_ = ((size_t)1ULL);
v___x_2808_ = lean_usize_add(v_i_2801_, v___x_2807_);
v_i_2801_ = v___x_2808_;
v_b_2803_ = v___x_2806_;
goto _start;
}
else
{
return v_b_2803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1___boxed(lean_object* v_as_2810_, lean_object* v_i_2811_, lean_object* v_stop_2812_, lean_object* v_b_2813_){
_start:
{
size_t v_i_boxed_2814_; size_t v_stop_boxed_2815_; lean_object* v_res_2816_; 
v_i_boxed_2814_ = lean_unbox_usize(v_i_2811_);
lean_dec(v_i_2811_);
v_stop_boxed_2815_ = lean_unbox_usize(v_stop_2812_);
lean_dec(v_stop_2812_);
v_res_2816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_as_2810_, v_i_boxed_2814_, v_stop_boxed_2815_, v_b_2813_);
lean_dec_ref(v_as_2810_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality(lean_object* v_p_2817_){
_start:
{
lean_object* v_equalities_2818_; lean_object* v_buckets_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; 
v_equalities_2818_ = lean_ctor_get(v_p_2817_, 3);
v_buckets_2819_ = lean_ctor_get(v_equalities_2818_, 1);
v___x_2820_ = lean_box(0);
v___x_2821_ = lean_unsigned_to_nat(0u);
v___x_2822_ = lean_array_get_size(v_buckets_2819_);
v___x_2823_ = lean_nat_dec_lt(v___x_2821_, v___x_2822_);
if (v___x_2823_ == 0)
{
return v___x_2820_;
}
else
{
uint8_t v___x_2824_; 
v___x_2824_ = lean_nat_dec_le(v___x_2822_, v___x_2822_);
if (v___x_2824_ == 0)
{
if (v___x_2823_ == 0)
{
return v___x_2820_;
}
else
{
size_t v___x_2825_; size_t v___x_2826_; lean_object* v___x_2827_; 
v___x_2825_ = ((size_t)0ULL);
v___x_2826_ = lean_usize_of_nat(v___x_2822_);
v___x_2827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2819_, v___x_2825_, v___x_2826_, v___x_2820_);
return v___x_2827_;
}
}
else
{
size_t v___x_2828_; size_t v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = ((size_t)0ULL);
v___x_2829_ = lean_usize_of_nat(v___x_2822_);
v___x_2830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2819_, v___x_2828_, v___x_2829_, v___x_2820_);
return v___x_2830_;
}
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
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1(lean_object* v_x_2882_){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v___x_2883_ = lean_nat_abs(v_x_2882_);
v___x_2884_ = lean_unsigned_to_nat(1u);
v___x_2885_ = lean_nat_dec_eq(v___x_2883_, v___x_2884_);
lean_dec(v___x_2883_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1___boxed(lean_object* v_x_2886_){
_start:
{
uint8_t v_res_2887_; lean_object* v_r_2888_; 
v_res_2887_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__1(v_x_2886_);
lean_dec(v_x_2886_);
v_r_2888_ = lean_box(v_res_2887_);
return v_r_2888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(lean_object* v___y_2889_, lean_object* v_sign_2890_, lean_object* v_val_2891_, lean_object* v_x_2892_, lean_object* v_x_2893_){
_start:
{
if (lean_obj_tag(v_x_2893_) == 0)
{
lean_dec_ref(v_val_2891_);
lean_dec(v___y_2889_);
return v_x_2892_;
}
else
{
lean_object* v_key_2894_; lean_object* v_value_2895_; lean_object* v_tail_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v_key_2894_ = lean_ctor_get(v_x_2893_, 0);
lean_inc(v_key_2894_);
v_value_2895_ = lean_ctor_get(v_x_2893_, 1);
lean_inc(v_value_2895_);
v_tail_2896_ = lean_ctor_get(v_x_2893_, 2);
lean_inc(v_tail_2896_);
lean_dec_ref(v_x_2893_);
lean_inc(v___y_2889_);
v___x_2897_ = l_Lean_Omega_IntList_get(v_key_2894_, v___y_2889_);
lean_dec(v_key_2894_);
v___x_2898_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2899_ = lean_int_dec_eq(v___x_2897_, v___x_2898_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v_k_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2900_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2901_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2902_ = lean_int_mul(v___x_2901_, v_sign_2890_);
v_k_2903_ = lean_int_mul(v___x_2902_, v___x_2897_);
lean_dec(v___x_2897_);
lean_dec(v___x_2902_);
lean_inc_ref(v_val_2891_);
v___x_2904_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_k_2903_, v_val_2891_, v___x_2900_, v_value_2895_);
v___x_2905_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_2904_);
v___x_2906_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2892_, v___x_2905_);
v_x_2892_ = v___x_2906_;
v_x_2893_ = v_tail_2896_;
goto _start;
}
else
{
lean_object* v___x_2908_; 
lean_dec(v___x_2897_);
v___x_2908_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2892_, v_value_2895_);
v_x_2892_ = v___x_2908_;
v_x_2893_ = v_tail_2896_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0___boxed(lean_object* v___y_2910_, lean_object* v_sign_2911_, lean_object* v_val_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2910_, v_sign_2911_, v_val_2912_, v_x_2913_, v_x_2914_);
lean_dec(v_sign_2911_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object* v___y_2916_, lean_object* v_sign_2917_, lean_object* v_val_2918_, lean_object* v_as_2919_, size_t v_i_2920_, size_t v_stop_2921_, lean_object* v_b_2922_){
_start:
{
uint8_t v___x_2923_; 
v___x_2923_ = lean_usize_dec_eq(v_i_2920_, v_stop_2921_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; size_t v___x_2926_; size_t v___x_2927_; 
v___x_2924_ = lean_array_uget_borrowed(v_as_2919_, v_i_2920_);
lean_inc(v___x_2924_);
lean_inc_ref(v_val_2918_);
lean_inc(v___y_2916_);
v___x_2925_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2916_, v_sign_2917_, v_val_2918_, v_b_2922_, v___x_2924_);
v___x_2926_ = ((size_t)1ULL);
v___x_2927_ = lean_usize_add(v_i_2920_, v___x_2926_);
v_i_2920_ = v___x_2927_;
v_b_2922_ = v___x_2925_;
goto _start;
}
else
{
lean_dec_ref(v_val_2918_);
lean_dec(v___y_2916_);
return v_b_2922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1___boxed(lean_object* v___y_2929_, lean_object* v_sign_2930_, lean_object* v_val_2931_, lean_object* v_as_2932_, lean_object* v_i_2933_, lean_object* v_stop_2934_, lean_object* v_b_2935_){
_start:
{
size_t v_i_boxed_2936_; size_t v_stop_boxed_2937_; lean_object* v_res_2938_; 
v_i_boxed_2936_ = lean_unbox_usize(v_i_2933_);
lean_dec(v_i_2933_);
v_stop_boxed_2937_ = lean_unbox_usize(v_stop_2934_);
lean_dec(v_stop_2934_);
v_res_2938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2929_, v_sign_2930_, v_val_2931_, v_as_2932_, v_i_boxed_2936_, v_stop_boxed_2937_, v_b_2935_);
lean_dec_ref(v_as_2932_);
lean_dec(v_sign_2930_);
return v_res_2938_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1(void){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2940_ = lean_box(0);
v___x_2941_ = lean_unsigned_to_nat(16u);
v___x_2942_ = lean_mk_array(v___x_2941_, v___x_2940_);
return v___x_2942_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2(void){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2943_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1);
v___x_2944_ = lean_unsigned_to_nat(0u);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
lean_ctor_set(v___x_2945_, 1, v___x_2943_);
return v___x_2945_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3(void){
_start:
{
lean_object* v___f_2946_; lean_object* v___x_2947_; 
v___f_2946_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0));
v___x_2947_ = lean_mk_thunk(v___f_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(lean_object* v_p_2949_, lean_object* v_c_2950_){
_start:
{
lean_object* v___y_2952_; lean_object* v___f_2999_; lean_object* v___x_3000_; 
v___f_2999_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__4));
lean_inc(v_c_2950_);
v___x_3000_ = l_List_findIdx_x3f___redArg(v___f_2999_, v_c_2950_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_unsigned_to_nat(0u);
v___y_2952_ = v___x_3001_;
goto v___jp_2951_;
}
else
{
lean_object* v_val_3002_; 
v_val_3002_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_val_3002_);
lean_dec_ref(v___x_3000_);
v___y_2952_ = v_val_3002_;
goto v___jp_2951_;
}
v___jp_2951_:
{
lean_object* v_assumptions_2953_; lean_object* v_constraints_2954_; lean_object* v_eliminations_2955_; lean_object* v___x_2956_; 
v_assumptions_2953_ = lean_ctor_get(v_p_2949_, 0);
v_constraints_2954_ = lean_ctor_get(v_p_2949_, 2);
lean_inc_ref(v_constraints_2954_);
v_eliminations_2955_ = lean_ctor_get(v_p_2949_, 4);
v___x_2956_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2954_, v_c_2950_);
if (lean_obj_tag(v___x_2956_) == 1)
{
lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2991_; 
lean_inc(v_eliminations_2955_);
lean_inc_ref(v_assumptions_2953_);
v_isSharedCheck_2991_ = !lean_is_exclusive(v_p_2949_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; lean_object* v_unused_2993_; lean_object* v_unused_2994_; lean_object* v_unused_2995_; lean_object* v_unused_2996_; lean_object* v_unused_2997_; lean_object* v_unused_2998_; 
v_unused_2992_ = lean_ctor_get(v_p_2949_, 6);
lean_dec(v_unused_2992_);
v_unused_2993_ = lean_ctor_get(v_p_2949_, 5);
lean_dec(v_unused_2993_);
v_unused_2994_ = lean_ctor_get(v_p_2949_, 4);
lean_dec(v_unused_2994_);
v_unused_2995_ = lean_ctor_get(v_p_2949_, 3);
lean_dec(v_unused_2995_);
v_unused_2996_ = lean_ctor_get(v_p_2949_, 2);
lean_dec(v_unused_2996_);
v_unused_2997_ = lean_ctor_get(v_p_2949_, 1);
lean_dec(v_unused_2997_);
v_unused_2998_ = lean_ctor_get(v_p_2949_, 0);
lean_dec(v_unused_2998_);
v___x_2958_ = v_p_2949_;
v_isShared_2959_ = v_isSharedCheck_2991_;
goto v_resetjp_2957_;
}
else
{
lean_dec(v_p_2949_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2991_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v_val_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v_buckets_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2989_; 
v_val_2960_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_val_2960_);
lean_dec_ref(v___x_2956_);
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v_buckets_2963_ = lean_ctor_get(v_constraints_2954_, 1);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_constraints_2954_);
if (v_isSharedCheck_2989_ == 0)
{
lean_object* v_unused_2990_; 
v_unused_2990_ = lean_ctor_get(v_constraints_2954_, 0);
lean_dec(v_unused_2990_);
v___x_2965_ = v_constraints_2954_;
v_isShared_2966_ = v_isSharedCheck_2989_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_buckets_2963_);
lean_dec(v_constraints_2954_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2989_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2967_; lean_object* v_sign_2968_; lean_object* v___x_2970_; 
lean_inc(v___y_2952_);
v___x_2967_ = l_Lean_Omega_IntList_get(v_c_2950_, v___y_2952_);
lean_dec(v_c_2950_);
v_sign_2968_ = l_Int_sign(v___x_2967_);
lean_dec(v___x_2967_);
lean_inc(v_sign_2968_);
lean_inc(v___y_2952_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 1, v_sign_2968_);
lean_ctor_set(v___x_2965_, 0, v___y_2952_);
v___x_2970_ = v___x_2965_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___y_2952_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_sign_2968_);
v___x_2970_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v_init_2977_; 
lean_inc(v_val_2960_);
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v_val_2960_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
lean_ctor_set(v___x_2972_, 1, v_eliminations_2955_);
v___x_2973_ = 1;
v___x_2974_ = lean_box(0);
v___x_2975_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 6, v___x_2975_);
lean_ctor_set(v___x_2958_, 5, v___x_2974_);
lean_ctor_set(v___x_2958_, 4, v___x_2972_);
lean_ctor_set(v___x_2958_, 3, v___x_2962_);
lean_ctor_set(v___x_2958_, 2, v___x_2962_);
lean_ctor_set(v___x_2958_, 1, v___x_2961_);
v_init_2977_ = v___x_2958_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_assumptions_2953_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2961_);
lean_ctor_set(v_reuseFailAlloc_2987_, 2, v___x_2962_);
lean_ctor_set(v_reuseFailAlloc_2987_, 3, v___x_2962_);
lean_ctor_set(v_reuseFailAlloc_2987_, 4, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_2987_, 5, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2987_, 6, v___x_2975_);
v_init_2977_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2978_; uint8_t v___x_2979_; 
lean_ctor_set_uint8(v_init_2977_, sizeof(void*)*7, v___x_2973_);
v___x_2978_ = lean_array_get_size(v_buckets_2963_);
v___x_2979_ = lean_nat_dec_lt(v___x_2961_, v___x_2978_);
if (v___x_2979_ == 0)
{
lean_dec(v_sign_2968_);
lean_dec_ref(v_buckets_2963_);
lean_dec(v_val_2960_);
lean_dec(v___y_2952_);
return v_init_2977_;
}
else
{
uint8_t v___x_2980_; 
v___x_2980_ = lean_nat_dec_le(v___x_2978_, v___x_2978_);
if (v___x_2980_ == 0)
{
if (v___x_2979_ == 0)
{
lean_dec(v_sign_2968_);
lean_dec_ref(v_buckets_2963_);
lean_dec(v_val_2960_);
lean_dec(v___y_2952_);
return v_init_2977_;
}
else
{
size_t v___x_2981_; size_t v___x_2982_; lean_object* v___x_2983_; 
v___x_2981_ = ((size_t)0ULL);
v___x_2982_ = lean_usize_of_nat(v___x_2978_);
v___x_2983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2952_, v_sign_2968_, v_val_2960_, v_buckets_2963_, v___x_2981_, v___x_2982_, v_init_2977_);
lean_dec_ref(v_buckets_2963_);
lean_dec(v_sign_2968_);
return v___x_2983_;
}
}
else
{
size_t v___x_2984_; size_t v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = ((size_t)0ULL);
v___x_2985_ = lean_usize_of_nat(v___x_2978_);
v___x_2986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2952_, v_sign_2968_, v_val_2960_, v_buckets_2963_, v___x_2984_, v___x_2985_, v_init_2977_);
lean_dec_ref(v_buckets_2963_);
lean_dec(v_sign_2968_);
return v___x_2986_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2956_);
lean_dec_ref(v_constraints_2954_);
lean_dec(v___y_2952_);
lean_dec(v_c_2950_);
return v_p_2949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(lean_object* v_msgData_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v___x_3009_; lean_object* v_env_3010_; lean_object* v___x_3011_; lean_object* v_mctx_3012_; lean_object* v_lctx_3013_; lean_object* v_options_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3009_ = lean_st_ref_get(v___y_3007_);
v_env_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc_ref(v_env_3010_);
lean_dec(v___x_3009_);
v___x_3011_ = lean_st_ref_get(v___y_3005_);
v_mctx_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc_ref(v_mctx_3012_);
lean_dec(v___x_3011_);
v_lctx_3013_ = lean_ctor_get(v___y_3004_, 2);
v_options_3014_ = lean_ctor_get(v___y_3006_, 2);
lean_inc_ref(v_options_3014_);
lean_inc_ref(v_lctx_3013_);
v___x_3015_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3015_, 0, v_env_3010_);
lean_ctor_set(v___x_3015_, 1, v_mctx_3012_);
lean_ctor_set(v___x_3015_, 2, v_lctx_3013_);
lean_ctor_set(v___x_3015_, 3, v_options_3014_);
v___x_3016_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
lean_ctor_set(v___x_3016_, 1, v_msgData_3003_);
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0___boxed(lean_object* v_msgData_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msgData_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(lean_object* v_msg_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_ref_3031_; lean_object* v___x_3032_; lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3041_; 
v_ref_3031_ = lean_ctor_get(v___y_3028_, 5);
v___x_3032_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3035_ = v___x_3032_;
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3032_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
lean_inc(v_ref_3031_);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v_ref_3031_);
lean_ctor_set(v___x_3037_, 1, v_a_3033_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set_tag(v___x_3035_, 1);
lean_ctor_set(v___x_3035_, 0, v___x_3037_);
v___x_3039_ = v___x_3035_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg___boxed(lean_object* v_msg_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
return v_res_3048_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0));
v___x_3051_ = l_Lean_stringToMessageData(v___x_3050_);
return v___x_3051_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2));
v___x_3054_ = l_Lean_stringToMessageData(v___x_3053_);
return v___x_3054_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4));
v___x_3057_ = l_Lean_stringToMessageData(v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(lean_object* v_p_3058_, lean_object* v_c_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, uint8_t v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v_constraints_3070_; lean_object* v___x_3071_; 
v_constraints_3070_ = lean_ctor_get(v_p_3058_, 2);
v___x_3071_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_3070_, v_c_3059_);
if (lean_obj_tag(v___x_3071_) == 1)
{
lean_object* v_val_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3171_; 
v_val_3072_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3074_ = v___x_3071_;
v_isShared_3075_ = v_isSharedCheck_3171_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_val_3072_);
lean_dec(v___x_3071_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3171_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v_constraint_3076_; lean_object* v_lowerBound_3077_; 
v_constraint_3076_ = lean_ctor_get(v_val_3072_, 1);
v_lowerBound_3077_ = lean_ctor_get(v_constraint_3076_, 0);
lean_inc(v_lowerBound_3077_);
if (lean_obj_tag(v_lowerBound_3077_) == 1)
{
lean_object* v_upperBound_3078_; 
lean_del_object(v___x_3074_);
v_upperBound_3078_ = lean_ctor_get(v_constraint_3076_, 1);
lean_inc(v_upperBound_3078_);
if (lean_obj_tag(v_upperBound_3078_) == 1)
{
lean_object* v_coeffs_3079_; lean_object* v_justification_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3158_; 
v_coeffs_3079_ = lean_ctor_get(v_val_3072_, 0);
v_justification_3080_ = lean_ctor_get(v_val_3072_, 2);
v_isSharedCheck_3158_ = !lean_is_exclusive(v_val_3072_);
if (v_isSharedCheck_3158_ == 0)
{
lean_object* v_unused_3159_; 
v_unused_3159_ = lean_ctor_get(v_val_3072_, 1);
lean_dec(v_unused_3159_);
v___x_3082_ = v_val_3072_;
v_isShared_3083_ = v_isSharedCheck_3158_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_justification_3080_);
lean_inc(v_coeffs_3079_);
lean_dec(v_val_3072_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3158_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v_val_3084_; lean_object* v_val_3085_; lean_object* v___x_3086_; 
v_val_3084_ = lean_ctor_get(v_lowerBound_3077_, 0);
lean_inc(v_val_3084_);
lean_dec_ref(v_lowerBound_3077_);
v_val_3085_ = lean_ctor_get(v_upperBound_3078_, 0);
lean_inc(v_val_3085_);
lean_dec_ref(v_upperBound_3078_);
v___x_3086_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3061_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v_m_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v_nil_3093_; lean_object* v_cons_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref(v___x_3086_);
lean_inc(v_c_3059_);
v___x_3088_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_c_3059_);
v___x_3089_ = lean_unsigned_to_nat(1u);
v_m_3090_ = lean_nat_add(v___x_3088_, v___x_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc(v_m_3090_);
v___x_3092_ = l_Lean_mkNatLit(v_m_3090_);
v_nil_3093_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3094_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3095_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3093_, v_cons_3094_, v_c_3059_);
lean_dec(v_c_3059_);
v___x_3096_ = l_Lean_mkApp3(v___x_3091_, v___x_3092_, v___x_3095_, v_a_3087_);
v___x_3097_ = l_Lean_Elab_Tactic_Omega_lookup(v___x_3096_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3141_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3100_ = v___x_3097_;
v_isShared_3101_ = v_isSharedCheck_3141_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3097_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3141_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v_fst_3102_; lean_object* v_snd_3103_; uint8_t v___x_3116_; 
v_fst_3102_ = lean_ctor_get(v_a_3098_, 0);
lean_inc(v_fst_3102_);
v_snd_3103_ = lean_ctor_get(v_a_3098_, 1);
lean_inc(v_snd_3103_);
lean_dec(v_a_3098_);
v___x_3116_ = lean_int_dec_eq(v_val_3085_, v_val_3084_);
lean_dec(v_val_3085_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_dec(v_snd_3103_);
lean_dec(v_fst_3102_);
lean_del_object(v___x_3100_);
lean_dec(v_m_3090_);
lean_dec(v_val_3084_);
lean_del_object(v___x_3082_);
lean_dec_ref(v_justification_3080_);
lean_dec(v_coeffs_3079_);
lean_dec_ref(v_p_3058_);
v___x_3117_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1);
v___x_3118_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3117_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3118_;
}
else
{
if (lean_obj_tag(v_snd_3103_) == 0)
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_fst_3102_);
lean_del_object(v___x_3100_);
lean_dec(v_m_3090_);
lean_dec(v_val_3084_);
lean_del_object(v___x_3082_);
lean_dec_ref(v_justification_3080_);
lean_dec(v_coeffs_3079_);
lean_dec_ref(v_p_3058_);
v___x_3119_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3);
v___x_3120_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3119_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
else
{
lean_object* v_val_3129_; uint8_t v___x_3130_; 
v_val_3129_ = lean_ctor_get(v_snd_3103_, 0);
lean_inc(v_val_3129_);
lean_dec_ref(v_snd_3103_);
v___x_3130_ = l_List_isEmpty___redArg(v_val_3129_);
lean_dec(v_val_3129_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec(v_fst_3102_);
lean_del_object(v___x_3100_);
lean_dec(v_m_3090_);
lean_dec(v_val_3084_);
lean_del_object(v___x_3082_);
lean_dec_ref(v_justification_3080_);
lean_dec(v_coeffs_3079_);
lean_dec_ref(v_p_3058_);
v___x_3131_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5);
v___x_3132_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3131_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3132_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3132_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
else
{
goto v___jp_3104_;
}
}
}
v___jp_3104_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
lean_inc(v_coeffs_3079_);
lean_inc(v_m_3090_);
v___x_3105_ = l_Lean_Omega_bmod__coeffs(v_m_3090_, v_fst_3102_, v_coeffs_3079_);
lean_inc(v_m_3090_);
v___x_3106_ = l_Int_bmod(v_val_3084_, v_m_3090_);
v___x_3107_ = l_Lean_Omega_Constraint_exact(v___x_3106_);
v___x_3108_ = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(v___x_3108_, 0, v_m_3090_);
lean_ctor_set(v___x_3108_, 1, v_val_3084_);
lean_ctor_set(v___x_3108_, 2, v_fst_3102_);
lean_ctor_set(v___x_3108_, 3, v_coeffs_3079_);
lean_ctor_set(v___x_3108_, 4, v_justification_3080_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 2, v___x_3108_);
lean_ctor_set(v___x_3082_, 1, v___x_3107_);
lean_ctor_set(v___x_3082_, 0, v___x_3105_);
v___x_3110_ = v___x_3082_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3115_, 2, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3111_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_3058_, v___x_3110_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 0, v___x_3111_);
v___x_3113_ = v___x_3100_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v_m_3090_);
lean_dec(v_val_3085_);
lean_dec(v_val_3084_);
lean_del_object(v___x_3082_);
lean_dec_ref(v_justification_3080_);
lean_dec(v_coeffs_3079_);
lean_dec_ref(v_p_3058_);
v_a_3142_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3097_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3097_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v_val_3085_);
lean_dec(v_val_3084_);
lean_del_object(v___x_3082_);
lean_dec_ref(v_justification_3080_);
lean_dec(v_coeffs_3079_);
lean_dec(v_c_3059_);
lean_dec_ref(v_p_3058_);
v_a_3150_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3086_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3086_);
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
}
else
{
lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec(v_upperBound_3078_);
lean_dec(v_val_3072_);
lean_dec(v_c_3059_);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_lowerBound_3077_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; 
v_unused_3167_ = lean_ctor_get(v_lowerBound_3077_, 0);
lean_dec(v_unused_3167_);
v___x_3161_ = v_lowerBound_3077_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_dec(v_lowerBound_3077_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
lean_ctor_set_tag(v___x_3161_, 0);
lean_ctor_set(v___x_3161_, 0, v_p_3058_);
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_p_3058_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
else
{
lean_object* v___x_3169_; 
lean_dec(v_lowerBound_3077_);
lean_dec(v_val_3072_);
lean_dec(v_c_3059_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set_tag(v___x_3074_, 0);
lean_ctor_set(v___x_3074_, 0, v_p_3058_);
v___x_3169_ = v___x_3074_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_p_3058_);
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
lean_object* v___x_3172_; 
lean_dec(v___x_3071_);
lean_dec(v_c_3059_);
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v_p_3058_);
return v___x_3172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___boxed(lean_object* v_p_3173_, lean_object* v_c_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_){
_start:
{
uint8_t v_a_boxed_3185_; lean_object* v_res_3186_; 
v_a_boxed_3185_ = lean_unbox(v_a_3178_);
v_res_3186_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3173_, v_c_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_boxed_3185_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_);
lean_dec(v_a_3183_);
lean_dec_ref(v_a_3182_);
lean_dec(v_a_3181_);
lean_dec_ref(v_a_3180_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3177_);
lean_dec(v_a_3176_);
lean_dec(v_a_3175_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_object* v_00_u03b1_3187_, lean_object* v_msg_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, uint8_t v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3188_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___boxed(lean_object* v_00_u03b1_3200_, lean_object* v_msg_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
uint8_t v___y_14890__boxed_3212_; lean_object* v_res_3213_; 
v___y_14890__boxed_3212_ = lean_unbox(v___y_3205_);
v_res_3213_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(v_00_u03b1_3200_, v_msg_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_14890__boxed_3212_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec(v___y_3202_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality(lean_object* v_p_3214_, lean_object* v_c_3215_, lean_object* v_m_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, uint8_t v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_){
_start:
{
lean_object* v___x_3227_; uint8_t v___x_3228_; 
v___x_3227_ = lean_unsigned_to_nat(1u);
v___x_3228_ = lean_nat_dec_eq(v_m_3216_, v___x_3227_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3214_, v_c_3215_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
return v___x_3229_;
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_3214_, v_c_3215_);
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
return v___x_3231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality___boxed(lean_object* v_p_3232_, lean_object* v_c_3233_, lean_object* v_m_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_){
_start:
{
uint8_t v_a_boxed_3245_; lean_object* v_res_3246_; 
v_a_boxed_3245_ = lean_unbox(v_a_3238_);
v_res_3246_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3232_, v_c_3233_, v_m_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_boxed_3245_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
lean_dec(v_a_3241_);
lean_dec_ref(v_a_3240_);
lean_dec(v_a_3239_);
lean_dec_ref(v_a_3237_);
lean_dec(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec(v_m_3234_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(lean_object* v_p_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, uint8_t v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_){
_start:
{
uint8_t v_possible_3258_; 
v_possible_3258_ = lean_ctor_get_uint8(v_p_3247_, sizeof(void*)*7);
if (v_possible_3258_ == 0)
{
lean_object* v___x_3259_; 
v___x_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3259_, 0, v_p_3247_);
return v___x_3259_;
}
else
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_3247_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v_p_3247_);
return v___x_3261_;
}
else
{
lean_object* v_val_3262_; lean_object* v_fst_3263_; lean_object* v_snd_3264_; lean_object* v___x_3265_; 
v_val_3262_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_val_3262_);
lean_dec_ref(v___x_3260_);
v_fst_3263_ = lean_ctor_get(v_val_3262_, 0);
lean_inc(v_fst_3263_);
v_snd_3264_ = lean_ctor_get(v_val_3262_, 1);
lean_inc(v_snd_3264_);
lean_dec(v_val_3262_);
v___x_3265_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3247_, v_fst_3263_, v_snd_3264_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_);
lean_dec(v_snd_3264_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref(v___x_3265_);
v_p_3247_ = v_a_3266_;
goto _start;
}
else
{
return v___x_3265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities___boxed(lean_object* v_p_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
uint8_t v_a_boxed_3279_; lean_object* v_res_3280_; 
v_a_boxed_3279_ = lean_unbox(v_a_3272_);
v_res_3280_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_boxed_3279_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec(v_a_3273_);
lean_dec_ref(v_a_3271_);
lean_dec(v_a_3270_);
lean_dec(v_a_3269_);
return v_res_3280_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2(void){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3287_ = lean_box(0);
v___x_3288_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1));
v___x_3289_ = l_Lean_Expr_const___override(v___x_3288_, v___x_3287_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object* v_c_3290_, lean_object* v_x_3291_, lean_object* v_p_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, uint8_t v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3294_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref(v___x_3303_);
v___x_3305_ = lean_box(v_a_3296_);
lean_inc(v_a_3301_);
lean_inc_ref(v_a_3300_);
lean_inc(v_a_3299_);
lean_inc_ref(v_a_3298_);
lean_inc(v_a_3297_);
lean_inc_ref(v_a_3295_);
lean_inc(v_a_3294_);
lean_inc(v_a_3293_);
v___x_3306_ = lean_apply_10(v_p_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v___x_3305_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, lean_box(0));
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3332_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3332_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3332_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___y_3313_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3311_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2);
v___x_3321_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3322_ = lean_int_dec_le(v___x_3321_, v_c_3290_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3323_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3324_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3325_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3326_ = lean_int_neg(v_c_3290_);
v___x_3327_ = l_Int_toNat(v___x_3326_);
lean_dec(v___x_3326_);
v___x_3328_ = l_Lean_instToExprInt_mkNat(v___x_3327_);
v___x_3329_ = l_Lean_mkApp3(v___x_3323_, v___x_3324_, v___x_3325_, v___x_3328_);
v___y_3313_ = v___x_3329_;
goto v___jp_3312_;
}
else
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = l_Int_toNat(v_c_3290_);
v___x_3331_ = l_Lean_instToExprInt_mkNat(v___x_3330_);
v___y_3313_ = v___x_3331_;
goto v___jp_3312_;
}
v___jp_3312_:
{
lean_object* v_nil_3314_; lean_object* v_cons_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3319_; 
v_nil_3314_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3315_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3316_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3314_, v_cons_3315_, v_x_3291_);
v___x_3317_ = l_Lean_mkApp4(v___x_3311_, v___y_3313_, v___x_3316_, v_a_3304_, v_a_3307_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3317_);
v___x_3319_ = v___x_3309_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
else
{
lean_dec(v_a_3304_);
return v___x_3306_;
}
}
else
{
lean_dec_ref(v_p_3292_);
return v___x_3303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object* v_c_3333_, lean_object* v_x_3334_, lean_object* v_p_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_){
_start:
{
uint8_t v_a_boxed_3346_; lean_object* v_res_3347_; 
v_a_boxed_3346_ = lean_unbox(v_a_3339_);
v_res_3347_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(v_c_3333_, v_x_3334_, v_p_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_boxed_3346_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_);
lean_dec(v_a_3344_);
lean_dec_ref(v_a_3343_);
lean_dec(v_a_3342_);
lean_dec_ref(v_a_3341_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3338_);
lean_dec(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec(v_x_3334_);
lean_dec(v_c_3333_);
return v_res_3347_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2(void){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3354_ = lean_box(0);
v___x_3355_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1));
v___x_3356_ = l_Lean_Expr_const___override(v___x_3355_, v___x_3354_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(lean_object* v_c_3357_, lean_object* v_x_3358_, lean_object* v_p_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, uint8_t v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3361_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref(v___x_3370_);
v___x_3372_ = lean_box(v_a_3363_);
lean_inc(v_a_3368_);
lean_inc_ref(v_a_3367_);
lean_inc(v_a_3366_);
lean_inc_ref(v_a_3365_);
lean_inc(v_a_3364_);
lean_inc_ref(v_a_3362_);
lean_inc(v_a_3361_);
lean_inc(v_a_3360_);
v___x_3373_ = lean_apply_10(v_p_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v___x_3372_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, lean_box(0));
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3399_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3376_ = v___x_3373_;
v_isShared_3377_ = v_isSharedCheck_3399_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3373_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3399_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3378_; lean_object* v___y_3380_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v___x_3378_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2);
v___x_3388_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3389_ = lean_int_dec_le(v___x_3388_, v_c_3357_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3390_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3391_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3392_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3393_ = lean_int_neg(v_c_3357_);
v___x_3394_ = l_Int_toNat(v___x_3393_);
lean_dec(v___x_3393_);
v___x_3395_ = l_Lean_instToExprInt_mkNat(v___x_3394_);
v___x_3396_ = l_Lean_mkApp3(v___x_3390_, v___x_3391_, v___x_3392_, v___x_3395_);
v___y_3380_ = v___x_3396_;
goto v___jp_3379_;
}
else
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = l_Int_toNat(v_c_3357_);
v___x_3398_ = l_Lean_instToExprInt_mkNat(v___x_3397_);
v___y_3380_ = v___x_3398_;
goto v___jp_3379_;
}
v___jp_3379_:
{
lean_object* v_nil_3381_; lean_object* v_cons_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3386_; 
v_nil_3381_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3382_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3383_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3381_, v_cons_3382_, v_x_3358_);
v___x_3384_ = l_Lean_mkApp4(v___x_3378_, v___y_3380_, v___x_3383_, v_a_3371_, v_a_3374_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v___x_3384_);
v___x_3386_ = v___x_3376_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
else
{
lean_dec(v_a_3371_);
return v___x_3373_;
}
}
else
{
lean_dec_ref(v_p_3359_);
return v___x_3370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed(lean_object* v_c_3400_, lean_object* v_x_3401_, lean_object* v_p_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_){
_start:
{
uint8_t v_a_boxed_3413_; lean_object* v_res_3414_; 
v_a_boxed_3413_ = lean_unbox(v_a_3406_);
v_res_3414_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(v_c_3400_, v_x_3401_, v_p_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_boxed_3413_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_);
lean_dec(v_a_3411_);
lean_dec_ref(v_a_3410_);
lean_dec(v_a_3409_);
lean_dec_ref(v_a_3408_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3405_);
lean_dec(v_a_3404_);
lean_dec(v_a_3403_);
lean_dec(v_x_3401_);
lean_dec(v_c_3400_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(lean_object* v_prf_x3f_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, uint8_t v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
if (lean_obj_tag(v_prf_x3f_3415_) == 0)
{
lean_object* v___x_3426_; uint8_t v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3426_ = lean_box(0);
v___x_3427_ = 0;
v___x_3428_ = lean_box(0);
v___x_3429_ = l_Lean_Meta_mkFreshExprMVar(v___x_3426_, v___x_3427_, v___x_3428_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; uint8_t v___x_3431_; lean_object* v___x_3432_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref(v___x_3429_);
v___x_3431_ = 0;
v___x_3432_ = l_Lean_Meta_mkSorry(v_a_3430_, v___x_3431_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
return v___x_3432_;
}
else
{
return v___x_3429_;
}
}
else
{
lean_object* v_val_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v_val_3433_ = lean_ctor_get(v_prf_x3f_3415_, 0);
lean_inc(v_val_3433_);
lean_dec_ref(v_prf_x3f_3415_);
v___x_3434_ = lean_box(v___y_3419_);
lean_inc(v___y_3424_);
lean_inc_ref(v___y_3423_);
lean_inc(v___y_3422_);
lean_inc_ref(v___y_3421_);
lean_inc(v___y_3420_);
lean_inc_ref(v___y_3418_);
lean_inc(v___y_3417_);
lean_inc(v___y_3416_);
v___x_3435_ = lean_apply_10(v_val_3433_, v___y_3416_, v___y_3417_, v___y_3418_, v___x_3434_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, lean_box(0));
return v___x_3435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed(lean_object* v_prf_x3f_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
uint8_t v___y_833__boxed_3447_; lean_object* v_res_3448_; 
v___y_833__boxed_3447_ = lean_unbox(v___y_3440_);
v_res_3448_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(v_prf_x3f_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_833__boxed_3447_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec(v___y_3437_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality(lean_object* v_p_3449_, lean_object* v_const_3450_, lean_object* v_coeffs_3451_, lean_object* v_prf_x3f_3452_){
_start:
{
lean_object* v_assumptions_3453_; lean_object* v_numVars_3454_; lean_object* v_constraints_3455_; lean_object* v_equalities_3456_; lean_object* v_eliminations_3457_; uint8_t v_possible_3458_; lean_object* v_proveFalse_x3f_3459_; lean_object* v_explanation_x3f_3460_; lean_object* v_prf_3461_; lean_object* v_i_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v_p_x27_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v_f_3471_; lean_object* v_f_3472_; lean_object* v_f_3473_; lean_object* v___x_3474_; 
v_assumptions_3453_ = lean_ctor_get(v_p_3449_, 0);
v_numVars_3454_ = lean_ctor_get(v_p_3449_, 1);
v_constraints_3455_ = lean_ctor_get(v_p_3449_, 2);
v_equalities_3456_ = lean_ctor_get(v_p_3449_, 3);
v_eliminations_3457_ = lean_ctor_get(v_p_3449_, 4);
v_possible_3458_ = lean_ctor_get_uint8(v_p_3449_, sizeof(void*)*7);
v_proveFalse_x3f_3459_ = lean_ctor_get(v_p_3449_, 5);
v_explanation_x3f_3460_ = lean_ctor_get(v_p_3449_, 6);
v_prf_3461_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3461_, 0, v_prf_x3f_3452_);
v_i_3462_ = lean_array_get_size(v_assumptions_3453_);
lean_inc(v_coeffs_3451_);
lean_inc(v_const_3450_);
v___x_3463_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed), 13, 3);
lean_closure_set(v___x_3463_, 0, v_const_3450_);
lean_closure_set(v___x_3463_, 1, v_coeffs_3451_);
lean_closure_set(v___x_3463_, 2, v_prf_3461_);
lean_inc_ref(v_assumptions_3453_);
v___x_3464_ = lean_array_push(v_assumptions_3453_, v___x_3463_);
lean_inc_ref(v_explanation_x3f_3460_);
lean_inc(v_proveFalse_x3f_3459_);
lean_inc(v_eliminations_3457_);
lean_inc_ref(v_equalities_3456_);
lean_inc_ref(v_constraints_3455_);
lean_inc(v_numVars_3454_);
v_p_x27_3465_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3465_, 0, v___x_3464_);
lean_ctor_set(v_p_x27_3465_, 1, v_numVars_3454_);
lean_ctor_set(v_p_x27_3465_, 2, v_constraints_3455_);
lean_ctor_set(v_p_x27_3465_, 3, v_equalities_3456_);
lean_ctor_set(v_p_x27_3465_, 4, v_eliminations_3457_);
lean_ctor_set(v_p_x27_3465_, 5, v_proveFalse_x3f_3459_);
lean_ctor_set(v_p_x27_3465_, 6, v_explanation_x3f_3460_);
lean_ctor_set_uint8(v_p_x27_3465_, sizeof(void*)*7, v_possible_3458_);
v___x_3466_ = lean_int_neg(v_const_3450_);
lean_dec(v_const_3450_);
v___x_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
v___x_3468_ = lean_box(0);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3467_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
lean_inc(v_coeffs_3451_);
lean_inc_ref(v___x_3469_);
v___x_3470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set(v___x_3470_, 1, v_coeffs_3451_);
lean_ctor_set(v___x_3470_, 2, v_i_3462_);
v_f_3471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3471_, 0, v_coeffs_3451_);
lean_ctor_set(v_f_3471_, 1, v___x_3469_);
lean_ctor_set(v_f_3471_, 2, v___x_3470_);
v_f_3472_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3449_, v_f_3471_);
v_f_3473_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3472_);
v___x_3474_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3465_, v_f_3473_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality(lean_object* v_p_3475_, lean_object* v_const_3476_, lean_object* v_coeffs_3477_, lean_object* v_prf_x3f_3478_){
_start:
{
lean_object* v_assumptions_3479_; lean_object* v_numVars_3480_; lean_object* v_constraints_3481_; lean_object* v_equalities_3482_; lean_object* v_eliminations_3483_; uint8_t v_possible_3484_; lean_object* v_proveFalse_x3f_3485_; lean_object* v_explanation_x3f_3486_; lean_object* v_prf_3487_; lean_object* v_i_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v_p_x27_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v_f_3496_; lean_object* v_f_3497_; lean_object* v_f_3498_; lean_object* v___x_3499_; 
v_assumptions_3479_ = lean_ctor_get(v_p_3475_, 0);
v_numVars_3480_ = lean_ctor_get(v_p_3475_, 1);
v_constraints_3481_ = lean_ctor_get(v_p_3475_, 2);
v_equalities_3482_ = lean_ctor_get(v_p_3475_, 3);
v_eliminations_3483_ = lean_ctor_get(v_p_3475_, 4);
v_possible_3484_ = lean_ctor_get_uint8(v_p_3475_, sizeof(void*)*7);
v_proveFalse_x3f_3485_ = lean_ctor_get(v_p_3475_, 5);
v_explanation_x3f_3486_ = lean_ctor_get(v_p_3475_, 6);
v_prf_3487_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3487_, 0, v_prf_x3f_3478_);
v_i_3488_ = lean_array_get_size(v_assumptions_3479_);
lean_inc(v_coeffs_3477_);
lean_inc(v_const_3476_);
v___x_3489_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed), 13, 3);
lean_closure_set(v___x_3489_, 0, v_const_3476_);
lean_closure_set(v___x_3489_, 1, v_coeffs_3477_);
lean_closure_set(v___x_3489_, 2, v_prf_3487_);
lean_inc_ref(v_assumptions_3479_);
v___x_3490_ = lean_array_push(v_assumptions_3479_, v___x_3489_);
lean_inc_ref(v_explanation_x3f_3486_);
lean_inc(v_proveFalse_x3f_3485_);
lean_inc(v_eliminations_3483_);
lean_inc_ref(v_equalities_3482_);
lean_inc_ref(v_constraints_3481_);
lean_inc(v_numVars_3480_);
v_p_x27_3491_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3491_, 0, v___x_3490_);
lean_ctor_set(v_p_x27_3491_, 1, v_numVars_3480_);
lean_ctor_set(v_p_x27_3491_, 2, v_constraints_3481_);
lean_ctor_set(v_p_x27_3491_, 3, v_equalities_3482_);
lean_ctor_set(v_p_x27_3491_, 4, v_eliminations_3483_);
lean_ctor_set(v_p_x27_3491_, 5, v_proveFalse_x3f_3485_);
lean_ctor_set(v_p_x27_3491_, 6, v_explanation_x3f_3486_);
lean_ctor_set_uint8(v_p_x27_3491_, sizeof(void*)*7, v_possible_3484_);
v___x_3492_ = lean_int_neg(v_const_3476_);
lean_dec(v_const_3476_);
v___x_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
lean_inc_ref(v___x_3493_);
v___x_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
lean_inc(v_coeffs_3477_);
lean_inc_ref(v___x_3494_);
v___x_3495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
lean_ctor_set(v___x_3495_, 1, v_coeffs_3477_);
lean_ctor_set(v___x_3495_, 2, v_i_3488_);
v_f_3496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3496_, 0, v_coeffs_3477_);
lean_ctor_set(v_f_3496_, 1, v___x_3494_);
lean_ctor_set(v_f_3496_, 2, v___x_3495_);
v_f_3497_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3475_, v_f_3496_);
v_f_3498_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3497_);
v___x_3499_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3491_, v_f_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(lean_object* v_x_3500_, lean_object* v_x_3501_){
_start:
{
if (lean_obj_tag(v_x_3501_) == 0)
{
return v_x_3500_;
}
else
{
lean_object* v_head_3502_; lean_object* v_snd_3503_; lean_object* v_tail_3504_; lean_object* v_fst_3505_; lean_object* v_fst_3506_; lean_object* v_snd_3507_; lean_object* v___x_3508_; 
v_head_3502_ = lean_ctor_get(v_x_3501_, 0);
lean_inc(v_head_3502_);
v_snd_3503_ = lean_ctor_get(v_head_3502_, 1);
lean_inc(v_snd_3503_);
v_tail_3504_ = lean_ctor_get(v_x_3501_, 1);
lean_inc(v_tail_3504_);
lean_dec_ref(v_x_3501_);
v_fst_3505_ = lean_ctor_get(v_head_3502_, 0);
lean_inc(v_fst_3505_);
lean_dec(v_head_3502_);
v_fst_3506_ = lean_ctor_get(v_snd_3503_, 0);
lean_inc(v_fst_3506_);
v_snd_3507_ = lean_ctor_get(v_snd_3503_, 1);
lean_inc(v_snd_3507_);
lean_dec(v_snd_3503_);
v___x_3508_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality(v_x_3500_, v_fst_3505_, v_fst_3506_, v_snd_3507_);
v_x_3500_ = v___x_3508_;
v_x_3501_ = v_tail_3504_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequalities(lean_object* v_p_3510_, lean_object* v_ineqs_3511_){
_start:
{
lean_object* v___x_3512_; 
v___x_3512_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(v_p_3510_, v_ineqs_3511_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(lean_object* v_x_3513_, lean_object* v_x_3514_){
_start:
{
if (lean_obj_tag(v_x_3514_) == 0)
{
return v_x_3513_;
}
else
{
lean_object* v_head_3515_; lean_object* v_snd_3516_; lean_object* v_tail_3517_; lean_object* v_fst_3518_; lean_object* v_fst_3519_; lean_object* v_snd_3520_; lean_object* v___x_3521_; 
v_head_3515_ = lean_ctor_get(v_x_3514_, 0);
lean_inc(v_head_3515_);
v_snd_3516_ = lean_ctor_get(v_head_3515_, 1);
lean_inc(v_snd_3516_);
v_tail_3517_ = lean_ctor_get(v_x_3514_, 1);
lean_inc(v_tail_3517_);
lean_dec_ref(v_x_3514_);
v_fst_3518_ = lean_ctor_get(v_head_3515_, 0);
lean_inc(v_fst_3518_);
lean_dec(v_head_3515_);
v_fst_3519_ = lean_ctor_get(v_snd_3516_, 0);
lean_inc(v_fst_3519_);
v_snd_3520_ = lean_ctor_get(v_snd_3516_, 1);
lean_inc(v_snd_3520_);
lean_dec(v_snd_3516_);
v___x_3521_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality(v_x_3513_, v_fst_3518_, v_fst_3519_, v_snd_3520_);
v_x_3513_ = v___x_3521_;
v_x_3514_ = v_tail_3517_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEqualities(lean_object* v_p_3523_, lean_object* v_eqs_3524_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(v_p_3523_, v_eqs_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0(lean_object* v___x_3532_, lean_object* v_x_3533_){
_start:
{
lean_object* v_constraint_3534_; lean_object* v_coeffs_3535_; lean_object* v_lowerBound_3536_; lean_object* v_upperBound_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___y_3542_; lean_object* v___y_3543_; 
v_constraint_3534_ = lean_ctor_get(v_x_3533_, 1);
lean_inc_ref(v_constraint_3534_);
v_coeffs_3535_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_coeffs_3535_);
lean_dec_ref(v_x_3533_);
v_lowerBound_3536_ = lean_ctor_get(v_constraint_3534_, 0);
lean_inc(v_lowerBound_3536_);
v_upperBound_3537_ = lean_ctor_get(v_constraint_3534_, 1);
lean_inc(v_upperBound_3537_);
lean_dec_ref(v_constraint_3534_);
v___x_3538_ = l_List_toString___redArg(v___x_3532_, v_coeffs_3535_);
v___x_3539_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3540_ = lean_string_append(v___x_3538_, v___x_3539_);
if (lean_obj_tag(v_lowerBound_3536_) == 0)
{
if (lean_obj_tag(v_upperBound_3537_) == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3549_ = lean_string_append(v___x_3540_, v___x_3548_);
return v___x_3549_;
}
else
{
lean_object* v_val_3550_; lean_object* v___x_3551_; lean_object* v___y_3553_; lean_object* v_intZero_3558_; uint8_t v_isNeg_3559_; 
v_val_3550_ = lean_ctor_get(v_upperBound_3537_, 0);
lean_inc(v_val_3550_);
lean_dec_ref(v_upperBound_3537_);
v___x_3551_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3558_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3559_ = lean_int_dec_lt(v_val_3550_, v_intZero_3558_);
if (v_isNeg_3559_ == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3561_; 
v_a_3560_ = lean_nat_abs(v_val_3550_);
lean_dec(v_val_3550_);
v___x_3561_ = l_Nat_reprFast(v_a_3560_);
v___y_3553_ = v___x_3561_;
goto v___jp_3552_;
}
else
{
lean_object* v_abs_3562_; lean_object* v_one_3563_; lean_object* v_a_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v_abs_3562_ = lean_nat_abs(v_val_3550_);
lean_dec(v_val_3550_);
v_one_3563_ = lean_unsigned_to_nat(1u);
v_a_3564_ = lean_nat_sub(v_abs_3562_, v_one_3563_);
lean_dec(v_abs_3562_);
v___x_3565_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3566_ = lean_nat_add(v_a_3564_, v_one_3563_);
lean_dec(v_a_3564_);
v___x_3567_ = l_Nat_reprFast(v___x_3566_);
v___x_3568_ = lean_string_append(v___x_3565_, v___x_3567_);
lean_dec_ref(v___x_3567_);
v___y_3553_ = v___x_3568_;
goto v___jp_3552_;
}
v___jp_3552_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3554_ = lean_string_append(v___x_3551_, v___y_3553_);
lean_dec_ref(v___y_3553_);
v___x_3555_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3556_ = lean_string_append(v___x_3554_, v___x_3555_);
v___x_3557_ = lean_string_append(v___x_3540_, v___x_3556_);
lean_dec_ref(v___x_3556_);
return v___x_3557_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3537_) == 0)
{
lean_object* v_val_3569_; lean_object* v___x_3570_; lean_object* v___y_3572_; lean_object* v_intZero_3577_; uint8_t v_isNeg_3578_; 
v_val_3569_ = lean_ctor_get(v_lowerBound_3536_, 0);
lean_inc(v_val_3569_);
lean_dec_ref(v_lowerBound_3536_);
v___x_3570_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3577_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3578_ = lean_int_dec_lt(v_val_3569_, v_intZero_3577_);
if (v_isNeg_3578_ == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3580_; 
v_a_3579_ = lean_nat_abs(v_val_3569_);
lean_dec(v_val_3569_);
v___x_3580_ = l_Nat_reprFast(v_a_3579_);
v___y_3572_ = v___x_3580_;
goto v___jp_3571_;
}
else
{
lean_object* v_abs_3581_; lean_object* v_one_3582_; lean_object* v_a_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v_abs_3581_ = lean_nat_abs(v_val_3569_);
lean_dec(v_val_3569_);
v_one_3582_ = lean_unsigned_to_nat(1u);
v_a_3583_ = lean_nat_sub(v_abs_3581_, v_one_3582_);
lean_dec(v_abs_3581_);
v___x_3584_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3585_ = lean_nat_add(v_a_3583_, v_one_3582_);
lean_dec(v_a_3583_);
v___x_3586_ = l_Nat_reprFast(v___x_3585_);
v___x_3587_ = lean_string_append(v___x_3584_, v___x_3586_);
lean_dec_ref(v___x_3586_);
v___y_3572_ = v___x_3587_;
goto v___jp_3571_;
}
v___jp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3573_ = lean_string_append(v___x_3570_, v___y_3572_);
lean_dec_ref(v___y_3572_);
v___x_3574_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3575_ = lean_string_append(v___x_3573_, v___x_3574_);
v___x_3576_ = lean_string_append(v___x_3540_, v___x_3575_);
lean_dec_ref(v___x_3575_);
return v___x_3576_;
}
}
else
{
lean_object* v_val_3588_; lean_object* v_val_3589_; uint8_t v___x_3590_; 
v_val_3588_ = lean_ctor_get(v_lowerBound_3536_, 0);
lean_inc(v_val_3588_);
lean_dec_ref(v_lowerBound_3536_);
v_val_3589_ = lean_ctor_get(v_upperBound_3537_, 0);
lean_inc(v_val_3589_);
lean_dec_ref(v_upperBound_3537_);
v___x_3590_ = lean_int_dec_lt(v_val_3589_, v_val_3588_);
if (v___x_3590_ == 0)
{
uint8_t v___x_3591_; 
v___x_3591_ = lean_int_dec_eq(v_val_3588_, v_val_3589_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; lean_object* v___y_3594_; lean_object* v_intZero_3609_; uint8_t v_isNeg_3610_; 
v___x_3592_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3609_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3610_ = lean_int_dec_lt(v_val_3588_, v_intZero_3609_);
if (v_isNeg_3610_ == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3612_; 
v_a_3611_ = lean_nat_abs(v_val_3588_);
lean_dec(v_val_3588_);
v___x_3612_ = l_Nat_reprFast(v_a_3611_);
v___y_3594_ = v___x_3612_;
goto v___jp_3593_;
}
else
{
lean_object* v_abs_3613_; lean_object* v_one_3614_; lean_object* v_a_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v_abs_3613_ = lean_nat_abs(v_val_3588_);
lean_dec(v_val_3588_);
v_one_3614_ = lean_unsigned_to_nat(1u);
v_a_3615_ = lean_nat_sub(v_abs_3613_, v_one_3614_);
lean_dec(v_abs_3613_);
v___x_3616_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3617_ = lean_nat_add(v_a_3615_, v_one_3614_);
lean_dec(v_a_3615_);
v___x_3618_ = l_Nat_reprFast(v___x_3617_);
v___x_3619_ = lean_string_append(v___x_3616_, v___x_3618_);
lean_dec_ref(v___x_3618_);
v___y_3594_ = v___x_3619_;
goto v___jp_3593_;
}
v___jp_3593_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v_intZero_3598_; uint8_t v_isNeg_3599_; 
v___x_3595_ = lean_string_append(v___x_3592_, v___y_3594_);
lean_dec_ref(v___y_3594_);
v___x_3596_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3597_ = lean_string_append(v___x_3595_, v___x_3596_);
v_intZero_3598_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3599_ = lean_int_dec_lt(v_val_3589_, v_intZero_3598_);
if (v_isNeg_3599_ == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3601_; 
v_a_3600_ = lean_nat_abs(v_val_3589_);
lean_dec(v_val_3589_);
v___x_3601_ = l_Nat_reprFast(v_a_3600_);
v___y_3542_ = v___x_3597_;
v___y_3543_ = v___x_3601_;
goto v___jp_3541_;
}
else
{
lean_object* v_abs_3602_; lean_object* v_one_3603_; lean_object* v_a_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v_abs_3602_ = lean_nat_abs(v_val_3589_);
lean_dec(v_val_3589_);
v_one_3603_ = lean_unsigned_to_nat(1u);
v_a_3604_ = lean_nat_sub(v_abs_3602_, v_one_3603_);
lean_dec(v_abs_3602_);
v___x_3605_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3606_ = lean_nat_add(v_a_3604_, v_one_3603_);
lean_dec(v_a_3604_);
v___x_3607_ = l_Nat_reprFast(v___x_3606_);
v___x_3608_ = lean_string_append(v___x_3605_, v___x_3607_);
lean_dec_ref(v___x_3607_);
v___y_3542_ = v___x_3597_;
v___y_3543_ = v___x_3608_;
goto v___jp_3541_;
}
}
}
else
{
lean_object* v___x_3620_; lean_object* v___y_3622_; lean_object* v_intZero_3627_; uint8_t v_isNeg_3628_; 
lean_dec(v_val_3589_);
v___x_3620_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3627_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3628_ = lean_int_dec_lt(v_val_3588_, v_intZero_3627_);
if (v_isNeg_3628_ == 0)
{
lean_object* v_a_3629_; lean_object* v___x_3630_; 
v_a_3629_ = lean_nat_abs(v_val_3588_);
lean_dec(v_val_3588_);
v___x_3630_ = l_Nat_reprFast(v_a_3629_);
v___y_3622_ = v___x_3630_;
goto v___jp_3621_;
}
else
{
lean_object* v_abs_3631_; lean_object* v_one_3632_; lean_object* v_a_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v_abs_3631_ = lean_nat_abs(v_val_3588_);
lean_dec(v_val_3588_);
v_one_3632_ = lean_unsigned_to_nat(1u);
v_a_3633_ = lean_nat_sub(v_abs_3631_, v_one_3632_);
lean_dec(v_abs_3631_);
v___x_3634_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3635_ = lean_nat_add(v_a_3633_, v_one_3632_);
lean_dec(v_a_3633_);
v___x_3636_ = l_Nat_reprFast(v___x_3635_);
v___x_3637_ = lean_string_append(v___x_3634_, v___x_3636_);
lean_dec_ref(v___x_3636_);
v___y_3622_ = v___x_3637_;
goto v___jp_3621_;
}
v___jp_3621_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3623_ = lean_string_append(v___x_3620_, v___y_3622_);
lean_dec_ref(v___y_3622_);
v___x_3624_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3625_ = lean_string_append(v___x_3623_, v___x_3624_);
v___x_3626_ = lean_string_append(v___x_3540_, v___x_3625_);
lean_dec_ref(v___x_3625_);
return v___x_3626_;
}
}
}
else
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
lean_dec(v_val_3589_);
lean_dec(v_val_3588_);
v___x_3638_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3639_ = lean_string_append(v___x_3540_, v___x_3638_);
return v___x_3639_;
}
}
}
v___jp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3544_ = lean_string_append(v___y_3542_, v___y_3543_);
lean_dec_ref(v___y_3543_);
v___x_3545_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3546_ = lean_string_append(v___x_3544_, v___x_3545_);
v___x_3547_ = lean_string_append(v___x_3540_, v___x_3546_);
lean_dec_ref(v___x_3546_);
return v___x_3547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1(lean_object* v___x_3640_, lean_object* v_x_3641_){
_start:
{
lean_object* v_fst_3642_; lean_object* v_constraint_3643_; lean_object* v_coeffs_3644_; lean_object* v_lowerBound_3645_; lean_object* v_upperBound_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___y_3651_; lean_object* v___y_3652_; 
v_fst_3642_ = lean_ctor_get(v_x_3641_, 0);
lean_inc(v_fst_3642_);
lean_dec_ref(v_x_3641_);
v_constraint_3643_ = lean_ctor_get(v_fst_3642_, 1);
lean_inc_ref(v_constraint_3643_);
v_coeffs_3644_ = lean_ctor_get(v_fst_3642_, 0);
lean_inc(v_coeffs_3644_);
lean_dec(v_fst_3642_);
v_lowerBound_3645_ = lean_ctor_get(v_constraint_3643_, 0);
lean_inc(v_lowerBound_3645_);
v_upperBound_3646_ = lean_ctor_get(v_constraint_3643_, 1);
lean_inc(v_upperBound_3646_);
lean_dec_ref(v_constraint_3643_);
v___x_3647_ = l_List_toString___redArg(v___x_3640_, v_coeffs_3644_);
v___x_3648_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3649_ = lean_string_append(v___x_3647_, v___x_3648_);
if (lean_obj_tag(v_lowerBound_3645_) == 0)
{
if (lean_obj_tag(v_upperBound_3646_) == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3658_ = lean_string_append(v___x_3649_, v___x_3657_);
return v___x_3658_;
}
else
{
lean_object* v_val_3659_; lean_object* v___x_3660_; lean_object* v___y_3662_; lean_object* v_intZero_3667_; uint8_t v_isNeg_3668_; 
v_val_3659_ = lean_ctor_get(v_upperBound_3646_, 0);
lean_inc(v_val_3659_);
lean_dec_ref(v_upperBound_3646_);
v___x_3660_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3667_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3668_ = lean_int_dec_lt(v_val_3659_, v_intZero_3667_);
if (v_isNeg_3668_ == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3670_; 
v_a_3669_ = lean_nat_abs(v_val_3659_);
lean_dec(v_val_3659_);
v___x_3670_ = l_Nat_reprFast(v_a_3669_);
v___y_3662_ = v___x_3670_;
goto v___jp_3661_;
}
else
{
lean_object* v_abs_3671_; lean_object* v_one_3672_; lean_object* v_a_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v_abs_3671_ = lean_nat_abs(v_val_3659_);
lean_dec(v_val_3659_);
v_one_3672_ = lean_unsigned_to_nat(1u);
v_a_3673_ = lean_nat_sub(v_abs_3671_, v_one_3672_);
lean_dec(v_abs_3671_);
v___x_3674_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3675_ = lean_nat_add(v_a_3673_, v_one_3672_);
lean_dec(v_a_3673_);
v___x_3676_ = l_Nat_reprFast(v___x_3675_);
v___x_3677_ = lean_string_append(v___x_3674_, v___x_3676_);
lean_dec_ref(v___x_3676_);
v___y_3662_ = v___x_3677_;
goto v___jp_3661_;
}
v___jp_3661_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3663_ = lean_string_append(v___x_3660_, v___y_3662_);
lean_dec_ref(v___y_3662_);
v___x_3664_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3665_ = lean_string_append(v___x_3663_, v___x_3664_);
v___x_3666_ = lean_string_append(v___x_3649_, v___x_3665_);
lean_dec_ref(v___x_3665_);
return v___x_3666_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3646_) == 0)
{
lean_object* v_val_3678_; lean_object* v___x_3679_; lean_object* v___y_3681_; lean_object* v_intZero_3686_; uint8_t v_isNeg_3687_; 
v_val_3678_ = lean_ctor_get(v_lowerBound_3645_, 0);
lean_inc(v_val_3678_);
lean_dec_ref(v_lowerBound_3645_);
v___x_3679_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3686_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3687_ = lean_int_dec_lt(v_val_3678_, v_intZero_3686_);
if (v_isNeg_3687_ == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3689_; 
v_a_3688_ = lean_nat_abs(v_val_3678_);
lean_dec(v_val_3678_);
v___x_3689_ = l_Nat_reprFast(v_a_3688_);
v___y_3681_ = v___x_3689_;
goto v___jp_3680_;
}
else
{
lean_object* v_abs_3690_; lean_object* v_one_3691_; lean_object* v_a_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v_abs_3690_ = lean_nat_abs(v_val_3678_);
lean_dec(v_val_3678_);
v_one_3691_ = lean_unsigned_to_nat(1u);
v_a_3692_ = lean_nat_sub(v_abs_3690_, v_one_3691_);
lean_dec(v_abs_3690_);
v___x_3693_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3694_ = lean_nat_add(v_a_3692_, v_one_3691_);
lean_dec(v_a_3692_);
v___x_3695_ = l_Nat_reprFast(v___x_3694_);
v___x_3696_ = lean_string_append(v___x_3693_, v___x_3695_);
lean_dec_ref(v___x_3695_);
v___y_3681_ = v___x_3696_;
goto v___jp_3680_;
}
v___jp_3680_:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3682_ = lean_string_append(v___x_3679_, v___y_3681_);
lean_dec_ref(v___y_3681_);
v___x_3683_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3684_ = lean_string_append(v___x_3682_, v___x_3683_);
v___x_3685_ = lean_string_append(v___x_3649_, v___x_3684_);
lean_dec_ref(v___x_3684_);
return v___x_3685_;
}
}
else
{
lean_object* v_val_3697_; lean_object* v_val_3698_; uint8_t v___x_3699_; 
v_val_3697_ = lean_ctor_get(v_lowerBound_3645_, 0);
lean_inc(v_val_3697_);
lean_dec_ref(v_lowerBound_3645_);
v_val_3698_ = lean_ctor_get(v_upperBound_3646_, 0);
lean_inc(v_val_3698_);
lean_dec_ref(v_upperBound_3646_);
v___x_3699_ = lean_int_dec_lt(v_val_3698_, v_val_3697_);
if (v___x_3699_ == 0)
{
uint8_t v___x_3700_; 
v___x_3700_ = lean_int_dec_eq(v_val_3697_, v_val_3698_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; lean_object* v___y_3703_; lean_object* v_intZero_3718_; uint8_t v_isNeg_3719_; 
v___x_3701_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3718_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3719_ = lean_int_dec_lt(v_val_3697_, v_intZero_3718_);
if (v_isNeg_3719_ == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3721_; 
v_a_3720_ = lean_nat_abs(v_val_3697_);
lean_dec(v_val_3697_);
v___x_3721_ = l_Nat_reprFast(v_a_3720_);
v___y_3703_ = v___x_3721_;
goto v___jp_3702_;
}
else
{
lean_object* v_abs_3722_; lean_object* v_one_3723_; lean_object* v_a_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v_abs_3722_ = lean_nat_abs(v_val_3697_);
lean_dec(v_val_3697_);
v_one_3723_ = lean_unsigned_to_nat(1u);
v_a_3724_ = lean_nat_sub(v_abs_3722_, v_one_3723_);
lean_dec(v_abs_3722_);
v___x_3725_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3726_ = lean_nat_add(v_a_3724_, v_one_3723_);
lean_dec(v_a_3724_);
v___x_3727_ = l_Nat_reprFast(v___x_3726_);
v___x_3728_ = lean_string_append(v___x_3725_, v___x_3727_);
lean_dec_ref(v___x_3727_);
v___y_3703_ = v___x_3728_;
goto v___jp_3702_;
}
v___jp_3702_:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v_intZero_3707_; uint8_t v_isNeg_3708_; 
v___x_3704_ = lean_string_append(v___x_3701_, v___y_3703_);
lean_dec_ref(v___y_3703_);
v___x_3705_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3706_ = lean_string_append(v___x_3704_, v___x_3705_);
v_intZero_3707_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3708_ = lean_int_dec_lt(v_val_3698_, v_intZero_3707_);
if (v_isNeg_3708_ == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3710_; 
v_a_3709_ = lean_nat_abs(v_val_3698_);
lean_dec(v_val_3698_);
v___x_3710_ = l_Nat_reprFast(v_a_3709_);
v___y_3651_ = v___x_3706_;
v___y_3652_ = v___x_3710_;
goto v___jp_3650_;
}
else
{
lean_object* v_abs_3711_; lean_object* v_one_3712_; lean_object* v_a_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v_abs_3711_ = lean_nat_abs(v_val_3698_);
lean_dec(v_val_3698_);
v_one_3712_ = lean_unsigned_to_nat(1u);
v_a_3713_ = lean_nat_sub(v_abs_3711_, v_one_3712_);
lean_dec(v_abs_3711_);
v___x_3714_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3715_ = lean_nat_add(v_a_3713_, v_one_3712_);
lean_dec(v_a_3713_);
v___x_3716_ = l_Nat_reprFast(v___x_3715_);
v___x_3717_ = lean_string_append(v___x_3714_, v___x_3716_);
lean_dec_ref(v___x_3716_);
v___y_3651_ = v___x_3706_;
v___y_3652_ = v___x_3717_;
goto v___jp_3650_;
}
}
}
else
{
lean_object* v___x_3729_; lean_object* v___y_3731_; lean_object* v_intZero_3736_; uint8_t v_isNeg_3737_; 
lean_dec(v_val_3698_);
v___x_3729_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3736_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3737_ = lean_int_dec_lt(v_val_3697_, v_intZero_3736_);
if (v_isNeg_3737_ == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3739_; 
v_a_3738_ = lean_nat_abs(v_val_3697_);
lean_dec(v_val_3697_);
v___x_3739_ = l_Nat_reprFast(v_a_3738_);
v___y_3731_ = v___x_3739_;
goto v___jp_3730_;
}
else
{
lean_object* v_abs_3740_; lean_object* v_one_3741_; lean_object* v_a_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v_abs_3740_ = lean_nat_abs(v_val_3697_);
lean_dec(v_val_3697_);
v_one_3741_ = lean_unsigned_to_nat(1u);
v_a_3742_ = lean_nat_sub(v_abs_3740_, v_one_3741_);
lean_dec(v_abs_3740_);
v___x_3743_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3744_ = lean_nat_add(v_a_3742_, v_one_3741_);
lean_dec(v_a_3742_);
v___x_3745_ = l_Nat_reprFast(v___x_3744_);
v___x_3746_ = lean_string_append(v___x_3743_, v___x_3745_);
lean_dec_ref(v___x_3745_);
v___y_3731_ = v___x_3746_;
goto v___jp_3730_;
}
v___jp_3730_:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3732_ = lean_string_append(v___x_3729_, v___y_3731_);
lean_dec_ref(v___y_3731_);
v___x_3733_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3734_ = lean_string_append(v___x_3732_, v___x_3733_);
v___x_3735_ = lean_string_append(v___x_3649_, v___x_3734_);
lean_dec_ref(v___x_3734_);
return v___x_3735_;
}
}
}
else
{
lean_object* v___x_3747_; lean_object* v___x_3748_; 
lean_dec(v_val_3698_);
lean_dec(v_val_3697_);
v___x_3747_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3748_ = lean_string_append(v___x_3649_, v___x_3747_);
return v___x_3748_;
}
}
}
v___jp_3650_:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3653_ = lean_string_append(v___y_3651_, v___y_3652_);
lean_dec_ref(v___y_3652_);
v___x_3654_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3655_ = lean_string_append(v___x_3653_, v___x_3654_);
v___x_3656_ = lean_string_append(v___x_3649_, v___x_3655_);
lean_dec_ref(v___x_3655_);
return v___x_3656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2(lean_object* v___f_3753_, lean_object* v___f_3754_, lean_object* v___f_3755_, lean_object* v_d_3756_){
_start:
{
lean_object* v_var_3757_; lean_object* v_irrelevant_3758_; lean_object* v_lowerBounds_3759_; lean_object* v_upperBounds_3760_; lean_object* v___x_3761_; lean_object* v_irrelevant_3762_; lean_object* v_lowerBounds_3763_; lean_object* v_upperBounds_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v_var_3757_ = lean_ctor_get(v_d_3756_, 0);
lean_inc(v_var_3757_);
v_irrelevant_3758_ = lean_ctor_get(v_d_3756_, 1);
lean_inc(v_irrelevant_3758_);
v_lowerBounds_3759_ = lean_ctor_get(v_d_3756_, 2);
lean_inc(v_lowerBounds_3759_);
v_upperBounds_3760_ = lean_ctor_get(v_d_3756_, 3);
lean_inc(v_upperBounds_3760_);
lean_dec_ref(v_d_3756_);
v___x_3761_ = lean_box(0);
v_irrelevant_3762_ = l_List_mapTR_loop___redArg(v___f_3753_, v_irrelevant_3758_, v___x_3761_);
lean_inc_ref(v___f_3754_);
v_lowerBounds_3763_ = l_List_mapTR_loop___redArg(v___f_3754_, v_lowerBounds_3759_, v___x_3761_);
v_upperBounds_3764_ = l_List_mapTR_loop___redArg(v___f_3754_, v_upperBounds_3760_, v___x_3761_);
v___x_3765_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0));
v___x_3766_ = l_Nat_reprFast(v_var_3757_);
v___x_3767_ = lean_string_append(v___x_3765_, v___x_3766_);
lean_dec_ref(v___x_3766_);
v___x_3768_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_3769_ = lean_string_append(v___x_3767_, v___x_3768_);
v___x_3770_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1));
lean_inc_ref(v___f_3755_);
v___x_3771_ = l_List_toString___redArg(v___f_3755_, v_irrelevant_3762_);
v___x_3772_ = lean_string_append(v___x_3770_, v___x_3771_);
lean_dec_ref(v___x_3771_);
v___x_3773_ = lean_string_append(v___x_3772_, v___x_3768_);
v___x_3774_ = lean_string_append(v___x_3769_, v___x_3773_);
lean_dec_ref(v___x_3773_);
v___x_3775_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2));
lean_inc_ref(v___f_3755_);
v___x_3776_ = l_List_toString___redArg(v___f_3755_, v_lowerBounds_3763_);
v___x_3777_ = lean_string_append(v___x_3775_, v___x_3776_);
lean_dec_ref(v___x_3776_);
v___x_3778_ = lean_string_append(v___x_3777_, v___x_3768_);
v___x_3779_ = lean_string_append(v___x_3774_, v___x_3778_);
lean_dec_ref(v___x_3778_);
v___x_3780_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3));
v___x_3781_ = l_List_toString___redArg(v___f_3755_, v_upperBounds_3764_);
v___x_3782_ = lean_string_append(v___x_3780_, v___x_3781_);
lean_dec_ref(v___x_3781_);
v___x_3783_ = lean_string_append(v___x_3779_, v___x_3782_);
lean_dec_ref(v___x_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(lean_object* v_d_3794_){
_start:
{
lean_object* v_lowerBounds_3795_; lean_object* v_upperBounds_3796_; uint8_t v___x_3797_; 
v_lowerBounds_3795_ = lean_ctor_get(v_d_3794_, 2);
v_upperBounds_3796_ = lean_ctor_get(v_d_3794_, 3);
v___x_3797_ = l_List_isEmpty___redArg(v_lowerBounds_3795_);
if (v___x_3797_ == 0)
{
return v___x_3797_;
}
else
{
uint8_t v___x_3798_; 
v___x_3798_ = l_List_isEmpty___redArg(v_upperBounds_3796_);
return v___x_3798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty___boxed(lean_object* v_d_3799_){
_start:
{
uint8_t v_res_3800_; lean_object* v_r_3801_; 
v_res_3800_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v_d_3799_);
lean_dec_ref(v_d_3799_);
v_r_3801_ = lean_box(v_res_3800_);
return v_r_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(lean_object* v_d_3802_){
_start:
{
lean_object* v_lowerBounds_3803_; lean_object* v_upperBounds_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v_lowerBounds_3803_ = lean_ctor_get(v_d_3802_, 2);
v_upperBounds_3804_ = lean_ctor_get(v_d_3802_, 3);
v___x_3805_ = l_List_lengthTR___redArg(v_lowerBounds_3803_);
v___x_3806_ = l_List_lengthTR___redArg(v_upperBounds_3804_);
v___x_3807_ = lean_nat_mul(v___x_3805_, v___x_3806_);
lean_dec(v___x_3806_);
lean_dec(v___x_3805_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size___boxed(lean_object* v_d_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_d_3808_);
lean_dec_ref(v_d_3808_);
return v_res_3809_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(lean_object* v_d_3810_){
_start:
{
uint8_t v_lowerExact_3811_; 
v_lowerExact_3811_ = lean_ctor_get_uint8(v_d_3810_, sizeof(void*)*4);
if (v_lowerExact_3811_ == 0)
{
uint8_t v_upperExact_3812_; 
v_upperExact_3812_ = lean_ctor_get_uint8(v_d_3810_, sizeof(void*)*4 + 1);
return v_upperExact_3812_;
}
else
{
return v_lowerExact_3811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact___boxed(lean_object* v_d_3813_){
_start:
{
uint8_t v_res_3814_; lean_object* v_r_3815_; 
v_res_3814_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_d_3813_);
lean_dec_ref(v_d_3813_);
v_r_3815_ = lean_box(v_res_3814_);
return v_r_3815_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(lean_object* v_x_3816_, lean_object* v_x_3817_){
_start:
{
if (lean_obj_tag(v_x_3817_) == 0)
{
return v_x_3816_;
}
else
{
lean_object* v_head_3818_; lean_object* v_tail_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v_head_3818_ = lean_ctor_get(v_x_3817_, 0);
v_tail_3819_ = lean_ctor_get(v_x_3817_, 1);
v___x_3820_ = lean_box(0);
v___x_3821_ = 1;
lean_inc(v_head_3818_);
v___x_3822_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3822_, 0, v_head_3818_);
lean_ctor_set(v___x_3822_, 1, v___x_3820_);
lean_ctor_set(v___x_3822_, 2, v___x_3820_);
lean_ctor_set(v___x_3822_, 3, v___x_3820_);
lean_ctor_set_uint8(v___x_3822_, sizeof(void*)*4, v___x_3821_);
lean_ctor_set_uint8(v___x_3822_, sizeof(void*)*4 + 1, v___x_3821_);
v___x_3823_ = lean_array_push(v_x_3816_, v___x_3822_);
v_x_3816_ = v___x_3823_;
v_x_3817_ = v_tail_3819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2___boxed(lean_object* v_x_3825_, lean_object* v_x_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v_x_3825_, v_x_3826_);
lean_dec(v_x_3826_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object* v___x_3828_, lean_object* v_b_3829_, lean_object* v___x_3830_, lean_object* v_____r_3831_, lean_object* v_d_x27_3832_){
_start:
{
lean_object* v_upperBound_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3860_; 
v_upperBound_3833_ = lean_ctor_get(v___x_3828_, 1);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3860_ == 0)
{
lean_object* v_unused_3861_; 
v_unused_3861_ = lean_ctor_get(v___x_3828_, 0);
lean_dec(v_unused_3861_);
v___x_3835_ = v___x_3828_;
v_isShared_3836_ = v_isSharedCheck_3860_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_upperBound_3833_);
lean_dec(v___x_3828_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3860_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
if (lean_obj_tag(v_upperBound_3833_) == 0)
{
lean_del_object(v___x_3835_);
lean_dec(v___x_3830_);
lean_dec_ref(v_b_3829_);
return v_d_x27_3832_;
}
else
{
lean_object* v_var_3837_; lean_object* v_irrelevant_3838_; lean_object* v_lowerBounds_3839_; lean_object* v_upperBounds_3840_; uint8_t v_lowerExact_3841_; uint8_t v_upperExact_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3859_; 
lean_dec_ref(v_upperBound_3833_);
v_var_3837_ = lean_ctor_get(v_d_x27_3832_, 0);
v_irrelevant_3838_ = lean_ctor_get(v_d_x27_3832_, 1);
v_lowerBounds_3839_ = lean_ctor_get(v_d_x27_3832_, 2);
v_upperBounds_3840_ = lean_ctor_get(v_d_x27_3832_, 3);
v_lowerExact_3841_ = lean_ctor_get_uint8(v_d_x27_3832_, sizeof(void*)*4);
v_upperExact_3842_ = lean_ctor_get_uint8(v_d_x27_3832_, sizeof(void*)*4 + 1);
v_isSharedCheck_3859_ = !lean_is_exclusive(v_d_x27_3832_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3844_ = v_d_x27_3832_;
v_isShared_3845_ = v_isSharedCheck_3859_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_upperBounds_3840_);
lean_inc(v_lowerBounds_3839_);
lean_inc(v_irrelevant_3838_);
lean_inc(v_var_3837_);
lean_dec(v_d_x27_3832_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3859_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
lean_inc(v___x_3830_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 1, v___x_3830_);
lean_ctor_set(v___x_3835_, 0, v_b_3829_);
v___x_3847_ = v___x_3835_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_b_3829_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v___x_3830_);
v___x_3847_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
lean_ctor_set(v___x_3848_, 1, v_upperBounds_3840_);
if (v_upperExact_3842_ == 0)
{
lean_object* v___x_3850_; 
lean_dec(v___x_3830_);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 3, v___x_3848_);
v___x_3850_ = v___x_3844_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_var_3837_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v_irrelevant_3838_);
lean_ctor_set(v_reuseFailAlloc_3851_, 2, v_lowerBounds_3839_);
lean_ctor_set(v_reuseFailAlloc_3851_, 3, v___x_3848_);
lean_ctor_set_uint8(v_reuseFailAlloc_3851_, sizeof(void*)*4, v_lowerExact_3841_);
lean_ctor_set_uint8(v_reuseFailAlloc_3851_, sizeof(void*)*4 + 1, v_upperExact_3842_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
else
{
lean_object* v___x_3852_; lean_object* v___x_3853_; uint8_t v___x_3854_; lean_object* v___x_3856_; 
v___x_3852_ = lean_nat_abs(v___x_3830_);
lean_dec(v___x_3830_);
v___x_3853_ = lean_unsigned_to_nat(1u);
v___x_3854_ = lean_nat_dec_eq(v___x_3852_, v___x_3853_);
lean_dec(v___x_3852_);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 3, v___x_3848_);
v___x_3856_ = v___x_3844_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_var_3837_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v_irrelevant_3838_);
lean_ctor_set(v_reuseFailAlloc_3857_, 2, v_lowerBounds_3839_);
lean_ctor_set(v_reuseFailAlloc_3857_, 3, v___x_3848_);
lean_ctor_set_uint8(v_reuseFailAlloc_3857_, sizeof(void*)*4, v_lowerExact_3841_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_ctor_set_uint8(v___x_3856_, sizeof(void*)*4 + 1, v___x_3854_);
return v___x_3856_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(lean_object* v_upperBound_3862_, lean_object* v_coeffs_3863_, lean_object* v_constraint_3864_, lean_object* v_b_3865_, lean_object* v_a_3866_, lean_object* v_b_3867_){
_start:
{
lean_object* v_a_3869_; uint8_t v___x_3873_; 
v___x_3873_ = lean_nat_dec_lt(v_a_3866_, v_upperBound_3862_);
if (v___x_3873_ == 0)
{
lean_dec(v_a_3866_);
lean_dec_ref(v_b_3865_);
lean_dec_ref(v_constraint_3864_);
return v_b_3867_;
}
else
{
lean_object* v___x_3874_; uint8_t v___x_3875_; 
v___x_3874_ = lean_array_get_size(v_b_3867_);
v___x_3875_ = lean_nat_dec_lt(v_a_3866_, v___x_3874_);
if (v___x_3875_ == 0)
{
v_a_3869_ = v_b_3867_;
goto v___jp_3868_;
}
else
{
lean_object* v___x_3876_; lean_object* v_v_3877_; lean_object* v___x_3878_; lean_object* v_xs_x27_3879_; lean_object* v___y_3881_; lean_object* v___x_3883_; uint8_t v___x_3884_; 
lean_inc(v_a_3866_);
v___x_3876_ = l_Lean_Omega_IntList_get(v_coeffs_3863_, v_a_3866_);
v_v_3877_ = lean_array_fget(v_b_3867_, v_a_3866_);
v___x_3878_ = lean_box(0);
v_xs_x27_3879_ = lean_array_fset(v_b_3867_, v_a_3866_, v___x_3878_);
v___x_3883_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3884_ = lean_int_dec_eq(v___x_3876_, v___x_3883_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; lean_object* v_lowerBound_3886_; 
lean_inc_ref(v_constraint_3864_);
lean_inc(v___x_3876_);
v___x_3885_ = l_Lean_Omega_Constraint_scale(v___x_3876_, v_constraint_3864_);
v_lowerBound_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_lowerBound_3886_);
if (lean_obj_tag(v_lowerBound_3886_) == 0)
{
lean_object* v___x_3887_; 
lean_inc_ref(v_b_3865_);
v___x_3887_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3885_, v_b_3865_, v___x_3876_, v___x_3878_, v_v_3877_);
v___y_3881_ = v___x_3887_;
goto v___jp_3880_;
}
else
{
lean_object* v_var_3888_; lean_object* v_irrelevant_3889_; lean_object* v_lowerBounds_3890_; lean_object* v_upperBounds_3891_; uint8_t v_lowerExact_3892_; uint8_t v_upperExact_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3908_; 
lean_dec_ref(v_lowerBound_3886_);
v_var_3888_ = lean_ctor_get(v_v_3877_, 0);
v_irrelevant_3889_ = lean_ctor_get(v_v_3877_, 1);
v_lowerBounds_3890_ = lean_ctor_get(v_v_3877_, 2);
v_upperBounds_3891_ = lean_ctor_get(v_v_3877_, 3);
v_lowerExact_3892_ = lean_ctor_get_uint8(v_v_3877_, sizeof(void*)*4);
v_upperExact_3893_ = lean_ctor_get_uint8(v_v_3877_, sizeof(void*)*4 + 1);
v_isSharedCheck_3908_ = !lean_is_exclusive(v_v_3877_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3895_ = v_v_3877_;
v_isShared_3896_ = v_isSharedCheck_3908_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_upperBounds_3891_);
lean_inc(v_lowerBounds_3890_);
lean_inc(v_irrelevant_3889_);
lean_inc(v_var_3888_);
lean_dec(v_v_3877_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3908_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; uint8_t v___y_3900_; 
lean_inc(v___x_3876_);
lean_inc_ref(v_b_3865_);
v___x_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3897_, 0, v_b_3865_);
lean_ctor_set(v___x_3897_, 1, v___x_3876_);
v___x_3898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
lean_ctor_set(v___x_3898_, 1, v_lowerBounds_3890_);
if (v_lowerExact_3892_ == 0)
{
v___y_3900_ = v_lowerExact_3892_;
goto v___jp_3899_;
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; 
v___x_3905_ = lean_nat_abs(v___x_3876_);
v___x_3906_ = lean_unsigned_to_nat(1u);
v___x_3907_ = lean_nat_dec_eq(v___x_3905_, v___x_3906_);
lean_dec(v___x_3905_);
v___y_3900_ = v___x_3907_;
goto v___jp_3899_;
}
v___jp_3899_:
{
lean_object* v___x_3902_; 
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 2, v___x_3898_);
v___x_3902_ = v___x_3895_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_var_3888_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_irrelevant_3889_);
lean_ctor_set(v_reuseFailAlloc_3904_, 2, v___x_3898_);
lean_ctor_set(v_reuseFailAlloc_3904_, 3, v_upperBounds_3891_);
lean_ctor_set_uint8(v_reuseFailAlloc_3904_, sizeof(void*)*4 + 1, v_upperExact_3893_);
v___x_3902_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3903_; 
lean_ctor_set_uint8(v___x_3902_, sizeof(void*)*4, v___y_3900_);
lean_inc_ref(v_b_3865_);
v___x_3903_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3885_, v_b_3865_, v___x_3876_, v___x_3878_, v___x_3902_);
v___y_3881_ = v___x_3903_;
goto v___jp_3880_;
}
}
}
}
}
else
{
lean_object* v_var_3909_; lean_object* v_irrelevant_3910_; lean_object* v_lowerBounds_3911_; lean_object* v_upperBounds_3912_; uint8_t v_lowerExact_3913_; uint8_t v_upperExact_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v___x_3876_);
v_var_3909_ = lean_ctor_get(v_v_3877_, 0);
v_irrelevant_3910_ = lean_ctor_get(v_v_3877_, 1);
v_lowerBounds_3911_ = lean_ctor_get(v_v_3877_, 2);
v_upperBounds_3912_ = lean_ctor_get(v_v_3877_, 3);
v_lowerExact_3913_ = lean_ctor_get_uint8(v_v_3877_, sizeof(void*)*4);
v_upperExact_3914_ = lean_ctor_get_uint8(v_v_3877_, sizeof(void*)*4 + 1);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_v_3877_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3916_ = v_v_3877_;
v_isShared_3917_ = v_isSharedCheck_3922_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_upperBounds_3912_);
lean_inc(v_lowerBounds_3911_);
lean_inc(v_irrelevant_3910_);
lean_inc(v_var_3909_);
lean_dec(v_v_3877_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3922_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3918_; lean_object* v___x_3920_; 
lean_inc_ref(v_b_3865_);
v___x_3918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3918_, 0, v_b_3865_);
lean_ctor_set(v___x_3918_, 1, v_irrelevant_3910_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 1, v___x_3918_);
v___x_3920_ = v___x_3916_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_var_3909_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3921_, 2, v_lowerBounds_3911_);
lean_ctor_set(v_reuseFailAlloc_3921_, 3, v_upperBounds_3912_);
lean_ctor_set_uint8(v_reuseFailAlloc_3921_, sizeof(void*)*4, v_lowerExact_3913_);
lean_ctor_set_uint8(v_reuseFailAlloc_3921_, sizeof(void*)*4 + 1, v_upperExact_3914_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
v___y_3881_ = v___x_3920_;
goto v___jp_3880_;
}
}
}
v___jp_3880_:
{
lean_object* v___x_3882_; 
v___x_3882_ = lean_array_fset(v_xs_x27_3879_, v_a_3866_, v___y_3881_);
v_a_3869_ = v___x_3882_;
goto v___jp_3868_;
}
}
}
v___jp_3868_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = lean_unsigned_to_nat(1u);
v___x_3871_ = lean_nat_add(v_a_3866_, v___x_3870_);
lean_dec(v_a_3866_);
v_a_3866_ = v___x_3871_;
v_b_3867_ = v_a_3869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___boxed(lean_object* v_upperBound_3923_, lean_object* v_coeffs_3924_, lean_object* v_constraint_3925_, lean_object* v_b_3926_, lean_object* v_a_3927_, lean_object* v_b_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3923_, v_coeffs_3924_, v_constraint_3925_, v_b_3926_, v_a_3927_, v_b_3928_);
lean_dec(v_coeffs_3924_);
lean_dec(v_upperBound_3923_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(lean_object* v_n_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_){
_start:
{
if (lean_obj_tag(v_a_3931_) == 0)
{
lean_object* v___x_3933_; 
v___x_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3933_, 0, v_a_3932_);
return v___x_3933_;
}
else
{
lean_object* v_value_3934_; lean_object* v_tail_3935_; lean_object* v_coeffs_3936_; lean_object* v_constraint_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v_value_3934_ = lean_ctor_get(v_a_3931_, 1);
lean_inc(v_value_3934_);
v_tail_3935_ = lean_ctor_get(v_a_3931_, 2);
lean_inc(v_tail_3935_);
lean_dec_ref(v_a_3931_);
v_coeffs_3936_ = lean_ctor_get(v_value_3934_, 0);
lean_inc(v_coeffs_3936_);
v_constraint_3937_ = lean_ctor_get(v_value_3934_, 1);
lean_inc_ref(v_constraint_3937_);
v___x_3938_ = lean_unsigned_to_nat(0u);
v___x_3939_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_n_3930_, v_coeffs_3936_, v_constraint_3937_, v_value_3934_, v___x_3938_, v_a_3932_);
lean_dec(v_coeffs_3936_);
v_a_3931_ = v_tail_3935_;
v_a_3932_ = v___x_3939_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1___boxed(lean_object* v_n_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3941_, v_a_3942_, v_a_3943_);
lean_dec(v_n_3941_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(lean_object* v_n_3945_, lean_object* v_as_3946_, size_t v_sz_3947_, size_t v_i_3948_, lean_object* v_b_3949_){
_start:
{
uint8_t v___x_3950_; 
v___x_3950_ = lean_usize_dec_lt(v_i_3948_, v_sz_3947_);
if (v___x_3950_ == 0)
{
return v_b_3949_;
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3952_; 
v_a_3951_ = lean_array_uget_borrowed(v_as_3946_, v_i_3948_);
lean_inc(v_a_3951_);
v___x_3952_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3945_, v_a_3951_, v_b_3949_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref(v___x_3952_);
return v_a_3953_;
}
else
{
lean_object* v_a_3954_; size_t v___x_3955_; size_t v___x_3956_; 
v_a_3954_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3954_);
lean_dec_ref(v___x_3952_);
v___x_3955_ = ((size_t)1ULL);
v___x_3956_ = lean_usize_add(v_i_3948_, v___x_3955_);
v_i_3948_ = v___x_3956_;
v_b_3949_ = v_a_3954_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3___boxed(lean_object* v_n_3958_, lean_object* v_as_3959_, lean_object* v_sz_3960_, lean_object* v_i_3961_, lean_object* v_b_3962_){
_start:
{
size_t v_sz_boxed_3963_; size_t v_i_boxed_3964_; lean_object* v_res_3965_; 
v_sz_boxed_3963_ = lean_unbox_usize(v_sz_3960_);
lean_dec(v_sz_3960_);
v_i_boxed_3964_ = lean_unbox_usize(v_i_3961_);
lean_dec(v_i_3961_);
v_res_3965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_n_3958_, v_as_3959_, v_sz_boxed_3963_, v_i_boxed_3964_, v_b_3962_);
lean_dec_ref(v_as_3959_);
lean_dec(v_n_3958_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(lean_object* v_p_3968_){
_start:
{
lean_object* v_constraints_3969_; lean_object* v_numVars_3970_; lean_object* v_buckets_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v_data_3974_; size_t v_sz_3975_; size_t v___x_3976_; lean_object* v___x_3977_; 
v_constraints_3969_ = lean_ctor_get(v_p_3968_, 2);
lean_inc_ref(v_constraints_3969_);
v_numVars_3970_ = lean_ctor_get(v_p_3968_, 1);
lean_inc(v_numVars_3970_);
lean_dec_ref(v_p_3968_);
v_buckets_3971_ = lean_ctor_get(v_constraints_3969_, 1);
lean_inc_ref(v_buckets_3971_);
lean_dec_ref(v_constraints_3969_);
v___x_3972_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
lean_inc(v_numVars_3970_);
v___x_3973_ = l_List_range(v_numVars_3970_);
v_data_3974_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v___x_3972_, v___x_3973_);
lean_dec(v___x_3973_);
v_sz_3975_ = lean_array_size(v_buckets_3971_);
v___x_3976_ = ((size_t)0ULL);
v___x_3977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_numVars_3970_, v_buckets_3971_, v_sz_3975_, v___x_3976_, v_data_3974_);
lean_dec_ref(v_buckets_3971_);
lean_dec(v_numVars_3970_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(lean_object* v_upperBound_3978_, lean_object* v_coeffs_3979_, lean_object* v_constraint_3980_, lean_object* v_b_3981_, lean_object* v_inst_3982_, lean_object* v_R_3983_, lean_object* v_a_3984_, lean_object* v_b_3985_, lean_object* v_c_3986_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3978_, v_coeffs_3979_, v_constraint_3980_, v_b_3981_, v_a_3984_, v_b_3985_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___boxed(lean_object* v_upperBound_3988_, lean_object* v_coeffs_3989_, lean_object* v_constraint_3990_, lean_object* v_b_3991_, lean_object* v_inst_3992_, lean_object* v_R_3993_, lean_object* v_a_3994_, lean_object* v_b_3995_, lean_object* v_c_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(v_upperBound_3988_, v_coeffs_3989_, v_constraint_3990_, v_b_3991_, v_inst_3992_, v_R_3993_, v_a_3994_, v_b_3995_, v_c_3996_);
lean_dec(v_coeffs_3989_);
lean_dec(v_upperBound_3988_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(lean_object* v_cls_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v_options_4004_; uint8_t v_hasTrace_4005_; 
v_options_4004_ = lean_ctor_get(v___y_4002_, 2);
v_hasTrace_4005_ = lean_ctor_get_uint8(v_options_4004_, sizeof(void*)*1);
if (v_hasTrace_4005_ == 0)
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_dec(v_cls_4001_);
v___x_4006_ = lean_box(v_hasTrace_4005_);
v___x_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4006_);
return v___x_4007_;
}
else
{
lean_object* v_inheritedTraceOptions_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; uint8_t v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v_inheritedTraceOptions_4008_ = lean_ctor_get(v___y_4002_, 13);
v___x_4009_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___closed__1));
v___x_4010_ = l_Lean_Name_append(v___x_4009_, v_cls_4001_);
v___x_4011_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4008_, v_options_4004_, v___x_4010_);
lean_dec(v___x_4010_);
v___x_4012_ = lean_box(v___x_4011_);
v___x_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
return v___x_4013_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___boxed(lean_object* v_cls_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v_cls_4014_, v___y_4015_);
lean_dec_ref(v___y_4015_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(lean_object* v_cls_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v_cls_4018_, v___y_4021_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___boxed(lean_object* v_cls_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5(lean_object* v_as_4032_, size_t v_i_4033_, size_t v_stop_4034_, lean_object* v_b_4035_){
_start:
{
lean_object* v___y_4037_; uint8_t v___x_4041_; 
v___x_4041_ = lean_usize_dec_eq(v_i_4033_, v_stop_4034_);
if (v___x_4041_ == 0)
{
lean_object* v___x_4042_; uint8_t v___x_4045_; 
v___x_4042_ = lean_array_uget_borrowed(v_as_4032_, v_i_4033_);
v___x_4045_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v___x_4042_);
if (v___x_4045_ == 0)
{
goto v___jp_4043_;
}
else
{
if (v___x_4041_ == 0)
{
v___y_4037_ = v_b_4035_;
goto v___jp_4036_;
}
else
{
goto v___jp_4043_;
}
}
v___jp_4043_:
{
lean_object* v___x_4044_; 
lean_inc(v___x_4042_);
v___x_4044_ = lean_array_push(v_b_4035_, v___x_4042_);
v___y_4037_ = v___x_4044_;
goto v___jp_4036_;
}
}
else
{
return v_b_4035_;
}
v___jp_4036_:
{
size_t v___x_4038_; size_t v___x_4039_; 
v___x_4038_ = ((size_t)1ULL);
v___x_4039_ = lean_usize_add(v_i_4033_, v___x_4038_);
v_i_4033_ = v___x_4039_;
v_b_4035_ = v___y_4037_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5___boxed(lean_object* v_as_4046_, lean_object* v_i_4047_, lean_object* v_stop_4048_, lean_object* v_b_4049_){
_start:
{
size_t v_i_boxed_4050_; size_t v_stop_boxed_4051_; lean_object* v_res_4052_; 
v_i_boxed_4050_ = lean_unbox_usize(v_i_4047_);
lean_dec(v_i_4047_);
v_stop_boxed_4051_ = lean_unbox_usize(v_stop_4048_);
lean_dec(v_stop_4048_);
v_res_4052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5(v_as_4046_, v_i_boxed_4050_, v_stop_boxed_4051_, v_b_4049_);
lean_dec_ref(v_as_4046_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0(lean_object* v___x_4053_, lean_object* v_fst_4054_, lean_object* v_snd_4055_, lean_object* v_fst_4056_, lean_object* v_____r_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4053_);
v___x_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4064_, 0, v_fst_4054_);
lean_ctor_set(v___x_4064_, 1, v_snd_4055_);
v___x_4065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4065_, 0, v_fst_4056_);
lean_ctor_set(v___x_4065_, 1, v___x_4064_);
v___x_4066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4063_);
lean_ctor_set(v___x_4066_, 1, v___x_4065_);
v___x_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
v___x_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0___boxed(lean_object* v___x_4069_, lean_object* v_fst_4070_, lean_object* v_snd_4071_, lean_object* v_fst_4072_, lean_object* v_____r_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0(v___x_4069_, v_fst_4070_, v_snd_4071_, v_fst_4072_, v_____r_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
return v_res_4079_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4080_; double v___x_4081_; 
v___x_4080_ = lean_unsigned_to_nat(0u);
v___x_4081_ = lean_float_of_nat(v___x_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object* v_cls_4084_, lean_object* v_msg_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v_ref_4091_; lean_object* v___x_4092_; lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4137_; 
v_ref_4091_ = lean_ctor_get(v___y_4088_, 5);
v___x_4092_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4095_ = v___x_4092_;
v_isShared_4096_ = v_isSharedCheck_4137_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4092_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4137_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4097_; lean_object* v_traceState_4098_; lean_object* v_env_4099_; lean_object* v_nextMacroScope_4100_; lean_object* v_ngen_4101_; lean_object* v_auxDeclNGen_4102_; lean_object* v_cache_4103_; lean_object* v_messages_4104_; lean_object* v_infoState_4105_; lean_object* v_snapshotTasks_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4136_; 
v___x_4097_ = lean_st_ref_take(v___y_4089_);
v_traceState_4098_ = lean_ctor_get(v___x_4097_, 4);
v_env_4099_ = lean_ctor_get(v___x_4097_, 0);
v_nextMacroScope_4100_ = lean_ctor_get(v___x_4097_, 1);
v_ngen_4101_ = lean_ctor_get(v___x_4097_, 2);
v_auxDeclNGen_4102_ = lean_ctor_get(v___x_4097_, 3);
v_cache_4103_ = lean_ctor_get(v___x_4097_, 5);
v_messages_4104_ = lean_ctor_get(v___x_4097_, 6);
v_infoState_4105_ = lean_ctor_get(v___x_4097_, 7);
v_snapshotTasks_4106_ = lean_ctor_get(v___x_4097_, 8);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4108_ = v___x_4097_;
v_isShared_4109_ = v_isSharedCheck_4136_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_snapshotTasks_4106_);
lean_inc(v_infoState_4105_);
lean_inc(v_messages_4104_);
lean_inc(v_cache_4103_);
lean_inc(v_traceState_4098_);
lean_inc(v_auxDeclNGen_4102_);
lean_inc(v_ngen_4101_);
lean_inc(v_nextMacroScope_4100_);
lean_inc(v_env_4099_);
lean_dec(v___x_4097_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4136_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
uint64_t v_tid_4110_; lean_object* v_traces_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4135_; 
v_tid_4110_ = lean_ctor_get_uint64(v_traceState_4098_, sizeof(void*)*1);
v_traces_4111_ = lean_ctor_get(v_traceState_4098_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v_traceState_4098_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4113_ = v_traceState_4098_;
v_isShared_4114_ = v_isSharedCheck_4135_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_traces_4111_);
lean_dec(v_traceState_4098_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4135_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4115_; double v___x_4116_; uint8_t v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4125_; 
v___x_4115_ = lean_box(0);
v___x_4116_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0);
v___x_4117_ = 0;
v___x_4118_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4119_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4119_, 0, v_cls_4084_);
lean_ctor_set(v___x_4119_, 1, v___x_4115_);
lean_ctor_set(v___x_4119_, 2, v___x_4118_);
lean_ctor_set_float(v___x_4119_, sizeof(void*)*3, v___x_4116_);
lean_ctor_set_float(v___x_4119_, sizeof(void*)*3 + 8, v___x_4116_);
lean_ctor_set_uint8(v___x_4119_, sizeof(void*)*3 + 16, v___x_4117_);
v___x_4120_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__1));
v___x_4121_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4119_);
lean_ctor_set(v___x_4121_, 1, v_a_4093_);
lean_ctor_set(v___x_4121_, 2, v___x_4120_);
lean_inc(v_ref_4091_);
v___x_4122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4122_, 0, v_ref_4091_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = l_Lean_PersistentArray_push___redArg(v_traces_4111_, v___x_4122_);
if (v_isShared_4114_ == 0)
{
lean_ctor_set(v___x_4113_, 0, v___x_4123_);
v___x_4125_ = v___x_4113_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4123_);
lean_ctor_set_uint64(v_reuseFailAlloc_4134_, sizeof(void*)*1, v_tid_4110_);
v___x_4125_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
lean_object* v___x_4127_; 
if (v_isShared_4109_ == 0)
{
lean_ctor_set(v___x_4108_, 4, v___x_4125_);
v___x_4127_ = v___x_4108_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_env_4099_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v_nextMacroScope_4100_);
lean_ctor_set(v_reuseFailAlloc_4133_, 2, v_ngen_4101_);
lean_ctor_set(v_reuseFailAlloc_4133_, 3, v_auxDeclNGen_4102_);
lean_ctor_set(v_reuseFailAlloc_4133_, 4, v___x_4125_);
lean_ctor_set(v_reuseFailAlloc_4133_, 5, v_cache_4103_);
lean_ctor_set(v_reuseFailAlloc_4133_, 6, v_messages_4104_);
lean_ctor_set(v_reuseFailAlloc_4133_, 7, v_infoState_4105_);
lean_ctor_set(v_reuseFailAlloc_4133_, 8, v_snapshotTasks_4106_);
v___x_4127_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4131_; 
v___x_4128_ = lean_st_ref_set(v___y_4089_, v___x_4127_);
v___x_4129_ = lean_box(0);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 0, v___x_4129_);
v___x_4131_ = v___x_4095_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object* v_cls_4138_, lean_object* v_msg_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_cls_4138_, v_msg_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
return v_res_4145_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4147_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__0));
v___x_4148_ = l_Lean_stringToMessageData(v___x_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg(lean_object* v_upperBound_4149_, lean_object* v___y_4150_, lean_object* v_a_4151_, lean_object* v_b_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_a_4159_; lean_object* v___y_4164_; uint8_t v___x_4183_; 
v___x_4183_ = lean_nat_dec_lt(v_a_4151_, v_upperBound_4149_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4184_; 
lean_dec(v_a_4151_);
v___x_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4184_, 0, v_b_4152_);
return v___x_4184_;
}
else
{
lean_object* v_snd_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4260_; 
v_snd_4185_ = lean_ctor_get(v_b_4152_, 1);
v_isSharedCheck_4260_ = !lean_is_exclusive(v_b_4152_);
if (v_isSharedCheck_4260_ == 0)
{
lean_object* v_unused_4261_; 
v_unused_4261_ = lean_ctor_get(v_b_4152_, 0);
lean_dec(v_unused_4261_);
v___x_4187_ = v_b_4152_;
v_isShared_4188_ = v_isSharedCheck_4260_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_snd_4185_);
lean_dec(v_b_4152_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4260_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v_snd_4189_; lean_object* v_fst_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4259_; 
v_snd_4189_ = lean_ctor_get(v_snd_4185_, 1);
v_fst_4190_ = lean_ctor_get(v_snd_4185_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v_snd_4185_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4192_ = v_snd_4185_;
v_isShared_4193_ = v_isSharedCheck_4259_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_snd_4189_);
lean_inc(v_fst_4190_);
lean_dec(v_snd_4185_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4259_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v_fst_4194_; lean_object* v_snd_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4258_; 
v_fst_4194_ = lean_ctor_get(v_snd_4189_, 0);
v_snd_4195_ = lean_ctor_get(v_snd_4189_, 1);
v_isSharedCheck_4258_ = !lean_is_exclusive(v_snd_4189_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4197_ = v_snd_4189_;
v_isShared_4198_ = v_isSharedCheck_4258_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_snd_4195_);
lean_inc(v_fst_4194_);
lean_dec(v_snd_4189_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4258_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v_bestIdx_4199_; lean_object* v___x_4200_; lean_object* v_cls_4211_; lean_object* v___x_4212_; uint8_t v___x_4213_; lean_object* v___x_4214_; uint8_t v___x_4215_; uint8_t v___y_4252_; uint8_t v___y_4255_; 
v_bestIdx_4199_ = lean_unsigned_to_nat(0u);
v___x_4200_ = lean_box(0);
v_cls_4211_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4212_ = lean_array_fget_borrowed(v___y_4150_, v_a_4151_);
v___x_4213_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4212_);
v___x_4214_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4212_);
v___x_4215_ = lean_nat_dec_eq(v___x_4214_, v_bestIdx_4199_);
if (v___x_4215_ == 0)
{
uint8_t v___x_4257_; 
v___x_4257_ = lean_unbox(v_snd_4195_);
if (v___x_4257_ == 0)
{
v___y_4255_ = v___x_4213_;
goto v___jp_4254_;
}
else
{
if (v___x_4215_ == 0)
{
v___y_4255_ = v___x_4215_;
goto v___jp_4254_;
}
else
{
v___y_4255_ = v___x_4213_;
goto v___jp_4254_;
}
}
}
else
{
v___y_4255_ = v___x_4215_;
goto v___jp_4254_;
}
v___jp_4201_:
{
lean_object* v___x_4203_; 
if (v_isShared_4198_ == 0)
{
v___x_4203_ = v___x_4197_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_fst_4194_);
lean_ctor_set(v_reuseFailAlloc_4210_, 1, v_snd_4195_);
v___x_4203_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
lean_object* v___x_4205_; 
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 1, v___x_4203_);
v___x_4205_ = v___x_4192_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_fst_4190_);
lean_ctor_set(v_reuseFailAlloc_4209_, 1, v___x_4203_);
v___x_4205_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
lean_object* v___x_4207_; 
if (v_isShared_4188_ == 0)
{
lean_ctor_set(v___x_4187_, 1, v___x_4205_);
lean_ctor_set(v___x_4187_, 0, v___x_4200_);
v___x_4207_ = v___x_4187_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4200_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v___x_4205_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
v_a_4159_ = v___x_4207_;
goto v___jp_4158_;
}
}
}
}
v___jp_4216_:
{
if (v___x_4215_ == 0)
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
lean_dec(v_snd_4195_);
lean_dec(v_fst_4194_);
lean_dec(v_fst_4190_);
v___x_4217_ = lean_box(v___x_4213_);
v___x_4218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4214_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
lean_inc(v_a_4151_);
v___x_4219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4219_, 0, v_a_4151_);
lean_ctor_set(v___x_4219_, 1, v___x_4218_);
v___x_4220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4200_);
lean_ctor_set(v___x_4220_, 1, v___x_4219_);
v_a_4159_ = v___x_4220_;
goto v___jp_4158_;
}
else
{
lean_object* v___x_4221_; 
lean_dec(v___x_4214_);
v___x_4221_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v_cls_4211_, v___y_4155_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; uint8_t v___x_4223_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_a_4222_);
lean_dec_ref(v___x_4221_);
v___x_4223_ = lean_unbox(v_a_4222_);
lean_dec(v_a_4222_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4224_ = lean_box(0);
lean_inc(v___x_4212_);
v___x_4225_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0(v___x_4212_, v_fst_4194_, v_snd_4195_, v_fst_4190_, v___x_4224_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
v___y_4164_ = v___x_4225_;
goto v___jp_4163_;
}
else
{
lean_object* v_var_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v_var_4226_ = lean_ctor_get(v___x_4212_, 0);
v___x_4227_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1);
lean_inc(v_var_4226_);
v___x_4228_ = l_Nat_reprFast(v_var_4226_);
v___x_4229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4228_);
v___x_4230_ = l_Lean_MessageData_ofFormat(v___x_4229_);
v___x_4231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4227_);
lean_ctor_set(v___x_4231_, 1, v___x_4230_);
v___x_4232_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_cls_4211_, v___x_4231_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; lean_object* v___x_4234_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref(v___x_4232_);
lean_inc(v___x_4212_);
v___x_4234_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___lam__0(v___x_4212_, v_fst_4194_, v_snd_4195_, v_fst_4190_, v_a_4233_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
v___y_4164_ = v___x_4234_;
goto v___jp_4163_;
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec(v_snd_4195_);
lean_dec(v_fst_4194_);
lean_dec(v_fst_4190_);
lean_dec(v_a_4151_);
v_a_4235_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4232_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4232_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec(v_snd_4195_);
lean_dec(v_fst_4194_);
lean_dec(v_fst_4190_);
lean_dec(v_a_4151_);
v_a_4243_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4221_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4221_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
}
v___jp_4251_:
{
if (v___y_4252_ == 0)
{
lean_dec(v___x_4214_);
goto v___jp_4201_;
}
else
{
uint8_t v___x_4253_; 
v___x_4253_ = lean_nat_dec_lt(v___x_4214_, v_fst_4194_);
if (v___x_4253_ == 0)
{
lean_dec(v___x_4214_);
goto v___jp_4201_;
}
else
{
lean_del_object(v___x_4197_);
lean_del_object(v___x_4192_);
lean_del_object(v___x_4187_);
goto v___jp_4216_;
}
}
}
v___jp_4254_:
{
if (v___y_4255_ == 0)
{
uint8_t v___x_4256_; 
v___x_4256_ = lean_unbox(v_snd_4195_);
if (v___x_4256_ == 0)
{
if (v___x_4213_ == 0)
{
v___y_4252_ = v___x_4183_;
goto v___jp_4251_;
}
else
{
lean_dec(v___x_4214_);
goto v___jp_4201_;
}
}
else
{
v___y_4252_ = v___x_4213_;
goto v___jp_4251_;
}
}
else
{
lean_del_object(v___x_4197_);
lean_del_object(v___x_4192_);
lean_del_object(v___x_4187_);
goto v___jp_4216_;
}
}
}
}
}
}
v___jp_4158_:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4160_ = lean_unsigned_to_nat(1u);
v___x_4161_ = lean_nat_add(v_a_4151_, v___x_4160_);
lean_dec(v_a_4151_);
v_a_4151_ = v___x_4161_;
v_b_4152_ = v_a_4159_;
goto _start;
}
v___jp_4163_:
{
if (lean_obj_tag(v___y_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4174_; 
v_a_4165_ = lean_ctor_get(v___y_4164_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___y_4164_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4167_ = v___y_4164_;
v_isShared_4168_ = v_isSharedCheck_4174_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___y_4164_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4174_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
if (lean_obj_tag(v_a_4165_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4171_; 
lean_dec(v_a_4151_);
v_a_4169_ = lean_ctor_get(v_a_4165_, 0);
lean_inc(v_a_4169_);
lean_dec_ref(v_a_4165_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v_a_4169_);
v___x_4171_ = v___x_4167_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4169_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
else
{
lean_object* v_a_4173_; 
lean_del_object(v___x_4167_);
v_a_4173_ = lean_ctor_get(v_a_4165_, 0);
lean_inc(v_a_4173_);
lean_dec_ref(v_a_4165_);
v_a_4159_ = v_a_4173_;
goto v___jp_4158_;
}
}
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
lean_dec(v_a_4151_);
v_a_4175_ = lean_ctor_get(v___y_4164_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___y_4164_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___y_4164_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___y_4164_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___boxed(lean_object* v_upperBound_4262_, lean_object* v___y_4263_, lean_object* v_a_4264_, lean_object* v_b_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg(v_upperBound_4262_, v___y_4263_, v_a_4264_, v_b_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec_ref(v___y_4263_);
lean_dec(v_upperBound_4262_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(size_t v_sz_4272_, size_t v_i_4273_, lean_object* v_bs_4274_){
_start:
{
uint8_t v___x_4275_; 
v___x_4275_ = lean_usize_dec_lt(v_i_4273_, v_sz_4272_);
if (v___x_4275_ == 0)
{
return v_bs_4274_;
}
else
{
lean_object* v_v_4276_; lean_object* v_var_4277_; lean_object* v___x_4278_; lean_object* v_bs_x27_4279_; lean_object* v___x_4280_; uint8_t v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; size_t v___x_4285_; size_t v___x_4286_; lean_object* v___x_4287_; 
v_v_4276_ = lean_array_uget(v_bs_4274_, v_i_4273_);
v_var_4277_ = lean_ctor_get(v_v_4276_, 0);
lean_inc(v_var_4277_);
v___x_4278_ = lean_unsigned_to_nat(0u);
v_bs_x27_4279_ = lean_array_uset(v_bs_4274_, v_i_4273_, v___x_4278_);
v___x_4280_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_v_4276_);
v___x_4281_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_v_4276_);
lean_dec(v_v_4276_);
v___x_4282_ = lean_box(v___x_4281_);
v___x_4283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4280_);
lean_ctor_set(v___x_4283_, 1, v___x_4282_);
v___x_4284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4284_, 0, v_var_4277_);
lean_ctor_set(v___x_4284_, 1, v___x_4283_);
v___x_4285_ = ((size_t)1ULL);
v___x_4286_ = lean_usize_add(v_i_4273_, v___x_4285_);
v___x_4287_ = lean_array_uset(v_bs_x27_4279_, v_i_4273_, v___x_4284_);
v_i_4273_ = v___x_4286_;
v_bs_4274_ = v___x_4287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___boxed(lean_object* v_sz_4289_, lean_object* v_i_4290_, lean_object* v_bs_4291_){
_start:
{
size_t v_sz_boxed_4292_; size_t v_i_boxed_4293_; lean_object* v_res_4294_; 
v_sz_boxed_4292_ = lean_unbox_usize(v_sz_4289_);
lean_dec(v_sz_4289_);
v_i_boxed_4293_ = lean_unbox_usize(v_i_4290_);
lean_dec(v_i_4290_);
v_res_4294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v_sz_boxed_4292_, v_i_boxed_4293_, v_bs_4291_);
return v_res_4294_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2(void){
_start:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4298_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__1));
v___x_4299_ = l_Lean_MessageData_ofFormat(v___x_4298_);
return v___x_4299_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3(void){
_start:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4300_ = lean_box(1);
v___x_4301_ = l_Lean_MessageData_ofFormat(v___x_4300_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(lean_object* v_a_4303_, lean_object* v_a_4304_){
_start:
{
if (lean_obj_tag(v_a_4303_) == 0)
{
lean_object* v___x_4305_; 
v___x_4305_ = l_List_reverse___redArg(v_a_4304_);
return v___x_4305_;
}
else
{
lean_object* v_head_4306_; lean_object* v_snd_4307_; lean_object* v_tail_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4355_; 
v_head_4306_ = lean_ctor_get(v_a_4303_, 0);
lean_inc(v_head_4306_);
v_snd_4307_ = lean_ctor_get(v_head_4306_, 1);
lean_inc(v_snd_4307_);
v_tail_4308_ = lean_ctor_get(v_a_4303_, 1);
v_isSharedCheck_4355_ = !lean_is_exclusive(v_a_4303_);
if (v_isSharedCheck_4355_ == 0)
{
lean_object* v_unused_4356_; 
v_unused_4356_ = lean_ctor_get(v_a_4303_, 0);
lean_dec(v_unused_4356_);
v___x_4310_ = v_a_4303_;
v_isShared_4311_ = v_isSharedCheck_4355_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_tail_4308_);
lean_dec(v_a_4303_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4355_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v_fst_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4353_; 
v_fst_4312_ = lean_ctor_get(v_head_4306_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v_head_4306_);
if (v_isSharedCheck_4353_ == 0)
{
lean_object* v_unused_4354_; 
v_unused_4354_ = lean_ctor_get(v_head_4306_, 1);
lean_dec(v_unused_4354_);
v___x_4314_ = v_head_4306_;
v_isShared_4315_ = v_isSharedCheck_4353_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_fst_4312_);
lean_dec(v_head_4306_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4353_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v_fst_4316_; lean_object* v_snd_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4352_; 
v_fst_4316_ = lean_ctor_get(v_snd_4307_, 0);
v_snd_4317_ = lean_ctor_get(v_snd_4307_, 1);
v_isSharedCheck_4352_ = !lean_is_exclusive(v_snd_4307_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4319_ = v_snd_4307_;
v_isShared_4320_ = v_isSharedCheck_4352_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_snd_4317_);
lean_inc(v_fst_4316_);
lean_dec(v_snd_4307_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4352_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4326_; 
v___x_4321_ = l_Nat_reprFast(v_fst_4312_);
v___x_4322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4321_);
v___x_4323_ = l_Lean_MessageData_ofFormat(v___x_4322_);
v___x_4324_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__2);
if (v_isShared_4320_ == 0)
{
lean_ctor_set_tag(v___x_4319_, 7);
lean_ctor_set(v___x_4319_, 1, v___x_4324_);
lean_ctor_set(v___x_4319_, 0, v___x_4323_);
v___x_4326_ = v___x_4319_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4323_);
lean_ctor_set(v_reuseFailAlloc_4351_, 1, v___x_4324_);
v___x_4326_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
lean_object* v___x_4327_; lean_object* v___x_4329_; 
v___x_4327_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__3);
if (v_isShared_4315_ == 0)
{
lean_ctor_set_tag(v___x_4314_, 7);
lean_ctor_set(v___x_4314_, 1, v___x_4327_);
lean_ctor_set(v___x_4314_, 0, v___x_4326_);
v___x_4329_ = v___x_4314_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4326_);
lean_ctor_set(v_reuseFailAlloc_4350_, 1, v___x_4327_);
v___x_4329_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___y_4336_; uint8_t v___x_4347_; 
v___x_4330_ = l_Nat_reprFast(v_fst_4316_);
v___x_4331_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4330_);
v___x_4332_ = l_Lean_MessageData_ofFormat(v___x_4331_);
v___x_4333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4332_);
lean_ctor_set(v___x_4333_, 1, v___x_4324_);
v___x_4334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
lean_ctor_set(v___x_4334_, 1, v___x_4327_);
v___x_4347_ = lean_unbox(v_snd_4317_);
lean_dec(v_snd_4317_);
if (v___x_4347_ == 0)
{
lean_object* v___x_4348_; 
v___x_4348_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___closed__4));
v___y_4336_ = v___x_4348_;
goto v___jp_4335_;
}
else
{
lean_object* v___x_4349_; 
v___x_4349_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4));
v___y_4336_ = v___x_4349_;
goto v___jp_4335_;
}
v___jp_4335_:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4344_; 
v___x_4337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4337_, 0, v___y_4336_);
v___x_4338_ = l_Lean_MessageData_ofFormat(v___x_4337_);
v___x_4339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4334_);
lean_ctor_set(v___x_4339_, 1, v___x_4338_);
v___x_4340_ = l_Lean_MessageData_paren(v___x_4339_);
v___x_4341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4329_);
lean_ctor_set(v___x_4341_, 1, v___x_4340_);
v___x_4342_ = l_Lean_MessageData_paren(v___x_4341_);
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 1, v_a_4304_);
lean_ctor_set(v___x_4310_, 0, v___x_4342_);
v___x_4344_ = v___x_4310_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4342_);
lean_ctor_set(v_reuseFailAlloc_4346_, 1, v_a_4304_);
v___x_4344_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
v_a_4303_ = v_tail_4308_;
v_a_4304_ = v___x_4344_;
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
lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4358_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0));
v___x_4359_ = l_Lean_stringToMessageData(v___x_4358_);
return v___x_4359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3(void){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4361_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2));
v___x_4362_ = l_Lean_stringToMessageData(v___x_4361_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(lean_object* v_data_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
lean_object* v___x_4369_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v_bestIdx_4375_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4493_; lean_object* v___x_4516_; lean_object* v___x_4517_; uint8_t v___x_4518_; 
v___x_4369_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default));
v_bestIdx_4375_ = lean_unsigned_to_nat(0u);
v___x_4516_ = lean_array_get_size(v_data_4363_);
v___x_4517_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_4518_ = lean_nat_dec_lt(v_bestIdx_4375_, v___x_4516_);
if (v___x_4518_ == 0)
{
v___y_4493_ = v___x_4517_;
goto v___jp_4492_;
}
else
{
uint8_t v___x_4519_; 
v___x_4519_ = lean_nat_dec_le(v___x_4516_, v___x_4516_);
if (v___x_4519_ == 0)
{
if (v___x_4518_ == 0)
{
v___y_4493_ = v___x_4517_;
goto v___jp_4492_;
}
else
{
size_t v___x_4520_; size_t v___x_4521_; lean_object* v___x_4522_; 
v___x_4520_ = ((size_t)0ULL);
v___x_4521_ = lean_usize_of_nat(v___x_4516_);
v___x_4522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5(v_data_4363_, v___x_4520_, v___x_4521_, v___x_4517_);
v___y_4493_ = v___x_4522_;
goto v___jp_4492_;
}
}
else
{
size_t v___x_4523_; size_t v___x_4524_; lean_object* v___x_4525_; 
v___x_4523_ = ((size_t)0ULL);
v___x_4524_ = lean_usize_of_nat(v___x_4516_);
v___x_4525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__5(v_data_4363_, v___x_4523_, v___x_4524_, v___x_4517_);
v___y_4493_ = v___x_4525_;
goto v___jp_4492_;
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
lean_object* v___x_4383_; lean_object* v___x_4384_; uint8_t v___x_4385_; 
v___x_4383_ = lean_array_get_borrowed(v___x_4369_, v___y_4378_, v_bestIdx_4375_);
v___x_4384_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4383_);
v___x_4385_ = lean_nat_dec_eq(v___x_4384_, v_bestIdx_4375_);
if (v___x_4385_ == 0)
{
lean_object* v___x_4386_; lean_object* v___x_4387_; uint8_t v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4386_ = lean_unsigned_to_nat(1u);
v___x_4387_ = lean_array_get_size(v___y_4378_);
v___x_4388_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4383_);
v___x_4389_ = lean_box(0);
v___x_4390_ = lean_box(v___x_4388_);
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4384_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4392_, 0, v_bestIdx_4375_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4389_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
v___x_4394_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg(v___x_4387_, v___y_4378_, v___x_4386_, v___x_4393_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4448_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4397_ = v___x_4394_;
v_isShared_4398_ = v_isSharedCheck_4448_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4394_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4448_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v_fst_4399_; 
v_fst_4399_ = lean_ctor_get(v_a_4395_, 0);
if (lean_obj_tag(v_fst_4399_) == 0)
{
lean_object* v_snd_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4442_; 
lean_del_object(v___x_4397_);
v_snd_4400_ = lean_ctor_get(v_a_4395_, 1);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_a_4395_);
if (v_isSharedCheck_4442_ == 0)
{
lean_object* v_unused_4443_; 
v_unused_4443_ = lean_ctor_get(v_a_4395_, 0);
lean_dec(v_unused_4443_);
v___x_4402_ = v_a_4395_;
v_isShared_4403_ = v_isSharedCheck_4442_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_snd_4400_);
lean_dec(v_a_4395_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4442_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4404_; lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4441_; 
lean_inc(v___y_4377_);
v___x_4404_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v___y_4377_, v___y_4381_);
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4407_ = v___x_4404_;
v_isShared_4408_ = v_isSharedCheck_4441_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v___x_4404_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4441_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
uint8_t v___x_4409_; 
v___x_4409_ = lean_unbox(v_a_4405_);
lean_dec(v_a_4405_);
if (v___x_4409_ == 0)
{
lean_object* v_fst_4410_; 
lean_del_object(v___x_4407_);
lean_del_object(v___x_4402_);
lean_dec(v___y_4377_);
v_fst_4410_ = lean_ctor_get(v_snd_4400_, 0);
lean_inc(v_fst_4410_);
lean_dec(v_snd_4400_);
v___y_4371_ = v___y_4378_;
v___y_4372_ = v_fst_4410_;
goto v___jp_4370_;
}
else
{
lean_object* v_fst_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4439_; 
v_fst_4411_ = lean_ctor_get(v_snd_4400_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v_snd_4400_);
if (v_isSharedCheck_4439_ == 0)
{
lean_object* v_unused_4440_; 
v_unused_4440_ = lean_ctor_get(v_snd_4400_, 1);
lean_dec(v_unused_4440_);
v___x_4413_ = v_snd_4400_;
v_isShared_4414_ = v_isSharedCheck_4439_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_fst_4411_);
lean_dec(v_snd_4400_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4439_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4415_; lean_object* v_var_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4420_; 
v___x_4415_ = lean_array_get_borrowed(v___x_4369_, v___y_4378_, v_fst_4411_);
v_var_4416_ = lean_ctor_get(v___x_4415_, 0);
v___x_4417_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1);
lean_inc(v_var_4416_);
v___x_4418_ = l_Nat_reprFast(v_var_4416_);
if (v_isShared_4408_ == 0)
{
lean_ctor_set_tag(v___x_4407_, 3);
lean_ctor_set(v___x_4407_, 0, v___x_4418_);
v___x_4420_ = v___x_4407_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v___x_4418_);
v___x_4420_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
lean_object* v___x_4421_; lean_object* v___x_4423_; 
v___x_4421_ = l_Lean_MessageData_ofFormat(v___x_4420_);
if (v_isShared_4414_ == 0)
{
lean_ctor_set_tag(v___x_4413_, 7);
lean_ctor_set(v___x_4413_, 1, v___x_4421_);
lean_ctor_set(v___x_4413_, 0, v___x_4417_);
v___x_4423_ = v___x_4413_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v___x_4417_);
lean_ctor_set(v_reuseFailAlloc_4437_, 1, v___x_4421_);
v___x_4423_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
lean_object* v___x_4424_; lean_object* v___x_4426_; 
v___x_4424_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
if (v_isShared_4403_ == 0)
{
lean_ctor_set_tag(v___x_4402_, 7);
lean_ctor_set(v___x_4402_, 1, v___x_4424_);
lean_ctor_set(v___x_4402_, 0, v___x_4423_);
v___x_4426_ = v___x_4402_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v___x_4423_);
lean_ctor_set(v_reuseFailAlloc_4436_, 1, v___x_4424_);
v___x_4426_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
lean_object* v___x_4427_; 
v___x_4427_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v___y_4377_, v___x_4426_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_dec_ref(v___x_4427_);
v___y_4371_ = v___y_4378_;
v___y_4372_ = v_fst_4411_;
goto v___jp_4370_;
}
else
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4435_; 
lean_dec(v_fst_4411_);
lean_dec_ref(v___y_4378_);
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4430_ = v___x_4427_;
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4427_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4433_; 
if (v_isShared_4431_ == 0)
{
v___x_4433_ = v___x_4430_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4428_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
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
lean_object* v_val_4444_; lean_object* v___x_4446_; 
lean_inc_ref(v_fst_4399_);
lean_dec(v_a_4395_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
v_val_4444_ = lean_ctor_get(v_fst_4399_, 0);
lean_inc(v_val_4444_);
lean_dec_ref(v_fst_4399_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 0, v_val_4444_);
v___x_4446_ = v___x_4397_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_val_4444_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
v_a_4449_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4394_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4394_);
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
else
{
lean_object* v___x_4457_; lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4491_; 
lean_inc(v___x_4383_);
lean_dec(v___x_4384_);
lean_dec_ref(v___y_4378_);
lean_inc(v___y_4377_);
v___x_4457_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v___y_4377_, v___y_4381_);
v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4460_ = v___x_4457_;
v_isShared_4461_ = v_isSharedCheck_4491_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4457_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4491_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
uint8_t v___x_4462_; 
v___x_4462_ = lean_unbox(v_a_4458_);
lean_dec(v_a_4458_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4464_; 
lean_dec(v___y_4377_);
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 0, v___x_4383_);
v___x_4464_ = v___x_4460_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4383_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
else
{
lean_object* v_var_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
lean_del_object(v___x_4460_);
v_var_4466_ = lean_ctor_get(v___x_4383_, 0);
v___x_4467_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg___closed__1);
lean_inc(v_var_4466_);
v___x_4468_ = l_Nat_reprFast(v_var_4466_);
v___x_4469_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4468_);
v___x_4470_ = l_Lean_MessageData_ofFormat(v___x_4469_);
v___x_4471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4467_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
v___x_4472_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
v___x_4473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4471_);
lean_ctor_set(v___x_4473_, 1, v___x_4472_);
v___x_4474_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v___y_4377_, v___x_4473_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4474_);
if (v_isSharedCheck_4481_ == 0)
{
lean_object* v_unused_4482_; 
v_unused_4482_ = lean_ctor_get(v___x_4474_, 0);
lean_dec(v_unused_4482_);
v___x_4476_ = v___x_4474_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_dec(v___x_4474_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
lean_ctor_set(v___x_4476_, 0, v___x_4383_);
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4383_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
else
{
lean_object* v_a_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4490_; 
lean_dec(v___x_4383_);
v_a_4483_ = lean_ctor_get(v___x_4474_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4474_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4485_ = v___x_4474_;
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_a_4483_);
lean_dec(v___x_4474_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4488_; 
if (v_isShared_4486_ == 0)
{
v___x_4488_ = v___x_4485_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_a_4483_);
v___x_4488_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
return v___x_4488_;
}
}
}
}
}
}
}
v___jp_4492_:
{
lean_object* v_cls_4494_; lean_object* v___x_4495_; lean_object* v_a_4496_; uint8_t v___x_4497_; 
v_cls_4494_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4495_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg(v_cls_4494_, v_a_4366_);
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4496_);
lean_dec_ref(v___x_4495_);
v___x_4497_ = lean_unbox(v_a_4496_);
lean_dec(v_a_4496_);
if (v___x_4497_ == 0)
{
v___y_4377_ = v_cls_4494_;
v___y_4378_ = v___y_4493_;
v___y_4379_ = v_a_4364_;
v___y_4380_ = v_a_4365_;
v___y_4381_ = v_a_4366_;
v___y_4382_ = v_a_4367_;
goto v___jp_4376_;
}
else
{
lean_object* v___x_4498_; size_t v_sz_4499_; size_t v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4498_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3);
v_sz_4499_ = lean_array_size(v___y_4493_);
v___x_4500_ = ((size_t)0ULL);
lean_inc_ref(v___y_4493_);
v___x_4501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v_sz_4499_, v___x_4500_, v___y_4493_);
v___x_4502_ = lean_array_to_list(v___x_4501_);
v___x_4503_ = lean_box(0);
v___x_4504_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v___x_4502_, v___x_4503_);
v___x_4505_ = l_Lean_MessageData_ofList(v___x_4504_);
v___x_4506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4498_);
lean_ctor_set(v___x_4506_, 1, v___x_4505_);
v___x_4507_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_cls_4494_, v___x_4506_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_dec_ref(v___x_4507_);
v___y_4377_ = v_cls_4494_;
v___y_4378_ = v___y_4493_;
v___y_4379_ = v_a_4364_;
v___y_4380_ = v_a_4365_;
v___y_4381_ = v_a_4366_;
v___y_4382_ = v_a_4367_;
goto v___jp_4376_;
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
lean_dec_ref(v___y_4493_);
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4507_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4507_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object* v_data_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec_ref(v_data_4526_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(lean_object* v_upperBound_4533_, lean_object* v___y_4534_, lean_object* v_inst_4535_, lean_object* v_R_4536_, lean_object* v_a_4537_, lean_object* v_b_4538_, lean_object* v_c_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v___x_4545_; 
v___x_4545_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___redArg(v_upperBound_4533_, v___y_4534_, v_a_4537_, v_b_4538_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
return v___x_4545_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___boxed(lean_object* v_upperBound_4546_, lean_object* v___y_4547_, lean_object* v_inst_4548_, lean_object* v_R_4549_, lean_object* v_a_4550_, lean_object* v_b_4551_, lean_object* v_c_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_upperBound_4546_, v___y_4547_, v_inst_4548_, v_R_4549_, v_a_4550_, v_b_4551_, v_c_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec_ref(v___y_4547_);
lean_dec(v_upperBound_4546_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(lean_object* v_snd_4559_, lean_object* v_fst_4560_, lean_object* v_as_x27_4561_, lean_object* v_b_4562_){
_start:
{
if (lean_obj_tag(v_as_x27_4561_) == 0)
{
lean_object* v___x_4564_; 
lean_dec_ref(v_fst_4560_);
v___x_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4564_, 0, v_b_4562_);
return v___x_4564_;
}
else
{
lean_object* v_head_4565_; lean_object* v_tail_4566_; lean_object* v_fst_4567_; lean_object* v_snd_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v_head_4565_ = lean_ctor_get(v_as_x27_4561_, 0);
lean_inc(v_head_4565_);
v_tail_4566_ = lean_ctor_get(v_as_x27_4561_, 1);
lean_inc(v_tail_4566_);
lean_dec_ref(v_as_x27_4561_);
v_fst_4567_ = lean_ctor_get(v_head_4565_, 0);
lean_inc(v_fst_4567_);
v_snd_4568_ = lean_ctor_get(v_head_4565_, 1);
lean_inc(v_snd_4568_);
lean_dec(v_head_4565_);
v___x_4569_ = lean_int_neg(v_snd_4559_);
lean_inc_ref(v_fst_4560_);
v___x_4570_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_snd_4568_, v_fst_4560_, v___x_4569_, v_fst_4567_);
v___x_4571_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_4570_);
v___x_4572_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_b_4562_, v___x_4571_);
v_as_x27_4561_ = v_tail_4566_;
v_b_4562_ = v___x_4572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg___boxed(lean_object* v_snd_4574_, lean_object* v_fst_4575_, lean_object* v_as_x27_4576_, lean_object* v_b_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4574_, v_fst_4575_, v_as_x27_4576_, v_b_4577_);
lean_dec(v_snd_4574_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(lean_object* v_upperBounds_4580_, lean_object* v_as_x27_4581_, lean_object* v_b_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
if (lean_obj_tag(v_as_x27_4581_) == 0)
{
lean_object* v___x_4588_; 
lean_dec(v_upperBounds_4580_);
v___x_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4588_, 0, v_b_4582_);
return v___x_4588_;
}
else
{
lean_object* v_head_4589_; lean_object* v_tail_4590_; lean_object* v_fst_4591_; lean_object* v_snd_4592_; lean_object* v___x_4593_; lean_object* v_a_4594_; 
v_head_4589_ = lean_ctor_get(v_as_x27_4581_, 0);
lean_inc(v_head_4589_);
v_tail_4590_ = lean_ctor_get(v_as_x27_4581_, 1);
lean_inc(v_tail_4590_);
lean_dec_ref(v_as_x27_4581_);
v_fst_4591_ = lean_ctor_get(v_head_4589_, 0);
lean_inc(v_fst_4591_);
v_snd_4592_ = lean_ctor_get(v_head_4589_, 1);
lean_inc(v_snd_4592_);
lean_dec(v_head_4589_);
lean_inc(v_upperBounds_4580_);
v___x_4593_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4592_, v_fst_4591_, v_upperBounds_4580_, v_b_4582_);
lean_dec(v_snd_4592_);
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
lean_inc(v_a_4594_);
lean_dec_ref(v___x_4593_);
v_as_x27_4581_ = v_tail_4590_;
v_b_4582_ = v_a_4594_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg___boxed(lean_object* v_upperBounds_4596_, lean_object* v_as_x27_4597_, lean_object* v_b_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
lean_object* v_res_4604_; 
v_res_4604_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4596_, v_as_x27_4597_, v_b_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(lean_object* v_as_x27_4605_, lean_object* v_b_4606_){
_start:
{
if (lean_obj_tag(v_as_x27_4605_) == 0)
{
lean_object* v___x_4608_; 
v___x_4608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4608_, 0, v_b_4606_);
return v___x_4608_;
}
else
{
lean_object* v_head_4609_; lean_object* v_tail_4610_; lean_object* v___x_4611_; 
v_head_4609_ = lean_ctor_get(v_as_x27_4605_, 0);
lean_inc(v_head_4609_);
v_tail_4610_ = lean_ctor_get(v_as_x27_4605_, 1);
lean_inc(v_tail_4610_);
lean_dec_ref(v_as_x27_4605_);
v___x_4611_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_b_4606_, v_head_4609_);
v_as_x27_4605_ = v_tail_4610_;
v_b_4606_ = v___x_4611_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg___boxed(lean_object* v_as_x27_4613_, lean_object* v_b_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v_res_4616_; 
v_res_4616_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4613_, v_b_4614_);
return v_res_4616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(lean_object* v_p_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v_data_4623_; lean_object* v___x_4624_; 
lean_inc_ref(v_p_4617_);
v_data_4623_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(v_p_4617_);
v___x_4624_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4623_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_);
lean_dec_ref(v_data_4623_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v_irrelevant_4626_; lean_object* v_lowerBounds_4627_; lean_object* v_upperBounds_4628_; lean_object* v_assumptions_4629_; lean_object* v_eliminations_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4645_; 
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_a_4625_);
lean_dec_ref(v___x_4624_);
v_irrelevant_4626_ = lean_ctor_get(v_a_4625_, 1);
lean_inc(v_irrelevant_4626_);
v_lowerBounds_4627_ = lean_ctor_get(v_a_4625_, 2);
lean_inc(v_lowerBounds_4627_);
v_upperBounds_4628_ = lean_ctor_get(v_a_4625_, 3);
lean_inc(v_upperBounds_4628_);
lean_dec(v_a_4625_);
v_assumptions_4629_ = lean_ctor_get(v_p_4617_, 0);
v_eliminations_4630_ = lean_ctor_get(v_p_4617_, 4);
v_isSharedCheck_4645_ = !lean_is_exclusive(v_p_4617_);
if (v_isSharedCheck_4645_ == 0)
{
lean_object* v_unused_4646_; lean_object* v_unused_4647_; lean_object* v_unused_4648_; lean_object* v_unused_4649_; lean_object* v_unused_4650_; 
v_unused_4646_ = lean_ctor_get(v_p_4617_, 6);
lean_dec(v_unused_4646_);
v_unused_4647_ = lean_ctor_get(v_p_4617_, 5);
lean_dec(v_unused_4647_);
v_unused_4648_ = lean_ctor_get(v_p_4617_, 3);
lean_dec(v_unused_4648_);
v_unused_4649_ = lean_ctor_get(v_p_4617_, 2);
lean_dec(v_unused_4649_);
v_unused_4650_ = lean_ctor_get(v_p_4617_, 1);
lean_dec(v_unused_4650_);
v___x_4632_ = v_p_4617_;
v_isShared_4633_ = v_isSharedCheck_4645_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_eliminations_4630_);
lean_inc(v_assumptions_4629_);
lean_dec(v_p_4617_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4645_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; uint8_t v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4640_; 
v___x_4634_ = lean_unsigned_to_nat(0u);
v___x_4635_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v___x_4636_ = 1;
v___x_4637_ = lean_box(0);
v___x_4638_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_4633_ == 0)
{
lean_ctor_set(v___x_4632_, 6, v___x_4638_);
lean_ctor_set(v___x_4632_, 5, v___x_4637_);
lean_ctor_set(v___x_4632_, 3, v___x_4635_);
lean_ctor_set(v___x_4632_, 2, v___x_4635_);
lean_ctor_set(v___x_4632_, 1, v___x_4634_);
v___x_4640_ = v___x_4632_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_assumptions_4629_);
lean_ctor_set(v_reuseFailAlloc_4644_, 1, v___x_4634_);
lean_ctor_set(v_reuseFailAlloc_4644_, 2, v___x_4635_);
lean_ctor_set(v_reuseFailAlloc_4644_, 3, v___x_4635_);
lean_ctor_set(v_reuseFailAlloc_4644_, 4, v_eliminations_4630_);
lean_ctor_set(v_reuseFailAlloc_4644_, 5, v___x_4637_);
lean_ctor_set(v_reuseFailAlloc_4644_, 6, v___x_4638_);
v___x_4640_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
lean_object* v___x_4641_; lean_object* v_a_4642_; lean_object* v___x_4643_; 
lean_ctor_set_uint8(v___x_4640_, sizeof(void*)*7, v___x_4636_);
v___x_4641_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_irrelevant_4626_, v___x_4640_);
v_a_4642_ = lean_ctor_get(v___x_4641_, 0);
lean_inc(v_a_4642_);
lean_dec_ref(v___x_4641_);
v___x_4643_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4628_, v_lowerBounds_4627_, v_a_4642_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_);
return v___x_4643_;
}
}
}
else
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4658_; 
lean_dec_ref(v_p_4617_);
v_a_4651_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4653_ = v___x_4624_;
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v___x_4624_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4656_; 
if (v_isShared_4654_ == 0)
{
v___x_4656_ = v___x_4653_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4651_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin___boxed(lean_object* v_p_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_);
lean_dec(v_a_4663_);
lean_dec_ref(v_a_4662_);
lean_dec(v_a_4661_);
lean_dec_ref(v_a_4660_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(lean_object* v_snd_4666_, lean_object* v_fst_4667_, lean_object* v_as_4668_, lean_object* v_as_x27_4669_, lean_object* v_b_4670_, lean_object* v_a_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v___x_4677_; 
v___x_4677_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4666_, v_fst_4667_, v_as_x27_4669_, v_b_4670_);
return v___x_4677_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___boxed(lean_object* v_snd_4678_, lean_object* v_fst_4679_, lean_object* v_as_4680_, lean_object* v_as_x27_4681_, lean_object* v_b_4682_, lean_object* v_a_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(v_snd_4678_, v_fst_4679_, v_as_4680_, v_as_x27_4681_, v_b_4682_, v_a_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v_as_4680_);
lean_dec(v_snd_4678_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(lean_object* v_as_4690_, lean_object* v_as_x27_4691_, lean_object* v_b_4692_, lean_object* v_a_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
lean_object* v___x_4699_; 
v___x_4699_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4691_, v_b_4692_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___boxed(lean_object* v_as_4700_, lean_object* v_as_x27_4701_, lean_object* v_b_4702_, lean_object* v_a_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(v_as_4700_, v_as_x27_4701_, v_b_4702_, v_a_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v_as_4700_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(lean_object* v_upperBounds_4710_, lean_object* v_as_4711_, lean_object* v_as_x27_4712_, lean_object* v_b_4713_, lean_object* v_a_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
lean_object* v___x_4720_; 
v___x_4720_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4710_, v_as_x27_4712_, v_b_4713_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
return v___x_4720_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___boxed(lean_object* v_upperBounds_4721_, lean_object* v_as_4722_, lean_object* v_as_x27_4723_, lean_object* v_b_4724_, lean_object* v_a_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(v_upperBounds_4721_, v_as_4722_, v_as_x27_4723_, v_b_4724_, v_a_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v_as_4722_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object* v_cls_4732_, lean_object* v___y_4733_){
_start:
{
lean_object* v_options_4735_; uint8_t v_hasTrace_4736_; 
v_options_4735_ = lean_ctor_get(v___y_4733_, 2);
v_hasTrace_4736_ = lean_ctor_get_uint8(v_options_4735_, sizeof(void*)*1);
if (v_hasTrace_4736_ == 0)
{
lean_object* v___x_4737_; lean_object* v___x_4738_; 
lean_dec(v_cls_4732_);
v___x_4737_ = lean_box(v_hasTrace_4736_);
v___x_4738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4737_);
return v___x_4738_;
}
else
{
lean_object* v_inheritedTraceOptions_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; uint8_t v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v_inheritedTraceOptions_4739_ = lean_ctor_get(v___y_4733_, 13);
v___x_4740_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___redArg___closed__1));
v___x_4741_ = l_Lean_Name_append(v___x_4740_, v_cls_4732_);
v___x_4742_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4739_, v_options_4735_, v___x_4741_);
lean_dec(v___x_4741_);
v___x_4743_ = lean_box(v___x_4742_);
v___x_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
return v___x_4744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg___boxed(lean_object* v_cls_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_){
_start:
{
lean_object* v_res_4748_; 
v_res_4748_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4745_, v___y_4746_);
lean_dec_ref(v___y_4746_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(lean_object* v_cls_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, uint8_t v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_){
_start:
{
lean_object* v___x_4760_; 
v___x_4760_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4749_, v___y_4757_);
return v___x_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___boxed(lean_object* v_cls_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_){
_start:
{
uint8_t v___y_18645__boxed_4772_; lean_object* v_res_4773_; 
v___y_18645__boxed_4772_ = lean_unbox(v___y_4765_);
v_res_4773_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(v_cls_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_18645__boxed_4772_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_);
lean_dec(v___y_4770_);
lean_dec_ref(v___y_4769_);
lean_dec(v___y_4768_);
lean_dec_ref(v___y_4767_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4764_);
lean_dec(v___y_4763_);
lean_dec(v___y_4762_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object* v_x_4774_, lean_object* v_x_4775_){
_start:
{
if (lean_obj_tag(v_x_4775_) == 0)
{
lean_inc(v_x_4774_);
return v_x_4774_;
}
else
{
lean_object* v_key_4776_; lean_object* v_value_4777_; lean_object* v_tail_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v_key_4776_ = lean_ctor_get(v_x_4775_, 0);
v_value_4777_ = lean_ctor_get(v_x_4775_, 1);
v_tail_4778_ = lean_ctor_get(v_x_4775_, 2);
v___x_4779_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_x_4774_, v_tail_4778_);
lean_inc(v_value_4777_);
lean_inc(v_key_4776_);
v___x_4780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4780_, 0, v_key_4776_);
lean_ctor_set(v___x_4780_, 1, v_value_4777_);
v___x_4781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4781_, 0, v___x_4780_);
lean_ctor_set(v___x_4781_, 1, v___x_4779_);
return v___x_4781_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object* v_x_4782_, lean_object* v_x_4783_){
_start:
{
lean_object* v_res_4784_; 
v_res_4784_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_x_4782_, v_x_4783_);
lean_dec(v_x_4783_);
lean_dec(v_x_4782_);
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4(lean_object* v_as_4785_, size_t v_i_4786_, size_t v_stop_4787_, lean_object* v_b_4788_){
_start:
{
uint8_t v___x_4789_; 
v___x_4789_ = lean_usize_dec_eq(v_i_4786_, v_stop_4787_);
if (v___x_4789_ == 0)
{
size_t v___x_4790_; size_t v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4790_ = ((size_t)1ULL);
v___x_4791_ = lean_usize_sub(v_i_4786_, v___x_4790_);
v___x_4792_ = lean_array_uget_borrowed(v_as_4785_, v___x_4791_);
v___x_4793_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_b_4788_, v___x_4792_);
lean_dec(v_b_4788_);
v_i_4786_ = v___x_4791_;
v_b_4788_ = v___x_4793_;
goto _start;
}
else
{
return v_b_4788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4___boxed(lean_object* v_as_4795_, lean_object* v_i_4796_, lean_object* v_stop_4797_, lean_object* v_b_4798_){
_start:
{
size_t v_i_boxed_4799_; size_t v_stop_boxed_4800_; lean_object* v_res_4801_; 
v_i_boxed_4799_ = lean_unbox_usize(v_i_4796_);
lean_dec(v_i_4796_);
v_stop_boxed_4800_ = lean_unbox_usize(v_stop_4797_);
lean_dec(v_stop_4797_);
v_res_4801_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4(v_as_4795_, v_i_boxed_4799_, v_stop_boxed_4800_, v_b_4798_);
lean_dec_ref(v_as_4795_);
return v_res_4801_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(lean_object* v_cls_4802_, lean_object* v_msg_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
lean_object* v_ref_4809_; lean_object* v___x_4810_; lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4855_; 
v_ref_4809_ = lean_ctor_get(v___y_4806_, 5);
v___x_4810_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4803_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_);
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4813_ = v___x_4810_;
v_isShared_4814_ = v_isSharedCheck_4855_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4810_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4855_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4815_; lean_object* v_traceState_4816_; lean_object* v_env_4817_; lean_object* v_nextMacroScope_4818_; lean_object* v_ngen_4819_; lean_object* v_auxDeclNGen_4820_; lean_object* v_cache_4821_; lean_object* v_messages_4822_; lean_object* v_infoState_4823_; lean_object* v_snapshotTasks_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4854_; 
v___x_4815_ = lean_st_ref_take(v___y_4807_);
v_traceState_4816_ = lean_ctor_get(v___x_4815_, 4);
v_env_4817_ = lean_ctor_get(v___x_4815_, 0);
v_nextMacroScope_4818_ = lean_ctor_get(v___x_4815_, 1);
v_ngen_4819_ = lean_ctor_get(v___x_4815_, 2);
v_auxDeclNGen_4820_ = lean_ctor_get(v___x_4815_, 3);
v_cache_4821_ = lean_ctor_get(v___x_4815_, 5);
v_messages_4822_ = lean_ctor_get(v___x_4815_, 6);
v_infoState_4823_ = lean_ctor_get(v___x_4815_, 7);
v_snapshotTasks_4824_ = lean_ctor_get(v___x_4815_, 8);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4826_ = v___x_4815_;
v_isShared_4827_ = v_isSharedCheck_4854_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_snapshotTasks_4824_);
lean_inc(v_infoState_4823_);
lean_inc(v_messages_4822_);
lean_inc(v_cache_4821_);
lean_inc(v_traceState_4816_);
lean_inc(v_auxDeclNGen_4820_);
lean_inc(v_ngen_4819_);
lean_inc(v_nextMacroScope_4818_);
lean_inc(v_env_4817_);
lean_dec(v___x_4815_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4854_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
uint64_t v_tid_4828_; lean_object* v_traces_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4853_; 
v_tid_4828_ = lean_ctor_get_uint64(v_traceState_4816_, sizeof(void*)*1);
v_traces_4829_ = lean_ctor_get(v_traceState_4816_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v_traceState_4816_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4831_ = v_traceState_4816_;
v_isShared_4832_ = v_isSharedCheck_4853_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_traces_4829_);
lean_dec(v_traceState_4816_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4853_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4833_; double v___x_4834_; uint8_t v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4843_; 
v___x_4833_ = lean_box(0);
v___x_4834_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__0);
v___x_4835_ = 0;
v___x_4836_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4837_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4837_, 0, v_cls_4802_);
lean_ctor_set(v___x_4837_, 1, v___x_4833_);
lean_ctor_set(v___x_4837_, 2, v___x_4836_);
lean_ctor_set_float(v___x_4837_, sizeof(void*)*3, v___x_4834_);
lean_ctor_set_float(v___x_4837_, sizeof(void*)*3 + 8, v___x_4834_);
lean_ctor_set_uint8(v___x_4837_, sizeof(void*)*3 + 16, v___x_4835_);
v___x_4838_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___closed__1));
v___x_4839_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4839_, 0, v___x_4837_);
lean_ctor_set(v___x_4839_, 1, v_a_4811_);
lean_ctor_set(v___x_4839_, 2, v___x_4838_);
lean_inc(v_ref_4809_);
v___x_4840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4840_, 0, v_ref_4809_);
lean_ctor_set(v___x_4840_, 1, v___x_4839_);
v___x_4841_ = l_Lean_PersistentArray_push___redArg(v_traces_4829_, v___x_4840_);
if (v_isShared_4832_ == 0)
{
lean_ctor_set(v___x_4831_, 0, v___x_4841_);
v___x_4843_ = v___x_4831_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4841_);
lean_ctor_set_uint64(v_reuseFailAlloc_4852_, sizeof(void*)*1, v_tid_4828_);
v___x_4843_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
lean_object* v___x_4845_; 
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 4, v___x_4843_);
v___x_4845_ = v___x_4826_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_env_4817_);
lean_ctor_set(v_reuseFailAlloc_4851_, 1, v_nextMacroScope_4818_);
lean_ctor_set(v_reuseFailAlloc_4851_, 2, v_ngen_4819_);
lean_ctor_set(v_reuseFailAlloc_4851_, 3, v_auxDeclNGen_4820_);
lean_ctor_set(v_reuseFailAlloc_4851_, 4, v___x_4843_);
lean_ctor_set(v_reuseFailAlloc_4851_, 5, v_cache_4821_);
lean_ctor_set(v_reuseFailAlloc_4851_, 6, v_messages_4822_);
lean_ctor_set(v_reuseFailAlloc_4851_, 7, v_infoState_4823_);
lean_ctor_set(v_reuseFailAlloc_4851_, 8, v_snapshotTasks_4824_);
v___x_4845_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4849_; 
v___x_4846_ = lean_st_ref_set(v___y_4807_, v___x_4845_);
v___x_4847_ = lean_box(0);
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 0, v___x_4847_);
v___x_4849_ = v___x_4813_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4847_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg___boxed(lean_object* v_cls_4856_, lean_object* v_msg_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(v_cls_4856_, v_msg_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object* v_a_4864_, lean_object* v_a_4865_){
_start:
{
if (lean_obj_tag(v_a_4864_) == 0)
{
lean_object* v___x_4866_; 
v___x_4866_ = l_List_reverse___redArg(v_a_4865_);
return v___x_4866_;
}
else
{
lean_object* v_head_4867_; lean_object* v_tail_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4985_; 
v_head_4867_ = lean_ctor_get(v_a_4864_, 0);
v_tail_4868_ = lean_ctor_get(v_a_4864_, 1);
v_isSharedCheck_4985_ = !lean_is_exclusive(v_a_4864_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4870_ = v_a_4864_;
v_isShared_4871_ = v_isSharedCheck_4985_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_tail_4868_);
lean_inc(v_head_4867_);
lean_dec(v_a_4864_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4985_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___y_4873_; lean_object* v_snd_4878_; lean_object* v_constraint_4879_; lean_object* v_fst_4880_; lean_object* v_lowerBound_4881_; lean_object* v_upperBound_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___y_4887_; lean_object* v___y_4888_; 
v_snd_4878_ = lean_ctor_get(v_head_4867_, 1);
v_constraint_4879_ = lean_ctor_get(v_snd_4878_, 1);
lean_inc_ref(v_constraint_4879_);
v_fst_4880_ = lean_ctor_get(v_head_4867_, 0);
lean_inc(v_fst_4880_);
lean_dec(v_head_4867_);
v_lowerBound_4881_ = lean_ctor_get(v_constraint_4879_, 0);
lean_inc(v_lowerBound_4881_);
v_upperBound_4882_ = lean_ctor_get(v_constraint_4879_, 1);
lean_inc(v_upperBound_4882_);
lean_dec_ref(v_constraint_4879_);
v___x_4883_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_fst_4880_);
lean_dec(v_fst_4880_);
v___x_4884_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_4885_ = lean_string_append(v___x_4883_, v___x_4884_);
if (lean_obj_tag(v_lowerBound_4881_) == 0)
{
if (lean_obj_tag(v_upperBound_4882_) == 0)
{
lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4893_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_4894_ = lean_string_append(v___x_4885_, v___x_4893_);
v___y_4873_ = v___x_4894_;
goto v___jp_4872_;
}
else
{
lean_object* v_val_4895_; lean_object* v___x_4896_; lean_object* v___y_4898_; lean_object* v_intZero_4903_; uint8_t v_isNeg_4904_; 
v_val_4895_ = lean_ctor_get(v_upperBound_4882_, 0);
lean_inc(v_val_4895_);
lean_dec_ref(v_upperBound_4882_);
v___x_4896_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_4903_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4904_ = lean_int_dec_lt(v_val_4895_, v_intZero_4903_);
if (v_isNeg_4904_ == 0)
{
lean_object* v_a_4905_; lean_object* v___x_4906_; 
v_a_4905_ = lean_nat_abs(v_val_4895_);
lean_dec(v_val_4895_);
v___x_4906_ = l_Nat_reprFast(v_a_4905_);
v___y_4898_ = v___x_4906_;
goto v___jp_4897_;
}
else
{
lean_object* v_abs_4907_; lean_object* v_one_4908_; lean_object* v_a_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; 
v_abs_4907_ = lean_nat_abs(v_val_4895_);
lean_dec(v_val_4895_);
v_one_4908_ = lean_unsigned_to_nat(1u);
v_a_4909_ = lean_nat_sub(v_abs_4907_, v_one_4908_);
lean_dec(v_abs_4907_);
v___x_4910_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4911_ = lean_nat_add(v_a_4909_, v_one_4908_);
lean_dec(v_a_4909_);
v___x_4912_ = l_Nat_reprFast(v___x_4911_);
v___x_4913_ = lean_string_append(v___x_4910_, v___x_4912_);
lean_dec_ref(v___x_4912_);
v___y_4898_ = v___x_4913_;
goto v___jp_4897_;
}
v___jp_4897_:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4899_ = lean_string_append(v___x_4896_, v___y_4898_);
lean_dec_ref(v___y_4898_);
v___x_4900_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4901_ = lean_string_append(v___x_4899_, v___x_4900_);
v___x_4902_ = lean_string_append(v___x_4885_, v___x_4901_);
lean_dec_ref(v___x_4901_);
v___y_4873_ = v___x_4902_;
goto v___jp_4872_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_4882_) == 0)
{
lean_object* v_val_4914_; lean_object* v___x_4915_; lean_object* v___y_4917_; lean_object* v_intZero_4922_; uint8_t v_isNeg_4923_; 
v_val_4914_ = lean_ctor_get(v_lowerBound_4881_, 0);
lean_inc(v_val_4914_);
lean_dec_ref(v_lowerBound_4881_);
v___x_4915_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4922_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4923_ = lean_int_dec_lt(v_val_4914_, v_intZero_4922_);
if (v_isNeg_4923_ == 0)
{
lean_object* v_a_4924_; lean_object* v___x_4925_; 
v_a_4924_ = lean_nat_abs(v_val_4914_);
lean_dec(v_val_4914_);
v___x_4925_ = l_Nat_reprFast(v_a_4924_);
v___y_4917_ = v___x_4925_;
goto v___jp_4916_;
}
else
{
lean_object* v_abs_4926_; lean_object* v_one_4927_; lean_object* v_a_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v_abs_4926_ = lean_nat_abs(v_val_4914_);
lean_dec(v_val_4914_);
v_one_4927_ = lean_unsigned_to_nat(1u);
v_a_4928_ = lean_nat_sub(v_abs_4926_, v_one_4927_);
lean_dec(v_abs_4926_);
v___x_4929_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4930_ = lean_nat_add(v_a_4928_, v_one_4927_);
lean_dec(v_a_4928_);
v___x_4931_ = l_Nat_reprFast(v___x_4930_);
v___x_4932_ = lean_string_append(v___x_4929_, v___x_4931_);
lean_dec_ref(v___x_4931_);
v___y_4917_ = v___x_4932_;
goto v___jp_4916_;
}
v___jp_4916_:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
v___x_4918_ = lean_string_append(v___x_4915_, v___y_4917_);
lean_dec_ref(v___y_4917_);
v___x_4919_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_4920_ = lean_string_append(v___x_4918_, v___x_4919_);
v___x_4921_ = lean_string_append(v___x_4885_, v___x_4920_);
lean_dec_ref(v___x_4920_);
v___y_4873_ = v___x_4921_;
goto v___jp_4872_;
}
}
else
{
lean_object* v_val_4933_; lean_object* v_val_4934_; uint8_t v___x_4935_; 
v_val_4933_ = lean_ctor_get(v_lowerBound_4881_, 0);
lean_inc(v_val_4933_);
lean_dec_ref(v_lowerBound_4881_);
v_val_4934_ = lean_ctor_get(v_upperBound_4882_, 0);
lean_inc(v_val_4934_);
lean_dec_ref(v_upperBound_4882_);
v___x_4935_ = lean_int_dec_lt(v_val_4934_, v_val_4933_);
if (v___x_4935_ == 0)
{
uint8_t v___x_4936_; 
v___x_4936_ = lean_int_dec_eq(v_val_4933_, v_val_4934_);
if (v___x_4936_ == 0)
{
lean_object* v___x_4937_; lean_object* v___y_4939_; lean_object* v_intZero_4954_; uint8_t v_isNeg_4955_; 
v___x_4937_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4954_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4955_ = lean_int_dec_lt(v_val_4933_, v_intZero_4954_);
if (v_isNeg_4955_ == 0)
{
lean_object* v_a_4956_; lean_object* v___x_4957_; 
v_a_4956_ = lean_nat_abs(v_val_4933_);
lean_dec(v_val_4933_);
v___x_4957_ = l_Nat_reprFast(v_a_4956_);
v___y_4939_ = v___x_4957_;
goto v___jp_4938_;
}
else
{
lean_object* v_abs_4958_; lean_object* v_one_4959_; lean_object* v_a_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
v_abs_4958_ = lean_nat_abs(v_val_4933_);
lean_dec(v_val_4933_);
v_one_4959_ = lean_unsigned_to_nat(1u);
v_a_4960_ = lean_nat_sub(v_abs_4958_, v_one_4959_);
lean_dec(v_abs_4958_);
v___x_4961_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4962_ = lean_nat_add(v_a_4960_, v_one_4959_);
lean_dec(v_a_4960_);
v___x_4963_ = l_Nat_reprFast(v___x_4962_);
v___x_4964_ = lean_string_append(v___x_4961_, v___x_4963_);
lean_dec_ref(v___x_4963_);
v___y_4939_ = v___x_4964_;
goto v___jp_4938_;
}
v___jp_4938_:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v_intZero_4943_; uint8_t v_isNeg_4944_; 
v___x_4940_ = lean_string_append(v___x_4937_, v___y_4939_);
lean_dec_ref(v___y_4939_);
v___x_4941_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_4942_ = lean_string_append(v___x_4940_, v___x_4941_);
v_intZero_4943_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4944_ = lean_int_dec_lt(v_val_4934_, v_intZero_4943_);
if (v_isNeg_4944_ == 0)
{
lean_object* v_a_4945_; lean_object* v___x_4946_; 
v_a_4945_ = lean_nat_abs(v_val_4934_);
lean_dec(v_val_4934_);
v___x_4946_ = l_Nat_reprFast(v_a_4945_);
v___y_4887_ = v___x_4942_;
v___y_4888_ = v___x_4946_;
goto v___jp_4886_;
}
else
{
lean_object* v_abs_4947_; lean_object* v_one_4948_; lean_object* v_a_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v_abs_4947_ = lean_nat_abs(v_val_4934_);
lean_dec(v_val_4934_);
v_one_4948_ = lean_unsigned_to_nat(1u);
v_a_4949_ = lean_nat_sub(v_abs_4947_, v_one_4948_);
lean_dec(v_abs_4947_);
v___x_4950_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4951_ = lean_nat_add(v_a_4949_, v_one_4948_);
lean_dec(v_a_4949_);
v___x_4952_ = l_Nat_reprFast(v___x_4951_);
v___x_4953_ = lean_string_append(v___x_4950_, v___x_4952_);
lean_dec_ref(v___x_4952_);
v___y_4887_ = v___x_4942_;
v___y_4888_ = v___x_4953_;
goto v___jp_4886_;
}
}
}
else
{
lean_object* v___x_4965_; lean_object* v___y_4967_; lean_object* v_intZero_4972_; uint8_t v_isNeg_4973_; 
lean_dec(v_val_4934_);
v___x_4965_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_4972_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4973_ = lean_int_dec_lt(v_val_4933_, v_intZero_4972_);
if (v_isNeg_4973_ == 0)
{
lean_object* v_a_4974_; lean_object* v___x_4975_; 
v_a_4974_ = lean_nat_abs(v_val_4933_);
lean_dec(v_val_4933_);
v___x_4975_ = l_Nat_reprFast(v_a_4974_);
v___y_4967_ = v___x_4975_;
goto v___jp_4966_;
}
else
{
lean_object* v_abs_4976_; lean_object* v_one_4977_; lean_object* v_a_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v_abs_4976_ = lean_nat_abs(v_val_4933_);
lean_dec(v_val_4933_);
v_one_4977_ = lean_unsigned_to_nat(1u);
v_a_4978_ = lean_nat_sub(v_abs_4976_, v_one_4977_);
lean_dec(v_abs_4976_);
v___x_4979_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4980_ = lean_nat_add(v_a_4978_, v_one_4977_);
lean_dec(v_a_4978_);
v___x_4981_ = l_Nat_reprFast(v___x_4980_);
v___x_4982_ = lean_string_append(v___x_4979_, v___x_4981_);
lean_dec_ref(v___x_4981_);
v___y_4967_ = v___x_4982_;
goto v___jp_4966_;
}
v___jp_4966_:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4968_ = lean_string_append(v___x_4965_, v___y_4967_);
lean_dec_ref(v___y_4967_);
v___x_4969_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_4970_ = lean_string_append(v___x_4968_, v___x_4969_);
v___x_4971_ = lean_string_append(v___x_4885_, v___x_4970_);
lean_dec_ref(v___x_4970_);
v___y_4873_ = v___x_4971_;
goto v___jp_4872_;
}
}
}
else
{
lean_object* v___x_4983_; lean_object* v___x_4984_; 
lean_dec(v_val_4934_);
lean_dec(v_val_4933_);
v___x_4983_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_4984_ = lean_string_append(v___x_4885_, v___x_4983_);
v___y_4873_ = v___x_4984_;
goto v___jp_4872_;
}
}
}
v___jp_4872_:
{
lean_object* v___x_4875_; 
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 1, v_a_4865_);
lean_ctor_set(v___x_4870_, 0, v___y_4873_);
v___x_4875_ = v___x_4870_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v___y_4873_);
lean_ctor_set(v_reuseFailAlloc_4877_, 1, v_a_4865_);
v___x_4875_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
v_a_4864_ = v_tail_4868_;
v_a_4865_ = v___x_4875_;
goto _start;
}
}
v___jp_4886_:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; 
v___x_4889_ = lean_string_append(v___y_4887_, v___y_4888_);
lean_dec_ref(v___y_4888_);
v___x_4890_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4891_ = lean_string_append(v___x_4889_, v___x_4890_);
v___x_4892_ = lean_string_append(v___x_4885_, v___x_4891_);
lean_dec_ref(v___x_4891_);
v___y_4873_ = v___x_4892_;
goto v___jp_4872_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1(void){
_start:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___x_4987_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__0));
v___x_4988_ = l_Lean_stringToMessageData(v___x_4987_);
return v___x_4988_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1(void){
_start:
{
lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4990_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__0));
v___x_4991_ = l_Lean_stringToMessageData(v___x_4990_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega(lean_object* v_p_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, uint8_t v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v___y_5004_; lean_object* v___y_5005_; lean_object* v___y_5006_; uint8_t v___y_5007_; lean_object* v___y_5008_; lean_object* v___y_5009_; lean_object* v___y_5010_; lean_object* v___y_5011_; lean_object* v___y_5012_; lean_object* v_cls_5018_; lean_object* v___x_5019_; 
v_cls_5018_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_5019_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5018_, v_a_5000_);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_object* v_a_5020_; uint8_t v___x_5021_; 
v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
lean_inc(v_a_5020_);
lean_dec_ref(v___x_5019_);
v___x_5021_ = lean_unbox(v_a_5020_);
lean_dec(v_a_5020_);
if (v___x_5021_ == 0)
{
v___y_5004_ = v_a_4993_;
v___y_5005_ = v_a_4994_;
v___y_5006_ = v_a_4995_;
v___y_5007_ = v_a_4996_;
v___y_5008_ = v_a_4997_;
v___y_5009_ = v_a_4998_;
v___y_5010_ = v_a_4999_;
v___y_5011_ = v_a_5000_;
v___y_5012_ = v_a_5001_;
goto v___jp_5003_;
}
else
{
lean_object* v_constraints_5022_; uint8_t v_possible_5023_; lean_object* v___x_5024_; lean_object* v___y_5026_; 
v_constraints_5022_ = lean_ctor_get(v_p_4992_, 2);
v_possible_5023_ = lean_ctor_get_uint8(v_p_4992_, sizeof(void*)*7);
v___x_5024_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1);
if (v_possible_5023_ == 0)
{
lean_object* v___x_5039_; 
v___x_5039_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
v___y_5026_ = v___x_5039_;
goto v___jp_5025_;
}
else
{
uint8_t v___x_5040_; 
v___x_5040_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_4992_);
if (v___x_5040_ == 0)
{
lean_object* v_buckets_5041_; lean_object* v___x_5042_; lean_object* v___y_5044_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; uint8_t v___x_5051_; 
v_buckets_5041_ = lean_ctor_get(v_constraints_5022_, 1);
v___x_5042_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5048_ = lean_box(0);
v___x_5049_ = lean_array_get_size(v_buckets_5041_);
v___x_5050_ = lean_unsigned_to_nat(0u);
v___x_5051_ = lean_nat_dec_lt(v___x_5050_, v___x_5049_);
if (v___x_5051_ == 0)
{
v___y_5044_ = v___x_5048_;
goto v___jp_5043_;
}
else
{
size_t v___x_5052_; size_t v___x_5053_; lean_object* v___x_5054_; 
v___x_5052_ = lean_usize_of_nat(v___x_5049_);
v___x_5053_ = ((size_t)0ULL);
v___x_5054_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4(v_buckets_5041_, v___x_5052_, v___x_5053_, v___x_5048_);
v___y_5044_ = v___x_5054_;
goto v___jp_5043_;
}
v___jp_5043_:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; 
v___x_5045_ = lean_box(0);
v___x_5046_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v___y_5044_, v___x_5045_);
v___x_5047_ = l_String_intercalate(v___x_5042_, v___x_5046_);
v___y_5026_ = v___x_5047_;
goto v___jp_5025_;
}
}
else
{
lean_object* v___x_5055_; 
v___x_5055_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_5026_ = v___x_5055_;
goto v___jp_5025_;
}
}
v___jp_5025_:
{
lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5027_, 0, v___y_5026_);
v___x_5028_ = l_Lean_MessageData_ofFormat(v___x_5027_);
v___x_5029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5029_, 0, v___x_5024_);
lean_ctor_set(v___x_5029_, 1, v___x_5028_);
v___x_5030_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(v_cls_5018_, v___x_5029_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
if (lean_obj_tag(v___x_5030_) == 0)
{
lean_dec_ref(v___x_5030_);
v___y_5004_ = v_a_4993_;
v___y_5005_ = v_a_4994_;
v___y_5006_ = v_a_4995_;
v___y_5007_ = v_a_4996_;
v___y_5008_ = v_a_4997_;
v___y_5009_ = v_a_4998_;
v___y_5010_ = v_a_4999_;
v___y_5011_ = v_a_5000_;
v___y_5012_ = v_a_5001_;
goto v___jp_5003_;
}
else
{
lean_object* v_a_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5038_; 
lean_dec_ref(v_p_4992_);
v_a_5031_ = lean_ctor_get(v___x_5030_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___x_5030_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5033_ = v___x_5030_;
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_a_5031_);
lean_dec(v___x_5030_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v___x_5036_; 
if (v_isShared_5034_ == 0)
{
v___x_5036_ = v___x_5033_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_a_5031_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
}
}
}
else
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5063_; 
lean_dec_ref(v_p_4992_);
v_a_5056_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5058_ = v___x_5019_;
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___x_5019_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5061_; 
if (v_isShared_5059_ == 0)
{
v___x_5061_ = v___x_5058_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_a_5056_);
v___x_5061_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
return v___x_5061_;
}
}
}
v___jp_5003_:
{
uint8_t v_possible_5013_; 
v_possible_5013_ = lean_ctor_get_uint8(v_p_4992_, sizeof(void*)*7);
if (v_possible_5013_ == 0)
{
lean_object* v___x_5014_; 
v___x_5014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5014_, 0, v_p_4992_);
return v___x_5014_;
}
else
{
lean_object* v___x_5015_; 
v___x_5015_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_4992_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_);
if (lean_obj_tag(v___x_5015_) == 0)
{
lean_object* v_a_5016_; lean_object* v___x_5017_; 
v_a_5016_ = lean_ctor_get(v___x_5015_, 0);
lean_inc(v_a_5016_);
lean_dec_ref(v___x_5015_);
v___x_5017_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_a_5016_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_);
return v___x_5017_;
}
else
{
return v___x_5015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination(lean_object* v_p_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, uint8_t v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_){
_start:
{
lean_object* v___y_5076_; lean_object* v___y_5077_; lean_object* v___y_5078_; uint8_t v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v___y_5084_; uint8_t v_possible_5088_; 
v_possible_5088_ = lean_ctor_get_uint8(v_p_5064_, sizeof(void*)*7);
if (v_possible_5088_ == 0)
{
lean_object* v___x_5089_; 
v___x_5089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5089_, 0, v_p_5064_);
return v___x_5089_;
}
else
{
lean_object* v_constraints_5090_; uint8_t v___x_5091_; 
v_constraints_5090_ = lean_ctor_get(v_p_5064_, 2);
v___x_5091_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_5064_);
if (v___x_5091_ == 0)
{
lean_object* v_cls_5092_; lean_object* v___x_5093_; 
v_cls_5092_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_5093_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5092_, v_a_5072_);
if (lean_obj_tag(v___x_5093_) == 0)
{
lean_object* v_a_5094_; uint8_t v___x_5095_; 
v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
lean_inc(v_a_5094_);
lean_dec_ref(v___x_5093_);
v___x_5095_ = lean_unbox(v_a_5094_);
lean_dec(v_a_5094_);
if (v___x_5095_ == 0)
{
v___y_5076_ = v_a_5065_;
v___y_5077_ = v_a_5066_;
v___y_5078_ = v_a_5067_;
v___y_5079_ = v_a_5068_;
v___y_5080_ = v_a_5069_;
v___y_5081_ = v_a_5070_;
v___y_5082_ = v_a_5071_;
v___y_5083_ = v_a_5072_;
v___y_5084_ = v_a_5073_;
goto v___jp_5075_;
}
else
{
lean_object* v___x_5096_; lean_object* v___y_5098_; 
v___x_5096_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1);
if (v___x_5091_ == 0)
{
lean_object* v_buckets_5111_; lean_object* v___x_5112_; lean_object* v___y_5114_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; uint8_t v___x_5121_; 
v_buckets_5111_ = lean_ctor_get(v_constraints_5090_, 1);
v___x_5112_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5118_ = lean_box(0);
v___x_5119_ = lean_array_get_size(v_buckets_5111_);
v___x_5120_ = lean_unsigned_to_nat(0u);
v___x_5121_ = lean_nat_dec_lt(v___x_5120_, v___x_5119_);
if (v___x_5121_ == 0)
{
v___y_5114_ = v___x_5118_;
goto v___jp_5113_;
}
else
{
size_t v___x_5122_; size_t v___x_5123_; lean_object* v___x_5124_; 
v___x_5122_ = lean_usize_of_nat(v___x_5119_);
v___x_5123_ = ((size_t)0ULL);
v___x_5124_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__4(v_buckets_5111_, v___x_5122_, v___x_5123_, v___x_5118_);
v___y_5114_ = v___x_5124_;
goto v___jp_5113_;
}
v___jp_5113_:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; 
v___x_5115_ = lean_box(0);
v___x_5116_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v___y_5114_, v___x_5115_);
v___x_5117_ = l_String_intercalate(v___x_5112_, v___x_5116_);
v___y_5098_ = v___x_5117_;
goto v___jp_5097_;
}
}
else
{
lean_object* v___x_5125_; 
v___x_5125_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_5098_ = v___x_5125_;
goto v___jp_5097_;
}
v___jp_5097_:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; 
v___x_5099_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5099_, 0, v___y_5098_);
v___x_5100_ = l_Lean_MessageData_ofFormat(v___x_5099_);
v___x_5101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5096_);
lean_ctor_set(v___x_5101_, 1, v___x_5100_);
v___x_5102_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(v_cls_5092_, v___x_5101_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_dec_ref(v___x_5102_);
v___y_5076_ = v_a_5065_;
v___y_5077_ = v_a_5066_;
v___y_5078_ = v_a_5067_;
v___y_5079_ = v_a_5068_;
v___y_5080_ = v_a_5069_;
v___y_5081_ = v_a_5070_;
v___y_5082_ = v_a_5071_;
v___y_5083_ = v_a_5072_;
v___y_5084_ = v_a_5073_;
goto v___jp_5075_;
}
else
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
lean_dec_ref(v_p_5064_);
v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_5102_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5105_ = v___x_5102_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_5102_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
}
}
}
else
{
lean_object* v_a_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5133_; 
lean_dec_ref(v_p_5064_);
v_a_5126_ = lean_ctor_get(v___x_5093_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5128_ = v___x_5093_;
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_a_5126_);
lean_dec(v___x_5093_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v___x_5131_; 
if (v_isShared_5129_ == 0)
{
v___x_5131_ = v___x_5128_;
goto v_reusejp_5130_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_a_5126_);
v___x_5131_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5130_;
}
v_reusejp_5130_:
{
return v___x_5131_;
}
}
}
}
else
{
lean_object* v___x_5134_; 
v___x_5134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5134_, 0, v_p_5064_);
return v___x_5134_;
}
}
v___jp_5075_:
{
lean_object* v___x_5085_; 
v___x_5085_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_5064_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v_a_5086_; lean_object* v___x_5087_; 
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
lean_inc(v_a_5086_);
lean_dec_ref(v___x_5085_);
v___x_5087_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_a_5086_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
return v___x_5087_;
}
else
{
return v___x_5085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___boxed(lean_object* v_p_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_){
_start:
{
uint8_t v_a_boxed_5146_; lean_object* v_res_5147_; 
v_a_boxed_5146_ = lean_unbox(v_a_5139_);
v_res_5147_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_p_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_boxed_5146_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_);
lean_dec(v_a_5144_);
lean_dec_ref(v_a_5143_);
lean_dec(v_a_5142_);
lean_dec_ref(v_a_5141_);
lean_dec(v_a_5140_);
lean_dec_ref(v_a_5138_);
lean_dec(v_a_5137_);
lean_dec(v_a_5136_);
return v_res_5147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___boxed(lean_object* v_p_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_){
_start:
{
uint8_t v_a_boxed_5159_; lean_object* v_res_5160_; 
v_a_boxed_5159_ = lean_unbox(v_a_5152_);
v_res_5160_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_p_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_boxed_5159_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_);
lean_dec(v_a_5157_);
lean_dec_ref(v_a_5156_);
lean_dec(v_a_5155_);
lean_dec_ref(v_a_5154_);
lean_dec(v_a_5153_);
lean_dec_ref(v_a_5151_);
lean_dec(v_a_5150_);
lean_dec(v_a_5149_);
return v_res_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object* v_cls_5161_, lean_object* v_msg_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, uint8_t v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_){
_start:
{
lean_object* v___x_5173_; 
v___x_5173_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___redArg(v_cls_5161_, v_msg_5162_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_);
return v___x_5173_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1___boxed(lean_object* v_cls_5174_, lean_object* v_msg_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_){
_start:
{
uint8_t v___y_19287__boxed_5186_; lean_object* v_res_5187_; 
v___y_19287__boxed_5186_ = lean_unbox(v___y_5179_);
v_res_5187_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v_cls_5174_, v_msg_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_19287__boxed_5186_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
lean_dec(v___y_5184_);
lean_dec_ref(v___y_5183_);
lean_dec(v___y_5182_);
lean_dec_ref(v___y_5181_);
lean_dec(v___y_5180_);
lean_dec_ref(v___y_5178_);
lean_dec(v___y_5177_);
lean_dec(v___y_5176_);
return v_res_5187_;
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
