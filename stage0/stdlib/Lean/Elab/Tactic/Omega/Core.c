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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_85_;
v_res_85_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_();
stack->m_obj
 = v_res_85_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2____boxed(lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_();
return v_res_87_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_box(0);
v___x_96_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__2));
v___x_97_ = l_Lean_Expr_const___override(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v_type_103_; 
v___x_101_ = lean_box(0);
v___x_102_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__5));
v_type_103_ = l_Lean_Expr_const___override(v___x_102_, v___x_101_);
return v_type_103_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_113_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__9));
v___x_114_ = l_Lean_mkConst(v___x_113_, v___x_112_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12(void){
_start:
{
lean_object* v_type_115_; lean_object* v___x_116_; lean_object* v_nil_117_; 
v_type_115_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_116_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__11);
v_nil_117_ = l_Lean_Expr_app___override(v___x_116_, v_type_115_);
return v_nil_117_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_123_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__14));
v___x_124_ = l_Lean_mkConst(v___x_123_, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16(void){
_start:
{
lean_object* v_type_125_; lean_object* v___x_126_; lean_object* v_cons_127_; 
v_type_125_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_126_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__15);
v_cons_127_ = l_Lean_Expr_app___override(v___x_126_, v_type_125_);
return v_cons_127_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_nat_to_int(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = l_Lean_Level_ofNat(v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_box(0);
v___x_138_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21);
v___x_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__22);
v___x_141_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__20));
v___x_142_ = l_Lean_Expr_const___override(v___x_141_, v___x_140_);
return v___x_142_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_box(0);
v___x_148_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__25));
v___x_149_ = l_Lean_Expr_const___override(v___x_148_, v___x_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0(lean_object* v___x_150_, lean_object* v_lc_151_){
_start:
{
lean_object* v_const_152_; lean_object* v_coeffs_153_; lean_object* v___x_154_; lean_object* v___y_156_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_const_152_ = lean_ctor_get(v_lc_151_, 0);
lean_inc(v_const_152_);
v_coeffs_153_ = lean_ctor_get(v_lc_151_, 1);
lean_inc(v_coeffs_153_);
lean_dec_ref(v_lc_151_);
v___x_154_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__3);
v___x_162_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_163_ = lean_int_dec_le(v___x_162_, v_const_152_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_164_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_165_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_166_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_167_ = lean_int_neg(v_const_152_);
lean_dec(v_const_152_);
v___x_168_ = l_Int_toNat(v___x_167_);
lean_dec(v___x_167_);
v___x_169_ = l_Lean_instToExprInt_mkNat(v___x_168_);
v___x_170_ = l_Lean_mkApp3(v___x_164_, v___x_165_, v___x_166_, v___x_169_);
v___y_156_ = v___x_170_;
goto v___jp_155_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = l_Int_toNat(v_const_152_);
lean_dec(v_const_152_);
v___x_172_ = l_Lean_instToExprInt_mkNat(v___x_171_);
v___y_156_ = v___x_172_;
goto v___jp_155_;
}
v___jp_155_:
{
lean_object* v_nil_157_; lean_object* v___x_158_; lean_object* v_cons_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_nil_157_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v___x_158_ = l_Lean_Expr_app___override(v___x_154_, v___y_156_);
v_cons_159_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_160_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_150_, v_nil_157_, v_cons_159_, v_coeffs_153_);
v___x_161_ = l_Lean_Expr_app___override(v___x_158_, v___x_160_);
return v___x_161_;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0(void){
_start:
{
lean_object* v___x_173_; lean_object* v___f_174_; 
v___x_173_ = l_Lean_instToExprInt;
v___f_174_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0), 2, 1);
lean_closure_set(v___f_174_, 0, v___x_173_);
return v___f_174_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_box(0);
v___x_180_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__1));
v___x_181_ = l_Lean_Expr_const___override(v___x_180_, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3(void){
_start:
{
lean_object* v___x_182_; lean_object* v___f_183_; lean_object* v___x_184_; 
v___x_182_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__2);
v___f_183_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__0);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___f_183_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo(void){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___closed__3);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_box(0);
v___x_193_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__1));
v___x_194_ = l_Lean_Expr_const___override(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_201_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__5));
v___x_202_ = l_Lean_mkConst(v___x_201_, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7(void){
_start:
{
lean_object* v_type_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_type_203_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_204_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_205_ = l_Lean_Expr_app___override(v___x_204_, v_type_203_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_211_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__9));
v___x_212_ = l_Lean_mkConst(v___x_211_, v___x_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0(lean_object* v_s_213_){
_start:
{
lean_object* v_lowerBound_214_; lean_object* v_upperBound_215_; lean_object* v___x_216_; lean_object* v_type_217_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_225_; 
v_lowerBound_214_ = lean_ctor_get(v_s_213_, 0);
v_upperBound_215_ = lean_ctor_get(v_s_213_, 1);
v___x_216_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_217_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_214_) == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_225_ = v___x_241_;
goto v___jp_224_;
}
else
{
lean_object* v_val_242_; lean_object* v___x_243_; lean_object* v___y_245_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_val_242_ = lean_ctor_get(v_lowerBound_214_, 0);
v___x_243_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_247_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_248_ = lean_int_dec_le(v___x_247_, v_val_242_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_249_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_250_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_251_ = lean_int_neg(v_val_242_);
v___x_252_ = l_Int_toNat(v___x_251_);
lean_dec(v___x_251_);
v___x_253_ = l_Lean_instToExprInt_mkNat(v___x_252_);
v___x_254_ = l_Lean_mkApp3(v___x_249_, v_type_217_, v___x_250_, v___x_253_);
v___y_245_ = v___x_254_;
goto v___jp_244_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = l_Int_toNat(v_val_242_);
v___x_256_ = l_Lean_instToExprInt_mkNat(v___x_255_);
v___y_245_ = v___x_256_;
goto v___jp_244_;
}
v___jp_244_:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_mkAppB(v___x_243_, v_type_217_, v___y_245_);
v___y_225_ = v___x_246_;
goto v___jp_224_;
}
}
v___jp_218_:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
lean_inc_ref(v___y_220_);
v___x_222_ = l_Lean_mkAppB(v___y_220_, v_type_217_, v___y_221_);
v___x_223_ = l_Lean_Expr_app___override(v___y_219_, v___x_222_);
return v___x_223_;
}
v___jp_224_:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Expr_app___override(v___x_216_, v___y_225_);
if (lean_obj_tag(v_upperBound_215_) == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_228_ = l_Lean_Expr_app___override(v___x_226_, v___x_227_);
return v___x_228_;
}
else
{
lean_object* v_val_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v_val_229_ = lean_ctor_get(v_upperBound_215_, 0);
v___x_230_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_231_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_232_ = lean_int_dec_le(v___x_231_, v_val_229_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_233_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_234_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_235_ = lean_int_neg(v_val_229_);
v___x_236_ = l_Int_toNat(v___x_235_);
lean_dec(v___x_235_);
v___x_237_ = l_Lean_instToExprInt_mkNat(v___x_236_);
v___x_238_ = l_Lean_mkApp3(v___x_233_, v_type_217_, v___x_234_, v___x_237_);
v___y_219_ = v___x_226_;
v___y_220_ = v___x_230_;
v___y_221_ = v___x_238_;
goto v___jp_218_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = l_Int_toNat(v_val_229_);
v___x_240_ = l_Lean_instToExprInt_mkNat(v___x_239_);
v___y_219_ = v___x_226_;
v___y_220_ = v___x_230_;
v___y_221_ = v___x_240_;
goto v___jp_218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___boxed(lean_object* v_s_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0(v_s_257_);
lean_dec_ref(v_s_257_);
return v_res_258_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_box(0);
v___x_265_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__1));
v___x_266_ = l_Lean_Expr_const___override(v___x_265_, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3(void){
_start:
{
lean_object* v___x_267_; lean_object* v___f_268_; lean_object* v___x_269_; 
v___x_267_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__2);
v___f_268_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__0));
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___f_268_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint(void){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___closed__3);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl___redArg(lean_object* v_x_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_tag_nat(v_x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl___redArg___boxed(lean_object* v_x_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl___redArg(v_x_273_);
lean_dec_ref(v_x_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl(lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_x_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_tag_nat(v_x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl___boxed(lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_x_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl(v_a_279_, v_a_280_, v_x_281_);
lean_dec_ref(v_x_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(lean_object* v_t_283_, lean_object* v_k_284_){
_start:
{
switch(lean_obj_tag(v_t_283_))
{
case 0:
{
lean_object* v_s_285_; lean_object* v_x_286_; lean_object* v_i_287_; lean_object* v___x_288_; 
v_s_285_ = lean_ctor_get(v_t_283_, 0);
lean_inc_ref(v_s_285_);
v_x_286_ = lean_ctor_get(v_t_283_, 1);
lean_inc(v_x_286_);
v_i_287_ = lean_ctor_get(v_t_283_, 2);
lean_inc(v_i_287_);
lean_dec_ref_known(v_t_283_, 3);
v___x_288_ = lean_apply_3(v_k_284_, v_s_285_, v_x_286_, v_i_287_);
return v___x_288_;
}
case 1:
{
lean_object* v_s_289_; lean_object* v_c_290_; lean_object* v_j_291_; lean_object* v___x_292_; 
v_s_289_ = lean_ctor_get(v_t_283_, 0);
lean_inc_ref(v_s_289_);
v_c_290_ = lean_ctor_get(v_t_283_, 1);
lean_inc(v_c_290_);
v_j_291_ = lean_ctor_get(v_t_283_, 2);
lean_inc_ref(v_j_291_);
lean_dec_ref_known(v_t_283_, 3);
v___x_292_ = lean_apply_3(v_k_284_, v_s_289_, v_c_290_, v_j_291_);
return v___x_292_;
}
case 2:
{
lean_object* v_s_293_; lean_object* v_t_294_; lean_object* v_c_295_; lean_object* v_j_296_; lean_object* v_k_297_; lean_object* v___x_298_; 
v_s_293_ = lean_ctor_get(v_t_283_, 0);
lean_inc_ref(v_s_293_);
v_t_294_ = lean_ctor_get(v_t_283_, 1);
lean_inc_ref(v_t_294_);
v_c_295_ = lean_ctor_get(v_t_283_, 2);
lean_inc(v_c_295_);
v_j_296_ = lean_ctor_get(v_t_283_, 3);
lean_inc_ref(v_j_296_);
v_k_297_ = lean_ctor_get(v_t_283_, 4);
lean_inc_ref(v_k_297_);
lean_dec_ref_known(v_t_283_, 5);
v___x_298_ = lean_apply_5(v_k_284_, v_s_293_, v_t_294_, v_c_295_, v_j_296_, v_k_297_);
return v___x_298_;
}
case 3:
{
lean_object* v_s_299_; lean_object* v_t_300_; lean_object* v_x_301_; lean_object* v_y_302_; lean_object* v_a_303_; lean_object* v_j_304_; lean_object* v_b_305_; lean_object* v_k_306_; lean_object* v___x_307_; 
v_s_299_ = lean_ctor_get(v_t_283_, 0);
lean_inc_ref(v_s_299_);
v_t_300_ = lean_ctor_get(v_t_283_, 1);
lean_inc_ref(v_t_300_);
v_x_301_ = lean_ctor_get(v_t_283_, 2);
lean_inc(v_x_301_);
v_y_302_ = lean_ctor_get(v_t_283_, 3);
lean_inc(v_y_302_);
v_a_303_ = lean_ctor_get(v_t_283_, 4);
lean_inc(v_a_303_);
v_j_304_ = lean_ctor_get(v_t_283_, 5);
lean_inc_ref(v_j_304_);
v_b_305_ = lean_ctor_get(v_t_283_, 6);
lean_inc(v_b_305_);
v_k_306_ = lean_ctor_get(v_t_283_, 7);
lean_inc_ref(v_k_306_);
lean_dec_ref_known(v_t_283_, 8);
v___x_307_ = lean_apply_8(v_k_284_, v_s_299_, v_t_300_, v_x_301_, v_y_302_, v_a_303_, v_j_304_, v_b_305_, v_k_306_);
return v___x_307_;
}
default: 
{
lean_object* v_m_308_; lean_object* v_r_309_; lean_object* v_i_310_; lean_object* v_x_311_; lean_object* v_j_312_; lean_object* v___x_313_; 
v_m_308_ = lean_ctor_get(v_t_283_, 0);
lean_inc(v_m_308_);
v_r_309_ = lean_ctor_get(v_t_283_, 1);
lean_inc(v_r_309_);
v_i_310_ = lean_ctor_get(v_t_283_, 2);
lean_inc(v_i_310_);
v_x_311_ = lean_ctor_get(v_t_283_, 3);
lean_inc(v_x_311_);
v_j_312_ = lean_ctor_get(v_t_283_, 4);
lean_inc_ref(v_j_312_);
lean_dec_ref_known(v_t_283_, 5);
v___x_313_ = lean_apply_5(v_k_284_, v_m_308_, v_r_309_, v_i_310_, v_x_311_, v_j_312_);
return v___x_313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim(lean_object* v_motive_314_, lean_object* v_ctorIdx_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_t_318_, lean_object* v_h_319_, lean_object* v_k_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_318_, v_k_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim___boxed(lean_object* v_motive_322_, lean_object* v_ctorIdx_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_t_326_, lean_object* v_h_327_, lean_object* v_k_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim(v_motive_322_, v_ctorIdx_323_, v_a_324_, v_a_325_, v_t_326_, v_h_327_, v_k_328_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_ctorIdx_323_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim___redArg(lean_object* v_t_330_, lean_object* v_assumption_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_330_, v_assumption_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim(lean_object* v_motive_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_t_336_, lean_object* v_h_337_, lean_object* v_assumption_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_336_, v_assumption_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim___boxed(lean_object* v_motive_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_t_343_, lean_object* v_h_344_, lean_object* v_assumption_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Elab_Tactic_Omega_Justification_assumption_elim(v_motive_340_, v_a_341_, v_a_342_, v_t_343_, v_h_344_, v_assumption_345_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim___redArg(lean_object* v_t_347_, lean_object* v_tidy_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_347_, v_tidy_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim(lean_object* v_motive_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_t_353_, lean_object* v_h_354_, lean_object* v_tidy_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_353_, v_tidy_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim___boxed(lean_object* v_motive_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_t_360_, lean_object* v_h_361_, lean_object* v_tidy_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_elim(v_motive_357_, v_a_358_, v_a_359_, v_t_360_, v_h_361_, v_tidy_362_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim___redArg(lean_object* v_t_364_, lean_object* v_combine_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_364_, v_combine_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim(lean_object* v_motive_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_t_370_, lean_object* v_h_371_, lean_object* v_combine_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_370_, v_combine_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim___boxed(lean_object* v_motive_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_t_377_, lean_object* v_h_378_, lean_object* v_combine_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Elab_Tactic_Omega_Justification_combine_elim(v_motive_374_, v_a_375_, v_a_376_, v_t_377_, v_h_378_, v_combine_379_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim___redArg(lean_object* v_t_381_, lean_object* v_combo_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_381_, v_combo_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim(lean_object* v_motive_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_combo_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_387_, v_combo_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim___boxed(lean_object* v_motive_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_t_394_, lean_object* v_h_395_, lean_object* v_combo_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Elab_Tactic_Omega_Justification_combo_elim(v_motive_391_, v_a_392_, v_a_393_, v_t_394_, v_h_395_, v_combo_396_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim___redArg(lean_object* v_t_398_, lean_object* v_bmod_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_398_, v_bmod_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim(lean_object* v_motive_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_t_404_, lean_object* v_h_405_, lean_object* v_bmod_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_404_, v_bmod_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim___boxed(lean_object* v_motive_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_t_411_, lean_object* v_h_412_, lean_object* v_bmod_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Elab_Tactic_Omega_Justification_bmod_elim(v_motive_408_, v_a_409_, v_a_410_, v_t_411_, v_h_412_, v_bmod_413_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(lean_object* v_s_415_, lean_object* v_c_416_, lean_object* v_j_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_inc(v_c_416_);
lean_inc_ref(v_s_415_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v_s_415_);
lean_ctor_set(v___x_418_, 1, v_c_416_);
lean_inc_ref(v___x_418_);
v___x_419_ = l_Lean_Omega_tidy_x3f(v___x_418_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v___x_420_; 
lean_dec_ref_known(v___x_418_, 2);
lean_dec_ref(v_j_417_);
lean_dec(v_c_416_);
lean_dec_ref(v_s_415_);
v___x_420_ = lean_box(0);
return v___x_420_;
}
else
{
lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_439_; 
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v___x_419_, 0);
lean_dec(v_unused_440_);
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_439_;
goto v_resetjp_421_;
}
else
{
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_439_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v_fst_425_; lean_object* v_snd_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_438_; 
v___x_424_ = l_Lean_Omega_tidy(v___x_418_);
v_fst_425_ = lean_ctor_get(v___x_424_, 0);
v_snd_426_ = lean_ctor_get(v___x_424_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_438_ == 0)
{
v___x_428_ = v___x_424_;
v_isShared_429_ = v_isSharedCheck_438_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_snd_426_);
lean_inc(v_fst_425_);
lean_dec(v___x_424_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_438_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_430_, 0, v_s_415_);
lean_ctor_set(v___x_430_, 1, v_c_416_);
lean_ctor_set(v___x_430_, 2, v_j_417_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_430_);
lean_ctor_set(v___x_428_, 0, v_snd_426_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_snd_426_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_430_);
v___x_432_ = v_reuseFailAlloc_437_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v_fst_425_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_433_);
v___x_435_ = v___x_422_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(lean_object* v_s_441_, lean_object* v_replacement_442_, lean_object* v_a_443_, lean_object* v_b_444_){
_start:
{
lean_object* v_it_446_; lean_object* v_startPos_447_; lean_object* v_endPos_448_; lean_object* v_it_457_; 
switch(lean_obj_tag(v_a_443_))
{
case 0:
{
lean_object* v_pos_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_475_; 
v_pos_463_ = lean_ctor_get(v_a_443_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_475_ == 0)
{
v___x_465_ = v_a_443_;
v_isShared_466_ = v_isSharedCheck_475_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_pos_463_);
lean_dec(v_a_443_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_475_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v_startInclusive_467_; lean_object* v_endExclusive_468_; lean_object* v___x_469_; uint8_t v_decide_470_; 
v_startInclusive_467_ = lean_ctor_get(v_s_441_, 1);
v_endExclusive_468_ = lean_ctor_get(v_s_441_, 2);
v___x_469_ = lean_nat_sub(v_endExclusive_468_, v_startInclusive_467_);
v_decide_470_ = lean_nat_dec_eq(v_pos_463_, v___x_469_);
lean_dec(v___x_469_);
if (v_decide_470_ == 0)
{
lean_object* v___x_472_; 
if (v_isShared_466_ == 0)
{
lean_ctor_set_tag(v___x_465_, 1);
v___x_472_ = v___x_465_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_pos_463_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
v_it_457_ = v___x_472_;
goto v___jp_456_;
}
}
else
{
lean_object* v___x_474_; 
lean_del_object(v___x_465_);
lean_dec(v_pos_463_);
v___x_474_ = lean_box(3);
v_it_457_ = v___x_474_;
goto v___jp_456_;
}
}
}
case 1:
{
lean_object* v_pos_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_488_; 
v_pos_476_ = lean_ctor_get(v_a_443_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_488_ == 0)
{
v___x_478_ = v_a_443_;
v_isShared_479_ = v_isSharedCheck_488_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_pos_476_);
lean_dec(v_a_443_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_488_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_str_480_; lean_object* v_startInclusive_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v_str_480_ = lean_ctor_get(v_s_441_, 0);
v_startInclusive_481_ = lean_ctor_get(v_s_441_, 1);
v___x_482_ = lean_nat_add(v_startInclusive_481_, v_pos_476_);
v___x_483_ = lean_string_utf8_next_fast(v_str_480_, v___x_482_);
lean_dec(v___x_482_);
v___x_484_ = lean_nat_sub(v___x_483_, v_startInclusive_481_);
lean_inc(v___x_484_);
if (v_isShared_479_ == 0)
{
lean_ctor_set_tag(v___x_478_, 0);
lean_ctor_set(v___x_478_, 0, v___x_484_);
v___x_486_ = v___x_478_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
v_it_446_ = v___x_486_;
v_startPos_447_ = v_pos_476_;
v_endPos_448_ = v___x_484_;
goto v___jp_445_;
}
}
}
case 2:
{
lean_object* v_needle_489_; lean_object* v_table_490_; lean_object* v_stackPos_491_; lean_object* v_needlePos_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_553_; 
v_needle_489_ = lean_ctor_get(v_a_443_, 0);
v_table_490_ = lean_ctor_get(v_a_443_, 1);
v_stackPos_491_ = lean_ctor_get(v_a_443_, 2);
v_needlePos_492_ = lean_ctor_get(v_a_443_, 3);
v_isSharedCheck_553_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_553_ == 0)
{
v___x_494_ = v_a_443_;
v_isShared_495_ = v_isSharedCheck_553_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_needlePos_492_);
lean_inc(v_stackPos_491_);
lean_inc(v_table_490_);
lean_inc(v_needle_489_);
lean_dec(v_a_443_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_553_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v_str_496_; lean_object* v_startInclusive_497_; lean_object* v_endExclusive_498_; lean_object* v_str_499_; lean_object* v_startInclusive_500_; lean_object* v_endExclusive_501_; lean_object* v_basePos_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_str_496_ = lean_ctor_get(v_needle_489_, 0);
v_startInclusive_497_ = lean_ctor_get(v_needle_489_, 1);
v_endExclusive_498_ = lean_ctor_get(v_needle_489_, 2);
v_str_499_ = lean_ctor_get(v_s_441_, 0);
v_startInclusive_500_ = lean_ctor_get(v_s_441_, 1);
v_endExclusive_501_ = lean_ctor_get(v_s_441_, 2);
v_basePos_502_ = lean_nat_sub(v_stackPos_491_, v_needlePos_492_);
v___x_503_ = lean_nat_sub(v_endExclusive_498_, v_startInclusive_497_);
v___x_504_ = lean_nat_add(v_basePos_502_, v___x_503_);
v___x_505_ = lean_nat_sub(v_endExclusive_501_, v_startInclusive_500_);
v___x_506_ = lean_nat_dec_le(v___x_504_, v___x_505_);
lean_dec(v___x_504_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
lean_dec(v___x_503_);
lean_del_object(v___x_494_);
lean_dec(v_needlePos_492_);
lean_dec(v_stackPos_491_);
lean_dec_ref(v_table_490_);
lean_dec_ref(v_needle_489_);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_basePos_502_, v___x_507_);
v___x_509_ = lean_nat_dec_le(v___x_508_, v___x_505_);
lean_dec(v___x_508_);
if (v___x_509_ == 0)
{
lean_dec(v___x_505_);
lean_dec(v_basePos_502_);
lean_dec_ref(v_s_441_);
return v_b_444_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = l_String_Slice_pos_x21(v_s_441_, v_basePos_502_);
lean_dec(v_basePos_502_);
v___x_511_ = lean_box(3);
v_it_446_ = v___x_511_;
v_startPos_447_ = v___x_510_;
v_endPos_448_ = v___x_505_;
goto v___jp_445_;
}
}
else
{
lean_object* v___x_512_; uint8_t v_stackByte_513_; lean_object* v___x_514_; uint8_t v_patByte_515_; uint8_t v___x_516_; 
lean_dec(v___x_505_);
v___x_512_ = lean_nat_add(v_startInclusive_500_, v_stackPos_491_);
v_stackByte_513_ = lean_string_get_byte_fast(v_str_499_, v___x_512_);
v___x_514_ = lean_nat_add(v_startInclusive_497_, v_needlePos_492_);
v_patByte_515_ = lean_string_get_byte_fast(v_str_496_, v___x_514_);
v___x_516_ = lean_uint8_dec_eq(v_stackByte_513_, v_patByte_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; uint8_t v_decide_518_; 
lean_dec(v___x_503_);
v___x_517_ = lean_unsigned_to_nat(0u);
v_decide_518_ = lean_nat_dec_eq(v_needlePos_492_, v___x_517_);
if (v_decide_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v_newNeedlePos_521_; uint8_t v___x_522_; 
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_sub(v_needlePos_492_, v___x_519_);
lean_dec(v_needlePos_492_);
v_newNeedlePos_521_ = lean_array_fget_borrowed(v_table_490_, v___x_520_);
lean_dec(v___x_520_);
v___x_522_ = lean_nat_dec_eq(v_newNeedlePos_521_, v___x_517_);
if (v___x_522_ == 0)
{
lean_object* v_oldBasePos_523_; lean_object* v___x_524_; lean_object* v_newBasePos_525_; lean_object* v___x_527_; 
lean_inc(v_newNeedlePos_521_);
v_oldBasePos_523_ = l_String_Slice_pos_x21(v_s_441_, v_basePos_502_);
lean_dec(v_basePos_502_);
v___x_524_ = lean_nat_sub(v_stackPos_491_, v_newNeedlePos_521_);
v_newBasePos_525_ = l_String_Slice_pos_x21(v_s_441_, v___x_524_);
lean_dec(v___x_524_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 3, v_newNeedlePos_521_);
v___x_527_ = v___x_494_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_needle_489_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_table_490_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_stackPos_491_);
lean_ctor_set(v_reuseFailAlloc_528_, 3, v_newNeedlePos_521_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
v_it_446_ = v___x_527_;
v_startPos_447_ = v_oldBasePos_523_;
v_endPos_448_ = v_newBasePos_525_;
goto v___jp_445_;
}
}
else
{
lean_object* v_basePos_529_; lean_object* v_nextStackPos_530_; lean_object* v___x_532_; 
v_basePos_529_ = l_String_Slice_pos_x21(v_s_441_, v_basePos_502_);
lean_dec(v_basePos_502_);
v_nextStackPos_530_ = l_String_Slice_posGE___redArg(v_s_441_, v_stackPos_491_);
lean_inc(v_nextStackPos_530_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 3, v___x_517_);
lean_ctor_set(v___x_494_, 2, v_nextStackPos_530_);
v___x_532_ = v___x_494_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_needle_489_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_table_490_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v_nextStackPos_530_);
lean_ctor_set(v_reuseFailAlloc_533_, 3, v___x_517_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
v_it_446_ = v___x_532_;
v_startPos_447_ = v_basePos_529_;
v_endPos_448_ = v_nextStackPos_530_;
goto v___jp_445_;
}
}
}
else
{
lean_object* v_basePos_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_nextStackPos_537_; lean_object* v___x_539_; 
lean_dec(v_basePos_502_);
lean_dec(v_needlePos_492_);
v_basePos_534_ = l_String_Slice_pos_x21(v_s_441_, v_stackPos_491_);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_stackPos_491_, v___x_535_);
lean_dec(v_stackPos_491_);
v_nextStackPos_537_ = l_String_Slice_posGE___redArg(v_s_441_, v___x_536_);
lean_inc(v_nextStackPos_537_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 3, v___x_517_);
lean_ctor_set(v___x_494_, 2, v_nextStackPos_537_);
v___x_539_ = v___x_494_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_needle_489_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_table_490_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v_nextStackPos_537_);
lean_ctor_set(v_reuseFailAlloc_540_, 3, v___x_517_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
v_it_446_ = v___x_539_;
v_startPos_447_ = v_basePos_534_;
v_endPos_448_ = v_nextStackPos_537_;
goto v___jp_445_;
}
}
}
else
{
lean_object* v___x_541_; lean_object* v_nextStackPos_542_; lean_object* v_nextNeedlePos_543_; uint8_t v_decide_544_; 
lean_dec(v_basePos_502_);
v___x_541_ = lean_unsigned_to_nat(1u);
v_nextStackPos_542_ = lean_nat_add(v_stackPos_491_, v___x_541_);
lean_dec(v_stackPos_491_);
v_nextNeedlePos_543_ = lean_nat_add(v_needlePos_492_, v___x_541_);
lean_dec(v_needlePos_492_);
v_decide_544_ = lean_nat_dec_eq(v_nextNeedlePos_543_, v___x_503_);
lean_dec(v___x_503_);
if (v_decide_544_ == 0)
{
lean_object* v___x_546_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 3, v_nextNeedlePos_543_);
lean_ctor_set(v___x_494_, 2, v_nextStackPos_542_);
v___x_546_ = v___x_494_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_needle_489_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_table_490_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_nextStackPos_542_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_nextNeedlePos_543_);
v___x_546_ = v_reuseFailAlloc_548_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
v_a_443_ = v___x_546_;
goto _start;
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_551_; 
lean_dec(v_nextNeedlePos_543_);
v___x_549_ = lean_unsigned_to_nat(0u);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 3, v___x_549_);
lean_ctor_set(v___x_494_, 2, v_nextStackPos_542_);
v___x_551_ = v___x_494_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_needle_489_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_table_490_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_nextStackPos_542_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
v_it_457_ = v___x_551_;
goto v___jp_456_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_441_);
return v_b_444_;
}
}
v___jp_445_:
{
lean_object* v___x_449_; lean_object* v_str_450_; lean_object* v_startInclusive_451_; lean_object* v_endExclusive_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc_ref(v_s_441_);
v___x_449_ = l_String_Slice_slice_x21(v_s_441_, v_startPos_447_, v_endPos_448_);
lean_dec(v_endPos_448_);
lean_dec(v_startPos_447_);
v_str_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc_ref(v_str_450_);
v_startInclusive_451_ = lean_ctor_get(v___x_449_, 1);
lean_inc(v_startInclusive_451_);
v_endExclusive_452_ = lean_ctor_get(v___x_449_, 2);
lean_inc(v_endExclusive_452_);
lean_dec_ref(v___x_449_);
v___x_453_ = lean_string_utf8_extract_fast(v_str_450_, v_startInclusive_451_, v_endExclusive_452_);
lean_dec(v_endExclusive_452_);
lean_dec(v_startInclusive_451_);
lean_dec_ref(v_str_450_);
v___x_454_ = lean_string_append(v_b_444_, v___x_453_);
lean_dec_ref(v___x_453_);
v_a_443_ = v_it_446_;
v_b_444_ = v___x_454_;
goto _start;
}
v___jp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_string_utf8_byte_size(v_replacement_442_);
v___x_460_ = lean_string_utf8_extract_fast(v_replacement_442_, v___x_458_, v___x_459_);
v___x_461_ = lean_string_append(v_b_444_, v___x_460_);
lean_dec_ref(v___x_460_);
v_a_443_ = v_it_457_;
v_b_444_ = v___x_461_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg___boxed(lean_object* v_s_554_, lean_object* v_replacement_555_, lean_object* v_a_556_, lean_object* v_b_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_554_, v_replacement_555_, v_a_556_, v_b_557_);
lean_dec_ref(v_replacement_555_);
return v_res_558_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2));
v___x_566_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3);
v___x_569_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2));
v___x_570_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
lean_ctor_set(v___x_570_, 2, v___x_567_);
lean_ctor_set(v___x_570_, 3, v___x_567_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(lean_object* v_s_571_, lean_object* v_replacement_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_574_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4);
v___x_575_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_571_, v_replacement_572_, v___x_574_, v___x_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___boxed(lean_object* v_s_576_, lean_object* v_replacement_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v_s_576_, v_replacement_577_);
lean_dec_ref(v_replacement_577_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(lean_object* v_s_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_582_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__0));
v___x_583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__1));
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_string_utf8_byte_size(v_s_581_);
v___x_586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_586_, 0, v_s_581_);
lean_ctor_set(v___x_586_, 1, v___x_584_);
lean_ctor_set(v___x_586_, 2, v___x_585_);
v___x_587_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v___x_586_, v___x_583_);
v___x_588_ = lean_string_append(v___x_582_, v___x_587_);
lean_dec_ref(v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0(lean_object* v_s_589_, lean_object* v_pattern_590_, lean_object* v_replacement_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v_s_589_, v_replacement_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___boxed(lean_object* v_s_593_, lean_object* v_pattern_594_, lean_object* v_replacement_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0(v_s_593_, v_pattern_594_, v_replacement_595_);
lean_dec_ref(v_replacement_595_);
lean_dec_ref(v_pattern_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0(lean_object* v_s_597_, lean_object* v_replacement_598_, lean_object* v_inst_599_, lean_object* v_R_600_, lean_object* v_a_601_, lean_object* v_b_602_, lean_object* v_c_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_597_, v_replacement_598_, v_a_601_, v_b_602_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___boxed(lean_object* v_s_605_, lean_object* v_replacement_606_, lean_object* v_inst_607_, lean_object* v_R_608_, lean_object* v_a_609_, lean_object* v_b_610_, lean_object* v_c_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0(v_s_605_, v_replacement_606_, v_inst_607_, v_R_608_, v_a_609_, v_b_610_, v_c_611_);
lean_dec_ref(v_replacement_606_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
return v_x_614_;
}
else
{
lean_object* v_head_616_; lean_object* v_tail_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_head_616_ = lean_ctor_get(v_x_615_, 0);
v_tail_617_ = lean_ctor_get(v_x_615_, 1);
v___x_618_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_619_ = lean_string_append(v_x_614_, v___x_618_);
v___x_620_ = l_Int_repr(v_head_616_);
v___x_621_ = lean_string_append(v___x_619_, v___x_620_);
lean_dec_ref(v___x_620_);
v_x_614_ = v___x_621_;
v_x_615_ = v_tail_617_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___boxed(lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v_x_623_, v_x_624_);
lean_dec(v_x_624_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(lean_object* v_x_629_){
_start:
{
if (lean_obj_tag(v_x_629_) == 0)
{
lean_object* v___x_630_; 
v___x_630_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__0));
return v___x_630_;
}
else
{
lean_object* v_tail_631_; 
v_tail_631_ = lean_ctor_get(v_x_629_, 1);
if (lean_obj_tag(v_tail_631_) == 0)
{
lean_object* v_head_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_head_632_ = lean_ctor_get(v_x_629_, 0);
v___x_633_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v___x_634_ = l_Int_repr(v_head_632_);
v___x_635_ = lean_string_append(v___x_633_, v___x_634_);
lean_dec_ref(v___x_634_);
v___x_636_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_637_ = lean_string_append(v___x_635_, v___x_636_);
return v___x_637_;
}
else
{
lean_object* v_head_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint32_t v___x_643_; lean_object* v___x_644_; 
v_head_638_ = lean_ctor_get(v_x_629_, 0);
v___x_639_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v___x_640_ = l_Int_repr(v_head_638_);
v___x_641_ = lean_string_append(v___x_639_, v___x_640_);
lean_dec_ref(v___x_640_);
v___x_642_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v___x_641_, v_tail_631_);
v___x_643_ = 93;
v___x_644_ = lean_string_push(v___x_642_, v___x_643_);
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___boxed(lean_object* v_x_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_645_);
lean_dec(v_x_645_);
return v_res_646_;
}
}
uint8_t l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
if (lean_obj_tag(v_x_647_) == 0)
{
if (lean_obj_tag(v_x_648_) == 0)
{
uint8_t v___x_649_; 
v___x_649_ = 1;
return v___x_649_;
}
else
{
uint8_t v___x_650_; 
v___x_650_ = 0;
return v___x_650_;
}
}
else
{
if (lean_obj_tag(v_x_648_) == 0)
{
uint8_t v___x_651_; 
v___x_651_ = 0;
return v___x_651_;
}
else
{
lean_object* v_head_652_; lean_object* v_tail_653_; lean_object* v_head_654_; lean_object* v_tail_655_; uint8_t v___x_656_; 
v_head_652_ = lean_ctor_get(v_x_647_, 0);
v_tail_653_ = lean_ctor_get(v_x_647_, 1);
v_head_654_ = lean_ctor_get(v_x_648_, 0);
v_tail_655_ = lean_ctor_get(v_x_648_, 1);
v___x_656_ = lean_int_dec_eq(v_head_652_, v_head_654_);
if (v___x_656_ == 0)
{
return v___x_656_;
}
else
{
v_x_647_ = v_tail_653_;
v_x_648_ = v_tail_655_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_647_ = stack[0].m_obj;
lean_object* v_x_648_ = stack[1].m_obj;
uint8_t v_res_658_;
v_res_658_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_647_, v_x_648_);
stack->m_num = v_res_658_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1___boxed(lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
uint8_t v_res_661_; lean_object* v_r_662_; 
v_res_661_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_659_, v_x_660_);
lean_dec(v_x_660_);
lean_dec(v_x_659_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString(lean_object* v_s_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
switch(lean_obj_tag(v_x_682_))
{
case 0:
{
lean_object* v_i_683_; lean_object* v_lowerBound_684_; lean_object* v_upperBound_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___y_690_; lean_object* v___y_697_; lean_object* v___y_698_; 
v_i_683_ = lean_ctor_get(v_x_682_, 2);
lean_inc(v_i_683_);
lean_dec_ref_known(v_x_682_, 3);
v_lowerBound_684_ = lean_ctor_get(v_s_680_, 0);
lean_inc(v_lowerBound_684_);
v_upperBound_685_ = lean_ctor_get(v_s_680_, 1);
lean_inc(v_upperBound_685_);
lean_dec_ref(v_s_680_);
v___x_686_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_681_);
lean_dec(v_x_681_);
v___x_687_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_688_ = lean_string_append(v___x_686_, v___x_687_);
if (lean_obj_tag(v_lowerBound_684_) == 0)
{
if (lean_obj_tag(v_upperBound_685_) == 0)
{
lean_object* v___x_702_; 
v___x_702_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_690_ = v___x_702_;
goto v___jp_689_;
}
else
{
lean_object* v_val_703_; lean_object* v___x_704_; lean_object* v___y_706_; lean_object* v_intZero_710_; uint8_t v_isNeg_711_; 
v_val_703_ = lean_ctor_get(v_upperBound_685_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v_upperBound_685_, 1);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_710_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_711_ = lean_int_dec_lt(v_val_703_, v_intZero_710_);
if (v_isNeg_711_ == 0)
{
lean_object* v_a_712_; lean_object* v___x_713_; 
v_a_712_ = lean_nat_abs(v_val_703_);
lean_dec(v_val_703_);
v___x_713_ = l_Nat_reprFast(v_a_712_);
v___y_706_ = v___x_713_;
goto v___jp_705_;
}
else
{
lean_object* v_abs_714_; lean_object* v_one_715_; lean_object* v_a_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_abs_714_ = lean_nat_abs(v_val_703_);
lean_dec(v_val_703_);
v_one_715_ = lean_unsigned_to_nat(1u);
v_a_716_ = lean_nat_sub(v_abs_714_, v_one_715_);
lean_dec(v_abs_714_);
v___x_717_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_718_ = lean_nat_add(v_a_716_, v_one_715_);
lean_dec(v_a_716_);
v___x_719_ = l_Nat_reprFast(v___x_718_);
v___x_720_ = lean_string_append(v___x_717_, v___x_719_);
lean_dec_ref(v___x_719_);
v___y_706_ = v___x_720_;
goto v___jp_705_;
}
v___jp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_string_append(v___x_704_, v___y_706_);
lean_dec_ref(v___y_706_);
v___x_708_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_709_ = lean_string_append(v___x_707_, v___x_708_);
v___y_690_ = v___x_709_;
goto v___jp_689_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_685_) == 0)
{
lean_object* v_val_721_; lean_object* v___x_722_; lean_object* v___y_724_; lean_object* v_intZero_728_; uint8_t v_isNeg_729_; 
v_val_721_ = lean_ctor_get(v_lowerBound_684_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v_lowerBound_684_, 1);
v___x_722_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_728_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_729_ = lean_int_dec_lt(v_val_721_, v_intZero_728_);
if (v_isNeg_729_ == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; 
v_a_730_ = lean_nat_abs(v_val_721_);
lean_dec(v_val_721_);
v___x_731_ = l_Nat_reprFast(v_a_730_);
v___y_724_ = v___x_731_;
goto v___jp_723_;
}
else
{
lean_object* v_abs_732_; lean_object* v_one_733_; lean_object* v_a_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_abs_732_ = lean_nat_abs(v_val_721_);
lean_dec(v_val_721_);
v_one_733_ = lean_unsigned_to_nat(1u);
v_a_734_ = lean_nat_sub(v_abs_732_, v_one_733_);
lean_dec(v_abs_732_);
v___x_735_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_736_ = lean_nat_add(v_a_734_, v_one_733_);
lean_dec(v_a_734_);
v___x_737_ = l_Nat_reprFast(v___x_736_);
v___x_738_ = lean_string_append(v___x_735_, v___x_737_);
lean_dec_ref(v___x_737_);
v___y_724_ = v___x_738_;
goto v___jp_723_;
}
v___jp_723_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_string_append(v___x_722_, v___y_724_);
lean_dec_ref(v___y_724_);
v___x_726_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_727_ = lean_string_append(v___x_725_, v___x_726_);
v___y_690_ = v___x_727_;
goto v___jp_689_;
}
}
else
{
lean_object* v_val_739_; lean_object* v_val_740_; uint8_t v___x_741_; 
v_val_739_ = lean_ctor_get(v_lowerBound_684_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v_lowerBound_684_, 1);
v_val_740_ = lean_ctor_get(v_upperBound_685_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v_upperBound_685_, 1);
v___x_741_ = lean_int_dec_lt(v_val_740_, v_val_739_);
if (v___x_741_ == 0)
{
uint8_t v___x_742_; 
v___x_742_ = lean_int_dec_eq(v_val_739_, v_val_740_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___y_745_; lean_object* v_intZero_760_; uint8_t v_isNeg_761_; 
v___x_743_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_760_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_761_ = lean_int_dec_lt(v_val_739_, v_intZero_760_);
if (v_isNeg_761_ == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_762_ = lean_nat_abs(v_val_739_);
lean_dec(v_val_739_);
v___x_763_ = l_Nat_reprFast(v_a_762_);
v___y_745_ = v___x_763_;
goto v___jp_744_;
}
else
{
lean_object* v_abs_764_; lean_object* v_one_765_; lean_object* v_a_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_abs_764_ = lean_nat_abs(v_val_739_);
lean_dec(v_val_739_);
v_one_765_ = lean_unsigned_to_nat(1u);
v_a_766_ = lean_nat_sub(v_abs_764_, v_one_765_);
lean_dec(v_abs_764_);
v___x_767_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_768_ = lean_nat_add(v_a_766_, v_one_765_);
lean_dec(v_a_766_);
v___x_769_ = l_Nat_reprFast(v___x_768_);
v___x_770_ = lean_string_append(v___x_767_, v___x_769_);
lean_dec_ref(v___x_769_);
v___y_745_ = v___x_770_;
goto v___jp_744_;
}
v___jp_744_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_intZero_749_; uint8_t v_isNeg_750_; 
v___x_746_ = lean_string_append(v___x_743_, v___y_745_);
lean_dec_ref(v___y_745_);
v___x_747_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_748_ = lean_string_append(v___x_746_, v___x_747_);
v_intZero_749_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_750_ = lean_int_dec_lt(v_val_740_, v_intZero_749_);
if (v_isNeg_750_ == 0)
{
lean_object* v_a_751_; lean_object* v___x_752_; 
v_a_751_ = lean_nat_abs(v_val_740_);
lean_dec(v_val_740_);
v___x_752_ = l_Nat_reprFast(v_a_751_);
v___y_697_ = v___x_748_;
v___y_698_ = v___x_752_;
goto v___jp_696_;
}
else
{
lean_object* v_abs_753_; lean_object* v_one_754_; lean_object* v_a_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_abs_753_ = lean_nat_abs(v_val_740_);
lean_dec(v_val_740_);
v_one_754_ = lean_unsigned_to_nat(1u);
v_a_755_ = lean_nat_sub(v_abs_753_, v_one_754_);
lean_dec(v_abs_753_);
v___x_756_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_757_ = lean_nat_add(v_a_755_, v_one_754_);
lean_dec(v_a_755_);
v___x_758_ = l_Nat_reprFast(v___x_757_);
v___x_759_ = lean_string_append(v___x_756_, v___x_758_);
lean_dec_ref(v___x_758_);
v___y_697_ = v___x_748_;
v___y_698_ = v___x_759_;
goto v___jp_696_;
}
}
}
else
{
lean_object* v___x_771_; lean_object* v___y_773_; lean_object* v_intZero_777_; uint8_t v_isNeg_778_; 
lean_dec(v_val_740_);
v___x_771_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_777_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_778_ = lean_int_dec_lt(v_val_739_, v_intZero_777_);
if (v_isNeg_778_ == 0)
{
lean_object* v_a_779_; lean_object* v___x_780_; 
v_a_779_ = lean_nat_abs(v_val_739_);
lean_dec(v_val_739_);
v___x_780_ = l_Nat_reprFast(v_a_779_);
v___y_773_ = v___x_780_;
goto v___jp_772_;
}
else
{
lean_object* v_abs_781_; lean_object* v_one_782_; lean_object* v_a_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_abs_781_ = lean_nat_abs(v_val_739_);
lean_dec(v_val_739_);
v_one_782_ = lean_unsigned_to_nat(1u);
v_a_783_ = lean_nat_sub(v_abs_781_, v_one_782_);
lean_dec(v_abs_781_);
v___x_784_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_785_ = lean_nat_add(v_a_783_, v_one_782_);
lean_dec(v_a_783_);
v___x_786_ = l_Nat_reprFast(v___x_785_);
v___x_787_ = lean_string_append(v___x_784_, v___x_786_);
lean_dec_ref(v___x_786_);
v___y_773_ = v___x_787_;
goto v___jp_772_;
}
v___jp_772_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_string_append(v___x_771_, v___y_773_);
lean_dec_ref(v___y_773_);
v___x_775_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_776_ = lean_string_append(v___x_774_, v___x_775_);
v___y_690_ = v___x_776_;
goto v___jp_689_;
}
}
}
else
{
lean_object* v___x_788_; 
lean_dec(v_val_740_);
lean_dec(v_val_739_);
v___x_788_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_690_ = v___x_788_;
goto v___jp_689_;
}
}
}
v___jp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_691_ = lean_string_append(v___x_688_, v___y_690_);
lean_dec_ref(v___y_690_);
v___x_692_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__1));
v___x_693_ = lean_string_append(v___x_691_, v___x_692_);
v___x_694_ = l_Nat_reprFast(v_i_683_);
v___x_695_ = lean_string_append(v___x_693_, v___x_694_);
lean_dec_ref(v___x_694_);
return v___x_695_;
}
v___jp_696_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_string_append(v___y_697_, v___y_698_);
lean_dec_ref(v___y_698_);
v___x_700_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_701_ = lean_string_append(v___x_699_, v___x_700_);
v___y_690_ = v___x_701_;
goto v___jp_689_;
}
}
case 1:
{
lean_object* v_s_789_; lean_object* v_c_790_; lean_object* v_j_791_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; uint8_t v___y_849_; uint8_t v___x_912_; 
v_s_789_ = lean_ctor_get(v_x_682_, 0);
lean_inc_ref(v_s_789_);
v_c_790_ = lean_ctor_get(v_x_682_, 1);
lean_inc(v_c_790_);
v_j_791_ = lean_ctor_get(v_x_682_, 2);
lean_inc_ref(v_j_791_);
lean_dec_ref_known(v_x_682_, 3);
v___x_912_ = l_Lean_Omega_instBEqConstraint_beq(v_s_680_, v_s_789_);
if (v___x_912_ == 0)
{
v___y_849_ = v___x_912_;
goto v___jp_848_;
}
else
{
uint8_t v___x_913_; 
v___x_913_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_681_, v_c_790_);
v___y_849_ = v___x_913_;
goto v___jp_848_;
}
v___jp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_795_ = lean_string_append(v___y_793_, v___y_794_);
lean_dec_ref(v___y_794_);
v___x_796_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9));
v___x_797_ = lean_string_append(v___x_795_, v___x_796_);
v___x_798_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_789_, v_c_790_, v_j_791_);
v___x_799_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_798_);
v___x_800_ = lean_string_append(v___x_797_, v___x_799_);
lean_dec_ref(v___x_799_);
return v___x_800_;
}
v___jp_801_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_inc_ref(v___y_802_);
v___x_805_ = lean_string_append(v___y_802_, v___y_804_);
lean_dec_ref(v___y_804_);
v___x_806_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_807_ = lean_string_append(v___x_805_, v___x_806_);
v___y_793_ = v___y_803_;
v___y_794_ = v___x_807_;
goto v___jp_792_;
}
v___jp_808_:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_inc_ref(v___y_810_);
v___x_812_ = lean_string_append(v___y_810_, v___y_811_);
lean_dec_ref(v___y_811_);
v___x_813_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_814_ = lean_string_append(v___x_812_, v___x_813_);
v___y_793_ = v___y_809_;
v___y_794_ = v___x_814_;
goto v___jp_792_;
}
v___jp_815_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = lean_string_append(v___y_816_, v___y_818_);
lean_dec_ref(v___y_818_);
v___x_820_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_821_ = lean_string_append(v___x_819_, v___x_820_);
v___y_793_ = v___y_817_;
v___y_794_ = v___x_821_;
goto v___jp_792_;
}
v___jp_822_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_intZero_830_; uint8_t v_isNeg_831_; 
lean_inc_ref(v___y_823_);
v___x_827_ = lean_string_append(v___y_823_, v___y_826_);
lean_dec_ref(v___y_826_);
v___x_828_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_829_ = lean_string_append(v___x_827_, v___x_828_);
v_intZero_830_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_831_ = lean_int_dec_lt(v___y_824_, v_intZero_830_);
if (v_isNeg_831_ == 0)
{
lean_object* v_a_832_; lean_object* v___x_833_; 
v_a_832_ = lean_nat_abs(v___y_824_);
lean_dec(v___y_824_);
v___x_833_ = l_Nat_reprFast(v_a_832_);
v___y_816_ = v___x_829_;
v___y_817_ = v___y_825_;
v___y_818_ = v___x_833_;
goto v___jp_815_;
}
else
{
lean_object* v_abs_834_; lean_object* v_one_835_; lean_object* v_a_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_abs_834_ = lean_nat_abs(v___y_824_);
lean_dec(v___y_824_);
v_one_835_ = lean_unsigned_to_nat(1u);
v_a_836_ = lean_nat_sub(v_abs_834_, v_one_835_);
lean_dec(v_abs_834_);
v___x_837_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_838_ = lean_nat_add(v_a_836_, v_one_835_);
lean_dec(v_a_836_);
v___x_839_ = l_Nat_reprFast(v___x_838_);
v___x_840_ = lean_string_append(v___x_837_, v___x_839_);
lean_dec_ref(v___x_839_);
v___y_816_ = v___x_829_;
v___y_817_ = v___y_825_;
v___y_818_ = v___x_840_;
goto v___jp_815_;
}
}
v___jp_841_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_inc_ref(v___y_842_);
v___x_845_ = lean_string_append(v___y_842_, v___y_844_);
lean_dec_ref(v___y_844_);
v___x_846_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_847_ = lean_string_append(v___x_845_, v___x_846_);
v___y_793_ = v___y_843_;
v___y_794_ = v___x_847_;
goto v___jp_792_;
}
v___jp_848_:
{
if (v___y_849_ == 0)
{
lean_object* v_lowerBound_850_; lean_object* v_upperBound_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_lowerBound_850_ = lean_ctor_get(v_s_680_, 0);
lean_inc(v_lowerBound_850_);
v_upperBound_851_ = lean_ctor_get(v_s_680_, 1);
lean_inc(v_upperBound_851_);
lean_dec_ref(v_s_680_);
v___x_852_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_681_);
lean_dec(v_x_681_);
v___x_853_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_854_ = lean_string_append(v___x_852_, v___x_853_);
if (lean_obj_tag(v_lowerBound_850_) == 0)
{
if (lean_obj_tag(v_upperBound_851_) == 0)
{
lean_object* v___x_855_; 
v___x_855_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_793_ = v___x_854_;
v___y_794_ = v___x_855_;
goto v___jp_792_;
}
else
{
lean_object* v_val_856_; lean_object* v___x_857_; lean_object* v_intZero_858_; uint8_t v_isNeg_859_; 
v_val_856_ = lean_ctor_get(v_upperBound_851_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v_upperBound_851_, 1);
v___x_857_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_858_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_859_ = lean_int_dec_lt(v_val_856_, v_intZero_858_);
if (v_isNeg_859_ == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; 
v_a_860_ = lean_nat_abs(v_val_856_);
lean_dec(v_val_856_);
v___x_861_ = l_Nat_reprFast(v_a_860_);
v___y_802_ = v___x_857_;
v___y_803_ = v___x_854_;
v___y_804_ = v___x_861_;
goto v___jp_801_;
}
else
{
lean_object* v_abs_862_; lean_object* v_one_863_; lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_abs_862_ = lean_nat_abs(v_val_856_);
lean_dec(v_val_856_);
v_one_863_ = lean_unsigned_to_nat(1u);
v_a_864_ = lean_nat_sub(v_abs_862_, v_one_863_);
lean_dec(v_abs_862_);
v___x_865_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_866_ = lean_nat_add(v_a_864_, v_one_863_);
lean_dec(v_a_864_);
v___x_867_ = l_Nat_reprFast(v___x_866_);
v___x_868_ = lean_string_append(v___x_865_, v___x_867_);
lean_dec_ref(v___x_867_);
v___y_802_ = v___x_857_;
v___y_803_ = v___x_854_;
v___y_804_ = v___x_868_;
goto v___jp_801_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_851_) == 0)
{
lean_object* v_val_869_; lean_object* v___x_870_; lean_object* v_intZero_871_; uint8_t v_isNeg_872_; 
v_val_869_ = lean_ctor_get(v_lowerBound_850_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v_lowerBound_850_, 1);
v___x_870_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_871_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_872_ = lean_int_dec_lt(v_val_869_, v_intZero_871_);
if (v_isNeg_872_ == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; 
v_a_873_ = lean_nat_abs(v_val_869_);
lean_dec(v_val_869_);
v___x_874_ = l_Nat_reprFast(v_a_873_);
v___y_809_ = v___x_854_;
v___y_810_ = v___x_870_;
v___y_811_ = v___x_874_;
goto v___jp_808_;
}
else
{
lean_object* v_abs_875_; lean_object* v_one_876_; lean_object* v_a_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_abs_875_ = lean_nat_abs(v_val_869_);
lean_dec(v_val_869_);
v_one_876_ = lean_unsigned_to_nat(1u);
v_a_877_ = lean_nat_sub(v_abs_875_, v_one_876_);
lean_dec(v_abs_875_);
v___x_878_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_879_ = lean_nat_add(v_a_877_, v_one_876_);
lean_dec(v_a_877_);
v___x_880_ = l_Nat_reprFast(v___x_879_);
v___x_881_ = lean_string_append(v___x_878_, v___x_880_);
lean_dec_ref(v___x_880_);
v___y_809_ = v___x_854_;
v___y_810_ = v___x_870_;
v___y_811_ = v___x_881_;
goto v___jp_808_;
}
}
else
{
lean_object* v_val_882_; lean_object* v_val_883_; uint8_t v___x_884_; 
v_val_882_ = lean_ctor_get(v_lowerBound_850_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v_lowerBound_850_, 1);
v_val_883_ = lean_ctor_get(v_upperBound_851_, 0);
lean_inc(v_val_883_);
lean_dec_ref_known(v_upperBound_851_, 1);
v___x_884_ = lean_int_dec_lt(v_val_883_, v_val_882_);
if (v___x_884_ == 0)
{
uint8_t v___x_885_; 
v___x_885_ = lean_int_dec_eq(v_val_882_, v_val_883_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v_intZero_887_; uint8_t v_isNeg_888_; 
v___x_886_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_887_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_888_ = lean_int_dec_lt(v_val_882_, v_intZero_887_);
if (v_isNeg_888_ == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; 
v_a_889_ = lean_nat_abs(v_val_882_);
lean_dec(v_val_882_);
v___x_890_ = l_Nat_reprFast(v_a_889_);
v___y_823_ = v___x_886_;
v___y_824_ = v_val_883_;
v___y_825_ = v___x_854_;
v___y_826_ = v___x_890_;
goto v___jp_822_;
}
else
{
lean_object* v_abs_891_; lean_object* v_one_892_; lean_object* v_a_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_abs_891_ = lean_nat_abs(v_val_882_);
lean_dec(v_val_882_);
v_one_892_ = lean_unsigned_to_nat(1u);
v_a_893_ = lean_nat_sub(v_abs_891_, v_one_892_);
lean_dec(v_abs_891_);
v___x_894_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_895_ = lean_nat_add(v_a_893_, v_one_892_);
lean_dec(v_a_893_);
v___x_896_ = l_Nat_reprFast(v___x_895_);
v___x_897_ = lean_string_append(v___x_894_, v___x_896_);
lean_dec_ref(v___x_896_);
v___y_823_ = v___x_886_;
v___y_824_ = v_val_883_;
v___y_825_ = v___x_854_;
v___y_826_ = v___x_897_;
goto v___jp_822_;
}
}
else
{
lean_object* v___x_898_; lean_object* v_intZero_899_; uint8_t v_isNeg_900_; 
lean_dec(v_val_883_);
v___x_898_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_899_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_900_ = lean_int_dec_lt(v_val_882_, v_intZero_899_);
if (v_isNeg_900_ == 0)
{
lean_object* v_a_901_; lean_object* v___x_902_; 
v_a_901_ = lean_nat_abs(v_val_882_);
lean_dec(v_val_882_);
v___x_902_ = l_Nat_reprFast(v_a_901_);
v___y_842_ = v___x_898_;
v___y_843_ = v___x_854_;
v___y_844_ = v___x_902_;
goto v___jp_841_;
}
else
{
lean_object* v_abs_903_; lean_object* v_one_904_; lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_abs_903_ = lean_nat_abs(v_val_882_);
lean_dec(v_val_882_);
v_one_904_ = lean_unsigned_to_nat(1u);
v_a_905_ = lean_nat_sub(v_abs_903_, v_one_904_);
lean_dec(v_abs_903_);
v___x_906_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_907_ = lean_nat_add(v_a_905_, v_one_904_);
lean_dec(v_a_905_);
v___x_908_ = l_Nat_reprFast(v___x_907_);
v___x_909_ = lean_string_append(v___x_906_, v___x_908_);
lean_dec_ref(v___x_908_);
v___y_842_ = v___x_898_;
v___y_843_ = v___x_854_;
v___y_844_ = v___x_909_;
goto v___jp_841_;
}
}
}
else
{
lean_object* v___x_910_; 
lean_dec(v_val_883_);
lean_dec(v_val_882_);
v___x_910_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_793_ = v___x_854_;
v___y_794_ = v___x_910_;
goto v___jp_792_;
}
}
}
}
else
{
lean_dec(v_x_681_);
lean_dec_ref(v_s_680_);
v_s_680_ = v_s_789_;
v_x_681_ = v_c_790_;
v_x_682_ = v_j_791_;
goto _start;
}
}
}
case 2:
{
lean_object* v_s_914_; lean_object* v_t_915_; lean_object* v_j_916_; lean_object* v_k_917_; lean_object* v_lowerBound_918_; lean_object* v_upperBound_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___y_924_; lean_object* v___y_937_; lean_object* v___y_938_; 
v_s_914_ = lean_ctor_get(v_x_682_, 0);
lean_inc_ref(v_s_914_);
v_t_915_ = lean_ctor_get(v_x_682_, 1);
lean_inc_ref(v_t_915_);
v_j_916_ = lean_ctor_get(v_x_682_, 3);
lean_inc_ref(v_j_916_);
v_k_917_ = lean_ctor_get(v_x_682_, 4);
lean_inc_ref(v_k_917_);
lean_dec_ref_known(v_x_682_, 5);
v_lowerBound_918_ = lean_ctor_get(v_s_680_, 0);
lean_inc(v_lowerBound_918_);
v_upperBound_919_ = lean_ctor_get(v_s_680_, 1);
lean_inc(v_upperBound_919_);
lean_dec_ref(v_s_680_);
v___x_920_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_681_);
v___x_921_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_922_ = lean_string_append(v___x_920_, v___x_921_);
if (lean_obj_tag(v_lowerBound_918_) == 0)
{
if (lean_obj_tag(v_upperBound_919_) == 0)
{
lean_object* v___x_942_; 
v___x_942_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_924_ = v___x_942_;
goto v___jp_923_;
}
else
{
lean_object* v_val_943_; lean_object* v___x_944_; lean_object* v___y_946_; lean_object* v_intZero_950_; uint8_t v_isNeg_951_; 
v_val_943_ = lean_ctor_get(v_upperBound_919_, 0);
lean_inc(v_val_943_);
lean_dec_ref_known(v_upperBound_919_, 1);
v___x_944_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_950_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_951_ = lean_int_dec_lt(v_val_943_, v_intZero_950_);
if (v_isNeg_951_ == 0)
{
lean_object* v_a_952_; lean_object* v___x_953_; 
v_a_952_ = lean_nat_abs(v_val_943_);
lean_dec(v_val_943_);
v___x_953_ = l_Nat_reprFast(v_a_952_);
v___y_946_ = v___x_953_;
goto v___jp_945_;
}
else
{
lean_object* v_abs_954_; lean_object* v_one_955_; lean_object* v_a_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_abs_954_ = lean_nat_abs(v_val_943_);
lean_dec(v_val_943_);
v_one_955_ = lean_unsigned_to_nat(1u);
v_a_956_ = lean_nat_sub(v_abs_954_, v_one_955_);
lean_dec(v_abs_954_);
v___x_957_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_958_ = lean_nat_add(v_a_956_, v_one_955_);
lean_dec(v_a_956_);
v___x_959_ = l_Nat_reprFast(v___x_958_);
v___x_960_ = lean_string_append(v___x_957_, v___x_959_);
lean_dec_ref(v___x_959_);
v___y_946_ = v___x_960_;
goto v___jp_945_;
}
v___jp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = lean_string_append(v___x_944_, v___y_946_);
lean_dec_ref(v___y_946_);
v___x_948_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_949_ = lean_string_append(v___x_947_, v___x_948_);
v___y_924_ = v___x_949_;
goto v___jp_923_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_919_) == 0)
{
lean_object* v_val_961_; lean_object* v___x_962_; lean_object* v___y_964_; lean_object* v_intZero_968_; uint8_t v_isNeg_969_; 
v_val_961_ = lean_ctor_get(v_lowerBound_918_, 0);
lean_inc(v_val_961_);
lean_dec_ref_known(v_lowerBound_918_, 1);
v___x_962_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_968_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_969_ = lean_int_dec_lt(v_val_961_, v_intZero_968_);
if (v_isNeg_969_ == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; 
v_a_970_ = lean_nat_abs(v_val_961_);
lean_dec(v_val_961_);
v___x_971_ = l_Nat_reprFast(v_a_970_);
v___y_964_ = v___x_971_;
goto v___jp_963_;
}
else
{
lean_object* v_abs_972_; lean_object* v_one_973_; lean_object* v_a_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_abs_972_ = lean_nat_abs(v_val_961_);
lean_dec(v_val_961_);
v_one_973_ = lean_unsigned_to_nat(1u);
v_a_974_ = lean_nat_sub(v_abs_972_, v_one_973_);
lean_dec(v_abs_972_);
v___x_975_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_976_ = lean_nat_add(v_a_974_, v_one_973_);
lean_dec(v_a_974_);
v___x_977_ = l_Nat_reprFast(v___x_976_);
v___x_978_ = lean_string_append(v___x_975_, v___x_977_);
lean_dec_ref(v___x_977_);
v___y_964_ = v___x_978_;
goto v___jp_963_;
}
v___jp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_string_append(v___x_962_, v___y_964_);
lean_dec_ref(v___y_964_);
v___x_966_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_967_ = lean_string_append(v___x_965_, v___x_966_);
v___y_924_ = v___x_967_;
goto v___jp_923_;
}
}
else
{
lean_object* v_val_979_; lean_object* v_val_980_; uint8_t v___x_981_; 
v_val_979_ = lean_ctor_get(v_lowerBound_918_, 0);
lean_inc(v_val_979_);
lean_dec_ref_known(v_lowerBound_918_, 1);
v_val_980_ = lean_ctor_get(v_upperBound_919_, 0);
lean_inc(v_val_980_);
lean_dec_ref_known(v_upperBound_919_, 1);
v___x_981_ = lean_int_dec_lt(v_val_980_, v_val_979_);
if (v___x_981_ == 0)
{
uint8_t v___x_982_; 
v___x_982_ = lean_int_dec_eq(v_val_979_, v_val_980_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___y_985_; lean_object* v_intZero_1000_; uint8_t v_isNeg_1001_; 
v___x_983_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1000_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1001_ = lean_int_dec_lt(v_val_979_, v_intZero_1000_);
if (v_isNeg_1001_ == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_nat_abs(v_val_979_);
lean_dec(v_val_979_);
v___x_1003_ = l_Nat_reprFast(v_a_1002_);
v___y_985_ = v___x_1003_;
goto v___jp_984_;
}
else
{
lean_object* v_abs_1004_; lean_object* v_one_1005_; lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_abs_1004_ = lean_nat_abs(v_val_979_);
lean_dec(v_val_979_);
v_one_1005_ = lean_unsigned_to_nat(1u);
v_a_1006_ = lean_nat_sub(v_abs_1004_, v_one_1005_);
lean_dec(v_abs_1004_);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1008_ = lean_nat_add(v_a_1006_, v_one_1005_);
lean_dec(v_a_1006_);
v___x_1009_ = l_Nat_reprFast(v___x_1008_);
v___x_1010_ = lean_string_append(v___x_1007_, v___x_1009_);
lean_dec_ref(v___x_1009_);
v___y_985_ = v___x_1010_;
goto v___jp_984_;
}
v___jp_984_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_intZero_989_; uint8_t v_isNeg_990_; 
v___x_986_ = lean_string_append(v___x_983_, v___y_985_);
lean_dec_ref(v___y_985_);
v___x_987_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_988_ = lean_string_append(v___x_986_, v___x_987_);
v_intZero_989_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_990_ = lean_int_dec_lt(v_val_980_, v_intZero_989_);
if (v_isNeg_990_ == 0)
{
lean_object* v_a_991_; lean_object* v___x_992_; 
v_a_991_ = lean_nat_abs(v_val_980_);
lean_dec(v_val_980_);
v___x_992_ = l_Nat_reprFast(v_a_991_);
v___y_937_ = v___x_988_;
v___y_938_ = v___x_992_;
goto v___jp_936_;
}
else
{
lean_object* v_abs_993_; lean_object* v_one_994_; lean_object* v_a_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_abs_993_ = lean_nat_abs(v_val_980_);
lean_dec(v_val_980_);
v_one_994_ = lean_unsigned_to_nat(1u);
v_a_995_ = lean_nat_sub(v_abs_993_, v_one_994_);
lean_dec(v_abs_993_);
v___x_996_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_997_ = lean_nat_add(v_a_995_, v_one_994_);
lean_dec(v_a_995_);
v___x_998_ = l_Nat_reprFast(v___x_997_);
v___x_999_ = lean_string_append(v___x_996_, v___x_998_);
lean_dec_ref(v___x_998_);
v___y_937_ = v___x_988_;
v___y_938_ = v___x_999_;
goto v___jp_936_;
}
}
}
else
{
lean_object* v___x_1011_; lean_object* v___y_1013_; lean_object* v_intZero_1017_; uint8_t v_isNeg_1018_; 
lean_dec(v_val_980_);
v___x_1011_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1017_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1018_ = lean_int_dec_lt(v_val_979_, v_intZero_1017_);
if (v_isNeg_1018_ == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; 
v_a_1019_ = lean_nat_abs(v_val_979_);
lean_dec(v_val_979_);
v___x_1020_ = l_Nat_reprFast(v_a_1019_);
v___y_1013_ = v___x_1020_;
goto v___jp_1012_;
}
else
{
lean_object* v_abs_1021_; lean_object* v_one_1022_; lean_object* v_a_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_abs_1021_ = lean_nat_abs(v_val_979_);
lean_dec(v_val_979_);
v_one_1022_ = lean_unsigned_to_nat(1u);
v_a_1023_ = lean_nat_sub(v_abs_1021_, v_one_1022_);
lean_dec(v_abs_1021_);
v___x_1024_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1025_ = lean_nat_add(v_a_1023_, v_one_1022_);
lean_dec(v_a_1023_);
v___x_1026_ = l_Nat_reprFast(v___x_1025_);
v___x_1027_ = lean_string_append(v___x_1024_, v___x_1026_);
lean_dec_ref(v___x_1026_);
v___y_1013_ = v___x_1027_;
goto v___jp_1012_;
}
v___jp_1012_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = lean_string_append(v___x_1011_, v___y_1013_);
lean_dec_ref(v___y_1013_);
v___x_1015_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1016_ = lean_string_append(v___x_1014_, v___x_1015_);
v___y_924_ = v___x_1016_;
goto v___jp_923_;
}
}
}
else
{
lean_object* v___x_1028_; 
lean_dec(v_val_980_);
lean_dec(v_val_979_);
v___x_1028_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_924_ = v___x_1028_;
goto v___jp_923_;
}
}
}
v___jp_923_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_925_ = lean_string_append(v___x_922_, v___y_924_);
lean_dec_ref(v___y_924_);
v___x_926_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__10));
v___x_927_ = lean_string_append(v___x_925_, v___x_926_);
lean_inc(v_x_681_);
v___x_928_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_914_, v_x_681_, v_j_916_);
v___x_929_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_928_);
v___x_930_ = lean_string_append(v___x_927_, v___x_929_);
lean_dec_ref(v___x_929_);
v___x_931_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
v___x_933_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_915_, v_x_681_, v_k_917_);
v___x_934_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_933_);
v___x_935_ = lean_string_append(v___x_932_, v___x_934_);
lean_dec_ref(v___x_934_);
return v___x_935_;
}
v___jp_936_:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_string_append(v___y_937_, v___y_938_);
lean_dec_ref(v___y_938_);
v___x_940_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_941_ = lean_string_append(v___x_939_, v___x_940_);
v___y_924_ = v___x_941_;
goto v___jp_923_;
}
}
case 3:
{
lean_object* v_s_1029_; lean_object* v_t_1030_; lean_object* v_x_1031_; lean_object* v_y_1032_; lean_object* v_a_1033_; lean_object* v_j_1034_; lean_object* v_b_1035_; lean_object* v_k_1036_; lean_object* v_lowerBound_1037_; lean_object* v_upperBound_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___y_1043_; lean_object* v___y_1064_; lean_object* v___y_1065_; 
v_s_1029_ = lean_ctor_get(v_x_682_, 0);
lean_inc_ref(v_s_1029_);
v_t_1030_ = lean_ctor_get(v_x_682_, 1);
lean_inc_ref(v_t_1030_);
v_x_1031_ = lean_ctor_get(v_x_682_, 2);
lean_inc(v_x_1031_);
v_y_1032_ = lean_ctor_get(v_x_682_, 3);
lean_inc(v_y_1032_);
v_a_1033_ = lean_ctor_get(v_x_682_, 4);
lean_inc(v_a_1033_);
v_j_1034_ = lean_ctor_get(v_x_682_, 5);
lean_inc_ref(v_j_1034_);
v_b_1035_ = lean_ctor_get(v_x_682_, 6);
lean_inc(v_b_1035_);
v_k_1036_ = lean_ctor_get(v_x_682_, 7);
lean_inc_ref(v_k_1036_);
lean_dec_ref_known(v_x_682_, 8);
v_lowerBound_1037_ = lean_ctor_get(v_s_680_, 0);
lean_inc(v_lowerBound_1037_);
v_upperBound_1038_ = lean_ctor_get(v_s_680_, 1);
lean_inc(v_upperBound_1038_);
lean_dec_ref(v_s_680_);
v___x_1039_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_681_);
lean_dec(v_x_681_);
v___x_1040_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1041_ = lean_string_append(v___x_1039_, v___x_1040_);
if (lean_obj_tag(v_lowerBound_1037_) == 0)
{
if (lean_obj_tag(v_upperBound_1038_) == 0)
{
lean_object* v___x_1069_; 
v___x_1069_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1043_ = v___x_1069_;
goto v___jp_1042_;
}
else
{
lean_object* v_val_1070_; lean_object* v___x_1071_; lean_object* v___y_1073_; lean_object* v_intZero_1077_; uint8_t v_isNeg_1078_; 
v_val_1070_ = lean_ctor_get(v_upperBound_1038_, 0);
lean_inc(v_val_1070_);
lean_dec_ref_known(v_upperBound_1038_, 1);
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1077_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1078_ = lean_int_dec_lt(v_val_1070_, v_intZero_1077_);
if (v_isNeg_1078_ == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1080_; 
v_a_1079_ = lean_nat_abs(v_val_1070_);
lean_dec(v_val_1070_);
v___x_1080_ = l_Nat_reprFast(v_a_1079_);
v___y_1073_ = v___x_1080_;
goto v___jp_1072_;
}
else
{
lean_object* v_abs_1081_; lean_object* v_one_1082_; lean_object* v_a_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_abs_1081_ = lean_nat_abs(v_val_1070_);
lean_dec(v_val_1070_);
v_one_1082_ = lean_unsigned_to_nat(1u);
v_a_1083_ = lean_nat_sub(v_abs_1081_, v_one_1082_);
lean_dec(v_abs_1081_);
v___x_1084_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1085_ = lean_nat_add(v_a_1083_, v_one_1082_);
lean_dec(v_a_1083_);
v___x_1086_ = l_Nat_reprFast(v___x_1085_);
v___x_1087_ = lean_string_append(v___x_1084_, v___x_1086_);
lean_dec_ref(v___x_1086_);
v___y_1073_ = v___x_1087_;
goto v___jp_1072_;
}
v___jp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = lean_string_append(v___x_1071_, v___y_1073_);
lean_dec_ref(v___y_1073_);
v___x_1075_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1076_ = lean_string_append(v___x_1074_, v___x_1075_);
v___y_1043_ = v___x_1076_;
goto v___jp_1042_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1038_) == 0)
{
lean_object* v_val_1088_; lean_object* v___x_1089_; lean_object* v___y_1091_; lean_object* v_intZero_1095_; uint8_t v_isNeg_1096_; 
v_val_1088_ = lean_ctor_get(v_lowerBound_1037_, 0);
lean_inc(v_val_1088_);
lean_dec_ref_known(v_lowerBound_1037_, 1);
v___x_1089_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1095_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1096_ = lean_int_dec_lt(v_val_1088_, v_intZero_1095_);
if (v_isNeg_1096_ == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1098_; 
v_a_1097_ = lean_nat_abs(v_val_1088_);
lean_dec(v_val_1088_);
v___x_1098_ = l_Nat_reprFast(v_a_1097_);
v___y_1091_ = v___x_1098_;
goto v___jp_1090_;
}
else
{
lean_object* v_abs_1099_; lean_object* v_one_1100_; lean_object* v_a_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_abs_1099_ = lean_nat_abs(v_val_1088_);
lean_dec(v_val_1088_);
v_one_1100_ = lean_unsigned_to_nat(1u);
v_a_1101_ = lean_nat_sub(v_abs_1099_, v_one_1100_);
lean_dec(v_abs_1099_);
v___x_1102_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1103_ = lean_nat_add(v_a_1101_, v_one_1100_);
lean_dec(v_a_1101_);
v___x_1104_ = l_Nat_reprFast(v___x_1103_);
v___x_1105_ = lean_string_append(v___x_1102_, v___x_1104_);
lean_dec_ref(v___x_1104_);
v___y_1091_ = v___x_1105_;
goto v___jp_1090_;
}
v___jp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = lean_string_append(v___x_1089_, v___y_1091_);
lean_dec_ref(v___y_1091_);
v___x_1093_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1094_ = lean_string_append(v___x_1092_, v___x_1093_);
v___y_1043_ = v___x_1094_;
goto v___jp_1042_;
}
}
else
{
lean_object* v_val_1106_; lean_object* v_val_1107_; uint8_t v___x_1108_; 
v_val_1106_ = lean_ctor_get(v_lowerBound_1037_, 0);
lean_inc(v_val_1106_);
lean_dec_ref_known(v_lowerBound_1037_, 1);
v_val_1107_ = lean_ctor_get(v_upperBound_1038_, 0);
lean_inc(v_val_1107_);
lean_dec_ref_known(v_upperBound_1038_, 1);
v___x_1108_ = lean_int_dec_lt(v_val_1107_, v_val_1106_);
if (v___x_1108_ == 0)
{
uint8_t v___x_1109_; 
v___x_1109_ = lean_int_dec_eq(v_val_1106_, v_val_1107_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; lean_object* v___y_1112_; lean_object* v_intZero_1127_; uint8_t v_isNeg_1128_; 
v___x_1110_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1127_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1128_ = lean_int_dec_lt(v_val_1106_, v_intZero_1127_);
if (v_isNeg_1128_ == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; 
v_a_1129_ = lean_nat_abs(v_val_1106_);
lean_dec(v_val_1106_);
v___x_1130_ = l_Nat_reprFast(v_a_1129_);
v___y_1112_ = v___x_1130_;
goto v___jp_1111_;
}
else
{
lean_object* v_abs_1131_; lean_object* v_one_1132_; lean_object* v_a_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_abs_1131_ = lean_nat_abs(v_val_1106_);
lean_dec(v_val_1106_);
v_one_1132_ = lean_unsigned_to_nat(1u);
v_a_1133_ = lean_nat_sub(v_abs_1131_, v_one_1132_);
lean_dec(v_abs_1131_);
v___x_1134_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1135_ = lean_nat_add(v_a_1133_, v_one_1132_);
lean_dec(v_a_1133_);
v___x_1136_ = l_Nat_reprFast(v___x_1135_);
v___x_1137_ = lean_string_append(v___x_1134_, v___x_1136_);
lean_dec_ref(v___x_1136_);
v___y_1112_ = v___x_1137_;
goto v___jp_1111_;
}
v___jp_1111_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v_intZero_1116_; uint8_t v_isNeg_1117_; 
v___x_1113_ = lean_string_append(v___x_1110_, v___y_1112_);
lean_dec_ref(v___y_1112_);
v___x_1114_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1115_ = lean_string_append(v___x_1113_, v___x_1114_);
v_intZero_1116_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1117_ = lean_int_dec_lt(v_val_1107_, v_intZero_1116_);
if (v_isNeg_1117_ == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; 
v_a_1118_ = lean_nat_abs(v_val_1107_);
lean_dec(v_val_1107_);
v___x_1119_ = l_Nat_reprFast(v_a_1118_);
v___y_1064_ = v___x_1115_;
v___y_1065_ = v___x_1119_;
goto v___jp_1063_;
}
else
{
lean_object* v_abs_1120_; lean_object* v_one_1121_; lean_object* v_a_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_abs_1120_ = lean_nat_abs(v_val_1107_);
lean_dec(v_val_1107_);
v_one_1121_ = lean_unsigned_to_nat(1u);
v_a_1122_ = lean_nat_sub(v_abs_1120_, v_one_1121_);
lean_dec(v_abs_1120_);
v___x_1123_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1124_ = lean_nat_add(v_a_1122_, v_one_1121_);
lean_dec(v_a_1122_);
v___x_1125_ = l_Nat_reprFast(v___x_1124_);
v___x_1126_ = lean_string_append(v___x_1123_, v___x_1125_);
lean_dec_ref(v___x_1125_);
v___y_1064_ = v___x_1115_;
v___y_1065_ = v___x_1126_;
goto v___jp_1063_;
}
}
}
else
{
lean_object* v___x_1138_; lean_object* v___y_1140_; lean_object* v_intZero_1144_; uint8_t v_isNeg_1145_; 
lean_dec(v_val_1107_);
v___x_1138_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1144_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1145_ = lean_int_dec_lt(v_val_1106_, v_intZero_1144_);
if (v_isNeg_1145_ == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; 
v_a_1146_ = lean_nat_abs(v_val_1106_);
lean_dec(v_val_1106_);
v___x_1147_ = l_Nat_reprFast(v_a_1146_);
v___y_1140_ = v___x_1147_;
goto v___jp_1139_;
}
else
{
lean_object* v_abs_1148_; lean_object* v_one_1149_; lean_object* v_a_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_abs_1148_ = lean_nat_abs(v_val_1106_);
lean_dec(v_val_1106_);
v_one_1149_ = lean_unsigned_to_nat(1u);
v_a_1150_ = lean_nat_sub(v_abs_1148_, v_one_1149_);
lean_dec(v_abs_1148_);
v___x_1151_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1152_ = lean_nat_add(v_a_1150_, v_one_1149_);
lean_dec(v_a_1150_);
v___x_1153_ = l_Nat_reprFast(v___x_1152_);
v___x_1154_ = lean_string_append(v___x_1151_, v___x_1153_);
lean_dec_ref(v___x_1153_);
v___y_1140_ = v___x_1154_;
goto v___jp_1139_;
}
v___jp_1139_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_string_append(v___x_1138_, v___y_1140_);
lean_dec_ref(v___y_1140_);
v___x_1142_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1143_ = lean_string_append(v___x_1141_, v___x_1142_);
v___y_1043_ = v___x_1143_;
goto v___jp_1042_;
}
}
}
else
{
lean_object* v___x_1155_; 
lean_dec(v_val_1107_);
lean_dec(v_val_1106_);
v___x_1155_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1043_ = v___x_1155_;
goto v___jp_1042_;
}
}
}
v___jp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1044_ = lean_string_append(v___x_1041_, v___y_1043_);
lean_dec_ref(v___y_1043_);
v___x_1045_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__11));
v___x_1046_ = lean_string_append(v___x_1044_, v___x_1045_);
v___x_1047_ = l_Int_repr(v_a_1033_);
lean_dec(v_a_1033_);
v___x_1048_ = lean_string_append(v___x_1046_, v___x_1047_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__12));
v___x_1050_ = lean_string_append(v___x_1048_, v___x_1049_);
v___x_1051_ = l_Int_repr(v_b_1035_);
lean_dec(v_b_1035_);
v___x_1052_ = lean_string_append(v___x_1050_, v___x_1051_);
lean_dec_ref(v___x_1051_);
v___x_1053_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__13));
v___x_1054_ = lean_string_append(v___x_1052_, v___x_1053_);
v___x_1055_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_1029_, v_x_1031_, v_j_1034_);
v___x_1056_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1055_);
v___x_1057_ = lean_string_append(v___x_1054_, v___x_1056_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_1059_ = lean_string_append(v___x_1057_, v___x_1058_);
v___x_1060_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_1030_, v_y_1032_, v_k_1036_);
v___x_1061_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1060_);
v___x_1062_ = lean_string_append(v___x_1059_, v___x_1061_);
lean_dec_ref(v___x_1061_);
return v___x_1062_;
}
v___jp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = lean_string_append(v___y_1064_, v___y_1065_);
lean_dec_ref(v___y_1065_);
v___x_1067_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1068_ = lean_string_append(v___x_1066_, v___x_1067_);
v___y_1043_ = v___x_1068_;
goto v___jp_1042_;
}
}
default: 
{
lean_object* v_m_1156_; lean_object* v_r_1157_; lean_object* v_i_1158_; lean_object* v_x_1159_; lean_object* v_j_1160_; lean_object* v_lowerBound_1161_; lean_object* v_upperBound_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___y_1167_; lean_object* v___y_1184_; lean_object* v___y_1185_; 
v_m_1156_ = lean_ctor_get(v_x_682_, 0);
lean_inc(v_m_1156_);
v_r_1157_ = lean_ctor_get(v_x_682_, 1);
lean_inc(v_r_1157_);
v_i_1158_ = lean_ctor_get(v_x_682_, 2);
lean_inc(v_i_1158_);
v_x_1159_ = lean_ctor_get(v_x_682_, 3);
lean_inc(v_x_1159_);
v_j_1160_ = lean_ctor_get(v_x_682_, 4);
lean_inc_ref(v_j_1160_);
lean_dec_ref_known(v_x_682_, 5);
v_lowerBound_1161_ = lean_ctor_get(v_s_680_, 0);
lean_inc(v_lowerBound_1161_);
v_upperBound_1162_ = lean_ctor_get(v_s_680_, 1);
lean_inc(v_upperBound_1162_);
lean_dec_ref(v_s_680_);
v___x_1163_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_681_);
lean_dec(v_x_681_);
v___x_1164_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1165_ = lean_string_append(v___x_1163_, v___x_1164_);
if (lean_obj_tag(v_lowerBound_1161_) == 0)
{
if (lean_obj_tag(v_upperBound_1162_) == 0)
{
lean_object* v___x_1189_; 
v___x_1189_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1167_ = v___x_1189_;
goto v___jp_1166_;
}
else
{
lean_object* v_val_1190_; lean_object* v___x_1191_; lean_object* v___y_1193_; lean_object* v_intZero_1197_; uint8_t v_isNeg_1198_; 
v_val_1190_ = lean_ctor_get(v_upperBound_1162_, 0);
lean_inc(v_val_1190_);
lean_dec_ref_known(v_upperBound_1162_, 1);
v___x_1191_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1197_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1198_ = lean_int_dec_lt(v_val_1190_, v_intZero_1197_);
if (v_isNeg_1198_ == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1200_; 
v_a_1199_ = lean_nat_abs(v_val_1190_);
lean_dec(v_val_1190_);
v___x_1200_ = l_Nat_reprFast(v_a_1199_);
v___y_1193_ = v___x_1200_;
goto v___jp_1192_;
}
else
{
lean_object* v_abs_1201_; lean_object* v_one_1202_; lean_object* v_a_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_abs_1201_ = lean_nat_abs(v_val_1190_);
lean_dec(v_val_1190_);
v_one_1202_ = lean_unsigned_to_nat(1u);
v_a_1203_ = lean_nat_sub(v_abs_1201_, v_one_1202_);
lean_dec(v_abs_1201_);
v___x_1204_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1205_ = lean_nat_add(v_a_1203_, v_one_1202_);
lean_dec(v_a_1203_);
v___x_1206_ = l_Nat_reprFast(v___x_1205_);
v___x_1207_ = lean_string_append(v___x_1204_, v___x_1206_);
lean_dec_ref(v___x_1206_);
v___y_1193_ = v___x_1207_;
goto v___jp_1192_;
}
v___jp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = lean_string_append(v___x_1191_, v___y_1193_);
lean_dec_ref(v___y_1193_);
v___x_1195_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1196_ = lean_string_append(v___x_1194_, v___x_1195_);
v___y_1167_ = v___x_1196_;
goto v___jp_1166_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1162_) == 0)
{
lean_object* v_val_1208_; lean_object* v___x_1209_; lean_object* v___y_1211_; lean_object* v_intZero_1215_; uint8_t v_isNeg_1216_; 
v_val_1208_ = lean_ctor_get(v_lowerBound_1161_, 0);
lean_inc(v_val_1208_);
lean_dec_ref_known(v_lowerBound_1161_, 1);
v___x_1209_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1215_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1216_ = lean_int_dec_lt(v_val_1208_, v_intZero_1215_);
if (v_isNeg_1216_ == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1218_; 
v_a_1217_ = lean_nat_abs(v_val_1208_);
lean_dec(v_val_1208_);
v___x_1218_ = l_Nat_reprFast(v_a_1217_);
v___y_1211_ = v___x_1218_;
goto v___jp_1210_;
}
else
{
lean_object* v_abs_1219_; lean_object* v_one_1220_; lean_object* v_a_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_abs_1219_ = lean_nat_abs(v_val_1208_);
lean_dec(v_val_1208_);
v_one_1220_ = lean_unsigned_to_nat(1u);
v_a_1221_ = lean_nat_sub(v_abs_1219_, v_one_1220_);
lean_dec(v_abs_1219_);
v___x_1222_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1223_ = lean_nat_add(v_a_1221_, v_one_1220_);
lean_dec(v_a_1221_);
v___x_1224_ = l_Nat_reprFast(v___x_1223_);
v___x_1225_ = lean_string_append(v___x_1222_, v___x_1224_);
lean_dec_ref(v___x_1224_);
v___y_1211_ = v___x_1225_;
goto v___jp_1210_;
}
v___jp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = lean_string_append(v___x_1209_, v___y_1211_);
lean_dec_ref(v___y_1211_);
v___x_1213_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1214_ = lean_string_append(v___x_1212_, v___x_1213_);
v___y_1167_ = v___x_1214_;
goto v___jp_1166_;
}
}
else
{
lean_object* v_val_1226_; lean_object* v_val_1227_; uint8_t v___x_1228_; 
v_val_1226_ = lean_ctor_get(v_lowerBound_1161_, 0);
lean_inc(v_val_1226_);
lean_dec_ref_known(v_lowerBound_1161_, 1);
v_val_1227_ = lean_ctor_get(v_upperBound_1162_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v_upperBound_1162_, 1);
v___x_1228_ = lean_int_dec_lt(v_val_1227_, v_val_1226_);
if (v___x_1228_ == 0)
{
uint8_t v___x_1229_; 
v___x_1229_ = lean_int_dec_eq(v_val_1226_, v_val_1227_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___y_1232_; lean_object* v_intZero_1247_; uint8_t v_isNeg_1248_; 
v___x_1230_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1247_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1248_ = lean_int_dec_lt(v_val_1226_, v_intZero_1247_);
if (v_isNeg_1248_ == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1250_; 
v_a_1249_ = lean_nat_abs(v_val_1226_);
lean_dec(v_val_1226_);
v___x_1250_ = l_Nat_reprFast(v_a_1249_);
v___y_1232_ = v___x_1250_;
goto v___jp_1231_;
}
else
{
lean_object* v_abs_1251_; lean_object* v_one_1252_; lean_object* v_a_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_abs_1251_ = lean_nat_abs(v_val_1226_);
lean_dec(v_val_1226_);
v_one_1252_ = lean_unsigned_to_nat(1u);
v_a_1253_ = lean_nat_sub(v_abs_1251_, v_one_1252_);
lean_dec(v_abs_1251_);
v___x_1254_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1255_ = lean_nat_add(v_a_1253_, v_one_1252_);
lean_dec(v_a_1253_);
v___x_1256_ = l_Nat_reprFast(v___x_1255_);
v___x_1257_ = lean_string_append(v___x_1254_, v___x_1256_);
lean_dec_ref(v___x_1256_);
v___y_1232_ = v___x_1257_;
goto v___jp_1231_;
}
v___jp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_intZero_1236_; uint8_t v_isNeg_1237_; 
v___x_1233_ = lean_string_append(v___x_1230_, v___y_1232_);
lean_dec_ref(v___y_1232_);
v___x_1234_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1235_ = lean_string_append(v___x_1233_, v___x_1234_);
v_intZero_1236_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1237_ = lean_int_dec_lt(v_val_1227_, v_intZero_1236_);
if (v_isNeg_1237_ == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1239_; 
v_a_1238_ = lean_nat_abs(v_val_1227_);
lean_dec(v_val_1227_);
v___x_1239_ = l_Nat_reprFast(v_a_1238_);
v___y_1184_ = v___x_1235_;
v___y_1185_ = v___x_1239_;
goto v___jp_1183_;
}
else
{
lean_object* v_abs_1240_; lean_object* v_one_1241_; lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_abs_1240_ = lean_nat_abs(v_val_1227_);
lean_dec(v_val_1227_);
v_one_1241_ = lean_unsigned_to_nat(1u);
v_a_1242_ = lean_nat_sub(v_abs_1240_, v_one_1241_);
lean_dec(v_abs_1240_);
v___x_1243_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1244_ = lean_nat_add(v_a_1242_, v_one_1241_);
lean_dec(v_a_1242_);
v___x_1245_ = l_Nat_reprFast(v___x_1244_);
v___x_1246_ = lean_string_append(v___x_1243_, v___x_1245_);
lean_dec_ref(v___x_1245_);
v___y_1184_ = v___x_1235_;
v___y_1185_ = v___x_1246_;
goto v___jp_1183_;
}
}
}
else
{
lean_object* v___x_1258_; lean_object* v___y_1260_; lean_object* v_intZero_1264_; uint8_t v_isNeg_1265_; 
lean_dec(v_val_1227_);
v___x_1258_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1264_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1265_ = lean_int_dec_lt(v_val_1226_, v_intZero_1264_);
if (v_isNeg_1265_ == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1267_; 
v_a_1266_ = lean_nat_abs(v_val_1226_);
lean_dec(v_val_1226_);
v___x_1267_ = l_Nat_reprFast(v_a_1266_);
v___y_1260_ = v___x_1267_;
goto v___jp_1259_;
}
else
{
lean_object* v_abs_1268_; lean_object* v_one_1269_; lean_object* v_a_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_abs_1268_ = lean_nat_abs(v_val_1226_);
lean_dec(v_val_1226_);
v_one_1269_ = lean_unsigned_to_nat(1u);
v_a_1270_ = lean_nat_sub(v_abs_1268_, v_one_1269_);
lean_dec(v_abs_1268_);
v___x_1271_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1272_ = lean_nat_add(v_a_1270_, v_one_1269_);
lean_dec(v_a_1270_);
v___x_1273_ = l_Nat_reprFast(v___x_1272_);
v___x_1274_ = lean_string_append(v___x_1271_, v___x_1273_);
lean_dec_ref(v___x_1273_);
v___y_1260_ = v___x_1274_;
goto v___jp_1259_;
}
v___jp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_string_append(v___x_1258_, v___y_1260_);
lean_dec_ref(v___y_1260_);
v___x_1262_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1263_ = lean_string_append(v___x_1261_, v___x_1262_);
v___y_1167_ = v___x_1263_;
goto v___jp_1166_;
}
}
}
else
{
lean_object* v___x_1275_; 
lean_dec(v_val_1227_);
lean_dec(v_val_1226_);
v___x_1275_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1167_ = v___x_1275_;
goto v___jp_1166_;
}
}
}
v___jp_1166_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1168_ = lean_string_append(v___x_1165_, v___y_1167_);
lean_dec_ref(v___y_1167_);
v___x_1169_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__14));
v___x_1170_ = lean_string_append(v___x_1168_, v___x_1169_);
v___x_1171_ = l_Nat_reprFast(v_m_1156_);
v___x_1172_ = lean_string_append(v___x_1170_, v___x_1171_);
lean_dec_ref(v___x_1171_);
v___x_1173_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__15));
v___x_1174_ = lean_string_append(v___x_1172_, v___x_1173_);
v___x_1175_ = l_Nat_reprFast(v_i_1158_);
v___x_1176_ = lean_string_append(v___x_1174_, v___x_1175_);
lean_dec_ref(v___x_1175_);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__16));
v___x_1178_ = lean_string_append(v___x_1176_, v___x_1177_);
v___x_1179_ = l_Lean_Omega_Constraint_exact(v_r_1157_);
v___x_1180_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v___x_1179_, v_x_1159_, v_j_1160_);
v___x_1181_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1180_);
v___x_1182_ = lean_string_append(v___x_1178_, v___x_1181_);
lean_dec_ref(v___x_1181_);
return v___x_1182_;
}
v___jp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1186_ = lean_string_append(v___y_1184_, v___y_1185_);
lean_dec_ref(v___y_1185_);
v___x_1187_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1188_ = lean_string_append(v___x_1186_, v___x_1187_);
v___y_1167_ = v___x_1188_;
goto v___jp_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_instToString(lean_object* v_s_1276_, lean_object* v_x_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Justification_toString), 3, 2);
lean_closure_set(v___x_1278_, 0, v_s_1276_);
lean_closure_set(v___x_1278_, 1, v_x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(lean_object* v_nilFn_1279_, lean_object* v_consFn_1280_, lean_object* v_x_1281_){
_start:
{
if (lean_obj_tag(v_x_1281_) == 0)
{
lean_dec_ref(v_consFn_1280_);
lean_inc_ref(v_nilFn_1279_);
return v_nilFn_1279_;
}
else
{
lean_object* v_head_1282_; lean_object* v_tail_1283_; lean_object* v___y_1285_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_head_1282_ = lean_ctor_get(v_x_1281_, 0);
v_tail_1283_ = lean_ctor_get(v_x_1281_, 1);
v___x_1288_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1289_ = lean_int_dec_le(v___x_1288_, v_head_1282_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1290_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1291_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1292_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1293_ = lean_int_neg(v_head_1282_);
v___x_1294_ = l_Int_toNat(v___x_1293_);
lean_dec(v___x_1293_);
v___x_1295_ = l_Lean_instToExprInt_mkNat(v___x_1294_);
v___x_1296_ = l_Lean_mkApp3(v___x_1290_, v___x_1291_, v___x_1292_, v___x_1295_);
v___y_1285_ = v___x_1296_;
goto v___jp_1284_;
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = l_Int_toNat(v_head_1282_);
v___x_1298_ = l_Lean_instToExprInt_mkNat(v___x_1297_);
v___y_1285_ = v___x_1298_;
goto v___jp_1284_;
}
v___jp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_inc_ref(v_consFn_1280_);
v___x_1286_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1279_, v_consFn_1280_, v_tail_1283_);
v___x_1287_ = l_Lean_mkAppB(v_consFn_1280_, v___y_1285_, v___x_1286_);
return v___x_1287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0___boxed(lean_object* v_nilFn_1299_, lean_object* v_consFn_1300_, lean_object* v_x_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1299_, v_consFn_1300_, v_x_1301_);
lean_dec(v_x_1301_);
lean_dec_ref(v_nilFn_1299_);
return v_res_1302_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = lean_box(0);
v___x_1309_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1));
v___x_1310_ = l_Lean_Expr_const___override(v___x_1309_, v___x_1308_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof(lean_object* v_s_1311_, lean_object* v_x_1312_, lean_object* v_v_1313_, lean_object* v_prf_1314_){
_start:
{
lean_object* v___x_1315_; lean_object* v___y_1317_; lean_object* v_lowerBound_1322_; lean_object* v_upperBound_1323_; lean_object* v___x_1324_; lean_object* v_type_1325_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1333_; 
v___x_1315_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2);
v_lowerBound_1322_ = lean_ctor_get(v_s_1311_, 0);
v_upperBound_1323_ = lean_ctor_get(v_s_1311_, 1);
v___x_1324_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1325_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1322_) == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1333_ = v___x_1349_;
goto v___jp_1332_;
}
else
{
lean_object* v_val_1350_; lean_object* v___x_1351_; lean_object* v___y_1353_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v_val_1350_ = lean_ctor_get(v_lowerBound_1322_, 0);
v___x_1351_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1355_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1356_ = lean_int_dec_le(v___x_1355_, v_val_1350_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1357_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1358_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1359_ = lean_int_neg(v_val_1350_);
v___x_1360_ = l_Int_toNat(v___x_1359_);
lean_dec(v___x_1359_);
v___x_1361_ = l_Lean_instToExprInt_mkNat(v___x_1360_);
v___x_1362_ = l_Lean_mkApp3(v___x_1357_, v_type_1325_, v___x_1358_, v___x_1361_);
v___y_1353_ = v___x_1362_;
goto v___jp_1352_;
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = l_Int_toNat(v_val_1350_);
v___x_1364_ = l_Lean_instToExprInt_mkNat(v___x_1363_);
v___y_1353_ = v___x_1364_;
goto v___jp_1352_;
}
v___jp_1352_:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_mkAppB(v___x_1351_, v_type_1325_, v___y_1353_);
v___y_1333_ = v___x_1354_;
goto v___jp_1332_;
}
}
v___jp_1316_:
{
lean_object* v_nil_1318_; lean_object* v_cons_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_nil_1318_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1319_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1320_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1318_, v_cons_1319_, v_x_1312_);
v___x_1321_ = l_Lean_mkApp4(v___x_1315_, v___y_1317_, v___x_1320_, v_v_1313_, v_prf_1314_);
return v___x_1321_;
}
v___jp_1326_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_inc_ref(v___y_1327_);
v___x_1330_ = l_Lean_mkAppB(v___y_1327_, v_type_1325_, v___y_1329_);
v___x_1331_ = l_Lean_Expr_app___override(v___y_1328_, v___x_1330_);
v___y_1317_ = v___x_1331_;
goto v___jp_1316_;
}
v___jp_1332_:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_Expr_app___override(v___x_1324_, v___y_1333_);
if (lean_obj_tag(v_upperBound_1323_) == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1336_ = l_Lean_Expr_app___override(v___x_1334_, v___x_1335_);
v___y_1317_ = v___x_1336_;
goto v___jp_1316_;
}
else
{
lean_object* v_val_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v_val_1337_ = lean_ctor_get(v_upperBound_1323_, 0);
v___x_1338_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1339_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1340_ = lean_int_dec_le(v___x_1339_, v_val_1337_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1341_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1342_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1343_ = lean_int_neg(v_val_1337_);
v___x_1344_ = l_Int_toNat(v___x_1343_);
lean_dec(v___x_1343_);
v___x_1345_ = l_Lean_instToExprInt_mkNat(v___x_1344_);
v___x_1346_ = l_Lean_mkApp3(v___x_1341_, v_type_1325_, v___x_1342_, v___x_1345_);
v___y_1327_ = v___x_1338_;
v___y_1328_ = v___x_1334_;
v___y_1329_ = v___x_1346_;
goto v___jp_1326_;
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = l_Int_toNat(v_val_1337_);
v___x_1348_ = l_Lean_instToExprInt_mkNat(v___x_1347_);
v___y_1327_ = v___x_1338_;
v___y_1328_ = v___x_1334_;
v___y_1329_ = v___x_1348_;
goto v___jp_1326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___boxed(lean_object* v_s_1365_, lean_object* v_x_1366_, lean_object* v_v_1367_, lean_object* v_prf_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1365_, v_x_1366_, v_v_1367_, v_prf_1368_);
lean_dec(v_x_1366_);
lean_dec_ref(v_s_1365_);
return v_res_1369_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = lean_box(0);
v___x_1377_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1));
v___x_1378_ = l_Lean_Expr_const___override(v___x_1377_, v___x_1376_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof(lean_object* v_s_1379_, lean_object* v_t_1380_, lean_object* v_x_1381_, lean_object* v_v_1382_, lean_object* v_ps_1383_, lean_object* v_pt_1384_){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1436_; lean_object* v_lowerBound_1454_; lean_object* v_upperBound_1455_; lean_object* v___x_1456_; lean_object* v_type_1457_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1465_; 
v___x_1385_ = lean_box(0);
v___x_1386_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2);
v_lowerBound_1454_ = lean_ctor_get(v_s_1379_, 0);
v_upperBound_1455_ = lean_ctor_get(v_s_1379_, 1);
v___x_1456_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1457_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1454_) == 0)
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1465_ = v___x_1481_;
goto v___jp_1464_;
}
else
{
lean_object* v_val_1482_; lean_object* v___x_1483_; lean_object* v___y_1485_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
v_val_1482_ = lean_ctor_get(v_lowerBound_1454_, 0);
v___x_1483_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1487_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1488_ = lean_int_dec_le(v___x_1487_, v_val_1482_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1489_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1490_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1491_ = lean_int_neg(v_val_1482_);
v___x_1492_ = l_Int_toNat(v___x_1491_);
lean_dec(v___x_1491_);
v___x_1493_ = l_Lean_instToExprInt_mkNat(v___x_1492_);
v___x_1494_ = l_Lean_mkApp3(v___x_1489_, v_type_1457_, v___x_1490_, v___x_1493_);
v___y_1485_ = v___x_1494_;
goto v___jp_1484_;
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = l_Int_toNat(v_val_1482_);
v___x_1496_ = l_Lean_instToExprInt_mkNat(v___x_1495_);
v___y_1485_ = v___x_1496_;
goto v___jp_1484_;
}
v___jp_1484_:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_mkAppB(v___x_1483_, v_type_1457_, v___y_1485_);
v___y_1465_ = v___x_1486_;
goto v___jp_1464_;
}
}
v___jp_1387_:
{
lean_object* v_nil_1390_; lean_object* v_cons_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_nil_1390_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1391_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1392_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1390_, v_cons_1391_, v_x_1381_);
v___x_1393_ = l_Lean_mkApp6(v___x_1386_, v___y_1388_, v___y_1389_, v___x_1392_, v_v_1382_, v_ps_1383_, v_pt_1384_);
return v___x_1393_;
}
v___jp_1394_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_inc_ref(v___y_1398_);
v___x_1400_ = l_Lean_mkAppB(v___y_1398_, v___y_1397_, v___y_1399_);
v___x_1401_ = l_Lean_Expr_app___override(v___y_1395_, v___x_1400_);
v___y_1388_ = v___y_1396_;
v___y_1389_ = v___x_1401_;
goto v___jp_1387_;
}
v___jp_1402_:
{
lean_object* v_upperBound_1408_; lean_object* v___x_1409_; 
v_upperBound_1408_ = lean_ctor_get(v_t_1380_, 1);
lean_inc_ref(v___y_1406_);
v___x_1409_ = l_Lean_Expr_app___override(v___y_1406_, v___y_1407_);
if (lean_obj_tag(v_upperBound_1408_) == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1411_ = l_Lean_Expr_app___override(v___x_1410_, v___y_1405_);
v___x_1412_ = l_Lean_Expr_app___override(v___x_1409_, v___x_1411_);
v___y_1388_ = v___y_1403_;
v___y_1389_ = v___x_1412_;
goto v___jp_1387_;
}
else
{
lean_object* v_val_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v_val_1413_ = lean_ctor_get(v_upperBound_1408_, 0);
v___x_1414_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1415_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1416_ = lean_int_dec_le(v___x_1415_, v_val_1413_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1417_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1418_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1404_);
v___x_1419_ = l_Lean_Name_mkStr2(v___y_1404_, v___x_1418_);
v___x_1420_ = l_Lean_Expr_const___override(v___x_1419_, v___x_1385_);
v___x_1421_ = lean_int_neg(v_val_1413_);
v___x_1422_ = l_Int_toNat(v___x_1421_);
lean_dec(v___x_1421_);
v___x_1423_ = l_Lean_instToExprInt_mkNat(v___x_1422_);
lean_inc_ref(v___y_1405_);
v___x_1424_ = l_Lean_mkApp3(v___x_1417_, v___y_1405_, v___x_1420_, v___x_1423_);
v___y_1395_ = v___x_1409_;
v___y_1396_ = v___y_1403_;
v___y_1397_ = v___y_1405_;
v___y_1398_ = v___x_1414_;
v___y_1399_ = v___x_1424_;
goto v___jp_1394_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = l_Int_toNat(v_val_1413_);
v___x_1426_ = l_Lean_instToExprInt_mkNat(v___x_1425_);
v___y_1395_ = v___x_1409_;
v___y_1396_ = v___y_1403_;
v___y_1397_ = v___y_1405_;
v___y_1398_ = v___x_1414_;
v___y_1399_ = v___x_1426_;
goto v___jp_1394_;
}
}
}
v___jp_1427_:
{
lean_object* v___x_1434_; 
lean_inc_ref(v___y_1431_);
lean_inc_ref(v___y_1428_);
v___x_1434_ = l_Lean_mkAppB(v___y_1428_, v___y_1431_, v___y_1433_);
v___y_1403_ = v___y_1429_;
v___y_1404_ = v___y_1430_;
v___y_1405_ = v___y_1431_;
v___y_1406_ = v___y_1432_;
v___y_1407_ = v___x_1434_;
goto v___jp_1402_;
}
v___jp_1435_:
{
lean_object* v_lowerBound_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v_type_1440_; 
v_lowerBound_1437_ = lean_ctor_get(v_t_1380_, 0);
v___x_1438_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1439_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1440_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1437_) == 0)
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1403_ = v___y_1436_;
v___y_1404_ = v___x_1439_;
v___y_1405_ = v_type_1440_;
v___y_1406_ = v___x_1438_;
v___y_1407_ = v___x_1441_;
goto v___jp_1402_;
}
else
{
lean_object* v_val_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v_val_1442_ = lean_ctor_get(v_lowerBound_1437_, 0);
v___x_1443_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1444_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1445_ = lean_int_dec_le(v___x_1444_, v_val_1442_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1446_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1447_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1448_ = lean_int_neg(v_val_1442_);
v___x_1449_ = l_Int_toNat(v___x_1448_);
lean_dec(v___x_1448_);
v___x_1450_ = l_Lean_instToExprInt_mkNat(v___x_1449_);
v___x_1451_ = l_Lean_mkApp3(v___x_1446_, v_type_1440_, v___x_1447_, v___x_1450_);
v___y_1428_ = v___x_1443_;
v___y_1429_ = v___y_1436_;
v___y_1430_ = v___x_1439_;
v___y_1431_ = v_type_1440_;
v___y_1432_ = v___x_1438_;
v___y_1433_ = v___x_1451_;
goto v___jp_1427_;
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = l_Int_toNat(v_val_1442_);
v___x_1453_ = l_Lean_instToExprInt_mkNat(v___x_1452_);
v___y_1428_ = v___x_1443_;
v___y_1429_ = v___y_1436_;
v___y_1430_ = v___x_1439_;
v___y_1431_ = v_type_1440_;
v___y_1432_ = v___x_1438_;
v___y_1433_ = v___x_1453_;
goto v___jp_1427_;
}
}
}
v___jp_1458_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_inc_ref(v___y_1459_);
v___x_1462_ = l_Lean_mkAppB(v___y_1459_, v_type_1457_, v___y_1461_);
v___x_1463_ = l_Lean_Expr_app___override(v___y_1460_, v___x_1462_);
v___y_1436_ = v___x_1463_;
goto v___jp_1435_;
}
v___jp_1464_:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_Expr_app___override(v___x_1456_, v___y_1465_);
if (lean_obj_tag(v_upperBound_1455_) == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1468_ = l_Lean_Expr_app___override(v___x_1466_, v___x_1467_);
v___y_1436_ = v___x_1468_;
goto v___jp_1435_;
}
else
{
lean_object* v_val_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v_val_1469_ = lean_ctor_get(v_upperBound_1455_, 0);
v___x_1470_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1471_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1472_ = lean_int_dec_le(v___x_1471_, v_val_1469_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1473_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1474_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1475_ = lean_int_neg(v_val_1469_);
v___x_1476_ = l_Int_toNat(v___x_1475_);
lean_dec(v___x_1475_);
v___x_1477_ = l_Lean_instToExprInt_mkNat(v___x_1476_);
v___x_1478_ = l_Lean_mkApp3(v___x_1473_, v_type_1457_, v___x_1474_, v___x_1477_);
v___y_1459_ = v___x_1470_;
v___y_1460_ = v___x_1466_;
v___y_1461_ = v___x_1478_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = l_Int_toNat(v_val_1469_);
v___x_1480_ = l_Lean_instToExprInt_mkNat(v___x_1479_);
v___y_1459_ = v___x_1470_;
v___y_1460_ = v___x_1466_;
v___y_1461_ = v___x_1480_;
goto v___jp_1458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___boxed(lean_object* v_s_1497_, lean_object* v_t_1498_, lean_object* v_x_1499_, lean_object* v_v_1500_, lean_object* v_ps_1501_, lean_object* v_pt_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1497_, v_t_1498_, v_x_1499_, v_v_1500_, v_ps_1501_, v_pt_1502_);
lean_dec(v_x_1499_);
lean_dec_ref(v_t_1498_);
lean_dec_ref(v_s_1497_);
return v_res_1503_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_box(0);
v___x_1510_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1));
v___x_1511_ = l_Lean_Expr_const___override(v___x_1510_, v___x_1509_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof(lean_object* v_s_1512_, lean_object* v_t_1513_, lean_object* v_a_1514_, lean_object* v_x_1515_, lean_object* v_b_1516_, lean_object* v_y_1517_, lean_object* v_v_1518_, lean_object* v_px_1519_, lean_object* v_py_1520_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1607_; lean_object* v_lowerBound_1625_; lean_object* v_upperBound_1626_; lean_object* v___x_1627_; lean_object* v_type_1628_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1636_; 
v___x_1521_ = lean_box(0);
v___x_1522_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2);
v_lowerBound_1625_ = lean_ctor_get(v_s_1512_, 0);
v_upperBound_1626_ = lean_ctor_get(v_s_1512_, 1);
v___x_1627_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1628_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1625_) == 0)
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1636_ = v___x_1652_;
goto v___jp_1635_;
}
else
{
lean_object* v_val_1653_; lean_object* v___x_1654_; lean_object* v___y_1656_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v_val_1653_ = lean_ctor_get(v_lowerBound_1625_, 0);
v___x_1654_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1658_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1659_ = lean_int_dec_le(v___x_1658_, v_val_1653_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1660_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1661_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1662_ = lean_int_neg(v_val_1653_);
v___x_1663_ = l_Int_toNat(v___x_1662_);
lean_dec(v___x_1662_);
v___x_1664_ = l_Lean_instToExprInt_mkNat(v___x_1663_);
v___x_1665_ = l_Lean_mkApp3(v___x_1660_, v_type_1628_, v___x_1661_, v___x_1664_);
v___y_1656_ = v___x_1665_;
goto v___jp_1655_;
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = l_Int_toNat(v_val_1653_);
v___x_1667_ = l_Lean_instToExprInt_mkNat(v___x_1666_);
v___y_1656_ = v___x_1667_;
goto v___jp_1655_;
}
v___jp_1655_:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_mkAppB(v___x_1654_, v_type_1628_, v___y_1656_);
v___y_1636_ = v___x_1657_;
goto v___jp_1635_;
}
}
v___jp_1523_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v___y_1529_, v___y_1528_, v_y_1517_);
v___x_1532_ = l_Lean_mkApp9(v___x_1522_, v___y_1525_, v___y_1524_, v___y_1526_, v___y_1527_, v___y_1530_, v___x_1531_, v_v_1518_, v_px_1519_, v_py_1520_);
return v___x_1532_;
}
v___jp_1533_:
{
lean_object* v_type_1537_; lean_object* v_nil_1538_; lean_object* v_cons_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v_type_1537_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_nil_1538_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1539_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1540_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1538_, v_cons_1539_, v_x_1515_);
v___x_1541_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1542_ = lean_int_dec_le(v___x_1541_, v_b_1516_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1543_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1544_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1545_ = lean_int_neg(v_b_1516_);
v___x_1546_ = l_Int_toNat(v___x_1545_);
lean_dec(v___x_1545_);
v___x_1547_ = l_Lean_instToExprInt_mkNat(v___x_1546_);
v___x_1548_ = l_Lean_mkApp3(v___x_1543_, v_type_1537_, v___x_1544_, v___x_1547_);
v___y_1524_ = v___y_1534_;
v___y_1525_ = v___y_1535_;
v___y_1526_ = v___y_1536_;
v___y_1527_ = v___x_1540_;
v___y_1528_ = v_cons_1539_;
v___y_1529_ = v_nil_1538_;
v___y_1530_ = v___x_1548_;
goto v___jp_1523_;
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = l_Int_toNat(v_b_1516_);
v___x_1550_ = l_Lean_instToExprInt_mkNat(v___x_1549_);
v___y_1524_ = v___y_1534_;
v___y_1525_ = v___y_1535_;
v___y_1526_ = v___y_1536_;
v___y_1527_ = v___x_1540_;
v___y_1528_ = v_cons_1539_;
v___y_1529_ = v_nil_1538_;
v___y_1530_ = v___x_1550_;
goto v___jp_1523_;
}
}
v___jp_1551_:
{
lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1555_ = lean_int_dec_le(v___x_1554_, v_a_1514_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1556_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1557_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1558_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1559_ = lean_int_neg(v_a_1514_);
v___x_1560_ = l_Int_toNat(v___x_1559_);
lean_dec(v___x_1559_);
v___x_1561_ = l_Lean_instToExprInt_mkNat(v___x_1560_);
v___x_1562_ = l_Lean_mkApp3(v___x_1556_, v___x_1557_, v___x_1558_, v___x_1561_);
v___y_1534_ = v___y_1553_;
v___y_1535_ = v___y_1552_;
v___y_1536_ = v___x_1562_;
goto v___jp_1533_;
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = l_Int_toNat(v_a_1514_);
v___x_1564_ = l_Lean_instToExprInt_mkNat(v___x_1563_);
v___y_1534_ = v___y_1553_;
v___y_1535_ = v___y_1552_;
v___y_1536_ = v___x_1564_;
goto v___jp_1533_;
}
}
v___jp_1565_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_inc_ref(v___y_1566_);
v___x_1571_ = l_Lean_mkAppB(v___y_1566_, v___y_1567_, v___y_1570_);
v___x_1572_ = l_Lean_Expr_app___override(v___y_1569_, v___x_1571_);
v___y_1552_ = v___y_1568_;
v___y_1553_ = v___x_1572_;
goto v___jp_1551_;
}
v___jp_1573_:
{
lean_object* v_upperBound_1579_; lean_object* v___x_1580_; 
v_upperBound_1579_ = lean_ctor_get(v_t_1513_, 1);
lean_inc_ref(v___y_1575_);
v___x_1580_ = l_Lean_Expr_app___override(v___y_1575_, v___y_1578_);
if (lean_obj_tag(v_upperBound_1579_) == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1582_ = l_Lean_Expr_app___override(v___x_1581_, v___y_1574_);
v___x_1583_ = l_Lean_Expr_app___override(v___x_1580_, v___x_1582_);
v___y_1552_ = v___y_1577_;
v___y_1553_ = v___x_1583_;
goto v___jp_1551_;
}
else
{
lean_object* v_val_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v_val_1584_ = lean_ctor_get(v_upperBound_1579_, 0);
v___x_1585_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1586_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1587_ = lean_int_dec_le(v___x_1586_, v_val_1584_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1588_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1589_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1576_);
v___x_1590_ = l_Lean_Name_mkStr2(v___y_1576_, v___x_1589_);
v___x_1591_ = l_Lean_Expr_const___override(v___x_1590_, v___x_1521_);
v___x_1592_ = lean_int_neg(v_val_1584_);
v___x_1593_ = l_Int_toNat(v___x_1592_);
lean_dec(v___x_1592_);
v___x_1594_ = l_Lean_instToExprInt_mkNat(v___x_1593_);
lean_inc_ref(v___y_1574_);
v___x_1595_ = l_Lean_mkApp3(v___x_1588_, v___y_1574_, v___x_1591_, v___x_1594_);
v___y_1566_ = v___x_1585_;
v___y_1567_ = v___y_1574_;
v___y_1568_ = v___y_1577_;
v___y_1569_ = v___x_1580_;
v___y_1570_ = v___x_1595_;
goto v___jp_1565_;
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = l_Int_toNat(v_val_1584_);
v___x_1597_ = l_Lean_instToExprInt_mkNat(v___x_1596_);
v___y_1566_ = v___x_1585_;
v___y_1567_ = v___y_1574_;
v___y_1568_ = v___y_1577_;
v___y_1569_ = v___x_1580_;
v___y_1570_ = v___x_1597_;
goto v___jp_1565_;
}
}
}
v___jp_1598_:
{
lean_object* v___x_1605_; 
lean_inc_ref(v___y_1599_);
lean_inc_ref(v___y_1601_);
v___x_1605_ = l_Lean_mkAppB(v___y_1601_, v___y_1599_, v___y_1604_);
v___y_1574_ = v___y_1599_;
v___y_1575_ = v___y_1600_;
v___y_1576_ = v___y_1602_;
v___y_1577_ = v___y_1603_;
v___y_1578_ = v___x_1605_;
goto v___jp_1573_;
}
v___jp_1606_:
{
lean_object* v_lowerBound_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_type_1611_; 
v_lowerBound_1608_ = lean_ctor_get(v_t_1513_, 0);
v___x_1609_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1610_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1611_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1608_) == 0)
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1574_ = v_type_1611_;
v___y_1575_ = v___x_1609_;
v___y_1576_ = v___x_1610_;
v___y_1577_ = v___y_1607_;
v___y_1578_ = v___x_1612_;
goto v___jp_1573_;
}
else
{
lean_object* v_val_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v_val_1613_ = lean_ctor_get(v_lowerBound_1608_, 0);
v___x_1614_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1615_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1616_ = lean_int_dec_le(v___x_1615_, v_val_1613_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1617_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1618_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1619_ = lean_int_neg(v_val_1613_);
v___x_1620_ = l_Int_toNat(v___x_1619_);
lean_dec(v___x_1619_);
v___x_1621_ = l_Lean_instToExprInt_mkNat(v___x_1620_);
v___x_1622_ = l_Lean_mkApp3(v___x_1617_, v_type_1611_, v___x_1618_, v___x_1621_);
v___y_1599_ = v_type_1611_;
v___y_1600_ = v___x_1609_;
v___y_1601_ = v___x_1614_;
v___y_1602_ = v___x_1610_;
v___y_1603_ = v___y_1607_;
v___y_1604_ = v___x_1622_;
goto v___jp_1598_;
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = l_Int_toNat(v_val_1613_);
v___x_1624_ = l_Lean_instToExprInt_mkNat(v___x_1623_);
v___y_1599_ = v_type_1611_;
v___y_1600_ = v___x_1609_;
v___y_1601_ = v___x_1614_;
v___y_1602_ = v___x_1610_;
v___y_1603_ = v___y_1607_;
v___y_1604_ = v___x_1624_;
goto v___jp_1598_;
}
}
}
v___jp_1629_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_inc_ref(v___y_1630_);
v___x_1633_ = l_Lean_mkAppB(v___y_1630_, v_type_1628_, v___y_1632_);
v___x_1634_ = l_Lean_Expr_app___override(v___y_1631_, v___x_1633_);
v___y_1607_ = v___x_1634_;
goto v___jp_1606_;
}
v___jp_1635_:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Expr_app___override(v___x_1627_, v___y_1636_);
if (lean_obj_tag(v_upperBound_1626_) == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1639_ = l_Lean_Expr_app___override(v___x_1637_, v___x_1638_);
v___y_1607_ = v___x_1639_;
goto v___jp_1606_;
}
else
{
lean_object* v_val_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v_val_1640_ = lean_ctor_get(v_upperBound_1626_, 0);
v___x_1641_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1642_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1643_ = lean_int_dec_le(v___x_1642_, v_val_1640_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1644_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1645_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1646_ = lean_int_neg(v_val_1640_);
v___x_1647_ = l_Int_toNat(v___x_1646_);
lean_dec(v___x_1646_);
v___x_1648_ = l_Lean_instToExprInt_mkNat(v___x_1647_);
v___x_1649_ = l_Lean_mkApp3(v___x_1644_, v_type_1628_, v___x_1645_, v___x_1648_);
v___y_1630_ = v___x_1641_;
v___y_1631_ = v___x_1637_;
v___y_1632_ = v___x_1649_;
goto v___jp_1629_;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = l_Int_toNat(v_val_1640_);
v___x_1651_ = l_Lean_instToExprInt_mkNat(v___x_1650_);
v___y_1630_ = v___x_1641_;
v___y_1631_ = v___x_1637_;
v___y_1632_ = v___x_1651_;
goto v___jp_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___boxed(lean_object* v_s_1668_, lean_object* v_t_1669_, lean_object* v_a_1670_, lean_object* v_x_1671_, lean_object* v_b_1672_, lean_object* v_y_1673_, lean_object* v_v_1674_, lean_object* v_px_1675_, lean_object* v_py_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1668_, v_t_1669_, v_a_1670_, v_x_1671_, v_b_1672_, v_y_1673_, v_v_1674_, v_px_1675_, v_py_1676_);
lean_dec(v_y_1673_);
lean_dec(v_b_1672_);
lean_dec(v_x_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_t_1669_);
lean_dec_ref(v_s_1668_);
return v_res_1677_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_1684_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2));
v___x_1685_ = l_Lean_Expr_const___override(v___x_1684_, v___x_1683_);
return v___x_1685_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = lean_box(0);
v___x_1690_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5));
v___x_1691_ = l_Lean_Expr_const___override(v___x_1690_, v___x_1689_);
return v___x_1691_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_box(0);
v___x_1696_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8));
v___x_1697_ = l_Lean_Expr_const___override(v___x_1696_, v___x_1695_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = lean_box(0);
v___x_1706_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12));
v___x_1707_ = l_Lean_Expr_const___override(v___x_1706_, v___x_1705_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = lean_box(0);
v___x_1715_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15));
v___x_1716_ = l_Lean_Expr_const___override(v___x_1715_, v___x_1714_);
return v___x_1716_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = lean_box(0);
v___x_1723_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18));
v___x_1724_ = l_Lean_Expr_const___override(v___x_1723_, v___x_1722_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1730_ = lean_box(0);
v___x_1731_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21));
v___x_1732_ = l_Lean_Expr_const___override(v___x_1731_, v___x_1730_);
return v___x_1732_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof(lean_object* v_m_1733_, lean_object* v_r_1734_, lean_object* v_i_1735_, lean_object* v_x_1736_, lean_object* v_v_1737_, lean_object* v_w_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v_m_1744_; lean_object* v___y_1746_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_m_1744_ = l_Lean_mkNatLit(v_m_1733_);
v___x_1774_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1775_ = lean_int_dec_le(v___x_1774_, v_r_1734_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1776_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1777_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1778_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1779_ = lean_int_neg(v_r_1734_);
v___x_1780_ = l_Int_toNat(v___x_1779_);
lean_dec(v___x_1779_);
v___x_1781_ = l_Lean_instToExprInt_mkNat(v___x_1780_);
v___x_1782_ = l_Lean_mkApp3(v___x_1776_, v___x_1777_, v___x_1778_, v___x_1781_);
v___y_1746_ = v___x_1782_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = l_Int_toNat(v_r_1734_);
v___x_1784_ = l_Lean_instToExprInt_mkNat(v___x_1783_);
v___y_1746_ = v___x_1784_;
goto v___jp_1745_;
}
v___jp_1745_:
{
lean_object* v_i_1747_; lean_object* v_nil_1748_; lean_object* v_cons_1749_; lean_object* v_x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v_i_1747_ = l_Lean_mkNatLit(v_i_1735_);
v_nil_1748_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1749_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v_x_1750_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1748_, v_cons_1749_, v_x_1736_);
v___x_1751_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3);
v___x_1752_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6);
v___x_1753_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9);
v___x_1754_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13);
lean_inc_ref(v_x_1750_);
v___x_1755_ = l_Lean_Expr_app___override(v___x_1754_, v_x_1750_);
lean_inc_ref(v_i_1747_);
v___x_1756_ = l_Lean_mkApp4(v___x_1751_, v___x_1752_, v___x_1753_, v___x_1755_, v_i_1747_);
v___x_1757_ = l_Lean_Meta_mkDecideProof(v___x_1756_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16);
lean_inc_ref(v_i_1747_);
lean_inc_ref_n(v_v_1737_, 2);
v___x_1760_ = l_Lean_mkAppB(v___x_1759_, v_v_1737_, v_i_1747_);
v___x_1761_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc_ref(v_x_1750_);
lean_inc_ref(v_m_1744_);
v___x_1762_ = l_Lean_mkApp3(v___x_1761_, v_m_1744_, v_x_1750_, v_v_1737_);
v___x_1763_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v___x_1760_, v___x_1762_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1773_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1773_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1773_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1768_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22);
v___x_1769_ = l_Lean_mkApp8(v___x_1768_, v_m_1744_, v___y_1746_, v_i_1747_, v_x_1750_, v_v_1737_, v_a_1758_, v_a_1764_, v_w_1738_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1769_);
v___x_1771_ = v___x_1766_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
else
{
lean_dec(v_a_1758_);
lean_dec_ref(v_x_1750_);
lean_dec_ref(v_i_1747_);
lean_dec_ref(v___y_1746_);
lean_dec_ref(v_m_1744_);
lean_dec_ref(v_w_1738_);
lean_dec_ref(v_v_1737_);
return v___x_1763_;
}
}
else
{
lean_dec_ref(v_x_1750_);
lean_dec_ref(v_i_1747_);
lean_dec_ref(v___y_1746_);
lean_dec_ref(v_m_1744_);
lean_dec_ref(v_w_1738_);
lean_dec_ref(v_v_1737_);
return v___x_1757_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Justification_bmodProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1733_ = stack[0].m_obj;
lean_object* v_r_1734_ = stack[1].m_obj;
lean_object* v_i_1735_ = stack[2].m_obj;
lean_object* v_x_1736_ = stack[3].m_obj;
lean_object* v_v_1737_ = stack[4].m_obj;
lean_object* v_w_1738_ = stack[5].m_obj;
lean_object* v_a_1739_ = stack[6].m_obj;
lean_object* v_a_1740_ = stack[7].m_obj;
lean_object* v_a_1741_ = stack[8].m_obj;
lean_object* v_a_1742_ = stack[9].m_obj;
lean_object* v_res_1785_;
v_res_1785_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1733_, v_r_1734_, v_i_1735_, v_x_1736_, v_v_1737_, v_w_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
stack->m_obj
 = v_res_1785_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___boxed(lean_object* v_m_1786_, lean_object* v_r_1787_, lean_object* v_i_1788_, lean_object* v_x_1789_, lean_object* v_v_1790_, lean_object* v_w_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1786_, v_r_1787_, v_i_1788_, v_x_1789_, v_v_1790_, v_w_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_x_1789_);
lean_dec(v_r_1787_);
return v_res_1797_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0(void){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_instMonadEIO___redArg();
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0);
v___x_1800_ = l_StateRefT_x27_instMonad___redArg(v___x_1799_);
return v___x_1800_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(lean_object* v_c_1805_, lean_object* v_v_1806_, lean_object* v_assumptions_1807_, lean_object* v_x_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, uint8_t v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v___x_1819_; lean_object* v_toApplicative_1820_; lean_object* v_toFunctor_1821_; lean_object* v_toSeq_1822_; lean_object* v_toSeqLeft_1823_; lean_object* v_toSeqRight_1824_; lean_object* v___f_1825_; lean_object* v___f_1826_; lean_object* v___f_1827_; lean_object* v___f_1828_; lean_object* v___x_1829_; lean_object* v___f_1830_; lean_object* v___f_1831_; lean_object* v___f_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v_toApplicative_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1931_; 
v___x_1819_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1);
v_toApplicative_1820_ = lean_ctor_get(v___x_1819_, 0);
v_toFunctor_1821_ = lean_ctor_get(v_toApplicative_1820_, 0);
v_toSeq_1822_ = lean_ctor_get(v_toApplicative_1820_, 2);
v_toSeqLeft_1823_ = lean_ctor_get(v_toApplicative_1820_, 3);
v_toSeqRight_1824_ = lean_ctor_get(v_toApplicative_1820_, 4);
v___f_1825_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2));
v___f_1826_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1821_, 2);
v___f_1827_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1827_, 0, v_toFunctor_1821_);
v___f_1828_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1828_, 0, v_toFunctor_1821_);
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___f_1827_);
lean_ctor_set(v___x_1829_, 1, v___f_1828_);
lean_inc(v_toSeqRight_1824_);
v___f_1830_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1830_, 0, v_toSeqRight_1824_);
lean_inc(v_toSeqLeft_1823_);
v___f_1831_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1831_, 0, v_toSeqLeft_1823_);
lean_inc(v_toSeq_1822_);
v___f_1832_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1832_, 0, v_toSeq_1822_);
v___x_1833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1829_);
lean_ctor_set(v___x_1833_, 1, v___f_1825_);
lean_ctor_set(v___x_1833_, 2, v___f_1832_);
lean_ctor_set(v___x_1833_, 3, v___f_1831_);
lean_ctor_set(v___x_1833_, 4, v___f_1830_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v___f_1826_);
v___x_1835_ = l_StateRefT_x27_instMonad___redArg(v___x_1834_);
v_toApplicative_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v___x_1835_, 1);
lean_dec(v_unused_1932_);
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1931_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_toApplicative_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1931_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v_toFunctor_1840_; lean_object* v_toSeq_1841_; lean_object* v_toSeqLeft_1842_; lean_object* v_toSeqRight_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1929_; 
v_toFunctor_1840_ = lean_ctor_get(v_toApplicative_1836_, 0);
v_toSeq_1841_ = lean_ctor_get(v_toApplicative_1836_, 2);
v_toSeqLeft_1842_ = lean_ctor_get(v_toApplicative_1836_, 3);
v_toSeqRight_1843_ = lean_ctor_get(v_toApplicative_1836_, 4);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_toApplicative_1836_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; 
v_unused_1930_ = lean_ctor_get(v_toApplicative_1836_, 1);
lean_dec(v_unused_1930_);
v___x_1845_ = v_toApplicative_1836_;
v_isShared_1846_ = v_isSharedCheck_1929_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_toSeqRight_1843_);
lean_inc(v_toSeqLeft_1842_);
lean_inc(v_toSeq_1841_);
lean_inc(v_toFunctor_1840_);
lean_dec(v_toApplicative_1836_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1929_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___f_1847_; lean_object* v___f_1848_; lean_object* v___f_1849_; lean_object* v___f_1850_; lean_object* v___x_1851_; lean_object* v___f_1852_; lean_object* v___f_1853_; lean_object* v___f_1854_; lean_object* v___x_1856_; 
v___f_1847_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4));
v___f_1848_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5));
lean_inc_ref(v_toFunctor_1840_);
v___f_1849_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1849_, 0, v_toFunctor_1840_);
v___f_1850_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1850_, 0, v_toFunctor_1840_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___f_1849_);
lean_ctor_set(v___x_1851_, 1, v___f_1850_);
v___f_1852_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1852_, 0, v_toSeqRight_1843_);
v___f_1853_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1853_, 0, v_toSeqLeft_1842_);
v___f_1854_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1854_, 0, v_toSeq_1841_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 4, v___f_1852_);
lean_ctor_set(v___x_1845_, 3, v___f_1853_);
lean_ctor_set(v___x_1845_, 2, v___f_1854_);
lean_ctor_set(v___x_1845_, 1, v___f_1847_);
lean_ctor_set(v___x_1845_, 0, v___x_1851_);
v___x_1856_ = v___x_1845_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v___f_1847_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v___f_1854_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v___f_1853_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v___f_1852_);
v___x_1856_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1858_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 1, v___f_1848_);
lean_ctor_set(v___x_1838_, 0, v___x_1856_);
v___x_1858_ = v___x_1838_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___f_1848_);
v___x_1858_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1859_ = l_StateRefT_x27_instMonad___redArg(v___x_1858_);
v___x_1860_ = l_ReaderT_instMonad___redArg(v___x_1859_);
v___x_1861_ = l_ReaderT_instMonad___redArg(v___x_1860_);
v___x_1862_ = l_StateRefT_x27_instMonad___redArg(v___x_1861_);
v___x_1863_ = l_StateRefT_x27_instMonad___redArg(v___x_1862_);
switch(lean_obj_tag(v_x_1808_))
{
case 0:
{
lean_object* v_i_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_3464__overap_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_dec_ref(v_v_1806_);
v_i_1864_ = lean_ctor_get(v_x_1808_, 2);
lean_inc(v_i_1864_);
lean_dec_ref_known(v_x_1808_, 3);
v___x_1865_ = l_Lean_instInhabitedExpr;
v___x_1866_ = l_instInhabitedOfMonad___redArg(v___x_1863_, v___x_1865_);
v___x_3464__overap_1867_ = lean_array_get(v___x_1866_, v_assumptions_1807_, v_i_1864_);
lean_dec(v_i_1864_);
lean_dec(v___x_1866_);
v___x_1868_ = lean_box(v_a_1812_);
lean_inc(v_a_1817_);
lean_inc_ref(v_a_1816_);
lean_inc(v_a_1815_);
lean_inc_ref(v_a_1814_);
lean_inc(v_a_1813_);
lean_inc_ref(v_a_1811_);
lean_inc(v_a_1810_);
lean_inc(v_a_1809_);
v___x_1869_ = lean_apply_10(v___x_3464__overap_1867_, v_a_1809_, v_a_1810_, v_a_1811_, v___x_1868_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, lean_box(0));
return v___x_1869_;
}
case 1:
{
lean_object* v_s_1870_; lean_object* v_c_1871_; lean_object* v_j_1872_; lean_object* v___x_1873_; 
lean_dec_ref(v___x_1863_);
v_s_1870_ = lean_ctor_get(v_x_1808_, 0);
lean_inc_ref(v_s_1870_);
v_c_1871_ = lean_ctor_get(v_x_1808_, 1);
lean_inc(v_c_1871_);
v_j_1872_ = lean_ctor_get(v_x_1808_, 2);
lean_inc_ref(v_j_1872_);
lean_dec_ref_known(v_x_1808_, 3);
lean_inc_ref(v_v_1806_);
v___x_1873_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1871_, v_v_1806_, v_assumptions_1807_, v_j_1872_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1882_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1870_, v_c_1871_, v_v_1806_, v_a_1874_);
lean_dec(v_c_1871_);
lean_dec_ref(v_s_1870_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1878_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
lean_dec(v_c_1871_);
lean_dec_ref(v_s_1870_);
lean_dec_ref(v_v_1806_);
return v___x_1873_;
}
}
case 2:
{
lean_object* v_s_1883_; lean_object* v_t_1884_; lean_object* v_j_1885_; lean_object* v_k_1886_; lean_object* v___x_1887_; 
lean_dec_ref(v___x_1863_);
v_s_1883_ = lean_ctor_get(v_x_1808_, 0);
lean_inc_ref(v_s_1883_);
v_t_1884_ = lean_ctor_get(v_x_1808_, 1);
lean_inc_ref(v_t_1884_);
v_j_1885_ = lean_ctor_get(v_x_1808_, 3);
lean_inc_ref(v_j_1885_);
v_k_1886_ = lean_ctor_get(v_x_1808_, 4);
lean_inc_ref(v_k_1886_);
lean_dec_ref_known(v_x_1808_, 5);
lean_inc_ref(v_v_1806_);
v___x_1887_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1805_, v_v_1806_, v_assumptions_1807_, v_j_1885_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
lean_inc_ref(v_v_1806_);
v___x_1889_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1805_, v_v_1806_, v_assumptions_1807_, v_k_1886_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1898_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1898_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1898_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1883_, v_t_1884_, v_c_1805_, v_v_1806_, v_a_1888_, v_a_1890_);
lean_dec_ref(v_t_1884_);
lean_dec_ref(v_s_1883_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1894_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
else
{
lean_dec(v_a_1888_);
lean_dec_ref(v_t_1884_);
lean_dec_ref(v_s_1883_);
lean_dec_ref(v_v_1806_);
return v___x_1889_;
}
}
else
{
lean_dec_ref(v_k_1886_);
lean_dec_ref(v_t_1884_);
lean_dec_ref(v_s_1883_);
lean_dec_ref(v_v_1806_);
return v___x_1887_;
}
}
case 3:
{
lean_object* v_s_1899_; lean_object* v_t_1900_; lean_object* v_x_1901_; lean_object* v_y_1902_; lean_object* v_a_1903_; lean_object* v_j_1904_; lean_object* v_b_1905_; lean_object* v_k_1906_; lean_object* v___x_1907_; 
lean_dec_ref(v___x_1863_);
v_s_1899_ = lean_ctor_get(v_x_1808_, 0);
lean_inc_ref(v_s_1899_);
v_t_1900_ = lean_ctor_get(v_x_1808_, 1);
lean_inc_ref(v_t_1900_);
v_x_1901_ = lean_ctor_get(v_x_1808_, 2);
lean_inc(v_x_1901_);
v_y_1902_ = lean_ctor_get(v_x_1808_, 3);
lean_inc(v_y_1902_);
v_a_1903_ = lean_ctor_get(v_x_1808_, 4);
lean_inc(v_a_1903_);
v_j_1904_ = lean_ctor_get(v_x_1808_, 5);
lean_inc_ref(v_j_1904_);
v_b_1905_ = lean_ctor_get(v_x_1808_, 6);
lean_inc(v_b_1905_);
v_k_1906_ = lean_ctor_get(v_x_1808_, 7);
lean_inc_ref(v_k_1906_);
lean_dec_ref_known(v_x_1808_, 8);
lean_inc_ref(v_v_1806_);
v___x_1907_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1901_, v_v_1806_, v_assumptions_1807_, v_j_1904_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1909_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
lean_inc_ref(v_v_1806_);
v___x_1909_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_y_1902_, v_v_1806_, v_assumptions_1807_, v_k_1906_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1918_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1899_, v_t_1900_, v_a_1903_, v_x_1901_, v_b_1905_, v_y_1902_, v_v_1806_, v_a_1908_, v_a_1910_);
lean_dec(v_y_1902_);
lean_dec(v_b_1905_);
lean_dec(v_x_1901_);
lean_dec(v_a_1903_);
lean_dec_ref(v_t_1900_);
lean_dec_ref(v_s_1899_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v___x_1914_);
v___x_1916_ = v___x_1912_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_dec(v_a_1908_);
lean_dec(v_b_1905_);
lean_dec(v_a_1903_);
lean_dec(v_y_1902_);
lean_dec(v_x_1901_);
lean_dec_ref(v_t_1900_);
lean_dec_ref(v_s_1899_);
lean_dec_ref(v_v_1806_);
return v___x_1909_;
}
}
else
{
lean_dec_ref(v_k_1906_);
lean_dec(v_b_1905_);
lean_dec(v_a_1903_);
lean_dec(v_y_1902_);
lean_dec(v_x_1901_);
lean_dec_ref(v_t_1900_);
lean_dec_ref(v_s_1899_);
lean_dec_ref(v_v_1806_);
return v___x_1907_;
}
}
default: 
{
lean_object* v_m_1919_; lean_object* v_r_1920_; lean_object* v_i_1921_; lean_object* v_x_1922_; lean_object* v_j_1923_; lean_object* v___x_1924_; 
lean_dec_ref(v___x_1863_);
v_m_1919_ = lean_ctor_get(v_x_1808_, 0);
lean_inc(v_m_1919_);
v_r_1920_ = lean_ctor_get(v_x_1808_, 1);
lean_inc(v_r_1920_);
v_i_1921_ = lean_ctor_get(v_x_1808_, 2);
lean_inc(v_i_1921_);
v_x_1922_ = lean_ctor_get(v_x_1808_, 3);
lean_inc(v_x_1922_);
v_j_1923_ = lean_ctor_get(v_x_1808_, 4);
lean_inc_ref(v_j_1923_);
lean_dec_ref_known(v_x_1808_, 5);
lean_inc_ref(v_v_1806_);
v___x_1924_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1922_, v_v_1806_, v_assumptions_1807_, v_j_1923_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1926_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v___x_1926_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1919_, v_r_1920_, v_i_1921_, v_x_1922_, v_v_1806_, v_a_1925_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_x_1922_);
lean_dec(v_r_1920_);
return v___x_1926_;
}
else
{
lean_dec(v_x_1922_);
lean_dec(v_i_1921_);
lean_dec(v_r_1920_);
lean_dec(v_m_1919_);
lean_dec_ref(v_v_1806_);
return v___x_1924_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Justification_proof___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1805_ = stack[0].m_obj;
lean_object* v_v_1806_ = stack[1].m_obj;
lean_object* v_assumptions_1807_ = stack[2].m_obj;
lean_object* v_x_1808_ = stack[3].m_obj;
lean_object* v_a_1809_ = stack[4].m_obj;
lean_object* v_a_1810_ = stack[5].m_obj;
lean_object* v_a_1811_ = stack[6].m_obj;
uint8_t v_a_1812_ = stack[7].m_num;
lean_object* v_a_1813_ = stack[8].m_obj;
lean_object* v_a_1814_ = stack[9].m_obj;
lean_object* v_a_1815_ = stack[10].m_obj;
lean_object* v_a_1816_ = stack[11].m_obj;
lean_object* v_a_1817_ = stack[12].m_obj;
lean_object* v_res_1933_;
v_res_1933_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1805_, v_v_1806_, v_assumptions_1807_, v_x_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
stack->m_obj
 = v_res_1933_;
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
lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof(lean_object* v_s_1950_, lean_object* v_c_1951_, lean_object* v_v_1952_, lean_object* v_assumptions_1953_, lean_object* v_x_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, uint8_t v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1951_, v_v_1952_, v_assumptions_1953_, v_x_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Justification_proof_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1950_ = stack[0].m_obj;
lean_object* v_c_1951_ = stack[1].m_obj;
lean_object* v_v_1952_ = stack[2].m_obj;
lean_object* v_assumptions_1953_ = stack[3].m_obj;
lean_object* v_x_1954_ = stack[4].m_obj;
lean_object* v_a_1955_ = stack[5].m_obj;
lean_object* v_a_1956_ = stack[6].m_obj;
lean_object* v_a_1957_ = stack[7].m_obj;
uint8_t v_a_1958_ = stack[8].m_num;
lean_object* v_a_1959_ = stack[9].m_obj;
lean_object* v_a_1960_ = stack[10].m_obj;
lean_object* v_a_1961_ = stack[11].m_obj;
lean_object* v_a_1962_ = stack[12].m_obj;
lean_object* v_a_1963_ = stack[13].m_obj;
lean_object* v_res_1966_;
v_res_1966_ = l_Lean_Elab_Tactic_Omega_Justification_proof(v_s_1950_, v_c_1951_, v_v_1952_, v_assumptions_1953_, v_x_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
stack->m_obj
 = v_res_1966_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___boxed(lean_object* v_s_1967_, lean_object* v_c_1968_, lean_object* v_v_1969_, lean_object* v_assumptions_1970_, lean_object* v_x_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
uint8_t v_a_boxed_1982_; lean_object* v_res_1983_; 
v_a_boxed_1982_ = lean_unbox(v_a_1975_);
v_res_1983_ = l_Lean_Elab_Tactic_Omega_Justification_proof(v_s_1967_, v_c_1968_, v_v_1969_, v_assumptions_1970_, v_x_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_boxed_1982_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_assumptions_1970_);
lean_dec(v_c_1968_);
lean_dec_ref(v_s_1967_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_instToString___lam__0(lean_object* v_f_1984_){
_start:
{
lean_object* v_coeffs_1985_; lean_object* v_constraint_1986_; lean_object* v_justification_1987_; lean_object* v___x_1988_; 
v_coeffs_1985_ = lean_ctor_get(v_f_1984_, 0);
lean_inc(v_coeffs_1985_);
v_constraint_1986_ = lean_ctor_get(v_f_1984_, 1);
lean_inc_ref(v_constraint_1986_);
v_justification_1987_ = lean_ctor_get(v_f_1984_, 2);
lean_inc_ref(v_justification_1987_);
lean_dec_ref(v_f_1984_);
v___x_1988_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_1986_, v_coeffs_1985_, v_justification_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_tidy(lean_object* v_f_1991_){
_start:
{
lean_object* v_coeffs_1992_; lean_object* v_constraint_1993_; lean_object* v_justification_1994_; lean_object* v___x_1995_; 
v_coeffs_1992_ = lean_ctor_get(v_f_1991_, 0);
v_constraint_1993_ = lean_ctor_get(v_f_1991_, 1);
v_justification_1994_ = lean_ctor_get(v_f_1991_, 2);
lean_inc_ref(v_justification_1994_);
lean_inc(v_coeffs_1992_);
lean_inc_ref(v_constraint_1993_);
v___x_1995_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(v_constraint_1993_, v_coeffs_1992_, v_justification_1994_);
if (lean_obj_tag(v___x_1995_) == 0)
{
return v_f_1991_;
}
else
{
lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2007_; 
v_isSharedCheck_2007_ = !lean_is_exclusive(v_f_1991_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; lean_object* v_unused_2009_; lean_object* v_unused_2010_; 
v_unused_2008_ = lean_ctor_get(v_f_1991_, 2);
lean_dec(v_unused_2008_);
v_unused_2009_ = lean_ctor_get(v_f_1991_, 1);
lean_dec(v_unused_2009_);
v_unused_2010_ = lean_ctor_get(v_f_1991_, 0);
lean_dec(v_unused_2010_);
v___x_1997_ = v_f_1991_;
v_isShared_1998_ = v_isSharedCheck_2007_;
goto v_resetjp_1996_;
}
else
{
lean_dec(v_f_1991_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2007_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_val_1999_; lean_object* v_snd_2000_; lean_object* v_fst_2001_; lean_object* v_fst_2002_; lean_object* v_snd_2003_; lean_object* v___x_2005_; 
v_val_1999_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_val_1999_);
lean_dec_ref_known(v___x_1995_, 1);
v_snd_2000_ = lean_ctor_get(v_val_1999_, 1);
lean_inc(v_snd_2000_);
v_fst_2001_ = lean_ctor_get(v_val_1999_, 0);
lean_inc(v_fst_2001_);
lean_dec(v_val_1999_);
v_fst_2002_ = lean_ctor_get(v_snd_2000_, 0);
lean_inc(v_fst_2002_);
v_snd_2003_ = lean_ctor_get(v_snd_2000_, 1);
lean_inc(v_snd_2003_);
lean_dec(v_snd_2000_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 2, v_snd_2003_);
lean_ctor_set(v___x_1997_, 1, v_fst_2001_);
lean_ctor_set(v___x_1997_, 0, v_fst_2002_);
v___x_2005_ = v___x_1997_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_fst_2002_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_fst_2001_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_snd_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_combo(lean_object* v_a_2011_, lean_object* v_f_2012_, lean_object* v_b_2013_, lean_object* v_g_2014_){
_start:
{
lean_object* v_coeffs_2015_; lean_object* v_constraint_2016_; lean_object* v_justification_2017_; lean_object* v_coeffs_2018_; lean_object* v_constraint_2019_; lean_object* v_justification_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2030_; 
v_coeffs_2015_ = lean_ctor_get(v_f_2012_, 0);
lean_inc(v_coeffs_2015_);
v_constraint_2016_ = lean_ctor_get(v_f_2012_, 1);
lean_inc_ref(v_constraint_2016_);
v_justification_2017_ = lean_ctor_get(v_f_2012_, 2);
lean_inc_ref(v_justification_2017_);
lean_dec_ref(v_f_2012_);
v_coeffs_2018_ = lean_ctor_get(v_g_2014_, 0);
v_constraint_2019_ = lean_ctor_get(v_g_2014_, 1);
v_justification_2020_ = lean_ctor_get(v_g_2014_, 2);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_g_2014_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2022_ = v_g_2014_;
v_isShared_2023_ = v_isSharedCheck_2030_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_justification_2020_);
lean_inc(v_constraint_2019_);
lean_inc(v_coeffs_2018_);
lean_dec(v_g_2014_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2030_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
lean_inc(v_coeffs_2018_);
lean_inc(v_coeffs_2015_);
v___x_2024_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_2011_, v_b_2013_, v_coeffs_2015_, v_coeffs_2018_);
lean_inc_ref(v_constraint_2019_);
lean_inc(v_b_2013_);
lean_inc_ref(v_constraint_2016_);
lean_inc(v_a_2011_);
v___x_2025_ = l_Lean_Omega_Constraint_combo(v_a_2011_, v_constraint_2016_, v_b_2013_, v_constraint_2019_);
v___x_2026_ = lean_alloc_ctor(3, 8, 0);
lean_ctor_set(v___x_2026_, 0, v_constraint_2016_);
lean_ctor_set(v___x_2026_, 1, v_constraint_2019_);
lean_ctor_set(v___x_2026_, 2, v_coeffs_2015_);
lean_ctor_set(v___x_2026_, 3, v_coeffs_2018_);
lean_ctor_set(v___x_2026_, 4, v_a_2011_);
lean_ctor_set(v___x_2026_, 5, v_justification_2017_);
lean_ctor_set(v___x_2026_, 6, v_b_2013_);
lean_ctor_set(v___x_2026_, 7, v_justification_2020_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 2, v___x_2026_);
lean_ctor_set(v___x_2022_, 1, v___x_2025_);
lean_ctor_set(v___x_2022_, 0, v___x_2024_);
v___x_2028_ = v___x_2022_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__10));
v___x_2057_ = l_Lean_mkAtom(v___x_2056_);
return v___x_2057_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11);
v___x_2059_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2060_ = lean_array_push(v___x_2059_, v___x_2058_);
return v___x_2060_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2061_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12);
v___x_2062_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9));
v___x_2063_ = lean_box(2);
v___x_2064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v___x_2062_);
lean_ctor_set(v___x_2064_, 2, v___x_2061_);
return v___x_2064_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13);
v___x_2066_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2067_ = lean_array_push(v___x_2066_, v___x_2065_);
return v___x_2067_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2068_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14);
v___x_2069_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7));
v___x_2070_ = lean_box(2);
v___x_2071_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v___x_2069_);
lean_ctor_set(v___x_2071_, 2, v___x_2068_);
return v___x_2071_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16(void){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15);
v___x_2073_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2074_ = lean_array_push(v___x_2073_, v___x_2072_);
return v___x_2074_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2075_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16);
v___x_2076_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5));
v___x_2077_ = lean_box(2);
v___x_2078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v___x_2076_);
lean_ctor_set(v___x_2078_, 2, v___x_2075_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17);
v___x_2080_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2081_ = lean_array_push(v___x_2080_, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2082_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18);
v___x_2083_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2));
v___x_2084_ = lean_box(2);
v___x_2085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v___x_2083_);
lean_ctor_set(v___x_2085_, 2, v___x_2082_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam(void){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19);
return v___x_2086_;
}
}
uint8_t l_Lean_Elab_Tactic_Omega_Problem_isEmpty(lean_object* v_p_2087_){
_start:
{
lean_object* v_constraints_2088_; lean_object* v_size_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v_constraints_2088_ = lean_ctor_get(v_p_2087_, 2);
v_size_2089_ = lean_ctor_get(v_constraints_2088_, 0);
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = lean_nat_dec_eq(v_size_2089_, v___x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2087_ = stack[0].m_obj;
uint8_t v_res_2092_;
v_res_2092_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2087_);
stack->m_num = v_res_2092_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_isEmpty___boxed(lean_object* v_p_2093_){
_start:
{
uint8_t v_res_2094_; lean_object* v_r_2095_; 
v_res_2094_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2093_);
lean_dec_ref(v_p_2093_);
v_r_2095_ = lean_box(v_res_2094_);
return v_r_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object* v_a_2096_, lean_object* v_b_2097_, lean_object* v_d_2098_){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v_a_2096_);
lean_ctor_set(v___x_2099_, 1, v_b_2097_);
v___x_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
lean_ctor_set(v___x_2100_, 1, v_d_2098_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object* v___x_2101_, lean_object* v_x_2102_){
_start:
{
lean_object* v_snd_2103_; lean_object* v_constraint_2104_; lean_object* v_fst_2105_; lean_object* v_lowerBound_2106_; lean_object* v_upperBound_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___y_2112_; lean_object* v___y_2113_; 
v_snd_2103_ = lean_ctor_get(v_x_2102_, 1);
v_constraint_2104_ = lean_ctor_get(v_snd_2103_, 1);
lean_inc_ref(v_constraint_2104_);
v_fst_2105_ = lean_ctor_get(v_x_2102_, 0);
lean_inc(v_fst_2105_);
lean_dec_ref(v_x_2102_);
v_lowerBound_2106_ = lean_ctor_get(v_constraint_2104_, 0);
lean_inc(v_lowerBound_2106_);
v_upperBound_2107_ = lean_ctor_get(v_constraint_2104_, 1);
lean_inc(v_upperBound_2107_);
lean_dec_ref(v_constraint_2104_);
v___x_2108_ = l_List_toString___redArg(v___x_2101_, v_fst_2105_);
v___x_2109_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_2110_ = lean_string_append(v___x_2108_, v___x_2109_);
if (lean_obj_tag(v_lowerBound_2106_) == 0)
{
if (lean_obj_tag(v_upperBound_2107_) == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_2119_ = lean_string_append(v___x_2110_, v___x_2118_);
return v___x_2119_;
}
else
{
lean_object* v_val_2120_; lean_object* v___x_2121_; lean_object* v___y_2123_; lean_object* v_intZero_2128_; uint8_t v_isNeg_2129_; 
v_val_2120_ = lean_ctor_get(v_upperBound_2107_, 0);
lean_inc(v_val_2120_);
lean_dec_ref_known(v_upperBound_2107_, 1);
v___x_2121_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_2128_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2129_ = lean_int_dec_lt(v_val_2120_, v_intZero_2128_);
if (v_isNeg_2129_ == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; 
v_a_2130_ = lean_nat_abs(v_val_2120_);
lean_dec(v_val_2120_);
v___x_2131_ = l_Nat_reprFast(v_a_2130_);
v___y_2123_ = v___x_2131_;
goto v___jp_2122_;
}
else
{
lean_object* v_abs_2132_; lean_object* v_one_2133_; lean_object* v_a_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_abs_2132_ = lean_nat_abs(v_val_2120_);
lean_dec(v_val_2120_);
v_one_2133_ = lean_unsigned_to_nat(1u);
v_a_2134_ = lean_nat_sub(v_abs_2132_, v_one_2133_);
lean_dec(v_abs_2132_);
v___x_2135_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2136_ = lean_nat_add(v_a_2134_, v_one_2133_);
lean_dec(v_a_2134_);
v___x_2137_ = l_Nat_reprFast(v___x_2136_);
v___x_2138_ = lean_string_append(v___x_2135_, v___x_2137_);
lean_dec_ref(v___x_2137_);
v___y_2123_ = v___x_2138_;
goto v___jp_2122_;
}
v___jp_2122_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2124_ = lean_string_append(v___x_2121_, v___y_2123_);
lean_dec_ref(v___y_2123_);
v___x_2125_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2126_ = lean_string_append(v___x_2124_, v___x_2125_);
v___x_2127_ = lean_string_append(v___x_2110_, v___x_2126_);
lean_dec_ref(v___x_2126_);
return v___x_2127_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_2107_) == 0)
{
lean_object* v_val_2139_; lean_object* v___x_2140_; lean_object* v___y_2142_; lean_object* v_intZero_2147_; uint8_t v_isNeg_2148_; 
v_val_2139_ = lean_ctor_get(v_lowerBound_2106_, 0);
lean_inc(v_val_2139_);
lean_dec_ref_known(v_lowerBound_2106_, 1);
v___x_2140_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2147_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2148_ = lean_int_dec_lt(v_val_2139_, v_intZero_2147_);
if (v_isNeg_2148_ == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; 
v_a_2149_ = lean_nat_abs(v_val_2139_);
lean_dec(v_val_2139_);
v___x_2150_ = l_Nat_reprFast(v_a_2149_);
v___y_2142_ = v___x_2150_;
goto v___jp_2141_;
}
else
{
lean_object* v_abs_2151_; lean_object* v_one_2152_; lean_object* v_a_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_abs_2151_ = lean_nat_abs(v_val_2139_);
lean_dec(v_val_2139_);
v_one_2152_ = lean_unsigned_to_nat(1u);
v_a_2153_ = lean_nat_sub(v_abs_2151_, v_one_2152_);
lean_dec(v_abs_2151_);
v___x_2154_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2155_ = lean_nat_add(v_a_2153_, v_one_2152_);
lean_dec(v_a_2153_);
v___x_2156_ = l_Nat_reprFast(v___x_2155_);
v___x_2157_ = lean_string_append(v___x_2154_, v___x_2156_);
lean_dec_ref(v___x_2156_);
v___y_2142_ = v___x_2157_;
goto v___jp_2141_;
}
v___jp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2143_ = lean_string_append(v___x_2140_, v___y_2142_);
lean_dec_ref(v___y_2142_);
v___x_2144_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_2145_ = lean_string_append(v___x_2143_, v___x_2144_);
v___x_2146_ = lean_string_append(v___x_2110_, v___x_2145_);
lean_dec_ref(v___x_2145_);
return v___x_2146_;
}
}
else
{
lean_object* v_val_2158_; lean_object* v_val_2159_; uint8_t v___x_2160_; 
v_val_2158_ = lean_ctor_get(v_lowerBound_2106_, 0);
lean_inc(v_val_2158_);
lean_dec_ref_known(v_lowerBound_2106_, 1);
v_val_2159_ = lean_ctor_get(v_upperBound_2107_, 0);
lean_inc(v_val_2159_);
lean_dec_ref_known(v_upperBound_2107_, 1);
v___x_2160_ = lean_int_dec_lt(v_val_2159_, v_val_2158_);
if (v___x_2160_ == 0)
{
uint8_t v___x_2161_; 
v___x_2161_ = lean_int_dec_eq(v_val_2158_, v_val_2159_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___y_2164_; lean_object* v_intZero_2179_; uint8_t v_isNeg_2180_; 
v___x_2162_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2179_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2180_ = lean_int_dec_lt(v_val_2158_, v_intZero_2179_);
if (v_isNeg_2180_ == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2182_; 
v_a_2181_ = lean_nat_abs(v_val_2158_);
lean_dec(v_val_2158_);
v___x_2182_ = l_Nat_reprFast(v_a_2181_);
v___y_2164_ = v___x_2182_;
goto v___jp_2163_;
}
else
{
lean_object* v_abs_2183_; lean_object* v_one_2184_; lean_object* v_a_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v_abs_2183_ = lean_nat_abs(v_val_2158_);
lean_dec(v_val_2158_);
v_one_2184_ = lean_unsigned_to_nat(1u);
v_a_2185_ = lean_nat_sub(v_abs_2183_, v_one_2184_);
lean_dec(v_abs_2183_);
v___x_2186_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2187_ = lean_nat_add(v_a_2185_, v_one_2184_);
lean_dec(v_a_2185_);
v___x_2188_ = l_Nat_reprFast(v___x_2187_);
v___x_2189_ = lean_string_append(v___x_2186_, v___x_2188_);
lean_dec_ref(v___x_2188_);
v___y_2164_ = v___x_2189_;
goto v___jp_2163_;
}
v___jp_2163_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v_intZero_2168_; uint8_t v_isNeg_2169_; 
v___x_2165_ = lean_string_append(v___x_2162_, v___y_2164_);
lean_dec_ref(v___y_2164_);
v___x_2166_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_2167_ = lean_string_append(v___x_2165_, v___x_2166_);
v_intZero_2168_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2169_ = lean_int_dec_lt(v_val_2159_, v_intZero_2168_);
if (v_isNeg_2169_ == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; 
v_a_2170_ = lean_nat_abs(v_val_2159_);
lean_dec(v_val_2159_);
v___x_2171_ = l_Nat_reprFast(v_a_2170_);
v___y_2112_ = v___x_2167_;
v___y_2113_ = v___x_2171_;
goto v___jp_2111_;
}
else
{
lean_object* v_abs_2172_; lean_object* v_one_2173_; lean_object* v_a_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_abs_2172_ = lean_nat_abs(v_val_2159_);
lean_dec(v_val_2159_);
v_one_2173_ = lean_unsigned_to_nat(1u);
v_a_2174_ = lean_nat_sub(v_abs_2172_, v_one_2173_);
lean_dec(v_abs_2172_);
v___x_2175_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2176_ = lean_nat_add(v_a_2174_, v_one_2173_);
lean_dec(v_a_2174_);
v___x_2177_ = l_Nat_reprFast(v___x_2176_);
v___x_2178_ = lean_string_append(v___x_2175_, v___x_2177_);
lean_dec_ref(v___x_2177_);
v___y_2112_ = v___x_2167_;
v___y_2113_ = v___x_2178_;
goto v___jp_2111_;
}
}
}
else
{
lean_object* v___x_2190_; lean_object* v___y_2192_; lean_object* v_intZero_2197_; uint8_t v_isNeg_2198_; 
lean_dec(v_val_2159_);
v___x_2190_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_2197_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2198_ = lean_int_dec_lt(v_val_2158_, v_intZero_2197_);
if (v_isNeg_2198_ == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; 
v_a_2199_ = lean_nat_abs(v_val_2158_);
lean_dec(v_val_2158_);
v___x_2200_ = l_Nat_reprFast(v_a_2199_);
v___y_2192_ = v___x_2200_;
goto v___jp_2191_;
}
else
{
lean_object* v_abs_2201_; lean_object* v_one_2202_; lean_object* v_a_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v_abs_2201_ = lean_nat_abs(v_val_2158_);
lean_dec(v_val_2158_);
v_one_2202_ = lean_unsigned_to_nat(1u);
v_a_2203_ = lean_nat_sub(v_abs_2201_, v_one_2202_);
lean_dec(v_abs_2201_);
v___x_2204_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2205_ = lean_nat_add(v_a_2203_, v_one_2202_);
lean_dec(v_a_2203_);
v___x_2206_ = l_Nat_reprFast(v___x_2205_);
v___x_2207_ = lean_string_append(v___x_2204_, v___x_2206_);
lean_dec_ref(v___x_2206_);
v___y_2192_ = v___x_2207_;
goto v___jp_2191_;
}
v___jp_2191_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2193_ = lean_string_append(v___x_2190_, v___y_2192_);
lean_dec_ref(v___y_2192_);
v___x_2194_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_2195_ = lean_string_append(v___x_2193_, v___x_2194_);
v___x_2196_ = lean_string_append(v___x_2110_, v___x_2195_);
lean_dec_ref(v___x_2195_);
return v___x_2196_;
}
}
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec(v_val_2159_);
lean_dec(v_val_2158_);
v___x_2208_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_2209_ = lean_string_append(v___x_2110_, v___x_2208_);
return v___x_2209_;
}
}
}
v___jp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2114_ = lean_string_append(v___y_2112_, v___y_2113_);
lean_dec_ref(v___y_2113_);
v___x_2115_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2116_ = lean_string_append(v___x_2114_, v___x_2115_);
v___x_2117_ = lean_string_append(v___x_2110_, v___x_2116_);
lean_dec_ref(v___x_2116_);
return v___x_2117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2(lean_object* v___x_2210_, lean_object* v___f_2211_, lean_object* v_l_2212_, lean_object* v_acc_2213_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2210_, v___f_2211_, v_acc_2213_, v_l_2212_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3(lean_object* v___f_2236_, lean_object* v___f_2237_, lean_object* v_p_2238_){
_start:
{
uint8_t v_possible_2239_; 
v_possible_2239_ = lean_ctor_get_uint8(v_p_2238_, sizeof(void*)*7);
if (v_possible_2239_ == 0)
{
lean_object* v___x_2240_; 
lean_dec_ref(v_p_2238_);
lean_dec_ref(v___f_2237_);
lean_dec_ref(v___f_2236_);
v___x_2240_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
return v___x_2240_;
}
else
{
lean_object* v_constraints_2241_; uint8_t v___x_2242_; 
v_constraints_2241_ = lean_ctor_get(v_p_2238_, 2);
lean_inc_ref(v_constraints_2241_);
v___x_2242_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2238_);
lean_dec_ref(v_p_2238_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; lean_object* v_buckets_2244_; lean_object* v___x_2245_; lean_object* v___y_2247_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2243_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10));
v_buckets_2244_ = lean_ctor_get(v_constraints_2241_, 1);
lean_inc_ref(v_buckets_2244_);
lean_dec_ref(v_constraints_2241_);
v___x_2245_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_array_get_size(v_buckets_2244_);
v___x_2253_ = lean_unsigned_to_nat(0u);
v___x_2254_ = lean_nat_dec_lt(v___x_2253_, v___x_2252_);
if (v___x_2254_ == 0)
{
lean_dec_ref(v_buckets_2244_);
lean_dec_ref(v___f_2237_);
v___y_2247_ = v___x_2251_;
goto v___jp_2246_;
}
else
{
lean_object* v___f_2255_; size_t v___x_2256_; size_t v___x_2257_; lean_object* v___x_2258_; 
v___f_2255_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2), 4, 2);
lean_closure_set(v___f_2255_, 0, v___x_2243_);
lean_closure_set(v___f_2255_, 1, v___f_2237_);
v___x_2256_ = lean_usize_of_nat(v___x_2252_);
v___x_2257_ = ((size_t)0ULL);
v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2243_, v___f_2255_, v_buckets_2244_, v___x_2256_, v___x_2257_, v___x_2251_);
v___y_2247_ = v___x_2258_;
goto v___jp_2246_;
}
v___jp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = lean_box(0);
v___x_2249_ = l_List_mapTR_loop___redArg(v___f_2236_, v___y_2247_, v___x_2248_);
v___x_2250_ = l_String_intercalate(v___x_2245_, v___x_2249_);
return v___x_2250_;
}
}
else
{
lean_object* v___x_2259_; 
lean_dec_ref(v_constraints_2241_);
lean_dec_ref(v___f_2237_);
lean_dec_ref(v___f_2236_);
v___x_2259_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
return v___x_2259_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = lean_box(0);
v___x_2275_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1));
v___x_2276_ = l_Lean_Expr_const___override(v___x_2275_, v___x_2274_);
return v___x_2276_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = lean_box(0);
v___x_2283_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5));
v___x_2284_ = l_Lean_Expr_const___override(v___x_2283_, v___x_2282_);
return v___x_2284_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = lean_box(0);
v___x_2292_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8));
v___x_2293_ = l_Lean_Expr_const___override(v___x_2292_, v___x_2291_);
return v___x_2293_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse(lean_object* v_s_2294_, lean_object* v_x_2295_, lean_object* v_j_2296_, lean_object* v_assumptions_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, uint8_t v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2299_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2310_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc_n(v_a_2309_, 2);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_2295_, v_a_2309_, v_assumptions_2297_, v_j_2296_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2312_; lean_object* v_lowerBound_2313_; lean_object* v_upperBound_2314_; lean_object* v_nil_2315_; lean_object* v_cons_2316_; lean_object* v___x_2317_; lean_object* v___y_2319_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___x_2342_; lean_object* v___y_2344_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2312_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_lowerBound_2313_ = lean_ctor_get(v_s_2294_, 0);
v_upperBound_2314_ = lean_ctor_get(v_s_2294_, 1);
v_nil_2315_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2316_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2317_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2315_, v_cons_2316_, v_x_2295_);
v___x_2342_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
if (lean_obj_tag(v_lowerBound_2313_) == 0)
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_2344_ = v___x_2360_;
goto v___jp_2343_;
}
else
{
lean_object* v_val_2361_; lean_object* v___x_2362_; lean_object* v___y_2364_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v_val_2361_ = lean_ctor_get(v_lowerBound_2313_, 0);
v___x_2362_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2366_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2367_ = lean_int_dec_le(v___x_2366_, v_val_2361_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2368_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2369_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2370_ = lean_int_neg(v_val_2361_);
v___x_2371_ = l_Int_toNat(v___x_2370_);
lean_dec(v___x_2370_);
v___x_2372_ = l_Lean_instToExprInt_mkNat(v___x_2371_);
v___x_2373_ = l_Lean_mkApp3(v___x_2368_, v___x_2312_, v___x_2369_, v___x_2372_);
v___y_2364_ = v___x_2373_;
goto v___jp_2363_;
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = l_Int_toNat(v_val_2361_);
v___x_2375_ = l_Lean_instToExprInt_mkNat(v___x_2374_);
v___y_2364_ = v___x_2375_;
goto v___jp_2363_;
}
v___jp_2363_:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_mkAppB(v___x_2362_, v___x_2312_, v___y_2364_);
v___y_2344_ = v___x_2365_;
goto v___jp_2343_;
}
}
v___jp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2320_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2);
lean_inc_ref(v___y_2319_);
v___x_2321_ = l_Lean_Expr_app___override(v___x_2320_, v___y_2319_);
v___x_2322_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6);
v___x_2323_ = l_Lean_Meta_mkEq(v___x_2321_, v___x_2322_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = l_Lean_Meta_mkDecideProof(v_a_2324_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2335_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2330_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9);
v___x_2331_ = l_Lean_mkApp5(v___x_2330_, v___y_2319_, v_a_2326_, v___x_2317_, v_a_2309_, v_a_2311_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2331_);
v___x_2333_ = v___x_2328_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
else
{
lean_dec_ref(v___y_2319_);
lean_dec_ref(v___x_2317_);
lean_dec(v_a_2311_);
lean_dec(v_a_2309_);
return v___x_2325_;
}
}
else
{
lean_dec_ref(v___y_2319_);
lean_dec_ref(v___x_2317_);
lean_dec(v_a_2311_);
lean_dec(v_a_2309_);
return v___x_2323_;
}
}
v___jp_2336_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_inc_ref(v___y_2337_);
v___x_2340_ = l_Lean_mkAppB(v___y_2337_, v___x_2312_, v___y_2339_);
v___x_2341_ = l_Lean_Expr_app___override(v___y_2338_, v___x_2340_);
v___y_2319_ = v___x_2341_;
goto v___jp_2318_;
}
v___jp_2343_:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Expr_app___override(v___x_2342_, v___y_2344_);
if (lean_obj_tag(v_upperBound_2314_) == 0)
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_2347_ = l_Lean_Expr_app___override(v___x_2345_, v___x_2346_);
v___y_2319_ = v___x_2347_;
goto v___jp_2318_;
}
else
{
lean_object* v_val_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_val_2348_ = lean_ctor_get(v_upperBound_2314_, 0);
v___x_2349_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2350_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2351_ = lean_int_dec_le(v___x_2350_, v_val_2348_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2352_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2353_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2354_ = lean_int_neg(v_val_2348_);
v___x_2355_ = l_Int_toNat(v___x_2354_);
lean_dec(v___x_2354_);
v___x_2356_ = l_Lean_instToExprInt_mkNat(v___x_2355_);
v___x_2357_ = l_Lean_mkApp3(v___x_2352_, v___x_2312_, v___x_2353_, v___x_2356_);
v___y_2337_ = v___x_2349_;
v___y_2338_ = v___x_2345_;
v___y_2339_ = v___x_2357_;
goto v___jp_2336_;
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = l_Int_toNat(v_val_2348_);
v___x_2359_ = l_Lean_instToExprInt_mkNat(v___x_2358_);
v___y_2337_ = v___x_2349_;
v___y_2338_ = v___x_2345_;
v___y_2339_ = v___x_2359_;
goto v___jp_2336_;
}
}
}
}
else
{
lean_dec(v_a_2309_);
return v___x_2310_;
}
}
else
{
lean_dec_ref(v_j_2296_);
return v___x_2308_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_proveFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2294_ = stack[0].m_obj;
lean_object* v_x_2295_ = stack[1].m_obj;
lean_object* v_j_2296_ = stack[2].m_obj;
lean_object* v_assumptions_2297_ = stack[3].m_obj;
lean_object* v_a_2298_ = stack[4].m_obj;
lean_object* v_a_2299_ = stack[5].m_obj;
lean_object* v_a_2300_ = stack[6].m_obj;
uint8_t v_a_2301_ = stack[7].m_num;
lean_object* v_a_2302_ = stack[8].m_obj;
lean_object* v_a_2303_ = stack[9].m_obj;
lean_object* v_a_2304_ = stack[10].m_obj;
lean_object* v_a_2305_ = stack[11].m_obj;
lean_object* v_a_2306_ = stack[12].m_obj;
lean_object* v_res_2376_;
v_res_2376_ = l_Lean_Elab_Tactic_Omega_Problem_proveFalse(v_s_2294_, v_x_2295_, v_j_2296_, v_assumptions_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
stack->m_obj
 = v_res_2376_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed(lean_object* v_s_2377_, lean_object* v_x_2378_, lean_object* v_j_2379_, lean_object* v_assumptions_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
uint8_t v_a_boxed_2391_; lean_object* v_res_2392_; 
v_a_boxed_2391_ = lean_unbox(v_a_2384_);
v_res_2392_ = l_Lean_Elab_Tactic_Omega_Problem_proveFalse(v_s_2377_, v_x_2378_, v_j_2379_, v_assumptions_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_boxed_2391_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_assumptions_2380_);
lean_dec(v_x_2378_);
lean_dec_ref(v_s_2377_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0(lean_object* v_constraint_2393_, lean_object* v_coeffs_2394_, lean_object* v_justification_2395_, lean_object* v_x_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_2393_, v_coeffs_2394_, v_justification_2395_);
return v___x_2397_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(lean_object* v_a_2398_, lean_object* v_x_2399_){
_start:
{
if (lean_obj_tag(v_x_2399_) == 0)
{
uint8_t v___x_2400_; 
v___x_2400_ = 0;
return v___x_2400_;
}
else
{
lean_object* v_key_2401_; lean_object* v_tail_2402_; uint8_t v___x_2403_; 
v_key_2401_ = lean_ctor_get(v_x_2399_, 0);
v_tail_2402_ = lean_ctor_get(v_x_2399_, 2);
v___x_2403_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2401_, v_a_2398_);
if (v___x_2403_ == 0)
{
v_x_2399_ = v_tail_2402_;
goto _start;
}
else
{
return v___x_2403_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2398_ = stack[0].m_obj;
lean_object* v_x_2399_ = stack[1].m_obj;
uint8_t v_res_2405_;
v_res_2405_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2398_, v_x_2399_);
stack->m_num = v_res_2405_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg___boxed(lean_object* v_a_2406_, lean_object* v_x_2407_){
_start:
{
uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_res_2408_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2406_, v_x_2407_);
lean_dec(v_x_2407_);
lean_dec(v_a_2406_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
uint64_t l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(uint64_t v_x_2410_, lean_object* v_x_2411_){
_start:
{
if (lean_obj_tag(v_x_2411_) == 0)
{
return v_x_2410_;
}
else
{
lean_object* v_head_2412_; lean_object* v_tail_2413_; lean_object* v_intZero_2414_; uint8_t v_isNeg_2415_; 
v_head_2412_ = lean_ctor_get(v_x_2411_, 0);
v_tail_2413_ = lean_ctor_get(v_x_2411_, 1);
v_intZero_2414_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2415_ = lean_int_dec_lt(v_head_2412_, v_intZero_2414_);
if (v_isNeg_2415_ == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; uint64_t v___x_2419_; uint64_t v___x_2420_; 
v_a_2416_ = lean_nat_abs(v_head_2412_);
v___x_2417_ = lean_unsigned_to_nat(2u);
v___x_2418_ = lean_nat_mul(v___x_2417_, v_a_2416_);
lean_dec(v_a_2416_);
v___x_2419_ = lean_uint64_of_nat(v___x_2418_);
lean_dec(v___x_2418_);
v___x_2420_ = lean_uint64_mix_hash(v_x_2410_, v___x_2419_);
v_x_2410_ = v___x_2420_;
v_x_2411_ = v_tail_2413_;
goto _start;
}
else
{
lean_object* v_abs_2422_; lean_object* v_one_2423_; lean_object* v_a_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint64_t v___x_2428_; uint64_t v___x_2429_; 
v_abs_2422_ = lean_nat_abs(v_head_2412_);
v_one_2423_ = lean_unsigned_to_nat(1u);
v_a_2424_ = lean_nat_sub(v_abs_2422_, v_one_2423_);
lean_dec(v_abs_2422_);
v___x_2425_ = lean_unsigned_to_nat(2u);
v___x_2426_ = lean_nat_mul(v___x_2425_, v_a_2424_);
lean_dec(v_a_2424_);
v___x_2427_ = lean_nat_add(v___x_2426_, v_one_2423_);
lean_dec(v___x_2426_);
v___x_2428_ = lean_uint64_of_nat(v___x_2427_);
lean_dec(v___x_2427_);
v___x_2429_ = lean_uint64_mix_hash(v_x_2410_, v___x_2428_);
v_x_2410_ = v___x_2429_;
v_x_2411_ = v_tail_2413_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_2410_ = stack[0].m_num;
lean_object* v_x_2411_ = stack[1].m_obj;
uint64_t v_res_2431_;
v_res_2431_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v_x_2410_, v_x_2411_);
stack->m_num = v_res_2431_;
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0___boxed(lean_object* v_x_2432_, lean_object* v_x_2433_){
_start:
{
uint64_t v_x_818__boxed_2434_; uint64_t v_res_2435_; lean_object* v_r_2436_; 
v_x_818__boxed_2434_ = lean_unbox_uint64(v_x_2432_);
lean_dec_ref(v_x_2432_);
v_res_2435_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v_x_818__boxed_2434_, v_x_2433_);
lean_dec(v_x_2433_);
v_r_2436_ = lean_box_uint64(v_res_2435_);
return v_r_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_2437_, lean_object* v_x_2438_){
_start:
{
if (lean_obj_tag(v_x_2438_) == 0)
{
return v_x_2437_;
}
else
{
lean_object* v_key_2439_; lean_object* v_value_2440_; lean_object* v_tail_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2465_; 
v_key_2439_ = lean_ctor_get(v_x_2438_, 0);
v_value_2440_ = lean_ctor_get(v_x_2438_, 1);
v_tail_2441_ = lean_ctor_get(v_x_2438_, 2);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_x_2438_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2443_ = v_x_2438_;
v_isShared_2444_ = v_isSharedCheck_2465_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_tail_2441_);
lean_inc(v_value_2440_);
lean_inc(v_key_2439_);
lean_dec(v_x_2438_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2465_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; uint64_t v___x_2446_; uint64_t v___x_2447_; uint64_t v___x_2448_; uint64_t v___x_2449_; uint64_t v_fold_2450_; uint64_t v___x_2451_; uint64_t v___x_2452_; uint64_t v___x_2453_; size_t v___x_2454_; size_t v___x_2455_; size_t v___x_2456_; size_t v___x_2457_; size_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2445_ = lean_array_get_size(v_x_2437_);
v___x_2446_ = 7ULL;
v___x_2447_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2446_, v_key_2439_);
v___x_2448_ = 32ULL;
v___x_2449_ = lean_uint64_shift_right(v___x_2447_, v___x_2448_);
v_fold_2450_ = lean_uint64_xor(v___x_2447_, v___x_2449_);
v___x_2451_ = 16ULL;
v___x_2452_ = lean_uint64_shift_right(v_fold_2450_, v___x_2451_);
v___x_2453_ = lean_uint64_xor(v_fold_2450_, v___x_2452_);
v___x_2454_ = lean_uint64_to_usize(v___x_2453_);
v___x_2455_ = lean_usize_of_nat(v___x_2445_);
v___x_2456_ = ((size_t)1ULL);
v___x_2457_ = lean_usize_sub(v___x_2455_, v___x_2456_);
v___x_2458_ = lean_usize_land(v___x_2454_, v___x_2457_);
v___x_2459_ = lean_array_uget_borrowed(v_x_2437_, v___x_2458_);
lean_inc(v___x_2459_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 2, v___x_2459_);
v___x_2461_ = v___x_2443_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_key_2439_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_value_2440_);
lean_ctor_set(v_reuseFailAlloc_2464_, 2, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_array_uset(v_x_2437_, v___x_2458_, v___x_2461_);
v_x_2437_ = v___x_2462_;
v_x_2438_ = v_tail_2441_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(lean_object* v_i_2466_, lean_object* v_source_2467_, lean_object* v_target_2468_){
_start:
{
lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2469_ = lean_array_get_size(v_source_2467_);
v___x_2470_ = lean_nat_dec_lt(v_i_2466_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_dec_ref(v_source_2467_);
lean_dec(v_i_2466_);
return v_target_2468_;
}
else
{
lean_object* v_es_2471_; lean_object* v___x_2472_; lean_object* v_source_2473_; lean_object* v_target_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_es_2471_ = lean_array_fget(v_source_2467_, v_i_2466_);
v___x_2472_ = lean_box(0);
v_source_2473_ = lean_array_fset(v_source_2467_, v_i_2466_, v___x_2472_);
v_target_2474_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_target_2468_, v_es_2471_);
v___x_2475_ = lean_unsigned_to_nat(1u);
v___x_2476_ = lean_nat_add(v_i_2466_, v___x_2475_);
lean_dec(v_i_2466_);
v_i_2466_ = v___x_2476_;
v_source_2467_ = v_source_2473_;
v_target_2468_ = v_target_2474_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(lean_object* v_data_2478_){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v_nbuckets_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2479_ = lean_array_get_size(v_data_2478_);
v___x_2480_ = lean_unsigned_to_nat(2u);
v_nbuckets_2481_ = lean_nat_mul(v___x_2479_, v___x_2480_);
v___x_2482_ = lean_unsigned_to_nat(0u);
v___x_2483_ = lean_box(0);
v___x_2484_ = lean_mk_array(v_nbuckets_2481_, v___x_2483_);
v___x_2485_ = lean_array_propagate_mark(v_data_2478_, v___x_2484_);
v___x_2486_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v___x_2482_, v_data_2478_, v___x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(lean_object* v_m_2487_, lean_object* v_a_2488_, lean_object* v_b_2489_){
_start:
{
lean_object* v_size_2490_; lean_object* v_buckets_2491_; lean_object* v___x_2492_; uint64_t v___x_2493_; uint64_t v___x_2494_; uint64_t v___x_2495_; uint64_t v___x_2496_; uint64_t v_fold_2497_; uint64_t v___x_2498_; uint64_t v___x_2499_; uint64_t v___x_2500_; size_t v___x_2501_; size_t v___x_2502_; size_t v___x_2503_; size_t v___x_2504_; size_t v___x_2505_; lean_object* v_bkt_2506_; uint8_t v___x_2507_; 
v_size_2490_ = lean_ctor_get(v_m_2487_, 0);
v_buckets_2491_ = lean_ctor_get(v_m_2487_, 1);
v___x_2492_ = lean_array_get_size(v_buckets_2491_);
v___x_2493_ = 7ULL;
v___x_2494_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2493_, v_a_2488_);
v___x_2495_ = 32ULL;
v___x_2496_ = lean_uint64_shift_right(v___x_2494_, v___x_2495_);
v_fold_2497_ = lean_uint64_xor(v___x_2494_, v___x_2496_);
v___x_2498_ = 16ULL;
v___x_2499_ = lean_uint64_shift_right(v_fold_2497_, v___x_2498_);
v___x_2500_ = lean_uint64_xor(v_fold_2497_, v___x_2499_);
v___x_2501_ = lean_uint64_to_usize(v___x_2500_);
v___x_2502_ = lean_usize_of_nat(v___x_2492_);
v___x_2503_ = ((size_t)1ULL);
v___x_2504_ = lean_usize_sub(v___x_2502_, v___x_2503_);
v___x_2505_ = lean_usize_land(v___x_2501_, v___x_2504_);
v_bkt_2506_ = lean_array_uget_borrowed(v_buckets_2491_, v___x_2505_);
v___x_2507_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2488_, v_bkt_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2528_; 
lean_inc_ref(v_buckets_2491_);
lean_inc(v_size_2490_);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_m_2487_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; lean_object* v_unused_2530_; 
v_unused_2529_ = lean_ctor_get(v_m_2487_, 1);
lean_dec(v_unused_2529_);
v_unused_2530_ = lean_ctor_get(v_m_2487_, 0);
lean_dec(v_unused_2530_);
v___x_2509_ = v_m_2487_;
v_isShared_2510_ = v_isSharedCheck_2528_;
goto v_resetjp_2508_;
}
else
{
lean_dec(v_m_2487_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2528_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2511_; lean_object* v_size_x27_2512_; lean_object* v___x_2513_; lean_object* v_buckets_x27_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; 
v___x_2511_ = lean_unsigned_to_nat(1u);
v_size_x27_2512_ = lean_nat_add(v_size_2490_, v___x_2511_);
lean_dec(v_size_2490_);
lean_inc(v_bkt_2506_);
v___x_2513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2513_, 0, v_a_2488_);
lean_ctor_set(v___x_2513_, 1, v_b_2489_);
lean_ctor_set(v___x_2513_, 2, v_bkt_2506_);
v_buckets_x27_2514_ = lean_array_uset(v_buckets_2491_, v___x_2505_, v___x_2513_);
v___x_2515_ = lean_unsigned_to_nat(4u);
v___x_2516_ = lean_nat_mul(v_size_x27_2512_, v___x_2515_);
v___x_2517_ = lean_unsigned_to_nat(3u);
v___x_2518_ = lean_nat_div(v___x_2516_, v___x_2517_);
lean_dec(v___x_2516_);
v___x_2519_ = lean_array_get_size(v_buckets_x27_2514_);
v___x_2520_ = lean_nat_dec_le(v___x_2518_, v___x_2519_);
lean_dec(v___x_2518_);
if (v___x_2520_ == 0)
{
lean_object* v_val_2521_; lean_object* v___x_2523_; 
v_val_2521_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2514_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 1, v_val_2521_);
lean_ctor_set(v___x_2509_, 0, v_size_x27_2512_);
v___x_2523_ = v___x_2509_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_size_x27_2512_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_val_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
else
{
lean_object* v___x_2526_; 
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 1, v_buckets_x27_2514_);
lean_ctor_set(v___x_2509_, 0, v_size_x27_2512_);
v___x_2526_ = v___x_2509_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_size_x27_2512_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v_buckets_x27_2514_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
else
{
lean_dec(v_b_2489_);
lean_dec(v_a_2488_);
return v_m_2487_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(lean_object* v_a_2531_, lean_object* v_b_2532_, lean_object* v_x_2533_){
_start:
{
if (lean_obj_tag(v_x_2533_) == 0)
{
lean_dec(v_b_2532_);
lean_dec(v_a_2531_);
return v_x_2533_;
}
else
{
lean_object* v_key_2534_; lean_object* v_value_2535_; lean_object* v_tail_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2548_; 
v_key_2534_ = lean_ctor_get(v_x_2533_, 0);
v_value_2535_ = lean_ctor_get(v_x_2533_, 1);
v_tail_2536_ = lean_ctor_get(v_x_2533_, 2);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_x_2533_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2538_ = v_x_2533_;
v_isShared_2539_ = v_isSharedCheck_2548_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_tail_2536_);
lean_inc(v_value_2535_);
lean_inc(v_key_2534_);
lean_dec(v_x_2533_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2548_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
uint8_t v___x_2540_; 
v___x_2540_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2534_, v_a_2531_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2541_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2531_, v_b_2532_, v_tail_2536_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 2, v___x_2541_);
v___x_2543_ = v___x_2538_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_key_2534_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_value_2535_);
lean_ctor_set(v_reuseFailAlloc_2544_, 2, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
else
{
lean_object* v___x_2546_; 
lean_dec(v_value_2535_);
lean_dec(v_key_2534_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 1, v_b_2532_);
lean_ctor_set(v___x_2538_, 0, v_a_2531_);
v___x_2546_ = v___x_2538_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2531_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_b_2532_);
lean_ctor_set(v_reuseFailAlloc_2547_, 2, v_tail_2536_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(lean_object* v_m_2549_, lean_object* v_a_2550_, lean_object* v_b_2551_){
_start:
{
lean_object* v_size_2552_; lean_object* v_buckets_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2597_; 
v_size_2552_ = lean_ctor_get(v_m_2549_, 0);
v_buckets_2553_ = lean_ctor_get(v_m_2549_, 1);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_m_2549_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2555_ = v_m_2549_;
v_isShared_2556_ = v_isSharedCheck_2597_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_buckets_2553_);
lean_inc(v_size_2552_);
lean_dec(v_m_2549_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2597_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; uint64_t v___x_2558_; uint64_t v___x_2559_; uint64_t v___x_2560_; uint64_t v___x_2561_; uint64_t v_fold_2562_; uint64_t v___x_2563_; uint64_t v___x_2564_; uint64_t v___x_2565_; size_t v___x_2566_; size_t v___x_2567_; size_t v___x_2568_; size_t v___x_2569_; size_t v___x_2570_; lean_object* v_bkt_2571_; uint8_t v___x_2572_; 
v___x_2557_ = lean_array_get_size(v_buckets_2553_);
v___x_2558_ = 7ULL;
v___x_2559_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2558_, v_a_2550_);
v___x_2560_ = 32ULL;
v___x_2561_ = lean_uint64_shift_right(v___x_2559_, v___x_2560_);
v_fold_2562_ = lean_uint64_xor(v___x_2559_, v___x_2561_);
v___x_2563_ = 16ULL;
v___x_2564_ = lean_uint64_shift_right(v_fold_2562_, v___x_2563_);
v___x_2565_ = lean_uint64_xor(v_fold_2562_, v___x_2564_);
v___x_2566_ = lean_uint64_to_usize(v___x_2565_);
v___x_2567_ = lean_usize_of_nat(v___x_2557_);
v___x_2568_ = ((size_t)1ULL);
v___x_2569_ = lean_usize_sub(v___x_2567_, v___x_2568_);
v___x_2570_ = lean_usize_land(v___x_2566_, v___x_2569_);
v_bkt_2571_ = lean_array_uget_borrowed(v_buckets_2553_, v___x_2570_);
v___x_2572_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2550_, v_bkt_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; lean_object* v_size_x27_2574_; lean_object* v___x_2575_; lean_object* v_buckets_x27_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2573_ = lean_unsigned_to_nat(1u);
v_size_x27_2574_ = lean_nat_add(v_size_2552_, v___x_2573_);
lean_dec(v_size_2552_);
lean_inc(v_bkt_2571_);
v___x_2575_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2575_, 0, v_a_2550_);
lean_ctor_set(v___x_2575_, 1, v_b_2551_);
lean_ctor_set(v___x_2575_, 2, v_bkt_2571_);
v_buckets_x27_2576_ = lean_array_uset(v_buckets_2553_, v___x_2570_, v___x_2575_);
v___x_2577_ = lean_unsigned_to_nat(4u);
v___x_2578_ = lean_nat_mul(v_size_x27_2574_, v___x_2577_);
v___x_2579_ = lean_unsigned_to_nat(3u);
v___x_2580_ = lean_nat_div(v___x_2578_, v___x_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_array_get_size(v_buckets_x27_2576_);
v___x_2582_ = lean_nat_dec_le(v___x_2580_, v___x_2581_);
lean_dec(v___x_2580_);
if (v___x_2582_ == 0)
{
lean_object* v_val_2583_; lean_object* v___x_2585_; 
v_val_2583_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2576_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 1, v_val_2583_);
lean_ctor_set(v___x_2555_, 0, v_size_x27_2574_);
v___x_2585_ = v___x_2555_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_size_x27_2574_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_val_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
else
{
lean_object* v___x_2588_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 1, v_buckets_x27_2576_);
lean_ctor_set(v___x_2555_, 0, v_size_x27_2574_);
v___x_2588_ = v___x_2555_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_size_x27_2574_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_buckets_x27_2576_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
else
{
lean_object* v___x_2590_; lean_object* v_buckets_x27_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
lean_inc(v_bkt_2571_);
v___x_2590_ = lean_box(0);
v_buckets_x27_2591_ = lean_array_uset(v_buckets_2553_, v___x_2570_, v___x_2590_);
v___x_2592_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2550_, v_b_2551_, v_bkt_2571_);
v___x_2593_ = lean_array_uset(v_buckets_x27_2591_, v___x_2570_, v___x_2592_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 1, v___x_2593_);
v___x_2595_ = v___x_2555_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_size_2552_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(lean_object* v_p_2598_, lean_object* v_x_2599_){
_start:
{
lean_object* v_coeffs_2600_; lean_object* v_constraint_2601_; lean_object* v_justification_2602_; uint8_t v___x_2603_; 
v_coeffs_2600_ = lean_ctor_get(v_x_2599_, 0);
lean_inc(v_coeffs_2600_);
v_constraint_2601_ = lean_ctor_get(v_x_2599_, 1);
lean_inc_ref(v_constraint_2601_);
v_justification_2602_ = lean_ctor_get(v_x_2599_, 2);
v___x_2603_ = l_Lean_Omega_Constraint_isImpossible(v_constraint_2601_);
if (v___x_2603_ == 0)
{
lean_object* v_assumptions_2604_; lean_object* v_numVars_2605_; lean_object* v_constraints_2606_; lean_object* v_equalities_2607_; lean_object* v_eliminations_2608_; uint8_t v_possible_2609_; lean_object* v_proveFalse_x3f_2610_; lean_object* v_explanation_x3f_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2629_; 
v_assumptions_2604_ = lean_ctor_get(v_p_2598_, 0);
v_numVars_2605_ = lean_ctor_get(v_p_2598_, 1);
v_constraints_2606_ = lean_ctor_get(v_p_2598_, 2);
v_equalities_2607_ = lean_ctor_get(v_p_2598_, 3);
v_eliminations_2608_ = lean_ctor_get(v_p_2598_, 4);
v_possible_2609_ = lean_ctor_get_uint8(v_p_2598_, sizeof(void*)*7);
v_proveFalse_x3f_2610_ = lean_ctor_get(v_p_2598_, 5);
v_explanation_x3f_2611_ = lean_ctor_get(v_p_2598_, 6);
v_isSharedCheck_2629_ = !lean_is_exclusive(v_p_2598_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2613_ = v_p_2598_;
v_isShared_2614_ = v_isSharedCheck_2629_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_explanation_x3f_2611_);
lean_inc(v_proveFalse_x3f_2610_);
lean_inc(v_eliminations_2608_);
lean_inc(v_equalities_2607_);
lean_inc(v_constraints_2606_);
lean_inc(v_numVars_2605_);
lean_inc(v_assumptions_2604_);
lean_dec(v_p_2598_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2629_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___y_2616_; lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = l_List_lengthTR___redArg(v_coeffs_2600_);
v___x_2628_ = lean_nat_dec_le(v_numVars_2605_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_dec(v___x_2627_);
v___y_2616_ = v_numVars_2605_;
goto v___jp_2615_;
}
else
{
lean_dec(v_numVars_2605_);
v___y_2616_ = v___x_2627_;
goto v___jp_2615_;
}
v___jp_2615_:
{
lean_object* v___x_2617_; uint8_t v___x_2618_; 
lean_inc(v_coeffs_2600_);
v___x_2617_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_constraints_2606_, v_coeffs_2600_, v_x_2599_);
v___x_2618_ = l_Lean_Omega_Constraint_isExact(v_constraint_2601_);
lean_dec_ref(v_constraint_2601_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2620_; 
lean_dec(v_coeffs_2600_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 2, v___x_2617_);
lean_ctor_set(v___x_2613_, 1, v___y_2616_);
v___x_2620_ = v___x_2613_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_assumptions_2604_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v___y_2616_);
lean_ctor_set(v_reuseFailAlloc_2621_, 2, v___x_2617_);
lean_ctor_set(v_reuseFailAlloc_2621_, 3, v_equalities_2607_);
lean_ctor_set(v_reuseFailAlloc_2621_, 4, v_eliminations_2608_);
lean_ctor_set(v_reuseFailAlloc_2621_, 5, v_proveFalse_x3f_2610_);
lean_ctor_set(v_reuseFailAlloc_2621_, 6, v_explanation_x3f_2611_);
lean_ctor_set_uint8(v_reuseFailAlloc_2621_, sizeof(void*)*7, v_possible_2609_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2622_ = lean_box(0);
v___x_2623_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_equalities_2607_, v_coeffs_2600_, v___x_2622_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 3, v___x_2623_);
lean_ctor_set(v___x_2613_, 2, v___x_2617_);
lean_ctor_set(v___x_2613_, 1, v___y_2616_);
v___x_2625_ = v___x_2613_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_assumptions_2604_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v___y_2616_);
lean_ctor_set(v_reuseFailAlloc_2626_, 2, v___x_2617_);
lean_ctor_set(v_reuseFailAlloc_2626_, 3, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2626_, 4, v_eliminations_2608_);
lean_ctor_set(v_reuseFailAlloc_2626_, 5, v_proveFalse_x3f_2610_);
lean_ctor_set(v_reuseFailAlloc_2626_, 6, v_explanation_x3f_2611_);
lean_ctor_set_uint8(v_reuseFailAlloc_2626_, sizeof(void*)*7, v_possible_2609_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
else
{
lean_object* v_assumptions_2630_; lean_object* v_numVars_2631_; lean_object* v_constraints_2632_; lean_object* v_equalities_2633_; lean_object* v_eliminations_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2646_; 
lean_inc_ref(v_justification_2602_);
lean_dec_ref(v_x_2599_);
v_assumptions_2630_ = lean_ctor_get(v_p_2598_, 0);
v_numVars_2631_ = lean_ctor_get(v_p_2598_, 1);
v_constraints_2632_ = lean_ctor_get(v_p_2598_, 2);
v_equalities_2633_ = lean_ctor_get(v_p_2598_, 3);
v_eliminations_2634_ = lean_ctor_get(v_p_2598_, 4);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_p_2598_);
if (v_isSharedCheck_2646_ == 0)
{
lean_object* v_unused_2647_; lean_object* v_unused_2648_; 
v_unused_2647_ = lean_ctor_get(v_p_2598_, 6);
lean_dec(v_unused_2647_);
v_unused_2648_ = lean_ctor_get(v_p_2598_, 5);
lean_dec(v_unused_2648_);
v___x_2636_ = v_p_2598_;
v_isShared_2637_ = v_isSharedCheck_2646_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_eliminations_2634_);
lean_inc(v_equalities_2633_);
lean_inc(v_constraints_2632_);
lean_inc(v_numVars_2631_);
lean_inc(v_assumptions_2630_);
lean_dec(v_p_2598_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2646_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___f_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2644_; 
lean_inc_ref(v_justification_2602_);
lean_inc(v_coeffs_2600_);
lean_inc_ref(v_constraint_2601_);
v___f_2638_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0), 4, 3);
lean_closure_set(v___f_2638_, 0, v_constraint_2601_);
lean_closure_set(v___f_2638_, 1, v_coeffs_2600_);
lean_closure_set(v___f_2638_, 2, v_justification_2602_);
v___x_2639_ = 0;
lean_inc_ref(v_assumptions_2630_);
v___x_2640_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed), 14, 4);
lean_closure_set(v___x_2640_, 0, v_constraint_2601_);
lean_closure_set(v___x_2640_, 1, v_coeffs_2600_);
lean_closure_set(v___x_2640_, 2, v_justification_2602_);
lean_closure_set(v___x_2640_, 3, v_assumptions_2630_);
v___x_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
v___x_2642_ = lean_mk_thunk(v___f_2638_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 6, v___x_2642_);
lean_ctor_set(v___x_2636_, 5, v___x_2641_);
v___x_2644_ = v___x_2636_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_assumptions_2630_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v_numVars_2631_);
lean_ctor_set(v_reuseFailAlloc_2645_, 2, v_constraints_2632_);
lean_ctor_set(v_reuseFailAlloc_2645_, 3, v_equalities_2633_);
lean_ctor_set(v_reuseFailAlloc_2645_, 4, v_eliminations_2634_);
lean_ctor_set(v_reuseFailAlloc_2645_, 5, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2645_, 6, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_ctor_set_uint8(v___x_2644_, sizeof(void*)*7, v___x_2639_);
return v___x_2644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0(lean_object* v_00_u03b2_2649_, lean_object* v_m_2650_, lean_object* v_a_2651_, lean_object* v_b_2652_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_m_2650_, v_a_2651_, v_b_2652_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1(lean_object* v_00_u03b2_2654_, lean_object* v_m_2655_, lean_object* v_a_2656_, lean_object* v_b_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_m_2655_, v_a_2656_, v_b_2657_);
return v___x_2658_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_object* v_00_u03b2_2659_, lean_object* v_a_2660_, lean_object* v_x_2661_){
_start:
{
uint8_t v___x_2662_; 
v___x_2662_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2660_, v_x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2660_ = stack[1].m_obj;
lean_object* v_x_2661_ = stack[2].m_obj;
uint8_t v_res_2663_;
v_res_2663_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_box(0), v_a_2660_, v_x_2661_);
stack->m_num = v_res_2663_;
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
lean_dec_ref_known(v___x_2727_, 1);
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
lean_dec_ref_known(v_x_2768_, 3);
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
lean_object* v_val_2775_; lean_object* v_key_2776_; lean_object* v_tail_2777_; lean_object* v_fst_2778_; lean_object* v_snd_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2800_; 
v_val_2775_ = lean_ctor_get(v_x_2767_, 0);
lean_inc(v_val_2775_);
v_key_2776_ = lean_ctor_get(v_x_2768_, 0);
lean_inc(v_key_2776_);
v_tail_2777_ = lean_ctor_get(v_x_2768_, 2);
lean_inc(v_tail_2777_);
lean_dec_ref_known(v_x_2768_, 3);
v_fst_2778_ = lean_ctor_get(v_val_2775_, 0);
v_snd_2779_ = lean_ctor_get(v_val_2775_, 1);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_val_2775_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2781_ = v_val_2775_;
v_isShared_2782_ = v_isSharedCheck_2800_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_snd_2779_);
lean_inc(v_fst_2778_);
lean_dec(v_val_2775_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2800_;
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
lean_object* v_m_x27_2786_; uint8_t v___x_2793_; 
lean_inc(v_key_2776_);
v_m_x27_2786_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2776_);
v___x_2793_ = lean_nat_dec_lt(v_m_x27_2786_, v_snd_2779_);
if (v___x_2793_ == 0)
{
uint8_t v___x_2794_; 
v___x_2794_ = lean_nat_dec_eq(v_m_x27_2786_, v_snd_2779_);
lean_dec(v_snd_2779_);
if (v___x_2794_ == 0)
{
lean_dec(v_m_x27_2786_);
lean_del_object(v___x_2781_);
lean_dec(v_fst_2778_);
lean_dec(v_key_2776_);
v_x_2768_ = v_tail_2777_;
goto _start;
}
else
{
lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
lean_inc(v_key_2776_);
v___x_2796_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_key_2776_);
v___x_2797_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_fst_2778_);
v___x_2798_ = lean_nat_dec_lt(v___x_2796_, v___x_2797_);
lean_dec(v___x_2797_);
lean_dec(v___x_2796_);
if (v___x_2798_ == 0)
{
lean_dec(v_m_x27_2786_);
lean_del_object(v___x_2781_);
lean_dec(v_key_2776_);
v_x_2768_ = v_tail_2777_;
goto _start;
}
else
{
lean_dec_ref_known(v_x_2767_, 1);
goto v___jp_2787_;
}
}
}
else
{
lean_dec(v_snd_2779_);
lean_dec(v_fst_2778_);
lean_dec_ref_known(v_x_2767_, 1);
goto v___jp_2787_;
}
v___jp_2787_:
{
lean_object* v___x_2789_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 1, v_m_x27_2786_);
lean_ctor_set(v___x_2781_, 0, v_key_2776_);
v___x_2789_ = v___x_2781_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_key_2776_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_m_x27_2786_);
v___x_2789_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2790_; 
v___x_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
v_x_2767_ = v___x_2790_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(lean_object* v_as_2801_, size_t v_i_2802_, size_t v_stop_2803_, lean_object* v_b_2804_){
_start:
{
uint8_t v___x_2805_; 
v___x_2805_ = lean_usize_dec_eq(v_i_2802_, v_stop_2803_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; lean_object* v___x_2807_; size_t v___x_2808_; size_t v___x_2809_; 
v___x_2806_ = lean_array_uget_borrowed(v_as_2801_, v_i_2802_);
lean_inc(v___x_2806_);
v___x_2807_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(v_b_2804_, v___x_2806_);
v___x_2808_ = ((size_t)1ULL);
v___x_2809_ = lean_usize_add(v_i_2802_, v___x_2808_);
v_i_2802_ = v___x_2809_;
v_b_2804_ = v___x_2807_;
goto _start;
}
else
{
return v_b_2804_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2801_ = stack[0].m_obj;
size_t v_i_2802_ = stack[1].m_num;
size_t v_stop_2803_ = stack[2].m_num;
lean_object* v_b_2804_ = stack[3].m_obj;
lean_object* v_res_2811_;
v_res_2811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_as_2801_, v_i_2802_, v_stop_2803_, v_b_2804_);
stack->m_obj
 = v_res_2811_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1___boxed(lean_object* v_as_2812_, lean_object* v_i_2813_, lean_object* v_stop_2814_, lean_object* v_b_2815_){
_start:
{
size_t v_i_boxed_2816_; size_t v_stop_boxed_2817_; lean_object* v_res_2818_; 
v_i_boxed_2816_ = lean_unbox_usize(v_i_2813_);
lean_dec(v_i_2813_);
v_stop_boxed_2817_ = lean_unbox_usize(v_stop_2814_);
lean_dec(v_stop_2814_);
v_res_2818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_as_2812_, v_i_boxed_2816_, v_stop_boxed_2817_, v_b_2815_);
lean_dec_ref(v_as_2812_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality(lean_object* v_p_2819_){
_start:
{
lean_object* v_equalities_2820_; lean_object* v_buckets_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; 
v_equalities_2820_ = lean_ctor_get(v_p_2819_, 3);
v_buckets_2821_ = lean_ctor_get(v_equalities_2820_, 1);
v___x_2822_ = lean_box(0);
v___x_2823_ = lean_unsigned_to_nat(0u);
v___x_2824_ = lean_array_get_size(v_buckets_2821_);
v___x_2825_ = lean_nat_dec_lt(v___x_2823_, v___x_2824_);
if (v___x_2825_ == 0)
{
return v___x_2822_;
}
else
{
size_t v___x_2826_; size_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = ((size_t)0ULL);
v___x_2827_ = lean_usize_of_nat(v___x_2824_);
v___x_2828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2821_, v___x_2826_, v___x_2827_, v___x_2822_);
return v___x_2828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality___boxed(lean_object* v_p_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_2829_);
lean_dec_ref(v_p_2829_);
return v_res_2830_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = lean_unsigned_to_nat(1u);
v___x_2832_ = lean_nat_to_int(v___x_2831_);
return v___x_2832_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2834_ = lean_int_neg(v___x_2833_);
return v___x_2834_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(lean_object* v_as_2835_, size_t v_i_2836_, size_t v_stop_2837_, lean_object* v_b_2838_){
_start:
{
uint8_t v___x_2839_; 
v___x_2839_ = lean_usize_dec_eq(v_i_2836_, v_stop_2837_);
if (v___x_2839_ == 0)
{
size_t v___x_2840_; size_t v___x_2841_; lean_object* v___x_2842_; lean_object* v_snd_2843_; lean_object* v_fst_2844_; lean_object* v_fst_2845_; lean_object* v_snd_2846_; lean_object* v_coeffs_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2840_ = ((size_t)1ULL);
v___x_2841_ = lean_usize_sub(v_i_2836_, v___x_2840_);
v___x_2842_ = lean_array_uget_borrowed(v_as_2835_, v___x_2841_);
v_snd_2843_ = lean_ctor_get(v___x_2842_, 1);
v_fst_2844_ = lean_ctor_get(v___x_2842_, 0);
v_fst_2845_ = lean_ctor_get(v_snd_2843_, 0);
v_snd_2846_ = lean_ctor_get(v_snd_2843_, 1);
v_coeffs_2847_ = lean_ctor_get(v_b_2838_, 0);
lean_inc(v_fst_2845_);
v___x_2848_ = l_Lean_Omega_IntList_get(v_coeffs_2847_, v_fst_2845_);
v___x_2849_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2850_ = lean_int_dec_eq(v___x_2848_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2851_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2852_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2853_ = lean_int_mul(v___x_2852_, v_snd_2846_);
v___x_2854_ = lean_int_mul(v___x_2853_, v___x_2848_);
lean_dec(v___x_2848_);
lean_dec(v___x_2853_);
lean_inc(v_fst_2844_);
v___x_2855_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v___x_2854_, v_fst_2844_, v___x_2851_, v_b_2838_);
v_i_2836_ = v___x_2841_;
v_b_2838_ = v___x_2855_;
goto _start;
}
else
{
lean_dec(v___x_2848_);
v_i_2836_ = v___x_2841_;
goto _start;
}
}
else
{
return v_b_2838_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2835_ = stack[0].m_obj;
size_t v_i_2836_ = stack[1].m_num;
size_t v_stop_2837_ = stack[2].m_num;
lean_object* v_b_2838_ = stack[3].m_obj;
lean_object* v_res_2858_;
v_res_2858_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v_as_2835_, v_i_2836_, v_stop_2837_, v_b_2838_);
stack->m_obj
 = v_res_2858_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___boxed(lean_object* v_as_2859_, lean_object* v_i_2860_, lean_object* v_stop_2861_, lean_object* v_b_2862_){
_start:
{
size_t v_i_boxed_2863_; size_t v_stop_boxed_2864_; lean_object* v_res_2865_; 
v_i_boxed_2863_ = lean_unbox_usize(v_i_2860_);
lean_dec(v_i_2860_);
v_stop_boxed_2864_ = lean_unbox_usize(v_stop_2861_);
lean_dec(v_stop_2861_);
v_res_2865_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v_as_2859_, v_i_boxed_2863_, v_stop_boxed_2864_, v_b_2862_);
lean_dec_ref(v_as_2859_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(lean_object* v_init_2866_, lean_object* v_l_2867_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2868_ = lean_array_mk(v_l_2867_);
v___x_2869_ = lean_array_get_size(v___x_2868_);
v___x_2870_ = lean_unsigned_to_nat(0u);
v___x_2871_ = lean_nat_dec_lt(v___x_2870_, v___x_2869_);
if (v___x_2871_ == 0)
{
lean_dec_ref(v___x_2868_);
return v_init_2866_;
}
else
{
size_t v___x_2872_; size_t v___x_2873_; lean_object* v___x_2874_; 
v___x_2872_ = lean_usize_of_nat(v___x_2869_);
v___x_2873_ = ((size_t)0ULL);
v___x_2874_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v___x_2868_, v___x_2872_, v___x_2873_, v_init_2866_);
lean_dec_ref(v___x_2868_);
return v___x_2874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(lean_object* v_p_2875_, lean_object* v_f_2876_){
_start:
{
lean_object* v_eliminations_2877_; lean_object* v___x_2878_; 
v_eliminations_2877_ = lean_ctor_get(v_p_2875_, 4);
lean_inc(v_eliminations_2877_);
lean_dec_ref(v_p_2875_);
v___x_2878_ = l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(v_f_2876_, v_eliminations_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__0(lean_object* v_x_2879_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(lean_object* v___y_2881_, lean_object* v_sign_2882_, lean_object* v_val_2883_, lean_object* v_x_2884_, lean_object* v_x_2885_){
_start:
{
if (lean_obj_tag(v_x_2885_) == 0)
{
lean_dec_ref(v_val_2883_);
lean_dec(v___y_2881_);
return v_x_2884_;
}
else
{
lean_object* v_key_2886_; lean_object* v_value_2887_; lean_object* v_tail_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; 
v_key_2886_ = lean_ctor_get(v_x_2885_, 0);
lean_inc(v_key_2886_);
v_value_2887_ = lean_ctor_get(v_x_2885_, 1);
lean_inc(v_value_2887_);
v_tail_2888_ = lean_ctor_get(v_x_2885_, 2);
lean_inc(v_tail_2888_);
lean_dec_ref_known(v_x_2885_, 3);
lean_inc(v___y_2881_);
v___x_2889_ = l_Lean_Omega_IntList_get(v_key_2886_, v___y_2881_);
lean_dec(v_key_2886_);
v___x_2890_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2891_ = lean_int_dec_eq(v___x_2889_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v_k_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2892_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2893_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2894_ = lean_int_mul(v___x_2893_, v_sign_2882_);
v_k_2895_ = lean_int_mul(v___x_2894_, v___x_2889_);
lean_dec(v___x_2889_);
lean_dec(v___x_2894_);
lean_inc_ref(v_val_2883_);
v___x_2896_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_k_2895_, v_val_2883_, v___x_2892_, v_value_2887_);
v___x_2897_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_2896_);
v___x_2898_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2884_, v___x_2897_);
v_x_2884_ = v___x_2898_;
v_x_2885_ = v_tail_2888_;
goto _start;
}
else
{
lean_object* v___x_2900_; 
lean_dec(v___x_2889_);
v___x_2900_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2884_, v_value_2887_);
v_x_2884_ = v___x_2900_;
v_x_2885_ = v_tail_2888_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0___boxed(lean_object* v___y_2902_, lean_object* v_sign_2903_, lean_object* v_val_2904_, lean_object* v_x_2905_, lean_object* v_x_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2902_, v_sign_2903_, v_val_2904_, v_x_2905_, v_x_2906_);
lean_dec(v_sign_2903_);
return v_res_2907_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object* v___y_2908_, lean_object* v_sign_2909_, lean_object* v_val_2910_, lean_object* v_as_2911_, size_t v_i_2912_, size_t v_stop_2913_, lean_object* v_b_2914_){
_start:
{
uint8_t v___x_2915_; 
v___x_2915_ = lean_usize_dec_eq(v_i_2912_, v_stop_2913_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; size_t v___x_2918_; size_t v___x_2919_; 
v___x_2916_ = lean_array_uget_borrowed(v_as_2911_, v_i_2912_);
lean_inc(v___x_2916_);
lean_inc_ref(v_val_2910_);
lean_inc(v___y_2908_);
v___x_2917_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2908_, v_sign_2909_, v_val_2910_, v_b_2914_, v___x_2916_);
v___x_2918_ = ((size_t)1ULL);
v___x_2919_ = lean_usize_add(v_i_2912_, v___x_2918_);
v_i_2912_ = v___x_2919_;
v_b_2914_ = v___x_2917_;
goto _start;
}
else
{
lean_dec_ref(v_val_2910_);
lean_dec(v___y_2908_);
return v_b_2914_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2908_ = stack[0].m_obj;
lean_object* v_sign_2909_ = stack[1].m_obj;
lean_object* v_val_2910_ = stack[2].m_obj;
lean_object* v_as_2911_ = stack[3].m_obj;
size_t v_i_2912_ = stack[4].m_num;
size_t v_stop_2913_ = stack[5].m_num;
lean_object* v_b_2914_ = stack[6].m_obj;
lean_object* v_res_2921_;
v_res_2921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2908_, v_sign_2909_, v_val_2910_, v_as_2911_, v_i_2912_, v_stop_2913_, v_b_2914_);
stack->m_obj
 = v_res_2921_;
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(lean_object* v_msgData_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v___x_3013_; lean_object* v_env_3014_; uint8_t v___x_3015_; lean_object* v_env_3016_; lean_object* v___x_3017_; lean_object* v_toCold_3018_; lean_object* v_mctx_3019_; lean_object* v_lctx_3020_; lean_object* v_options_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3013_ = lean_st_ref_get(v___y_3011_);
v_env_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc_ref(v_env_3014_);
lean_dec(v___x_3013_);
v___x_3015_ = 0;
v_env_3016_ = l_Lean_Environment_setRecordingDeps(v_env_3014_, v___x_3015_);
v___x_3017_ = lean_st_ref_get(v___y_3009_);
v_toCold_3018_ = lean_ctor_get(v___y_3010_, 0);
v_mctx_3019_ = lean_ctor_get(v___x_3017_, 0);
lean_inc_ref(v_mctx_3019_);
lean_dec(v___x_3017_);
v_lctx_3020_ = lean_ctor_get(v___y_3008_, 2);
v_options_3021_ = lean_ctor_get(v_toCold_3018_, 2);
lean_inc_ref(v_options_3021_);
lean_inc_ref(v_lctx_3020_);
v___x_3022_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3022_, 0, v_env_3016_);
lean_ctor_set(v___x_3022_, 1, v_mctx_3019_);
lean_ctor_set(v___x_3022_, 2, v_lctx_3020_);
lean_ctor_set(v___x_3022_, 3, v_options_3021_);
v___x_3023_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
lean_ctor_set(v___x_3023_, 1, v_msgData_3007_);
v___x_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3007_ = stack[0].m_obj;
lean_object* v___y_3008_ = stack[1].m_obj;
lean_object* v___y_3009_ = stack[2].m_obj;
lean_object* v___y_3010_ = stack[3].m_obj;
lean_object* v___y_3011_ = stack[4].m_obj;
lean_object* v_res_3025_;
v_res_3025_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msgData_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
stack->m_obj
 = v_res_3025_;
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
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(lean_object* v_msg_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_ref_3039_; lean_object* v___x_3040_; lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3049_; 
v_ref_3039_ = lean_ctor_get(v___y_3036_, 2);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3033_ = stack[0].m_obj;
lean_object* v___y_3034_ = stack[1].m_obj;
lean_object* v___y_3035_ = stack[2].m_obj;
lean_object* v___y_3036_ = stack[3].m_obj;
lean_object* v___y_3037_ = stack[4].m_obj;
lean_object* v_res_3050_;
v_res_3050_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
stack->m_obj
 = v_res_3050_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg___boxed(lean_object* v_msg_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
return v_res_3057_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0));
v___x_3060_ = l_Lean_stringToMessageData(v___x_3059_);
return v___x_3060_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2));
v___x_3063_ = l_Lean_stringToMessageData(v___x_3062_);
return v___x_3063_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4));
v___x_3066_ = l_Lean_stringToMessageData(v___x_3065_);
return v___x_3066_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(lean_object* v_p_3067_, lean_object* v_c_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, uint8_t v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v_constraints_3079_; lean_object* v___x_3080_; 
v_constraints_3079_ = lean_ctor_get(v_p_3067_, 2);
v___x_3080_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_3079_, v_c_3068_);
if (lean_obj_tag(v___x_3080_) == 1)
{
lean_object* v_val_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3180_; 
v_val_3081_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3083_ = v___x_3080_;
v_isShared_3084_ = v_isSharedCheck_3180_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_val_3081_);
lean_dec(v___x_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3180_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v_constraint_3085_; lean_object* v_lowerBound_3086_; 
v_constraint_3085_ = lean_ctor_get(v_val_3081_, 1);
v_lowerBound_3086_ = lean_ctor_get(v_constraint_3085_, 0);
lean_inc(v_lowerBound_3086_);
if (lean_obj_tag(v_lowerBound_3086_) == 1)
{
lean_object* v_upperBound_3087_; 
lean_del_object(v___x_3083_);
v_upperBound_3087_ = lean_ctor_get(v_constraint_3085_, 1);
lean_inc(v_upperBound_3087_);
if (lean_obj_tag(v_upperBound_3087_) == 1)
{
lean_object* v_coeffs_3088_; lean_object* v_justification_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3167_; 
v_coeffs_3088_ = lean_ctor_get(v_val_3081_, 0);
v_justification_3089_ = lean_ctor_get(v_val_3081_, 2);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_val_3081_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; 
v_unused_3168_ = lean_ctor_get(v_val_3081_, 1);
lean_dec(v_unused_3168_);
v___x_3091_ = v_val_3081_;
v_isShared_3092_ = v_isSharedCheck_3167_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_justification_3089_);
lean_inc(v_coeffs_3088_);
lean_dec(v_val_3081_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3167_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v_val_3093_; lean_object* v_val_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v_m_3097_; lean_object* v___x_3098_; 
v_val_3093_ = lean_ctor_get(v_lowerBound_3086_, 0);
lean_inc(v_val_3093_);
lean_dec_ref_known(v_lowerBound_3086_, 1);
v_val_3094_ = lean_ctor_get(v_upperBound_3087_, 0);
lean_inc(v_val_3094_);
lean_dec_ref_known(v_upperBound_3087_, 1);
lean_inc(v_c_3068_);
v___x_3095_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_c_3068_);
v___x_3096_ = lean_unsigned_to_nat(1u);
v_m_3097_ = lean_nat_add(v___x_3095_, v___x_3096_);
lean_dec(v___x_3095_);
v___x_3098_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3070_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v_nil_3102_; lean_object* v_cons_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_a_3099_);
lean_dec_ref_known(v___x_3098_, 1);
v___x_3100_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc(v_m_3097_);
v___x_3101_ = l_Lean_mkNatLit(v_m_3097_);
v_nil_3102_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3103_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3104_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3102_, v_cons_3103_, v_c_3068_);
lean_dec(v_c_3068_);
v___x_3105_ = l_Lean_mkApp3(v___x_3100_, v___x_3101_, v___x_3104_, v_a_3099_);
v___x_3106_ = l_Lean_Elab_Tactic_Omega_lookup(v___x_3105_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3150_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3150_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3150_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v_fst_3111_; lean_object* v_snd_3112_; uint8_t v___x_3125_; 
v_fst_3111_ = lean_ctor_get(v_a_3107_, 0);
lean_inc(v_fst_3111_);
v_snd_3112_ = lean_ctor_get(v_a_3107_, 1);
lean_inc(v_snd_3112_);
lean_dec(v_a_3107_);
v___x_3125_ = lean_int_dec_eq(v_val_3094_, v_val_3093_);
lean_dec(v_val_3094_);
if (v___x_3125_ == 0)
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec(v_snd_3112_);
lean_dec(v_fst_3111_);
lean_del_object(v___x_3109_);
lean_dec(v_m_3097_);
lean_dec(v_val_3093_);
lean_del_object(v___x_3091_);
lean_dec_ref(v_justification_3089_);
lean_dec(v_coeffs_3088_);
lean_dec_ref(v_p_3067_);
v___x_3126_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1);
v___x_3127_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3126_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
return v___x_3127_;
}
else
{
if (lean_obj_tag(v_snd_3112_) == 0)
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_dec(v_fst_3111_);
lean_del_object(v___x_3109_);
lean_dec(v_m_3097_);
lean_dec(v_val_3093_);
lean_del_object(v___x_3091_);
lean_dec_ref(v_justification_3089_);
lean_dec(v_coeffs_3088_);
lean_dec_ref(v_p_3067_);
v___x_3128_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3);
v___x_3129_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3128_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3129_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
else
{
lean_object* v_val_3138_; uint8_t v___x_3139_; 
v_val_3138_ = lean_ctor_get(v_snd_3112_, 0);
lean_inc(v_val_3138_);
lean_dec_ref_known(v_snd_3112_, 1);
v___x_3139_ = l_List_isEmpty___redArg(v_val_3138_);
lean_dec(v_val_3138_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v_fst_3111_);
lean_del_object(v___x_3109_);
lean_dec(v_m_3097_);
lean_dec(v_val_3093_);
lean_del_object(v___x_3091_);
lean_dec_ref(v_justification_3089_);
lean_dec(v_coeffs_3088_);
lean_dec_ref(v_p_3067_);
v___x_3140_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5);
v___x_3141_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3140_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
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
else
{
goto v___jp_3113_;
}
}
}
v___jp_3113_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
lean_inc(v_coeffs_3088_);
lean_inc_n(v_m_3097_, 2);
v___x_3114_ = l_Lean_Omega_bmod__coeffs(v_m_3097_, v_fst_3111_, v_coeffs_3088_);
v___x_3115_ = l_Int_bmod(v_val_3093_, v_m_3097_);
v___x_3116_ = l_Lean_Omega_Constraint_exact(v___x_3115_);
v___x_3117_ = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(v___x_3117_, 0, v_m_3097_);
lean_ctor_set(v___x_3117_, 1, v_val_3093_);
lean_ctor_set(v___x_3117_, 2, v_fst_3111_);
lean_ctor_set(v___x_3117_, 3, v_coeffs_3088_);
lean_ctor_set(v___x_3117_, 4, v_justification_3089_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 2, v___x_3117_);
lean_ctor_set(v___x_3091_, 1, v___x_3116_);
lean_ctor_set(v___x_3091_, 0, v___x_3114_);
v___x_3119_ = v___x_3091_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3124_, 2, v___x_3117_);
v___x_3119_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3120_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_3067_, v___x_3119_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3120_);
v___x_3122_ = v___x_3109_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3120_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
lean_dec(v_m_3097_);
lean_dec(v_val_3094_);
lean_dec(v_val_3093_);
lean_del_object(v___x_3091_);
lean_dec_ref(v_justification_3089_);
lean_dec(v_coeffs_3088_);
lean_dec_ref(v_p_3067_);
v_a_3151_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3106_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3106_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec(v_m_3097_);
lean_dec(v_val_3094_);
lean_dec(v_val_3093_);
lean_del_object(v___x_3091_);
lean_dec_ref(v_justification_3089_);
lean_dec(v_coeffs_3088_);
lean_dec(v_c_3068_);
lean_dec_ref(v_p_3067_);
v_a_3159_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3098_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3098_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
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
}
else
{
lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec(v_upperBound_3087_);
lean_dec(v_val_3081_);
lean_dec(v_c_3068_);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_lowerBound_3086_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; 
v_unused_3176_ = lean_ctor_get(v_lowerBound_3086_, 0);
lean_dec(v_unused_3176_);
v___x_3170_ = v_lowerBound_3086_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_dec(v_lowerBound_3086_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set_tag(v___x_3170_, 0);
lean_ctor_set(v___x_3170_, 0, v_p_3067_);
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_p_3067_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_object* v___x_3178_; 
lean_dec(v_lowerBound_3086_);
lean_dec(v_val_3081_);
lean_dec(v_c_3068_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set_tag(v___x_3083_, 0);
lean_ctor_set(v___x_3083_, 0, v_p_3067_);
v___x_3178_ = v___x_3083_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_p_3067_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_object* v___x_3181_; 
lean_dec(v___x_3080_);
lean_dec(v_c_3068_);
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v_p_3067_);
return v___x_3181_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3067_ = stack[0].m_obj;
lean_object* v_c_3068_ = stack[1].m_obj;
lean_object* v_a_3069_ = stack[2].m_obj;
lean_object* v_a_3070_ = stack[3].m_obj;
lean_object* v_a_3071_ = stack[4].m_obj;
uint8_t v_a_3072_ = stack[5].m_num;
lean_object* v_a_3073_ = stack[6].m_obj;
lean_object* v_a_3074_ = stack[7].m_obj;
lean_object* v_a_3075_ = stack[8].m_obj;
lean_object* v_a_3076_ = stack[9].m_obj;
lean_object* v_a_3077_ = stack[10].m_obj;
lean_object* v_res_3182_;
v_res_3182_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3067_, v_c_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
stack->m_obj
 = v_res_3182_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___boxed(lean_object* v_p_3183_, lean_object* v_c_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_){
_start:
{
uint8_t v_a_boxed_3195_; lean_object* v_res_3196_; 
v_a_boxed_3195_ = lean_unbox(v_a_3188_);
v_res_3196_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3183_, v_c_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_boxed_3195_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
lean_dec(v_a_3193_);
lean_dec_ref(v_a_3192_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec(v_a_3185_);
return v_res_3196_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_object* v_00_u03b1_3197_, lean_object* v_msg_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, uint8_t v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3198_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
return v___x_3209_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3198_ = stack[1].m_obj;
lean_object* v___y_3199_ = stack[2].m_obj;
lean_object* v___y_3200_ = stack[3].m_obj;
lean_object* v___y_3201_ = stack[4].m_obj;
uint8_t v___y_3202_ = stack[5].m_num;
lean_object* v___y_3203_ = stack[6].m_obj;
lean_object* v___y_3204_ = stack[7].m_obj;
lean_object* v___y_3205_ = stack[8].m_obj;
lean_object* v___y_3206_ = stack[9].m_obj;
lean_object* v___y_3207_ = stack[10].m_obj;
lean_object* v_res_3210_;
v_res_3210_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_box(0), v_msg_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
stack->m_obj
 = v_res_3210_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___boxed(lean_object* v_00_u03b1_3211_, lean_object* v_msg_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
uint8_t v___y_9138__boxed_3223_; lean_object* v_res_3224_; 
v___y_9138__boxed_3223_ = lean_unbox(v___y_3216_);
v_res_3224_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(v_00_u03b1_3211_, v_msg_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_9138__boxed_3223_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec(v___y_3213_);
return v_res_3224_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality(lean_object* v_p_3225_, lean_object* v_c_3226_, lean_object* v_m_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, uint8_t v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v___x_3238_; uint8_t v___x_3239_; 
v___x_3238_ = lean_unsigned_to_nat(1u);
v___x_3239_ = lean_nat_dec_eq(v_m_3227_, v___x_3238_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; 
v___x_3240_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3225_, v_c_3226_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
return v___x_3240_;
}
else
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_3225_, v_c_3226_);
lean_dec(v_c_3226_);
v___x_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
return v___x_3242_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_solveEquality_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3225_ = stack[0].m_obj;
lean_object* v_c_3226_ = stack[1].m_obj;
lean_object* v_m_3227_ = stack[2].m_obj;
lean_object* v_a_3228_ = stack[3].m_obj;
lean_object* v_a_3229_ = stack[4].m_obj;
lean_object* v_a_3230_ = stack[5].m_obj;
uint8_t v_a_3231_ = stack[6].m_num;
lean_object* v_a_3232_ = stack[7].m_obj;
lean_object* v_a_3233_ = stack[8].m_obj;
lean_object* v_a_3234_ = stack[9].m_obj;
lean_object* v_a_3235_ = stack[10].m_obj;
lean_object* v_a_3236_ = stack[11].m_obj;
lean_object* v_res_3243_;
v_res_3243_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3225_, v_c_3226_, v_m_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
stack->m_obj
 = v_res_3243_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality___boxed(lean_object* v_p_3244_, lean_object* v_c_3245_, lean_object* v_m_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_){
_start:
{
uint8_t v_a_boxed_3257_; lean_object* v_res_3258_; 
v_a_boxed_3257_ = lean_unbox(v_a_3250_);
v_res_3258_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3244_, v_c_3245_, v_m_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_boxed_3257_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_);
lean_dec(v_a_3255_);
lean_dec_ref(v_a_3254_);
lean_dec(v_a_3253_);
lean_dec_ref(v_a_3252_);
lean_dec(v_a_3251_);
lean_dec_ref(v_a_3249_);
lean_dec(v_a_3248_);
lean_dec(v_a_3247_);
lean_dec(v_m_3246_);
return v_res_3258_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(lean_object* v_p_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, uint8_t v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_){
_start:
{
uint8_t v_possible_3270_; 
v_possible_3270_ = lean_ctor_get_uint8(v_p_3259_, sizeof(void*)*7);
if (v_possible_3270_ == 0)
{
lean_object* v___x_3271_; 
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_p_3259_);
return v___x_3271_;
}
else
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_3259_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v___x_3273_; 
v___x_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3273_, 0, v_p_3259_);
return v___x_3273_;
}
else
{
lean_object* v_val_3274_; lean_object* v_fst_3275_; lean_object* v_snd_3276_; lean_object* v___x_3277_; 
v_val_3274_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_val_3274_);
lean_dec_ref_known(v___x_3272_, 1);
v_fst_3275_ = lean_ctor_get(v_val_3274_, 0);
lean_inc(v_fst_3275_);
v_snd_3276_ = lean_ctor_get(v_val_3274_, 1);
lean_inc(v_snd_3276_);
lean_dec(v_val_3274_);
v___x_3277_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3259_, v_fst_3275_, v_snd_3276_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_);
lean_dec(v_snd_3276_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v_p_3259_ = v_a_3278_;
goto _start;
}
else
{
return v___x_3277_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_solveEqualities_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3259_ = stack[0].m_obj;
lean_object* v_a_3260_ = stack[1].m_obj;
lean_object* v_a_3261_ = stack[2].m_obj;
lean_object* v_a_3262_ = stack[3].m_obj;
uint8_t v_a_3263_ = stack[4].m_num;
lean_object* v_a_3264_ = stack[5].m_obj;
lean_object* v_a_3265_ = stack[6].m_obj;
lean_object* v_a_3266_ = stack[7].m_obj;
lean_object* v_a_3267_ = stack[8].m_obj;
lean_object* v_a_3268_ = stack[9].m_obj;
lean_object* v_res_3280_;
v_res_3280_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_);
stack->m_obj
 = v_res_3280_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities___boxed(lean_object* v_p_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_){
_start:
{
uint8_t v_a_boxed_3292_; lean_object* v_res_3293_; 
v_a_boxed_3292_ = lean_unbox(v_a_3285_);
v_res_3293_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_boxed_3292_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec(v_a_3282_);
return v_res_3293_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = lean_box(0);
v___x_3301_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1));
v___x_3302_ = l_Lean_Expr_const___override(v___x_3301_, v___x_3300_);
return v___x_3302_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object* v_c_3303_, lean_object* v_x_3304_, lean_object* v_p_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, uint8_t v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3307_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v___x_3316_, 1);
v___x_3318_ = lean_box(v_a_3309_);
lean_inc(v_a_3314_);
lean_inc_ref(v_a_3313_);
lean_inc(v_a_3312_);
lean_inc_ref(v_a_3311_);
lean_inc(v_a_3310_);
lean_inc_ref(v_a_3308_);
lean_inc(v_a_3307_);
lean_inc(v_a_3306_);
v___x_3319_ = lean_apply_10(v_p_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v___x_3318_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, lean_box(0));
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3345_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3322_ = v___x_3319_;
v_isShared_3323_ = v_isSharedCheck_3345_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3319_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3345_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3324_; lean_object* v___y_3326_; lean_object* v___x_3334_; uint8_t v___x_3335_; 
v___x_3324_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2);
v___x_3334_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3335_ = lean_int_dec_le(v___x_3334_, v_c_3303_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3336_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3337_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3338_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3339_ = lean_int_neg(v_c_3303_);
v___x_3340_ = l_Int_toNat(v___x_3339_);
lean_dec(v___x_3339_);
v___x_3341_ = l_Lean_instToExprInt_mkNat(v___x_3340_);
v___x_3342_ = l_Lean_mkApp3(v___x_3336_, v___x_3337_, v___x_3338_, v___x_3341_);
v___y_3326_ = v___x_3342_;
goto v___jp_3325_;
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = l_Int_toNat(v_c_3303_);
v___x_3344_ = l_Lean_instToExprInt_mkNat(v___x_3343_);
v___y_3326_ = v___x_3344_;
goto v___jp_3325_;
}
v___jp_3325_:
{
lean_object* v_nil_3327_; lean_object* v_cons_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3332_; 
v_nil_3327_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3328_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3329_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3327_, v_cons_3328_, v_x_3304_);
v___x_3330_ = l_Lean_mkApp4(v___x_3324_, v___y_3326_, v___x_3329_, v_a_3317_, v_a_3320_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v___x_3330_);
v___x_3332_ = v___x_3322_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
else
{
lean_dec(v_a_3317_);
return v___x_3319_;
}
}
else
{
lean_dec_ref(v_p_3305_);
return v___x_3316_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3303_ = stack[0].m_obj;
lean_object* v_x_3304_ = stack[1].m_obj;
lean_object* v_p_3305_ = stack[2].m_obj;
lean_object* v_a_3306_ = stack[3].m_obj;
lean_object* v_a_3307_ = stack[4].m_obj;
lean_object* v_a_3308_ = stack[5].m_obj;
uint8_t v_a_3309_ = stack[6].m_num;
lean_object* v_a_3310_ = stack[7].m_obj;
lean_object* v_a_3311_ = stack[8].m_obj;
lean_object* v_a_3312_ = stack[9].m_obj;
lean_object* v_a_3313_ = stack[10].m_obj;
lean_object* v_a_3314_ = stack[11].m_obj;
lean_object* v_res_3346_;
v_res_3346_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(v_c_3303_, v_x_3304_, v_p_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
stack->m_obj
 = v_res_3346_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object* v_c_3347_, lean_object* v_x_3348_, lean_object* v_p_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
uint8_t v_a_boxed_3360_; lean_object* v_res_3361_; 
v_a_boxed_3360_ = lean_unbox(v_a_3353_);
v_res_3361_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(v_c_3347_, v_x_3348_, v_p_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_boxed_3360_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3352_);
lean_dec(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec(v_x_3348_);
lean_dec(v_c_3347_);
return v_res_3361_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2(void){
_start:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3368_ = lean_box(0);
v___x_3369_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1));
v___x_3370_ = l_Lean_Expr_const___override(v___x_3369_, v___x_3368_);
return v___x_3370_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(lean_object* v_c_3371_, lean_object* v_x_3372_, lean_object* v_p_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, uint8_t v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v___x_3384_; 
v___x_3384_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3375_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3386_ = lean_box(v_a_3377_);
lean_inc(v_a_3382_);
lean_inc_ref(v_a_3381_);
lean_inc(v_a_3380_);
lean_inc_ref(v_a_3379_);
lean_inc(v_a_3378_);
lean_inc_ref(v_a_3376_);
lean_inc(v_a_3375_);
lean_inc(v_a_3374_);
v___x_3387_ = lean_apply_10(v_p_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v___x_3386_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, lean_box(0));
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3413_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3390_ = v___x_3387_;
v_isShared_3391_ = v_isSharedCheck_3413_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3413_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; lean_object* v___y_3394_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
v___x_3392_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2);
v___x_3402_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3403_ = lean_int_dec_le(v___x_3402_, v_c_3371_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3404_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3405_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3406_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3407_ = lean_int_neg(v_c_3371_);
v___x_3408_ = l_Int_toNat(v___x_3407_);
lean_dec(v___x_3407_);
v___x_3409_ = l_Lean_instToExprInt_mkNat(v___x_3408_);
v___x_3410_ = l_Lean_mkApp3(v___x_3404_, v___x_3405_, v___x_3406_, v___x_3409_);
v___y_3394_ = v___x_3410_;
goto v___jp_3393_;
}
else
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = l_Int_toNat(v_c_3371_);
v___x_3412_ = l_Lean_instToExprInt_mkNat(v___x_3411_);
v___y_3394_ = v___x_3412_;
goto v___jp_3393_;
}
v___jp_3393_:
{
lean_object* v_nil_3395_; lean_object* v_cons_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3400_; 
v_nil_3395_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3396_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3397_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3395_, v_cons_3396_, v_x_3372_);
v___x_3398_ = l_Lean_mkApp4(v___x_3392_, v___y_3394_, v___x_3397_, v_a_3385_, v_a_3388_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3398_);
v___x_3400_ = v___x_3390_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
else
{
lean_dec(v_a_3385_);
return v___x_3387_;
}
}
else
{
lean_dec_ref(v_p_3373_);
return v___x_3384_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3371_ = stack[0].m_obj;
lean_object* v_x_3372_ = stack[1].m_obj;
lean_object* v_p_3373_ = stack[2].m_obj;
lean_object* v_a_3374_ = stack[3].m_obj;
lean_object* v_a_3375_ = stack[4].m_obj;
lean_object* v_a_3376_ = stack[5].m_obj;
uint8_t v_a_3377_ = stack[6].m_num;
lean_object* v_a_3378_ = stack[7].m_obj;
lean_object* v_a_3379_ = stack[8].m_obj;
lean_object* v_a_3380_ = stack[9].m_obj;
lean_object* v_a_3381_ = stack[10].m_obj;
lean_object* v_a_3382_ = stack[11].m_obj;
lean_object* v_res_3414_;
v_res_3414_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(v_c_3371_, v_x_3372_, v_p_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
stack->m_obj
 = v_res_3414_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed(lean_object* v_c_3415_, lean_object* v_x_3416_, lean_object* v_p_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
uint8_t v_a_boxed_3428_; lean_object* v_res_3429_; 
v_a_boxed_3428_ = lean_unbox(v_a_3421_);
v_res_3429_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(v_c_3415_, v_x_3416_, v_p_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_boxed_3428_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
lean_dec(v_a_3426_);
lean_dec_ref(v_a_3425_);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3423_);
lean_dec(v_a_3422_);
lean_dec_ref(v_a_3420_);
lean_dec(v_a_3419_);
lean_dec(v_a_3418_);
lean_dec(v_x_3416_);
lean_dec(v_c_3415_);
return v_res_3429_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(lean_object* v_prf_x3f_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, uint8_t v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
if (lean_obj_tag(v_prf_x3f_3430_) == 0)
{
lean_object* v___x_3441_; uint8_t v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3441_ = lean_box(0);
v___x_3442_ = 0;
v___x_3443_ = lean_box(0);
v___x_3444_ = l_Lean_Meta_mkFreshExprMVar(v___x_3441_, v___x_3442_, v___x_3443_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; uint8_t v___x_3446_; lean_object* v___x_3447_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref_known(v___x_3444_, 1);
v___x_3446_ = 0;
v___x_3447_ = l_Lean_Meta_mkSorry(v_a_3445_, v___x_3446_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
return v___x_3447_;
}
else
{
return v___x_3444_;
}
}
else
{
lean_object* v_val_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v_val_3448_ = lean_ctor_get(v_prf_x3f_3430_, 0);
lean_inc(v_val_3448_);
lean_dec_ref_known(v_prf_x3f_3430_, 1);
v___x_3449_ = lean_box(v___y_3434_);
lean_inc(v___y_3439_);
lean_inc_ref(v___y_3438_);
lean_inc(v___y_3437_);
lean_inc_ref(v___y_3436_);
lean_inc(v___y_3435_);
lean_inc_ref(v___y_3433_);
lean_inc(v___y_3432_);
lean_inc(v___y_3431_);
v___x_3450_ = lean_apply_10(v_val_3448_, v___y_3431_, v___y_3432_, v___y_3433_, v___x_3449_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, lean_box(0));
return v___x_3450_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_prf_x3f_3430_ = stack[0].m_obj;
lean_object* v___y_3431_ = stack[1].m_obj;
lean_object* v___y_3432_ = stack[2].m_obj;
lean_object* v___y_3433_ = stack[3].m_obj;
uint8_t v___y_3434_ = stack[4].m_num;
lean_object* v___y_3435_ = stack[5].m_obj;
lean_object* v___y_3436_ = stack[6].m_obj;
lean_object* v___y_3437_ = stack[7].m_obj;
lean_object* v___y_3438_ = stack[8].m_obj;
lean_object* v___y_3439_ = stack[9].m_obj;
lean_object* v_res_3451_;
v_res_3451_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(v_prf_x3f_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
stack->m_obj
 = v_res_3451_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed(lean_object* v_prf_x3f_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
uint8_t v___y_833__boxed_3463_; lean_object* v_res_3464_; 
v___y_833__boxed_3463_ = lean_unbox(v___y_3456_);
v_res_3464_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(v_prf_x3f_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_833__boxed_3463_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec(v___y_3453_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality(lean_object* v_p_3465_, lean_object* v_const_3466_, lean_object* v_coeffs_3467_, lean_object* v_prf_x3f_3468_){
_start:
{
lean_object* v_assumptions_3469_; lean_object* v_numVars_3470_; lean_object* v_constraints_3471_; lean_object* v_equalities_3472_; lean_object* v_eliminations_3473_; uint8_t v_possible_3474_; lean_object* v_proveFalse_x3f_3475_; lean_object* v_explanation_x3f_3476_; lean_object* v_prf_3477_; lean_object* v_i_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v_p_x27_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v_f_3487_; lean_object* v_f_3488_; lean_object* v_f_3489_; lean_object* v___x_3490_; 
v_assumptions_3469_ = lean_ctor_get(v_p_3465_, 0);
v_numVars_3470_ = lean_ctor_get(v_p_3465_, 1);
v_constraints_3471_ = lean_ctor_get(v_p_3465_, 2);
v_equalities_3472_ = lean_ctor_get(v_p_3465_, 3);
v_eliminations_3473_ = lean_ctor_get(v_p_3465_, 4);
v_possible_3474_ = lean_ctor_get_uint8(v_p_3465_, sizeof(void*)*7);
v_proveFalse_x3f_3475_ = lean_ctor_get(v_p_3465_, 5);
v_explanation_x3f_3476_ = lean_ctor_get(v_p_3465_, 6);
v_prf_3477_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3477_, 0, v_prf_x3f_3468_);
v_i_3478_ = lean_array_get_size(v_assumptions_3469_);
lean_inc_n(v_coeffs_3467_, 2);
lean_inc(v_const_3466_);
v___x_3479_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed), 13, 3);
lean_closure_set(v___x_3479_, 0, v_const_3466_);
lean_closure_set(v___x_3479_, 1, v_coeffs_3467_);
lean_closure_set(v___x_3479_, 2, v_prf_3477_);
lean_inc_ref(v_assumptions_3469_);
v___x_3480_ = lean_array_push(v_assumptions_3469_, v___x_3479_);
lean_inc_ref(v_explanation_x3f_3476_);
lean_inc(v_proveFalse_x3f_3475_);
lean_inc(v_eliminations_3473_);
lean_inc_ref(v_equalities_3472_);
lean_inc_ref(v_constraints_3471_);
lean_inc(v_numVars_3470_);
v_p_x27_3481_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3481_, 0, v___x_3480_);
lean_ctor_set(v_p_x27_3481_, 1, v_numVars_3470_);
lean_ctor_set(v_p_x27_3481_, 2, v_constraints_3471_);
lean_ctor_set(v_p_x27_3481_, 3, v_equalities_3472_);
lean_ctor_set(v_p_x27_3481_, 4, v_eliminations_3473_);
lean_ctor_set(v_p_x27_3481_, 5, v_proveFalse_x3f_3475_);
lean_ctor_set(v_p_x27_3481_, 6, v_explanation_x3f_3476_);
lean_ctor_set_uint8(v_p_x27_3481_, sizeof(void*)*7, v_possible_3474_);
v___x_3482_ = lean_int_neg(v_const_3466_);
lean_dec(v_const_3466_);
v___x_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
v___x_3484_ = lean_box(0);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3483_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
lean_inc_ref(v___x_3485_);
v___x_3486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_ctor_set(v___x_3486_, 1, v_coeffs_3467_);
lean_ctor_set(v___x_3486_, 2, v_i_3478_);
v_f_3487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3487_, 0, v_coeffs_3467_);
lean_ctor_set(v_f_3487_, 1, v___x_3485_);
lean_ctor_set(v_f_3487_, 2, v___x_3486_);
v_f_3488_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3465_, v_f_3487_);
v_f_3489_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3488_);
v___x_3490_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3481_, v_f_3489_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality(lean_object* v_p_3491_, lean_object* v_const_3492_, lean_object* v_coeffs_3493_, lean_object* v_prf_x3f_3494_){
_start:
{
lean_object* v_assumptions_3495_; lean_object* v_numVars_3496_; lean_object* v_constraints_3497_; lean_object* v_equalities_3498_; lean_object* v_eliminations_3499_; uint8_t v_possible_3500_; lean_object* v_proveFalse_x3f_3501_; lean_object* v_explanation_x3f_3502_; lean_object* v_prf_3503_; lean_object* v_i_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v_p_x27_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v_f_3512_; lean_object* v_f_3513_; lean_object* v_f_3514_; lean_object* v___x_3515_; 
v_assumptions_3495_ = lean_ctor_get(v_p_3491_, 0);
v_numVars_3496_ = lean_ctor_get(v_p_3491_, 1);
v_constraints_3497_ = lean_ctor_get(v_p_3491_, 2);
v_equalities_3498_ = lean_ctor_get(v_p_3491_, 3);
v_eliminations_3499_ = lean_ctor_get(v_p_3491_, 4);
v_possible_3500_ = lean_ctor_get_uint8(v_p_3491_, sizeof(void*)*7);
v_proveFalse_x3f_3501_ = lean_ctor_get(v_p_3491_, 5);
v_explanation_x3f_3502_ = lean_ctor_get(v_p_3491_, 6);
v_prf_3503_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3503_, 0, v_prf_x3f_3494_);
v_i_3504_ = lean_array_get_size(v_assumptions_3495_);
lean_inc_n(v_coeffs_3493_, 2);
lean_inc(v_const_3492_);
v___x_3505_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed), 13, 3);
lean_closure_set(v___x_3505_, 0, v_const_3492_);
lean_closure_set(v___x_3505_, 1, v_coeffs_3493_);
lean_closure_set(v___x_3505_, 2, v_prf_3503_);
lean_inc_ref(v_assumptions_3495_);
v___x_3506_ = lean_array_push(v_assumptions_3495_, v___x_3505_);
lean_inc_ref(v_explanation_x3f_3502_);
lean_inc(v_proveFalse_x3f_3501_);
lean_inc(v_eliminations_3499_);
lean_inc_ref(v_equalities_3498_);
lean_inc_ref(v_constraints_3497_);
lean_inc(v_numVars_3496_);
v_p_x27_3507_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3507_, 0, v___x_3506_);
lean_ctor_set(v_p_x27_3507_, 1, v_numVars_3496_);
lean_ctor_set(v_p_x27_3507_, 2, v_constraints_3497_);
lean_ctor_set(v_p_x27_3507_, 3, v_equalities_3498_);
lean_ctor_set(v_p_x27_3507_, 4, v_eliminations_3499_);
lean_ctor_set(v_p_x27_3507_, 5, v_proveFalse_x3f_3501_);
lean_ctor_set(v_p_x27_3507_, 6, v_explanation_x3f_3502_);
lean_ctor_set_uint8(v_p_x27_3507_, sizeof(void*)*7, v_possible_3500_);
v___x_3508_ = lean_int_neg(v_const_3492_);
lean_dec(v_const_3492_);
v___x_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
lean_inc_ref(v___x_3509_);
v___x_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
lean_ctor_set(v___x_3510_, 1, v___x_3509_);
lean_inc_ref(v___x_3510_);
v___x_3511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
lean_ctor_set(v___x_3511_, 1, v_coeffs_3493_);
lean_ctor_set(v___x_3511_, 2, v_i_3504_);
v_f_3512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3512_, 0, v_coeffs_3493_);
lean_ctor_set(v_f_3512_, 1, v___x_3510_);
lean_ctor_set(v_f_3512_, 2, v___x_3511_);
v_f_3513_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3491_, v_f_3512_);
v_f_3514_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3513_);
v___x_3515_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3507_, v_f_3514_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(lean_object* v_x_3516_, lean_object* v_x_3517_){
_start:
{
if (lean_obj_tag(v_x_3517_) == 0)
{
return v_x_3516_;
}
else
{
lean_object* v_head_3518_; lean_object* v_snd_3519_; lean_object* v_tail_3520_; lean_object* v_fst_3521_; lean_object* v_fst_3522_; lean_object* v_snd_3523_; lean_object* v___x_3524_; 
v_head_3518_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_head_3518_);
v_snd_3519_ = lean_ctor_get(v_head_3518_, 1);
lean_inc(v_snd_3519_);
v_tail_3520_ = lean_ctor_get(v_x_3517_, 1);
lean_inc(v_tail_3520_);
lean_dec_ref_known(v_x_3517_, 2);
v_fst_3521_ = lean_ctor_get(v_head_3518_, 0);
lean_inc(v_fst_3521_);
lean_dec(v_head_3518_);
v_fst_3522_ = lean_ctor_get(v_snd_3519_, 0);
lean_inc(v_fst_3522_);
v_snd_3523_ = lean_ctor_get(v_snd_3519_, 1);
lean_inc(v_snd_3523_);
lean_dec(v_snd_3519_);
v___x_3524_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality(v_x_3516_, v_fst_3521_, v_fst_3522_, v_snd_3523_);
v_x_3516_ = v___x_3524_;
v_x_3517_ = v_tail_3520_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequalities(lean_object* v_p_3526_, lean_object* v_ineqs_3527_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(v_p_3526_, v_ineqs_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(lean_object* v_x_3529_, lean_object* v_x_3530_){
_start:
{
if (lean_obj_tag(v_x_3530_) == 0)
{
return v_x_3529_;
}
else
{
lean_object* v_head_3531_; lean_object* v_snd_3532_; lean_object* v_tail_3533_; lean_object* v_fst_3534_; lean_object* v_fst_3535_; lean_object* v_snd_3536_; lean_object* v___x_3537_; 
v_head_3531_ = lean_ctor_get(v_x_3530_, 0);
lean_inc(v_head_3531_);
v_snd_3532_ = lean_ctor_get(v_head_3531_, 1);
lean_inc(v_snd_3532_);
v_tail_3533_ = lean_ctor_get(v_x_3530_, 1);
lean_inc(v_tail_3533_);
lean_dec_ref_known(v_x_3530_, 2);
v_fst_3534_ = lean_ctor_get(v_head_3531_, 0);
lean_inc(v_fst_3534_);
lean_dec(v_head_3531_);
v_fst_3535_ = lean_ctor_get(v_snd_3532_, 0);
lean_inc(v_fst_3535_);
v_snd_3536_ = lean_ctor_get(v_snd_3532_, 1);
lean_inc(v_snd_3536_);
lean_dec(v_snd_3532_);
v___x_3537_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality(v_x_3529_, v_fst_3534_, v_fst_3535_, v_snd_3536_);
v_x_3529_ = v___x_3537_;
v_x_3530_ = v_tail_3533_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEqualities(lean_object* v_p_3539_, lean_object* v_eqs_3540_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(v_p_3539_, v_eqs_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0(lean_object* v___x_3548_, lean_object* v_x_3549_){
_start:
{
lean_object* v_constraint_3550_; lean_object* v_coeffs_3551_; lean_object* v_lowerBound_3552_; lean_object* v_upperBound_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___y_3558_; lean_object* v___y_3559_; 
v_constraint_3550_ = lean_ctor_get(v_x_3549_, 1);
lean_inc_ref(v_constraint_3550_);
v_coeffs_3551_ = lean_ctor_get(v_x_3549_, 0);
lean_inc(v_coeffs_3551_);
lean_dec_ref(v_x_3549_);
v_lowerBound_3552_ = lean_ctor_get(v_constraint_3550_, 0);
lean_inc(v_lowerBound_3552_);
v_upperBound_3553_ = lean_ctor_get(v_constraint_3550_, 1);
lean_inc(v_upperBound_3553_);
lean_dec_ref(v_constraint_3550_);
v___x_3554_ = l_List_toString___redArg(v___x_3548_, v_coeffs_3551_);
v___x_3555_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3556_ = lean_string_append(v___x_3554_, v___x_3555_);
if (lean_obj_tag(v_lowerBound_3552_) == 0)
{
if (lean_obj_tag(v_upperBound_3553_) == 0)
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3565_ = lean_string_append(v___x_3556_, v___x_3564_);
return v___x_3565_;
}
else
{
lean_object* v_val_3566_; lean_object* v___x_3567_; lean_object* v___y_3569_; lean_object* v_intZero_3574_; uint8_t v_isNeg_3575_; 
v_val_3566_ = lean_ctor_get(v_upperBound_3553_, 0);
lean_inc(v_val_3566_);
lean_dec_ref_known(v_upperBound_3553_, 1);
v___x_3567_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3574_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3575_ = lean_int_dec_lt(v_val_3566_, v_intZero_3574_);
if (v_isNeg_3575_ == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3577_; 
v_a_3576_ = lean_nat_abs(v_val_3566_);
lean_dec(v_val_3566_);
v___x_3577_ = l_Nat_reprFast(v_a_3576_);
v___y_3569_ = v___x_3577_;
goto v___jp_3568_;
}
else
{
lean_object* v_abs_3578_; lean_object* v_one_3579_; lean_object* v_a_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v_abs_3578_ = lean_nat_abs(v_val_3566_);
lean_dec(v_val_3566_);
v_one_3579_ = lean_unsigned_to_nat(1u);
v_a_3580_ = lean_nat_sub(v_abs_3578_, v_one_3579_);
lean_dec(v_abs_3578_);
v___x_3581_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3582_ = lean_nat_add(v_a_3580_, v_one_3579_);
lean_dec(v_a_3580_);
v___x_3583_ = l_Nat_reprFast(v___x_3582_);
v___x_3584_ = lean_string_append(v___x_3581_, v___x_3583_);
lean_dec_ref(v___x_3583_);
v___y_3569_ = v___x_3584_;
goto v___jp_3568_;
}
v___jp_3568_:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3570_ = lean_string_append(v___x_3567_, v___y_3569_);
lean_dec_ref(v___y_3569_);
v___x_3571_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3572_ = lean_string_append(v___x_3570_, v___x_3571_);
v___x_3573_ = lean_string_append(v___x_3556_, v___x_3572_);
lean_dec_ref(v___x_3572_);
return v___x_3573_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3553_) == 0)
{
lean_object* v_val_3585_; lean_object* v___x_3586_; lean_object* v___y_3588_; lean_object* v_intZero_3593_; uint8_t v_isNeg_3594_; 
v_val_3585_ = lean_ctor_get(v_lowerBound_3552_, 0);
lean_inc(v_val_3585_);
lean_dec_ref_known(v_lowerBound_3552_, 1);
v___x_3586_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3593_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3594_ = lean_int_dec_lt(v_val_3585_, v_intZero_3593_);
if (v_isNeg_3594_ == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3596_; 
v_a_3595_ = lean_nat_abs(v_val_3585_);
lean_dec(v_val_3585_);
v___x_3596_ = l_Nat_reprFast(v_a_3595_);
v___y_3588_ = v___x_3596_;
goto v___jp_3587_;
}
else
{
lean_object* v_abs_3597_; lean_object* v_one_3598_; lean_object* v_a_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v_abs_3597_ = lean_nat_abs(v_val_3585_);
lean_dec(v_val_3585_);
v_one_3598_ = lean_unsigned_to_nat(1u);
v_a_3599_ = lean_nat_sub(v_abs_3597_, v_one_3598_);
lean_dec(v_abs_3597_);
v___x_3600_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3601_ = lean_nat_add(v_a_3599_, v_one_3598_);
lean_dec(v_a_3599_);
v___x_3602_ = l_Nat_reprFast(v___x_3601_);
v___x_3603_ = lean_string_append(v___x_3600_, v___x_3602_);
lean_dec_ref(v___x_3602_);
v___y_3588_ = v___x_3603_;
goto v___jp_3587_;
}
v___jp_3587_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3589_ = lean_string_append(v___x_3586_, v___y_3588_);
lean_dec_ref(v___y_3588_);
v___x_3590_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3591_ = lean_string_append(v___x_3589_, v___x_3590_);
v___x_3592_ = lean_string_append(v___x_3556_, v___x_3591_);
lean_dec_ref(v___x_3591_);
return v___x_3592_;
}
}
else
{
lean_object* v_val_3604_; lean_object* v_val_3605_; uint8_t v___x_3606_; 
v_val_3604_ = lean_ctor_get(v_lowerBound_3552_, 0);
lean_inc(v_val_3604_);
lean_dec_ref_known(v_lowerBound_3552_, 1);
v_val_3605_ = lean_ctor_get(v_upperBound_3553_, 0);
lean_inc(v_val_3605_);
lean_dec_ref_known(v_upperBound_3553_, 1);
v___x_3606_ = lean_int_dec_lt(v_val_3605_, v_val_3604_);
if (v___x_3606_ == 0)
{
uint8_t v___x_3607_; 
v___x_3607_ = lean_int_dec_eq(v_val_3604_, v_val_3605_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; lean_object* v___y_3610_; lean_object* v_intZero_3625_; uint8_t v_isNeg_3626_; 
v___x_3608_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3625_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3626_ = lean_int_dec_lt(v_val_3604_, v_intZero_3625_);
if (v_isNeg_3626_ == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3628_; 
v_a_3627_ = lean_nat_abs(v_val_3604_);
lean_dec(v_val_3604_);
v___x_3628_ = l_Nat_reprFast(v_a_3627_);
v___y_3610_ = v___x_3628_;
goto v___jp_3609_;
}
else
{
lean_object* v_abs_3629_; lean_object* v_one_3630_; lean_object* v_a_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v_abs_3629_ = lean_nat_abs(v_val_3604_);
lean_dec(v_val_3604_);
v_one_3630_ = lean_unsigned_to_nat(1u);
v_a_3631_ = lean_nat_sub(v_abs_3629_, v_one_3630_);
lean_dec(v_abs_3629_);
v___x_3632_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3633_ = lean_nat_add(v_a_3631_, v_one_3630_);
lean_dec(v_a_3631_);
v___x_3634_ = l_Nat_reprFast(v___x_3633_);
v___x_3635_ = lean_string_append(v___x_3632_, v___x_3634_);
lean_dec_ref(v___x_3634_);
v___y_3610_ = v___x_3635_;
goto v___jp_3609_;
}
v___jp_3609_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v_intZero_3614_; uint8_t v_isNeg_3615_; 
v___x_3611_ = lean_string_append(v___x_3608_, v___y_3610_);
lean_dec_ref(v___y_3610_);
v___x_3612_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3613_ = lean_string_append(v___x_3611_, v___x_3612_);
v_intZero_3614_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3615_ = lean_int_dec_lt(v_val_3605_, v_intZero_3614_);
if (v_isNeg_3615_ == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3617_; 
v_a_3616_ = lean_nat_abs(v_val_3605_);
lean_dec(v_val_3605_);
v___x_3617_ = l_Nat_reprFast(v_a_3616_);
v___y_3558_ = v___x_3613_;
v___y_3559_ = v___x_3617_;
goto v___jp_3557_;
}
else
{
lean_object* v_abs_3618_; lean_object* v_one_3619_; lean_object* v_a_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v_abs_3618_ = lean_nat_abs(v_val_3605_);
lean_dec(v_val_3605_);
v_one_3619_ = lean_unsigned_to_nat(1u);
v_a_3620_ = lean_nat_sub(v_abs_3618_, v_one_3619_);
lean_dec(v_abs_3618_);
v___x_3621_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3622_ = lean_nat_add(v_a_3620_, v_one_3619_);
lean_dec(v_a_3620_);
v___x_3623_ = l_Nat_reprFast(v___x_3622_);
v___x_3624_ = lean_string_append(v___x_3621_, v___x_3623_);
lean_dec_ref(v___x_3623_);
v___y_3558_ = v___x_3613_;
v___y_3559_ = v___x_3624_;
goto v___jp_3557_;
}
}
}
else
{
lean_object* v___x_3636_; lean_object* v___y_3638_; lean_object* v_intZero_3643_; uint8_t v_isNeg_3644_; 
lean_dec(v_val_3605_);
v___x_3636_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3643_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3644_ = lean_int_dec_lt(v_val_3604_, v_intZero_3643_);
if (v_isNeg_3644_ == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3646_; 
v_a_3645_ = lean_nat_abs(v_val_3604_);
lean_dec(v_val_3604_);
v___x_3646_ = l_Nat_reprFast(v_a_3645_);
v___y_3638_ = v___x_3646_;
goto v___jp_3637_;
}
else
{
lean_object* v_abs_3647_; lean_object* v_one_3648_; lean_object* v_a_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v_abs_3647_ = lean_nat_abs(v_val_3604_);
lean_dec(v_val_3604_);
v_one_3648_ = lean_unsigned_to_nat(1u);
v_a_3649_ = lean_nat_sub(v_abs_3647_, v_one_3648_);
lean_dec(v_abs_3647_);
v___x_3650_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3651_ = lean_nat_add(v_a_3649_, v_one_3648_);
lean_dec(v_a_3649_);
v___x_3652_ = l_Nat_reprFast(v___x_3651_);
v___x_3653_ = lean_string_append(v___x_3650_, v___x_3652_);
lean_dec_ref(v___x_3652_);
v___y_3638_ = v___x_3653_;
goto v___jp_3637_;
}
v___jp_3637_:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3639_ = lean_string_append(v___x_3636_, v___y_3638_);
lean_dec_ref(v___y_3638_);
v___x_3640_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3641_ = lean_string_append(v___x_3639_, v___x_3640_);
v___x_3642_ = lean_string_append(v___x_3556_, v___x_3641_);
lean_dec_ref(v___x_3641_);
return v___x_3642_;
}
}
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
lean_dec(v_val_3605_);
lean_dec(v_val_3604_);
v___x_3654_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3655_ = lean_string_append(v___x_3556_, v___x_3654_);
return v___x_3655_;
}
}
}
v___jp_3557_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3560_ = lean_string_append(v___y_3558_, v___y_3559_);
lean_dec_ref(v___y_3559_);
v___x_3561_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3562_ = lean_string_append(v___x_3560_, v___x_3561_);
v___x_3563_ = lean_string_append(v___x_3556_, v___x_3562_);
lean_dec_ref(v___x_3562_);
return v___x_3563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1(lean_object* v___x_3656_, lean_object* v_x_3657_){
_start:
{
lean_object* v_fst_3658_; lean_object* v_constraint_3659_; lean_object* v_coeffs_3660_; lean_object* v_lowerBound_3661_; lean_object* v_upperBound_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___y_3667_; lean_object* v___y_3668_; 
v_fst_3658_ = lean_ctor_get(v_x_3657_, 0);
lean_inc(v_fst_3658_);
lean_dec_ref(v_x_3657_);
v_constraint_3659_ = lean_ctor_get(v_fst_3658_, 1);
lean_inc_ref(v_constraint_3659_);
v_coeffs_3660_ = lean_ctor_get(v_fst_3658_, 0);
lean_inc(v_coeffs_3660_);
lean_dec(v_fst_3658_);
v_lowerBound_3661_ = lean_ctor_get(v_constraint_3659_, 0);
lean_inc(v_lowerBound_3661_);
v_upperBound_3662_ = lean_ctor_get(v_constraint_3659_, 1);
lean_inc(v_upperBound_3662_);
lean_dec_ref(v_constraint_3659_);
v___x_3663_ = l_List_toString___redArg(v___x_3656_, v_coeffs_3660_);
v___x_3664_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3665_ = lean_string_append(v___x_3663_, v___x_3664_);
if (lean_obj_tag(v_lowerBound_3661_) == 0)
{
if (lean_obj_tag(v_upperBound_3662_) == 0)
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3674_ = lean_string_append(v___x_3665_, v___x_3673_);
return v___x_3674_;
}
else
{
lean_object* v_val_3675_; lean_object* v___x_3676_; lean_object* v___y_3678_; lean_object* v_intZero_3683_; uint8_t v_isNeg_3684_; 
v_val_3675_ = lean_ctor_get(v_upperBound_3662_, 0);
lean_inc(v_val_3675_);
lean_dec_ref_known(v_upperBound_3662_, 1);
v___x_3676_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3683_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3684_ = lean_int_dec_lt(v_val_3675_, v_intZero_3683_);
if (v_isNeg_3684_ == 0)
{
lean_object* v_a_3685_; lean_object* v___x_3686_; 
v_a_3685_ = lean_nat_abs(v_val_3675_);
lean_dec(v_val_3675_);
v___x_3686_ = l_Nat_reprFast(v_a_3685_);
v___y_3678_ = v___x_3686_;
goto v___jp_3677_;
}
else
{
lean_object* v_abs_3687_; lean_object* v_one_3688_; lean_object* v_a_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v_abs_3687_ = lean_nat_abs(v_val_3675_);
lean_dec(v_val_3675_);
v_one_3688_ = lean_unsigned_to_nat(1u);
v_a_3689_ = lean_nat_sub(v_abs_3687_, v_one_3688_);
lean_dec(v_abs_3687_);
v___x_3690_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3691_ = lean_nat_add(v_a_3689_, v_one_3688_);
lean_dec(v_a_3689_);
v___x_3692_ = l_Nat_reprFast(v___x_3691_);
v___x_3693_ = lean_string_append(v___x_3690_, v___x_3692_);
lean_dec_ref(v___x_3692_);
v___y_3678_ = v___x_3693_;
goto v___jp_3677_;
}
v___jp_3677_:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3679_ = lean_string_append(v___x_3676_, v___y_3678_);
lean_dec_ref(v___y_3678_);
v___x_3680_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3681_ = lean_string_append(v___x_3679_, v___x_3680_);
v___x_3682_ = lean_string_append(v___x_3665_, v___x_3681_);
lean_dec_ref(v___x_3681_);
return v___x_3682_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3662_) == 0)
{
lean_object* v_val_3694_; lean_object* v___x_3695_; lean_object* v___y_3697_; lean_object* v_intZero_3702_; uint8_t v_isNeg_3703_; 
v_val_3694_ = lean_ctor_get(v_lowerBound_3661_, 0);
lean_inc(v_val_3694_);
lean_dec_ref_known(v_lowerBound_3661_, 1);
v___x_3695_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3702_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3703_ = lean_int_dec_lt(v_val_3694_, v_intZero_3702_);
if (v_isNeg_3703_ == 0)
{
lean_object* v_a_3704_; lean_object* v___x_3705_; 
v_a_3704_ = lean_nat_abs(v_val_3694_);
lean_dec(v_val_3694_);
v___x_3705_ = l_Nat_reprFast(v_a_3704_);
v___y_3697_ = v___x_3705_;
goto v___jp_3696_;
}
else
{
lean_object* v_abs_3706_; lean_object* v_one_3707_; lean_object* v_a_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v_abs_3706_ = lean_nat_abs(v_val_3694_);
lean_dec(v_val_3694_);
v_one_3707_ = lean_unsigned_to_nat(1u);
v_a_3708_ = lean_nat_sub(v_abs_3706_, v_one_3707_);
lean_dec(v_abs_3706_);
v___x_3709_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3710_ = lean_nat_add(v_a_3708_, v_one_3707_);
lean_dec(v_a_3708_);
v___x_3711_ = l_Nat_reprFast(v___x_3710_);
v___x_3712_ = lean_string_append(v___x_3709_, v___x_3711_);
lean_dec_ref(v___x_3711_);
v___y_3697_ = v___x_3712_;
goto v___jp_3696_;
}
v___jp_3696_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3698_ = lean_string_append(v___x_3695_, v___y_3697_);
lean_dec_ref(v___y_3697_);
v___x_3699_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3700_ = lean_string_append(v___x_3698_, v___x_3699_);
v___x_3701_ = lean_string_append(v___x_3665_, v___x_3700_);
lean_dec_ref(v___x_3700_);
return v___x_3701_;
}
}
else
{
lean_object* v_val_3713_; lean_object* v_val_3714_; uint8_t v___x_3715_; 
v_val_3713_ = lean_ctor_get(v_lowerBound_3661_, 0);
lean_inc(v_val_3713_);
lean_dec_ref_known(v_lowerBound_3661_, 1);
v_val_3714_ = lean_ctor_get(v_upperBound_3662_, 0);
lean_inc(v_val_3714_);
lean_dec_ref_known(v_upperBound_3662_, 1);
v___x_3715_ = lean_int_dec_lt(v_val_3714_, v_val_3713_);
if (v___x_3715_ == 0)
{
uint8_t v___x_3716_; 
v___x_3716_ = lean_int_dec_eq(v_val_3713_, v_val_3714_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; lean_object* v___y_3719_; lean_object* v_intZero_3734_; uint8_t v_isNeg_3735_; 
v___x_3717_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3734_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3735_ = lean_int_dec_lt(v_val_3713_, v_intZero_3734_);
if (v_isNeg_3735_ == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3737_; 
v_a_3736_ = lean_nat_abs(v_val_3713_);
lean_dec(v_val_3713_);
v___x_3737_ = l_Nat_reprFast(v_a_3736_);
v___y_3719_ = v___x_3737_;
goto v___jp_3718_;
}
else
{
lean_object* v_abs_3738_; lean_object* v_one_3739_; lean_object* v_a_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v_abs_3738_ = lean_nat_abs(v_val_3713_);
lean_dec(v_val_3713_);
v_one_3739_ = lean_unsigned_to_nat(1u);
v_a_3740_ = lean_nat_sub(v_abs_3738_, v_one_3739_);
lean_dec(v_abs_3738_);
v___x_3741_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3742_ = lean_nat_add(v_a_3740_, v_one_3739_);
lean_dec(v_a_3740_);
v___x_3743_ = l_Nat_reprFast(v___x_3742_);
v___x_3744_ = lean_string_append(v___x_3741_, v___x_3743_);
lean_dec_ref(v___x_3743_);
v___y_3719_ = v___x_3744_;
goto v___jp_3718_;
}
v___jp_3718_:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v_intZero_3723_; uint8_t v_isNeg_3724_; 
v___x_3720_ = lean_string_append(v___x_3717_, v___y_3719_);
lean_dec_ref(v___y_3719_);
v___x_3721_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3722_ = lean_string_append(v___x_3720_, v___x_3721_);
v_intZero_3723_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3724_ = lean_int_dec_lt(v_val_3714_, v_intZero_3723_);
if (v_isNeg_3724_ == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3726_; 
v_a_3725_ = lean_nat_abs(v_val_3714_);
lean_dec(v_val_3714_);
v___x_3726_ = l_Nat_reprFast(v_a_3725_);
v___y_3667_ = v___x_3722_;
v___y_3668_ = v___x_3726_;
goto v___jp_3666_;
}
else
{
lean_object* v_abs_3727_; lean_object* v_one_3728_; lean_object* v_a_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v_abs_3727_ = lean_nat_abs(v_val_3714_);
lean_dec(v_val_3714_);
v_one_3728_ = lean_unsigned_to_nat(1u);
v_a_3729_ = lean_nat_sub(v_abs_3727_, v_one_3728_);
lean_dec(v_abs_3727_);
v___x_3730_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3731_ = lean_nat_add(v_a_3729_, v_one_3728_);
lean_dec(v_a_3729_);
v___x_3732_ = l_Nat_reprFast(v___x_3731_);
v___x_3733_ = lean_string_append(v___x_3730_, v___x_3732_);
lean_dec_ref(v___x_3732_);
v___y_3667_ = v___x_3722_;
v___y_3668_ = v___x_3733_;
goto v___jp_3666_;
}
}
}
else
{
lean_object* v___x_3745_; lean_object* v___y_3747_; lean_object* v_intZero_3752_; uint8_t v_isNeg_3753_; 
lean_dec(v_val_3714_);
v___x_3745_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3752_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3753_ = lean_int_dec_lt(v_val_3713_, v_intZero_3752_);
if (v_isNeg_3753_ == 0)
{
lean_object* v_a_3754_; lean_object* v___x_3755_; 
v_a_3754_ = lean_nat_abs(v_val_3713_);
lean_dec(v_val_3713_);
v___x_3755_ = l_Nat_reprFast(v_a_3754_);
v___y_3747_ = v___x_3755_;
goto v___jp_3746_;
}
else
{
lean_object* v_abs_3756_; lean_object* v_one_3757_; lean_object* v_a_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v_abs_3756_ = lean_nat_abs(v_val_3713_);
lean_dec(v_val_3713_);
v_one_3757_ = lean_unsigned_to_nat(1u);
v_a_3758_ = lean_nat_sub(v_abs_3756_, v_one_3757_);
lean_dec(v_abs_3756_);
v___x_3759_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3760_ = lean_nat_add(v_a_3758_, v_one_3757_);
lean_dec(v_a_3758_);
v___x_3761_ = l_Nat_reprFast(v___x_3760_);
v___x_3762_ = lean_string_append(v___x_3759_, v___x_3761_);
lean_dec_ref(v___x_3761_);
v___y_3747_ = v___x_3762_;
goto v___jp_3746_;
}
v___jp_3746_:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3748_ = lean_string_append(v___x_3745_, v___y_3747_);
lean_dec_ref(v___y_3747_);
v___x_3749_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3750_ = lean_string_append(v___x_3748_, v___x_3749_);
v___x_3751_ = lean_string_append(v___x_3665_, v___x_3750_);
lean_dec_ref(v___x_3750_);
return v___x_3751_;
}
}
}
else
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
lean_dec(v_val_3714_);
lean_dec(v_val_3713_);
v___x_3763_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3764_ = lean_string_append(v___x_3665_, v___x_3763_);
return v___x_3764_;
}
}
}
v___jp_3666_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3669_ = lean_string_append(v___y_3667_, v___y_3668_);
lean_dec_ref(v___y_3668_);
v___x_3670_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3671_ = lean_string_append(v___x_3669_, v___x_3670_);
v___x_3672_ = lean_string_append(v___x_3665_, v___x_3671_);
lean_dec_ref(v___x_3671_);
return v___x_3672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2(lean_object* v___f_3769_, lean_object* v___f_3770_, lean_object* v___f_3771_, lean_object* v_d_3772_){
_start:
{
lean_object* v_var_3773_; lean_object* v_irrelevant_3774_; lean_object* v_lowerBounds_3775_; lean_object* v_upperBounds_3776_; lean_object* v___x_3777_; lean_object* v_irrelevant_3778_; lean_object* v_lowerBounds_3779_; lean_object* v_upperBounds_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v_var_3773_ = lean_ctor_get(v_d_3772_, 0);
lean_inc(v_var_3773_);
v_irrelevant_3774_ = lean_ctor_get(v_d_3772_, 1);
lean_inc(v_irrelevant_3774_);
v_lowerBounds_3775_ = lean_ctor_get(v_d_3772_, 2);
lean_inc(v_lowerBounds_3775_);
v_upperBounds_3776_ = lean_ctor_get(v_d_3772_, 3);
lean_inc(v_upperBounds_3776_);
lean_dec_ref(v_d_3772_);
v___x_3777_ = lean_box(0);
v_irrelevant_3778_ = l_List_mapTR_loop___redArg(v___f_3769_, v_irrelevant_3774_, v___x_3777_);
lean_inc_ref(v___f_3770_);
v_lowerBounds_3779_ = l_List_mapTR_loop___redArg(v___f_3770_, v_lowerBounds_3775_, v___x_3777_);
v_upperBounds_3780_ = l_List_mapTR_loop___redArg(v___f_3770_, v_upperBounds_3776_, v___x_3777_);
v___x_3781_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0));
v___x_3782_ = l_Nat_reprFast(v_var_3773_);
v___x_3783_ = lean_string_append(v___x_3781_, v___x_3782_);
lean_dec_ref(v___x_3782_);
v___x_3784_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_3785_ = lean_string_append(v___x_3783_, v___x_3784_);
v___x_3786_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1));
lean_inc_ref_n(v___f_3771_, 2);
v___x_3787_ = l_List_toString___redArg(v___f_3771_, v_irrelevant_3778_);
v___x_3788_ = lean_string_append(v___x_3786_, v___x_3787_);
lean_dec_ref(v___x_3787_);
v___x_3789_ = lean_string_append(v___x_3788_, v___x_3784_);
v___x_3790_ = lean_string_append(v___x_3785_, v___x_3789_);
lean_dec_ref(v___x_3789_);
v___x_3791_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2));
v___x_3792_ = l_List_toString___redArg(v___f_3771_, v_lowerBounds_3779_);
v___x_3793_ = lean_string_append(v___x_3791_, v___x_3792_);
lean_dec_ref(v___x_3792_);
v___x_3794_ = lean_string_append(v___x_3793_, v___x_3784_);
v___x_3795_ = lean_string_append(v___x_3790_, v___x_3794_);
lean_dec_ref(v___x_3794_);
v___x_3796_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3));
v___x_3797_ = l_List_toString___redArg(v___f_3771_, v_upperBounds_3780_);
v___x_3798_ = lean_string_append(v___x_3796_, v___x_3797_);
lean_dec_ref(v___x_3797_);
v___x_3799_ = lean_string_append(v___x_3795_, v___x_3798_);
lean_dec_ref(v___x_3798_);
return v___x_3799_;
}
}
uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(lean_object* v_d_3810_){
_start:
{
lean_object* v_lowerBounds_3811_; lean_object* v_upperBounds_3812_; uint8_t v___x_3813_; 
v_lowerBounds_3811_ = lean_ctor_get(v_d_3810_, 2);
v_upperBounds_3812_ = lean_ctor_get(v_d_3810_, 3);
v___x_3813_ = l_List_isEmpty___redArg(v_lowerBounds_3811_);
if (v___x_3813_ == 0)
{
return v___x_3813_;
}
else
{
uint8_t v___x_3814_; 
v___x_3814_ = l_List_isEmpty___redArg(v_upperBounds_3812_);
return v___x_3814_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_3810_ = stack[0].m_obj;
uint8_t v_res_3815_;
v_res_3815_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v_d_3810_);
stack->m_num = v_res_3815_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty___boxed(lean_object* v_d_3816_){
_start:
{
uint8_t v_res_3817_; lean_object* v_r_3818_; 
v_res_3817_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v_d_3816_);
lean_dec_ref(v_d_3816_);
v_r_3818_ = lean_box(v_res_3817_);
return v_r_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(lean_object* v_d_3819_){
_start:
{
lean_object* v_lowerBounds_3820_; lean_object* v_upperBounds_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v_lowerBounds_3820_ = lean_ctor_get(v_d_3819_, 2);
v_upperBounds_3821_ = lean_ctor_get(v_d_3819_, 3);
v___x_3822_ = l_List_lengthTR___redArg(v_lowerBounds_3820_);
v___x_3823_ = l_List_lengthTR___redArg(v_upperBounds_3821_);
v___x_3824_ = lean_nat_mul(v___x_3822_, v___x_3823_);
lean_dec(v___x_3823_);
lean_dec(v___x_3822_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size___boxed(lean_object* v_d_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_d_3825_);
lean_dec_ref(v_d_3825_);
return v_res_3826_;
}
}
uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(lean_object* v_d_3827_){
_start:
{
uint8_t v_lowerExact_3828_; 
v_lowerExact_3828_ = lean_ctor_get_uint8(v_d_3827_, sizeof(void*)*4);
if (v_lowerExact_3828_ == 0)
{
uint8_t v_upperExact_3829_; 
v_upperExact_3829_ = lean_ctor_get_uint8(v_d_3827_, sizeof(void*)*4 + 1);
return v_upperExact_3829_;
}
else
{
return v_lowerExact_3828_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_3827_ = stack[0].m_obj;
uint8_t v_res_3830_;
v_res_3830_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_d_3827_);
stack->m_num = v_res_3830_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact___boxed(lean_object* v_d_3831_){
_start:
{
uint8_t v_res_3832_; lean_object* v_r_3833_; 
v_res_3832_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_d_3831_);
lean_dec_ref(v_d_3831_);
v_r_3833_ = lean_box(v_res_3832_);
return v_r_3833_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(lean_object* v_x_3834_, lean_object* v_x_3835_){
_start:
{
if (lean_obj_tag(v_x_3835_) == 0)
{
return v_x_3834_;
}
else
{
lean_object* v_head_3836_; lean_object* v_tail_3837_; lean_object* v___x_3838_; uint8_t v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v_head_3836_ = lean_ctor_get(v_x_3835_, 0);
v_tail_3837_ = lean_ctor_get(v_x_3835_, 1);
v___x_3838_ = lean_box(0);
v___x_3839_ = 1;
lean_inc(v_head_3836_);
v___x_3840_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3840_, 0, v_head_3836_);
lean_ctor_set(v___x_3840_, 1, v___x_3838_);
lean_ctor_set(v___x_3840_, 2, v___x_3838_);
lean_ctor_set(v___x_3840_, 3, v___x_3838_);
lean_ctor_set_uint8(v___x_3840_, sizeof(void*)*4, v___x_3839_);
lean_ctor_set_uint8(v___x_3840_, sizeof(void*)*4 + 1, v___x_3839_);
v___x_3841_ = lean_array_push(v_x_3834_, v___x_3840_);
v_x_3834_ = v___x_3841_;
v_x_3835_ = v_tail_3837_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2___boxed(lean_object* v_x_3843_, lean_object* v_x_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v_x_3843_, v_x_3844_);
lean_dec(v_x_3844_);
return v_res_3845_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object* v___x_3846_, lean_object* v_b_3847_, lean_object* v___x_3848_, uint8_t v___x_3849_, lean_object* v_____r_3850_, lean_object* v_d_x27_3851_){
_start:
{
lean_object* v_upperBound_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3879_; 
v_upperBound_3852_ = lean_ctor_get(v___x_3846_, 1);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3879_ == 0)
{
lean_object* v_unused_3880_; 
v_unused_3880_ = lean_ctor_get(v___x_3846_, 0);
lean_dec(v_unused_3880_);
v___x_3854_ = v___x_3846_;
v_isShared_3855_ = v_isSharedCheck_3879_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_upperBound_3852_);
lean_dec(v___x_3846_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3879_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
if (lean_obj_tag(v_upperBound_3852_) == 0)
{
lean_del_object(v___x_3854_);
lean_dec(v___x_3848_);
lean_dec_ref(v_b_3847_);
return v_d_x27_3851_;
}
else
{
lean_object* v_var_3856_; lean_object* v_irrelevant_3857_; lean_object* v_lowerBounds_3858_; lean_object* v_upperBounds_3859_; uint8_t v_lowerExact_3860_; uint8_t v_upperExact_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3878_; 
lean_dec_ref_known(v_upperBound_3852_, 1);
v_var_3856_ = lean_ctor_get(v_d_x27_3851_, 0);
v_irrelevant_3857_ = lean_ctor_get(v_d_x27_3851_, 1);
v_lowerBounds_3858_ = lean_ctor_get(v_d_x27_3851_, 2);
v_upperBounds_3859_ = lean_ctor_get(v_d_x27_3851_, 3);
v_lowerExact_3860_ = lean_ctor_get_uint8(v_d_x27_3851_, sizeof(void*)*4);
v_upperExact_3861_ = lean_ctor_get_uint8(v_d_x27_3851_, sizeof(void*)*4 + 1);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_d_x27_3851_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3863_ = v_d_x27_3851_;
v_isShared_3864_ = v_isSharedCheck_3878_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_upperBounds_3859_);
lean_inc(v_lowerBounds_3858_);
lean_inc(v_irrelevant_3857_);
lean_inc(v_var_3856_);
lean_dec(v_d_x27_3851_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3878_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
lean_inc(v___x_3848_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 1, v___x_3848_);
lean_ctor_set(v___x_3854_, 0, v_b_3847_);
v___x_3866_ = v___x_3854_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_b_3847_);
lean_ctor_set(v_reuseFailAlloc_3877_, 1, v___x_3848_);
v___x_3866_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3867_; 
v___x_3867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
lean_ctor_set(v___x_3867_, 1, v_upperBounds_3859_);
if (v_upperExact_3861_ == 0)
{
lean_object* v___x_3869_; 
lean_dec(v___x_3848_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 3, v___x_3867_);
v___x_3869_ = v___x_3863_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_var_3856_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_irrelevant_3857_);
lean_ctor_set(v_reuseFailAlloc_3870_, 2, v_lowerBounds_3858_);
lean_ctor_set(v_reuseFailAlloc_3870_, 3, v___x_3867_);
lean_ctor_set_uint8(v_reuseFailAlloc_3870_, sizeof(void*)*4, v_lowerExact_3860_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_ctor_set_uint8(v___x_3869_, sizeof(void*)*4 + 1, v___x_3849_);
return v___x_3869_;
}
}
else
{
lean_object* v___x_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; lean_object* v___x_3875_; 
v___x_3871_ = lean_nat_abs(v___x_3848_);
lean_dec(v___x_3848_);
v___x_3872_ = lean_unsigned_to_nat(1u);
v___x_3873_ = lean_nat_dec_eq(v___x_3871_, v___x_3872_);
lean_dec(v___x_3871_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 3, v___x_3867_);
v___x_3875_ = v___x_3863_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_var_3856_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v_irrelevant_3857_);
lean_ctor_set(v_reuseFailAlloc_3876_, 2, v_lowerBounds_3858_);
lean_ctor_set(v_reuseFailAlloc_3876_, 3, v___x_3867_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, sizeof(void*)*4, v_lowerExact_3860_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*4 + 1, v___x_3873_);
return v___x_3875_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3846_ = stack[0].m_obj;
lean_object* v_b_3847_ = stack[1].m_obj;
lean_object* v___x_3848_ = stack[2].m_obj;
uint8_t v___x_3849_ = stack[3].m_num;
lean_object* v_____r_3850_ = stack[4].m_obj;
lean_object* v_d_x27_3851_ = stack[5].m_obj;
lean_object* v_res_3881_;
v_res_3881_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3846_, v_b_3847_, v___x_3848_, v___x_3849_, v_____r_3850_, v_d_x27_3851_);
stack->m_obj
 = v_res_3881_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0___boxed(lean_object* v___x_3882_, lean_object* v_b_3883_, lean_object* v___x_3884_, lean_object* v___x_3885_, lean_object* v_____r_3886_, lean_object* v_d_x27_3887_){
_start:
{
uint8_t v___x_1969__boxed_3888_; lean_object* v_res_3889_; 
v___x_1969__boxed_3888_ = lean_unbox(v___x_3885_);
v_res_3889_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3882_, v_b_3883_, v___x_3884_, v___x_1969__boxed_3888_, v_____r_3886_, v_d_x27_3887_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(lean_object* v_upperBound_3890_, lean_object* v_coeffs_3891_, lean_object* v_constraint_3892_, lean_object* v_b_3893_, lean_object* v_a_3894_, lean_object* v_b_3895_){
_start:
{
lean_object* v_a_3897_; uint8_t v___x_3901_; 
v___x_3901_ = lean_nat_dec_lt(v_a_3894_, v_upperBound_3890_);
if (v___x_3901_ == 0)
{
lean_dec(v_a_3894_);
lean_dec_ref(v_b_3893_);
lean_dec_ref(v_constraint_3892_);
return v_b_3895_;
}
else
{
lean_object* v___x_3902_; uint8_t v___x_3903_; 
v___x_3902_ = lean_array_get_size(v_b_3895_);
v___x_3903_ = lean_nat_dec_lt(v_a_3894_, v___x_3902_);
if (v___x_3903_ == 0)
{
v_a_3897_ = v_b_3895_;
goto v___jp_3896_;
}
else
{
lean_object* v___x_3904_; lean_object* v_v_3905_; lean_object* v___x_3906_; lean_object* v_xs_x27_3907_; lean_object* v___y_3909_; lean_object* v___x_3911_; uint8_t v___x_3912_; 
lean_inc(v_a_3894_);
v___x_3904_ = l_Lean_Omega_IntList_get(v_coeffs_3891_, v_a_3894_);
v_v_3905_ = lean_array_fget(v_b_3895_, v_a_3894_);
v___x_3906_ = lean_box(0);
v_xs_x27_3907_ = lean_array_fset(v_b_3895_, v_a_3894_, v___x_3906_);
v___x_3911_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3912_ = lean_int_dec_eq(v___x_3904_, v___x_3911_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; lean_object* v_lowerBound_3914_; 
lean_inc_ref(v_constraint_3892_);
lean_inc(v___x_3904_);
v___x_3913_ = l_Lean_Omega_Constraint_scale(v___x_3904_, v_constraint_3892_);
v_lowerBound_3914_ = lean_ctor_get(v___x_3913_, 0);
if (lean_obj_tag(v_lowerBound_3914_) == 0)
{
lean_object* v___x_3915_; 
lean_inc_ref(v_b_3893_);
v___x_3915_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3913_, v_b_3893_, v___x_3904_, v___x_3912_, v___x_3906_, v_v_3905_);
v___y_3909_ = v___x_3915_;
goto v___jp_3908_;
}
else
{
lean_object* v_var_3916_; lean_object* v_irrelevant_3917_; lean_object* v_lowerBounds_3918_; lean_object* v_upperBounds_3919_; uint8_t v_lowerExact_3920_; uint8_t v_upperExact_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3936_; 
v_var_3916_ = lean_ctor_get(v_v_3905_, 0);
v_irrelevant_3917_ = lean_ctor_get(v_v_3905_, 1);
v_lowerBounds_3918_ = lean_ctor_get(v_v_3905_, 2);
v_upperBounds_3919_ = lean_ctor_get(v_v_3905_, 3);
v_lowerExact_3920_ = lean_ctor_get_uint8(v_v_3905_, sizeof(void*)*4);
v_upperExact_3921_ = lean_ctor_get_uint8(v_v_3905_, sizeof(void*)*4 + 1);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_v_3905_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3923_ = v_v_3905_;
v_isShared_3924_ = v_isSharedCheck_3936_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_upperBounds_3919_);
lean_inc(v_lowerBounds_3918_);
lean_inc(v_irrelevant_3917_);
lean_inc(v_var_3916_);
lean_dec(v_v_3905_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3936_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; uint8_t v___y_3928_; 
lean_inc(v___x_3904_);
lean_inc_ref(v_b_3893_);
v___x_3925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3925_, 0, v_b_3893_);
lean_ctor_set(v___x_3925_, 1, v___x_3904_);
v___x_3926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
lean_ctor_set(v___x_3926_, 1, v_lowerBounds_3918_);
if (v_lowerExact_3920_ == 0)
{
v___y_3928_ = v___x_3912_;
goto v___jp_3927_;
}
else
{
lean_object* v___x_3933_; lean_object* v___x_3934_; uint8_t v___x_3935_; 
v___x_3933_ = lean_nat_abs(v___x_3904_);
v___x_3934_ = lean_unsigned_to_nat(1u);
v___x_3935_ = lean_nat_dec_eq(v___x_3933_, v___x_3934_);
lean_dec(v___x_3933_);
v___y_3928_ = v___x_3935_;
goto v___jp_3927_;
}
v___jp_3927_:
{
lean_object* v___x_3930_; 
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 2, v___x_3926_);
v___x_3930_ = v___x_3923_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_var_3916_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v_irrelevant_3917_);
lean_ctor_set(v_reuseFailAlloc_3932_, 2, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3932_, 3, v_upperBounds_3919_);
lean_ctor_set_uint8(v_reuseFailAlloc_3932_, sizeof(void*)*4 + 1, v_upperExact_3921_);
v___x_3930_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3931_; 
lean_ctor_set_uint8(v___x_3930_, sizeof(void*)*4, v___y_3928_);
lean_inc_ref(v_b_3893_);
v___x_3931_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3913_, v_b_3893_, v___x_3904_, v___x_3912_, v___x_3906_, v___x_3930_);
v___y_3909_ = v___x_3931_;
goto v___jp_3908_;
}
}
}
}
}
else
{
lean_object* v_var_3937_; lean_object* v_irrelevant_3938_; lean_object* v_lowerBounds_3939_; lean_object* v_upperBounds_3940_; uint8_t v_lowerExact_3941_; uint8_t v_upperExact_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3950_; 
lean_dec(v___x_3904_);
v_var_3937_ = lean_ctor_get(v_v_3905_, 0);
v_irrelevant_3938_ = lean_ctor_get(v_v_3905_, 1);
v_lowerBounds_3939_ = lean_ctor_get(v_v_3905_, 2);
v_upperBounds_3940_ = lean_ctor_get(v_v_3905_, 3);
v_lowerExact_3941_ = lean_ctor_get_uint8(v_v_3905_, sizeof(void*)*4);
v_upperExact_3942_ = lean_ctor_get_uint8(v_v_3905_, sizeof(void*)*4 + 1);
v_isSharedCheck_3950_ = !lean_is_exclusive(v_v_3905_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3944_ = v_v_3905_;
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_upperBounds_3940_);
lean_inc(v_lowerBounds_3939_);
lean_inc(v_irrelevant_3938_);
lean_inc(v_var_3937_);
lean_dec(v_v_3905_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3946_; lean_object* v___x_3948_; 
lean_inc_ref(v_b_3893_);
v___x_3946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3946_, 0, v_b_3893_);
lean_ctor_set(v___x_3946_, 1, v_irrelevant_3938_);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 1, v___x_3946_);
v___x_3948_ = v___x_3944_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_var_3937_);
lean_ctor_set(v_reuseFailAlloc_3949_, 1, v___x_3946_);
lean_ctor_set(v_reuseFailAlloc_3949_, 2, v_lowerBounds_3939_);
lean_ctor_set(v_reuseFailAlloc_3949_, 3, v_upperBounds_3940_);
lean_ctor_set_uint8(v_reuseFailAlloc_3949_, sizeof(void*)*4, v_lowerExact_3941_);
lean_ctor_set_uint8(v_reuseFailAlloc_3949_, sizeof(void*)*4 + 1, v_upperExact_3942_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
v___y_3909_ = v___x_3948_;
goto v___jp_3908_;
}
}
}
v___jp_3908_:
{
lean_object* v___x_3910_; 
v___x_3910_ = lean_array_fset(v_xs_x27_3907_, v_a_3894_, v___y_3909_);
v_a_3897_ = v___x_3910_;
goto v___jp_3896_;
}
}
}
v___jp_3896_:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = lean_unsigned_to_nat(1u);
v___x_3899_ = lean_nat_add(v_a_3894_, v___x_3898_);
lean_dec(v_a_3894_);
v_a_3894_ = v___x_3899_;
v_b_3895_ = v_a_3897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___boxed(lean_object* v_upperBound_3951_, lean_object* v_coeffs_3952_, lean_object* v_constraint_3953_, lean_object* v_b_3954_, lean_object* v_a_3955_, lean_object* v_b_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3951_, v_coeffs_3952_, v_constraint_3953_, v_b_3954_, v_a_3955_, v_b_3956_);
lean_dec(v_coeffs_3952_);
lean_dec(v_upperBound_3951_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(lean_object* v_n_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
if (lean_obj_tag(v_a_3959_) == 0)
{
lean_object* v___x_3961_; 
v___x_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3961_, 0, v_a_3960_);
return v___x_3961_;
}
else
{
lean_object* v_value_3962_; lean_object* v_tail_3963_; lean_object* v_coeffs_3964_; lean_object* v_constraint_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v_value_3962_ = lean_ctor_get(v_a_3959_, 1);
lean_inc(v_value_3962_);
v_tail_3963_ = lean_ctor_get(v_a_3959_, 2);
lean_inc(v_tail_3963_);
lean_dec_ref_known(v_a_3959_, 3);
v_coeffs_3964_ = lean_ctor_get(v_value_3962_, 0);
lean_inc(v_coeffs_3964_);
v_constraint_3965_ = lean_ctor_get(v_value_3962_, 1);
lean_inc_ref(v_constraint_3965_);
v___x_3966_ = lean_unsigned_to_nat(0u);
v___x_3967_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_n_3958_, v_coeffs_3964_, v_constraint_3965_, v_value_3962_, v___x_3966_, v_a_3960_);
lean_dec(v_coeffs_3964_);
v_a_3959_ = v_tail_3963_;
v_a_3960_ = v___x_3967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1___boxed(lean_object* v_n_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3969_, v_a_3970_, v_a_3971_);
lean_dec(v_n_3969_);
return v_res_3972_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(lean_object* v_n_3973_, lean_object* v_as_3974_, size_t v_sz_3975_, size_t v_i_3976_, lean_object* v_b_3977_){
_start:
{
uint8_t v___x_3978_; 
v___x_3978_ = lean_usize_dec_lt(v_i_3976_, v_sz_3975_);
if (v___x_3978_ == 0)
{
return v_b_3977_;
}
else
{
lean_object* v_a_3979_; lean_object* v___x_3980_; 
v_a_3979_ = lean_array_uget_borrowed(v_as_3974_, v_i_3976_);
lean_inc(v_a_3979_);
v___x_3980_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3973_, v_a_3979_, v_b_3977_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_3981_);
lean_dec_ref_known(v___x_3980_, 1);
return v_a_3981_;
}
else
{
lean_object* v_a_3982_; size_t v___x_3983_; size_t v___x_3984_; 
v_a_3982_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v___x_3980_, 1);
v___x_3983_ = ((size_t)1ULL);
v___x_3984_ = lean_usize_add(v_i_3976_, v___x_3983_);
v_i_3976_ = v___x_3984_;
v_b_3977_ = v_a_3982_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3973_ = stack[0].m_obj;
lean_object* v_as_3974_ = stack[1].m_obj;
size_t v_sz_3975_ = stack[2].m_num;
size_t v_i_3976_ = stack[3].m_num;
lean_object* v_b_3977_ = stack[4].m_obj;
lean_object* v_res_3986_;
v_res_3986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_n_3973_, v_as_3974_, v_sz_3975_, v_i_3976_, v_b_3977_);
stack->m_obj
 = v_res_3986_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3___boxed(lean_object* v_n_3987_, lean_object* v_as_3988_, lean_object* v_sz_3989_, lean_object* v_i_3990_, lean_object* v_b_3991_){
_start:
{
size_t v_sz_boxed_3992_; size_t v_i_boxed_3993_; lean_object* v_res_3994_; 
v_sz_boxed_3992_ = lean_unbox_usize(v_sz_3989_);
lean_dec(v_sz_3989_);
v_i_boxed_3993_ = lean_unbox_usize(v_i_3990_);
lean_dec(v_i_3990_);
v_res_3994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_n_3987_, v_as_3988_, v_sz_boxed_3992_, v_i_boxed_3993_, v_b_3991_);
lean_dec_ref(v_as_3988_);
lean_dec(v_n_3987_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(lean_object* v_p_3997_){
_start:
{
lean_object* v_constraints_3998_; lean_object* v_numVars_3999_; lean_object* v_buckets_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v_data_4003_; size_t v_sz_4004_; size_t v___x_4005_; lean_object* v___x_4006_; 
v_constraints_3998_ = lean_ctor_get(v_p_3997_, 2);
lean_inc_ref(v_constraints_3998_);
v_numVars_3999_ = lean_ctor_get(v_p_3997_, 1);
lean_inc_n(v_numVars_3999_, 2);
lean_dec_ref(v_p_3997_);
v_buckets_4000_ = lean_ctor_get(v_constraints_3998_, 1);
lean_inc_ref(v_buckets_4000_);
lean_dec_ref(v_constraints_3998_);
v___x_4001_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_4002_ = l_List_range(v_numVars_3999_);
v_data_4003_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v___x_4001_, v___x_4002_);
lean_dec(v___x_4002_);
v_sz_4004_ = lean_array_size(v_buckets_4000_);
v___x_4005_ = ((size_t)0ULL);
v___x_4006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_numVars_3999_, v_buckets_4000_, v_sz_4004_, v___x_4005_, v_data_4003_);
lean_dec_ref(v_buckets_4000_);
lean_dec(v_numVars_3999_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(lean_object* v_upperBound_4007_, lean_object* v_coeffs_4008_, lean_object* v_constraint_4009_, lean_object* v_b_4010_, lean_object* v_inst_4011_, lean_object* v_R_4012_, lean_object* v_a_4013_, lean_object* v_b_4014_, lean_object* v_c_4015_){
_start:
{
lean_object* v___x_4016_; 
v___x_4016_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_4007_, v_coeffs_4008_, v_constraint_4009_, v_b_4010_, v_a_4013_, v_b_4014_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___boxed(lean_object* v_upperBound_4017_, lean_object* v_coeffs_4018_, lean_object* v_constraint_4019_, lean_object* v_b_4020_, lean_object* v_inst_4021_, lean_object* v_R_4022_, lean_object* v_a_4023_, lean_object* v_b_4024_, lean_object* v_c_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(v_upperBound_4017_, v_coeffs_4018_, v_constraint_4019_, v_b_4020_, v_inst_4021_, v_R_4022_, v_a_4023_, v_b_4024_, v_c_4025_);
lean_dec(v_coeffs_4018_);
lean_dec(v_upperBound_4017_);
return v_res_4026_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(lean_object* v_cls_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_toCold_4036_; lean_object* v_options_4037_; uint8_t v_hasTrace_4038_; 
v_toCold_4036_ = lean_ctor_get(v___y_4033_, 0);
v_options_4037_ = lean_ctor_get(v_toCold_4036_, 2);
v_hasTrace_4038_ = lean_ctor_get_uint8(v_options_4037_, sizeof(void*)*1);
if (v_hasTrace_4038_ == 0)
{
lean_object* v___x_4039_; lean_object* v___x_4040_; 
lean_dec(v_cls_4030_);
v___x_4039_ = lean_box(v_hasTrace_4038_);
v___x_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4039_);
return v___x_4040_;
}
else
{
lean_object* v_inheritedTraceOptions_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; uint8_t v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v_inheritedTraceOptions_4041_ = lean_ctor_get(v_toCold_4036_, 11);
v___x_4042_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4043_ = l_Lean_Name_append(v___x_4042_, v_cls_4030_);
v___x_4044_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4041_, v_options_4037_, v___x_4043_);
lean_dec(v___x_4043_);
v___x_4045_ = lean_box(v___x_4044_);
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4030_ = stack[0].m_obj;
lean_object* v___y_4031_ = stack[1].m_obj;
lean_object* v___y_4032_ = stack[2].m_obj;
lean_object* v___y_4033_ = stack[3].m_obj;
lean_object* v___y_4034_ = stack[4].m_obj;
lean_object* v_res_4047_;
v_res_4047_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_);
stack->m_obj
 = v_res_4047_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___boxed(lean_object* v_cls_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
return v_res_4054_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(lean_object* v___x_4055_, lean_object* v_fst_4056_, lean_object* v_snd_4057_, lean_object* v_fst_4058_, lean_object* v_____r_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4055_);
v___x_4066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4066_, 0, v_fst_4056_);
lean_ctor_set(v___x_4066_, 1, v_snd_4057_);
v___x_4067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4067_, 0, v_fst_4058_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4065_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
v___x_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4068_);
v___x_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4069_);
return v___x_4070_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4055_ = stack[0].m_obj;
lean_object* v_fst_4056_ = stack[1].m_obj;
lean_object* v_snd_4057_ = stack[2].m_obj;
lean_object* v_fst_4058_ = stack[3].m_obj;
lean_object* v_____r_4059_ = stack[4].m_obj;
lean_object* v___y_4060_ = stack[5].m_obj;
lean_object* v___y_4061_ = stack[6].m_obj;
lean_object* v___y_4062_ = stack[7].m_obj;
lean_object* v___y_4063_ = stack[8].m_obj;
lean_object* v_res_4071_;
v_res_4071_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4055_, v_fst_4056_, v_snd_4057_, v_fst_4058_, v_____r_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
stack->m_obj
 = v_res_4071_;
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
lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(lean_object* v_cls_4087_, lean_object* v_msg_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v_ref_4094_; lean_object* v___x_4095_; lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4141_; 
v_ref_4094_ = lean_ctor_get(v___y_4091_, 2);
v___x_4095_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4098_ = v___x_4095_;
v_isShared_4099_ = v_isSharedCheck_4141_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4095_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4141_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4100_; lean_object* v_traceState_4101_; lean_object* v_env_4102_; lean_object* v_nextMacroScope_4103_; lean_object* v_ngen_4104_; lean_object* v_auxDeclNGen_4105_; lean_object* v_cache_4106_; lean_object* v_recordedDeps_4107_; lean_object* v_messages_4108_; lean_object* v_infoState_4109_; lean_object* v_snapshotTasks_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4140_; 
v___x_4100_ = lean_st_ref_take(v___y_4092_);
v_traceState_4101_ = lean_ctor_get(v___x_4100_, 4);
v_env_4102_ = lean_ctor_get(v___x_4100_, 0);
v_nextMacroScope_4103_ = lean_ctor_get(v___x_4100_, 1);
v_ngen_4104_ = lean_ctor_get(v___x_4100_, 2);
v_auxDeclNGen_4105_ = lean_ctor_get(v___x_4100_, 3);
v_cache_4106_ = lean_ctor_get(v___x_4100_, 5);
v_recordedDeps_4107_ = lean_ctor_get(v___x_4100_, 6);
v_messages_4108_ = lean_ctor_get(v___x_4100_, 7);
v_infoState_4109_ = lean_ctor_get(v___x_4100_, 8);
v_snapshotTasks_4110_ = lean_ctor_get(v___x_4100_, 9);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4112_ = v___x_4100_;
v_isShared_4113_ = v_isSharedCheck_4140_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_snapshotTasks_4110_);
lean_inc(v_infoState_4109_);
lean_inc(v_messages_4108_);
lean_inc(v_recordedDeps_4107_);
lean_inc(v_cache_4106_);
lean_inc(v_traceState_4101_);
lean_inc(v_auxDeclNGen_4105_);
lean_inc(v_ngen_4104_);
lean_inc(v_nextMacroScope_4103_);
lean_inc(v_env_4102_);
lean_dec(v___x_4100_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4140_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
uint64_t v_tid_4114_; lean_object* v_traces_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4139_; 
v_tid_4114_ = lean_ctor_get_uint64(v_traceState_4101_, sizeof(void*)*1);
v_traces_4115_ = lean_ctor_get(v_traceState_4101_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v_traceState_4101_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4117_ = v_traceState_4101_;
v_isShared_4118_ = v_isSharedCheck_4139_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_traces_4115_);
lean_dec(v_traceState_4101_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4139_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; double v___x_4121_; uint8_t v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4130_; 
v___x_4119_ = lean_box(0);
v___x_4120_ = lean_box(0);
v___x_4121_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4122_ = 0;
v___x_4123_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4124_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4124_, 0, v_cls_4087_);
lean_ctor_set(v___x_4124_, 1, v___x_4120_);
lean_ctor_set(v___x_4124_, 2, v___x_4123_);
lean_ctor_set_float(v___x_4124_, sizeof(void*)*3, v___x_4121_);
lean_ctor_set_float(v___x_4124_, sizeof(void*)*3 + 8, v___x_4121_);
lean_ctor_set_uint8(v___x_4124_, sizeof(void*)*3 + 16, v___x_4122_);
v___x_4125_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4126_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4124_);
lean_ctor_set(v___x_4126_, 1, v_a_4096_);
lean_ctor_set(v___x_4126_, 2, v___x_4125_);
lean_inc(v_ref_4094_);
v___x_4127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4127_, 0, v_ref_4094_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = l_Lean_PersistentArray_push___redArg(v_traces_4115_, v___x_4127_);
if (v_isShared_4118_ == 0)
{
lean_ctor_set(v___x_4117_, 0, v___x_4128_);
v___x_4130_ = v___x_4117_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_4128_);
lean_ctor_set_uint64(v_reuseFailAlloc_4138_, sizeof(void*)*1, v_tid_4114_);
v___x_4130_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
lean_object* v___x_4132_; 
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 4, v___x_4130_);
v___x_4132_ = v___x_4112_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_env_4102_);
lean_ctor_set(v_reuseFailAlloc_4137_, 1, v_nextMacroScope_4103_);
lean_ctor_set(v_reuseFailAlloc_4137_, 2, v_ngen_4104_);
lean_ctor_set(v_reuseFailAlloc_4137_, 3, v_auxDeclNGen_4105_);
lean_ctor_set(v_reuseFailAlloc_4137_, 4, v___x_4130_);
lean_ctor_set(v_reuseFailAlloc_4137_, 5, v_cache_4106_);
lean_ctor_set(v_reuseFailAlloc_4137_, 6, v_recordedDeps_4107_);
lean_ctor_set(v_reuseFailAlloc_4137_, 7, v_messages_4108_);
lean_ctor_set(v_reuseFailAlloc_4137_, 8, v_infoState_4109_);
lean_ctor_set(v_reuseFailAlloc_4137_, 9, v_snapshotTasks_4110_);
v___x_4132_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
lean_object* v___x_4133_; lean_object* v___x_4135_; 
v___x_4133_ = lean_st_ref_put(v___y_4092_, v___x_4132_);
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 0, v___x_4119_);
v___x_4135_ = v___x_4098_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4119_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4087_ = stack[0].m_obj;
lean_object* v_msg_4088_ = stack[1].m_obj;
lean_object* v___y_4089_ = stack[2].m_obj;
lean_object* v___y_4090_ = stack[3].m_obj;
lean_object* v___y_4091_ = stack[4].m_obj;
lean_object* v___y_4092_ = stack[5].m_obj;
lean_object* v_res_4142_;
v_res_4142_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4087_, v_msg_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
stack->m_obj
 = v_res_4142_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___boxed(lean_object* v_cls_4143_, lean_object* v_msg_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4143_, v_msg_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
return v_res_4150_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v_cls_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v_cls_4151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4152_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4153_ = l_Lean_Name_append(v___x_4152_, v_cls_4151_);
return v___x_4153_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4155_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__1));
v___x_4156_ = l_Lean_stringToMessageData(v___x_4155_);
return v___x_4156_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(lean_object* v_upperBound_4157_, lean_object* v___y_4158_, lean_object* v_a_4159_, lean_object* v_b_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v_a_4167_; lean_object* v___y_4172_; uint8_t v___x_4191_; 
v___x_4191_ = lean_nat_dec_lt(v_a_4159_, v_upperBound_4157_);
if (v___x_4191_ == 0)
{
lean_object* v___x_4192_; 
lean_dec(v_a_4159_);
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v_b_4160_);
return v___x_4192_;
}
else
{
lean_object* v_snd_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4264_; 
v_snd_4193_ = lean_ctor_get(v_b_4160_, 1);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_b_4160_);
if (v_isSharedCheck_4264_ == 0)
{
lean_object* v_unused_4265_; 
v_unused_4265_ = lean_ctor_get(v_b_4160_, 0);
lean_dec(v_unused_4265_);
v___x_4195_ = v_b_4160_;
v_isShared_4196_ = v_isSharedCheck_4264_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_snd_4193_);
lean_dec(v_b_4160_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4264_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v_snd_4197_; lean_object* v_fst_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4263_; 
v_snd_4197_ = lean_ctor_get(v_snd_4193_, 1);
v_fst_4198_ = lean_ctor_get(v_snd_4193_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v_snd_4193_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4200_ = v_snd_4193_;
v_isShared_4201_ = v_isSharedCheck_4263_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_snd_4197_);
lean_inc(v_fst_4198_);
lean_dec(v_snd_4193_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4263_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v_fst_4202_; lean_object* v_snd_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4262_; 
v_fst_4202_ = lean_ctor_get(v_snd_4197_, 0);
v_snd_4203_ = lean_ctor_get(v_snd_4197_, 1);
v_isSharedCheck_4262_ = !lean_is_exclusive(v_snd_4197_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4205_ = v_snd_4197_;
v_isShared_4206_ = v_isSharedCheck_4262_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_snd_4203_);
lean_inc(v_fst_4202_);
lean_dec(v_snd_4197_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4262_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4207_; lean_object* v_bestIdx_4218_; lean_object* v_cls_4219_; lean_object* v___x_4220_; uint8_t v___x_4224_; lean_object* v___x_4225_; uint8_t v___x_4226_; uint8_t v___y_4256_; 
v___x_4207_ = lean_box(0);
v_bestIdx_4218_ = lean_unsigned_to_nat(0u);
v_cls_4219_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4220_ = lean_array_fget_borrowed(v___y_4158_, v_a_4159_);
v___x_4224_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4220_);
v___x_4225_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4220_);
v___x_4226_ = lean_nat_dec_eq(v___x_4225_, v_bestIdx_4218_);
if (v___x_4226_ == 0)
{
uint8_t v___x_4261_; 
v___x_4261_ = lean_unbox(v_snd_4203_);
if (v___x_4261_ == 0)
{
if (v___x_4224_ == 0)
{
goto v___jp_4258_;
}
else
{
lean_del_object(v___x_4205_);
lean_del_object(v___x_4200_);
lean_del_object(v___x_4195_);
goto v___jp_4227_;
}
}
else
{
goto v___jp_4258_;
}
}
else
{
lean_del_object(v___x_4205_);
lean_del_object(v___x_4200_);
lean_del_object(v___x_4195_);
goto v___jp_4227_;
}
v___jp_4208_:
{
lean_object* v___x_4210_; 
if (v_isShared_4206_ == 0)
{
v___x_4210_ = v___x_4205_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_fst_4202_);
lean_ctor_set(v_reuseFailAlloc_4217_, 1, v_snd_4203_);
v___x_4210_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
lean_object* v___x_4212_; 
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 1, v___x_4210_);
v___x_4212_ = v___x_4200_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_fst_4198_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v___x_4210_);
v___x_4212_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
lean_object* v___x_4214_; 
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 1, v___x_4212_);
lean_ctor_set(v___x_4195_, 0, v___x_4207_);
v___x_4214_ = v___x_4195_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v___x_4207_);
lean_ctor_set(v_reuseFailAlloc_4215_, 1, v___x_4212_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
v_a_4167_ = v___x_4214_;
goto v___jp_4166_;
}
}
}
}
v___jp_4221_:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4222_ = lean_box(0);
lean_inc(v___x_4220_);
v___x_4223_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4220_, v_fst_4202_, v_snd_4203_, v_fst_4198_, v___x_4222_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
v___y_4172_ = v___x_4223_;
goto v___jp_4171_;
}
v___jp_4227_:
{
if (v___x_4226_ == 0)
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
lean_dec(v_snd_4203_);
lean_dec(v_fst_4202_);
lean_dec(v_fst_4198_);
v___x_4228_ = lean_box(v___x_4224_);
v___x_4229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4225_);
lean_ctor_set(v___x_4229_, 1, v___x_4228_);
lean_inc(v_a_4159_);
v___x_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4230_, 0, v_a_4159_);
lean_ctor_set(v___x_4230_, 1, v___x_4229_);
v___x_4231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4207_);
lean_ctor_set(v___x_4231_, 1, v___x_4230_);
v_a_4167_ = v___x_4231_;
goto v___jp_4166_;
}
else
{
lean_object* v_toCold_4232_; lean_object* v_options_4233_; uint8_t v_hasTrace_4234_; 
lean_dec(v___x_4225_);
v_toCold_4232_ = lean_ctor_get(v___y_4163_, 0);
v_options_4233_ = lean_ctor_get(v_toCold_4232_, 2);
v_hasTrace_4234_ = lean_ctor_get_uint8(v_options_4233_, sizeof(void*)*1);
if (v_hasTrace_4234_ == 0)
{
goto v___jp_4221_;
}
else
{
lean_object* v_inheritedTraceOptions_4235_; lean_object* v___x_4236_; uint8_t v___x_4237_; 
v_inheritedTraceOptions_4235_ = lean_ctor_get(v_toCold_4232_, 11);
v___x_4236_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_4237_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4235_, v_options_4233_, v___x_4236_);
if (v___x_4237_ == 0)
{
goto v___jp_4221_;
}
else
{
lean_object* v_var_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v_var_4238_ = lean_ctor_get(v___x_4220_, 0);
v___x_4239_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4238_);
v___x_4240_ = l_Nat_reprFast(v_var_4238_);
v___x_4241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4240_);
v___x_4242_ = l_Lean_MessageData_ofFormat(v___x_4241_);
v___x_4243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4239_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
v___x_4244_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4219_, v___x_4243_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v___x_4246_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref_known(v___x_4244_, 1);
lean_inc(v___x_4220_);
v___x_4246_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4220_, v_fst_4202_, v_snd_4203_, v_fst_4198_, v_a_4245_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
v___y_4172_ = v___x_4246_;
goto v___jp_4171_;
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
lean_dec(v_snd_4203_);
lean_dec(v_fst_4202_);
lean_dec(v_fst_4198_);
lean_dec(v_a_4159_);
v_a_4247_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4244_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4244_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
}
}
}
v___jp_4255_:
{
if (v___y_4256_ == 0)
{
lean_dec(v___x_4225_);
goto v___jp_4208_;
}
else
{
uint8_t v___x_4257_; 
v___x_4257_ = lean_nat_dec_lt(v___x_4225_, v_fst_4202_);
if (v___x_4257_ == 0)
{
lean_dec(v___x_4225_);
goto v___jp_4208_;
}
else
{
lean_del_object(v___x_4205_);
lean_del_object(v___x_4200_);
lean_del_object(v___x_4195_);
goto v___jp_4227_;
}
}
}
v___jp_4258_:
{
if (v___x_4224_ == 0)
{
uint8_t v___x_4259_; 
v___x_4259_ = lean_unbox(v_snd_4203_);
if (v___x_4259_ == 0)
{
v___y_4256_ = v___x_4191_;
goto v___jp_4255_;
}
else
{
v___y_4256_ = v___x_4224_;
goto v___jp_4255_;
}
}
else
{
uint8_t v___x_4260_; 
v___x_4260_ = lean_unbox(v_snd_4203_);
v___y_4256_ = v___x_4260_;
goto v___jp_4255_;
}
}
}
}
}
}
v___jp_4166_:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4168_ = lean_unsigned_to_nat(1u);
v___x_4169_ = lean_nat_add(v_a_4159_, v___x_4168_);
lean_dec(v_a_4159_);
v_a_4159_ = v___x_4169_;
v_b_4160_ = v_a_4167_;
goto _start;
}
v___jp_4171_:
{
if (lean_obj_tag(v___y_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4182_; 
v_a_4173_ = lean_ctor_get(v___y_4172_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___y_4172_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4175_ = v___y_4172_;
v_isShared_4176_ = v_isSharedCheck_4182_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___y_4172_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4182_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
if (lean_obj_tag(v_a_4173_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4179_; 
lean_dec(v_a_4159_);
v_a_4177_ = lean_ctor_get(v_a_4173_, 0);
lean_inc(v_a_4177_);
lean_dec_ref_known(v_a_4173_, 1);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v_a_4177_);
v___x_4179_ = v___x_4175_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4177_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
else
{
lean_object* v_a_4181_; 
lean_del_object(v___x_4175_);
v_a_4181_ = lean_ctor_get(v_a_4173_, 0);
lean_inc(v_a_4181_);
lean_dec_ref_known(v_a_4173_, 1);
v_a_4167_ = v_a_4181_;
goto v___jp_4166_;
}
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
lean_dec(v_a_4159_);
v_a_4183_ = lean_ctor_get(v___y_4172_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___y_4172_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___y_4172_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___y_4172_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_4157_ = stack[0].m_obj;
lean_object* v___y_4158_ = stack[1].m_obj;
lean_object* v_a_4159_ = stack[2].m_obj;
lean_object* v_b_4160_ = stack[3].m_obj;
lean_object* v___y_4161_ = stack[4].m_obj;
lean_object* v___y_4162_ = stack[5].m_obj;
lean_object* v___y_4163_ = stack[6].m_obj;
lean_object* v___y_4164_ = stack[7].m_obj;
lean_object* v_res_4266_;
v_res_4266_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4157_, v___y_4158_, v_a_4159_, v_b_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
stack->m_obj
 = v_res_4266_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___boxed(lean_object* v_upperBound_4267_, lean_object* v___y_4268_, lean_object* v_a_4269_, lean_object* v_b_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4267_, v___y_4268_, v_a_4269_, v_b_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec_ref(v___y_4268_);
lean_dec(v_upperBound_4267_);
return v_res_4276_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(lean_object* v_as_4277_, size_t v_i_4278_, size_t v_stop_4279_, lean_object* v_b_4280_){
_start:
{
lean_object* v___y_4282_; uint8_t v___x_4286_; 
v___x_4286_ = lean_usize_dec_eq(v_i_4278_, v_stop_4279_);
if (v___x_4286_ == 0)
{
lean_object* v___x_4287_; uint8_t v___x_4290_; 
v___x_4287_ = lean_array_uget_borrowed(v_as_4277_, v_i_4278_);
v___x_4290_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v___x_4287_);
if (v___x_4290_ == 0)
{
goto v___jp_4288_;
}
else
{
if (v___x_4286_ == 0)
{
v___y_4282_ = v_b_4280_;
goto v___jp_4281_;
}
else
{
goto v___jp_4288_;
}
}
v___jp_4288_:
{
lean_object* v___x_4289_; 
lean_inc(v___x_4287_);
v___x_4289_ = lean_array_push(v_b_4280_, v___x_4287_);
v___y_4282_ = v___x_4289_;
goto v___jp_4281_;
}
}
else
{
return v_b_4280_;
}
v___jp_4281_:
{
size_t v___x_4283_; size_t v___x_4284_; 
v___x_4283_ = ((size_t)1ULL);
v___x_4284_ = lean_usize_add(v_i_4278_, v___x_4283_);
v_i_4278_ = v___x_4284_;
v_b_4280_ = v___y_4282_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4277_ = stack[0].m_obj;
size_t v_i_4278_ = stack[1].m_num;
size_t v_stop_4279_ = stack[2].m_num;
lean_object* v_b_4280_ = stack[3].m_obj;
lean_object* v_res_4291_;
v_res_4291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_as_4277_, v_i_4278_, v_stop_4279_, v_b_4280_);
stack->m_obj
 = v_res_4291_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___boxed(lean_object* v_as_4292_, lean_object* v_i_4293_, lean_object* v_stop_4294_, lean_object* v_b_4295_){
_start:
{
size_t v_i_boxed_4296_; size_t v_stop_boxed_4297_; lean_object* v_res_4298_; 
v_i_boxed_4296_ = lean_unbox_usize(v_i_4293_);
lean_dec(v_i_4293_);
v_stop_boxed_4297_ = lean_unbox_usize(v_stop_4294_);
lean_dec(v_stop_4294_);
v_res_4298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_as_4292_, v_i_boxed_4296_, v_stop_boxed_4297_, v_b_4295_);
lean_dec_ref(v_as_4292_);
return v_res_4298_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2(void){
_start:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; 
v___x_4302_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__1));
v___x_4303_ = l_Lean_MessageData_ofFormat(v___x_4302_);
return v___x_4303_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4304_ = lean_box(1);
v___x_4305_ = l_Lean_MessageData_ofFormat(v___x_4304_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(lean_object* v_a_4307_, lean_object* v_a_4308_){
_start:
{
if (lean_obj_tag(v_a_4307_) == 0)
{
lean_object* v___x_4309_; 
v___x_4309_ = l_List_reverse___redArg(v_a_4308_);
return v___x_4309_;
}
else
{
lean_object* v_head_4310_; lean_object* v_snd_4311_; lean_object* v_tail_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4359_; 
v_head_4310_ = lean_ctor_get(v_a_4307_, 0);
lean_inc(v_head_4310_);
v_snd_4311_ = lean_ctor_get(v_head_4310_, 1);
lean_inc(v_snd_4311_);
v_tail_4312_ = lean_ctor_get(v_a_4307_, 1);
v_isSharedCheck_4359_ = !lean_is_exclusive(v_a_4307_);
if (v_isSharedCheck_4359_ == 0)
{
lean_object* v_unused_4360_; 
v_unused_4360_ = lean_ctor_get(v_a_4307_, 0);
lean_dec(v_unused_4360_);
v___x_4314_ = v_a_4307_;
v_isShared_4315_ = v_isSharedCheck_4359_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_tail_4312_);
lean_dec(v_a_4307_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4359_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v_fst_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4357_; 
v_fst_4316_ = lean_ctor_get(v_head_4310_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v_head_4310_);
if (v_isSharedCheck_4357_ == 0)
{
lean_object* v_unused_4358_; 
v_unused_4358_ = lean_ctor_get(v_head_4310_, 1);
lean_dec(v_unused_4358_);
v___x_4318_ = v_head_4310_;
v_isShared_4319_ = v_isSharedCheck_4357_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_fst_4316_);
lean_dec(v_head_4310_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4357_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v_fst_4320_; lean_object* v_snd_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4356_; 
v_fst_4320_ = lean_ctor_get(v_snd_4311_, 0);
v_snd_4321_ = lean_ctor_get(v_snd_4311_, 1);
v_isSharedCheck_4356_ = !lean_is_exclusive(v_snd_4311_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4323_ = v_snd_4311_;
v_isShared_4324_ = v_isSharedCheck_4356_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_snd_4321_);
lean_inc(v_fst_4320_);
lean_dec(v_snd_4311_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4356_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4330_; 
v___x_4325_ = l_Nat_reprFast(v_fst_4316_);
v___x_4326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4326_, 0, v___x_4325_);
v___x_4327_ = l_Lean_MessageData_ofFormat(v___x_4326_);
v___x_4328_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2);
if (v_isShared_4324_ == 0)
{
lean_ctor_set_tag(v___x_4323_, 7);
lean_ctor_set(v___x_4323_, 1, v___x_4328_);
lean_ctor_set(v___x_4323_, 0, v___x_4327_);
v___x_4330_ = v___x_4323_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v___x_4327_);
lean_ctor_set(v_reuseFailAlloc_4355_, 1, v___x_4328_);
v___x_4330_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
lean_object* v___x_4331_; lean_object* v___x_4333_; 
v___x_4331_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3);
if (v_isShared_4319_ == 0)
{
lean_ctor_set_tag(v___x_4318_, 7);
lean_ctor_set(v___x_4318_, 1, v___x_4331_);
lean_ctor_set(v___x_4318_, 0, v___x_4330_);
v___x_4333_ = v___x_4318_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4330_);
lean_ctor_set(v_reuseFailAlloc_4354_, 1, v___x_4331_);
v___x_4333_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___y_4340_; uint8_t v___x_4351_; 
v___x_4334_ = l_Nat_reprFast(v_fst_4320_);
v___x_4335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4334_);
v___x_4336_ = l_Lean_MessageData_ofFormat(v___x_4335_);
v___x_4337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4336_);
lean_ctor_set(v___x_4337_, 1, v___x_4328_);
v___x_4338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4337_);
lean_ctor_set(v___x_4338_, 1, v___x_4331_);
v___x_4351_ = lean_unbox(v_snd_4321_);
lean_dec(v_snd_4321_);
if (v___x_4351_ == 0)
{
lean_object* v___x_4352_; 
v___x_4352_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__4));
v___y_4340_ = v___x_4352_;
goto v___jp_4339_;
}
else
{
lean_object* v___x_4353_; 
v___x_4353_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4));
v___y_4340_ = v___x_4353_;
goto v___jp_4339_;
}
v___jp_4339_:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4348_; 
lean_inc_ref(v___y_4340_);
v___x_4341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4341_, 0, v___y_4340_);
v___x_4342_ = l_Lean_MessageData_ofFormat(v___x_4341_);
v___x_4343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4338_);
lean_ctor_set(v___x_4343_, 1, v___x_4342_);
v___x_4344_ = l_Lean_MessageData_paren(v___x_4343_);
v___x_4345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4333_);
lean_ctor_set(v___x_4345_, 1, v___x_4344_);
v___x_4346_ = l_Lean_MessageData_paren(v___x_4345_);
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 1, v_a_4308_);
lean_ctor_set(v___x_4314_, 0, v___x_4346_);
v___x_4348_ = v___x_4314_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4346_);
lean_ctor_set(v_reuseFailAlloc_4350_, 1, v_a_4308_);
v___x_4348_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
v_a_4307_ = v_tail_4312_;
v_a_4308_ = v___x_4348_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(size_t v_sz_4361_, size_t v_i_4362_, lean_object* v_bs_4363_){
_start:
{
uint8_t v___x_4364_; 
v___x_4364_ = lean_usize_dec_lt(v_i_4362_, v_sz_4361_);
if (v___x_4364_ == 0)
{
return v_bs_4363_;
}
else
{
lean_object* v_v_4365_; lean_object* v_var_4366_; lean_object* v___x_4367_; lean_object* v_bs_x27_4368_; lean_object* v___x_4369_; uint8_t v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; size_t v___x_4374_; size_t v___x_4375_; lean_object* v___x_4376_; 
v_v_4365_ = lean_array_uget(v_bs_4363_, v_i_4362_);
v_var_4366_ = lean_ctor_get(v_v_4365_, 0);
lean_inc(v_var_4366_);
v___x_4367_ = lean_unsigned_to_nat(0u);
v_bs_x27_4368_ = lean_array_uset(v_bs_4363_, v_i_4362_, v___x_4367_);
v___x_4369_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_v_4365_);
v___x_4370_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_v_4365_);
lean_dec(v_v_4365_);
v___x_4371_ = lean_box(v___x_4370_);
v___x_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4369_);
lean_ctor_set(v___x_4372_, 1, v___x_4371_);
v___x_4373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4373_, 0, v_var_4366_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = ((size_t)1ULL);
v___x_4375_ = lean_usize_add(v_i_4362_, v___x_4374_);
v___x_4376_ = lean_array_uset(v_bs_x27_4368_, v_i_4362_, v___x_4373_);
v_i_4362_ = v___x_4375_;
v_bs_4363_ = v___x_4376_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4361_ = stack[0].m_num;
size_t v_i_4362_ = stack[1].m_num;
lean_object* v_bs_4363_ = stack[2].m_obj;
lean_object* v_res_4378_;
v_res_4378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_4361_, v_i_4362_, v_bs_4363_);
stack->m_obj
 = v_res_4378_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___boxed(lean_object* v_sz_4379_, lean_object* v_i_4380_, lean_object* v_bs_4381_){
_start:
{
size_t v_sz_boxed_4382_; size_t v_i_boxed_4383_; lean_object* v_res_4384_; 
v_sz_boxed_4382_ = lean_unbox_usize(v_sz_4379_);
lean_dec(v_sz_4379_);
v_i_boxed_4383_ = lean_unbox_usize(v_i_4380_);
lean_dec(v_i_4380_);
v_res_4384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_boxed_4382_, v_i_boxed_4383_, v_bs_4381_);
return v_res_4384_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1(void){
_start:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0));
v___x_4387_ = l_Lean_stringToMessageData(v___x_4386_);
return v___x_4387_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4(void){
_start:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4391_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3));
v___x_4392_ = l_Lean_stringToMessageData(v___x_4391_);
return v___x_4392_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(lean_object* v_data_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_){
_start:
{
lean_object* v___x_4399_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v_bestIdx_4405_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4533_; lean_object* v___x_4557_; lean_object* v___x_4558_; uint8_t v___x_4559_; 
v___x_4399_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default));
v_bestIdx_4405_ = lean_unsigned_to_nat(0u);
v___x_4557_ = lean_array_get_size(v_data_4393_);
v___x_4558_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_4559_ = lean_nat_dec_lt(v_bestIdx_4405_, v___x_4557_);
if (v___x_4559_ == 0)
{
v___y_4533_ = v___x_4558_;
goto v___jp_4532_;
}
else
{
uint8_t v___x_4560_; 
v___x_4560_ = lean_nat_dec_le(v___x_4557_, v___x_4557_);
if (v___x_4560_ == 0)
{
if (v___x_4559_ == 0)
{
v___y_4533_ = v___x_4558_;
goto v___jp_4532_;
}
else
{
size_t v___x_4561_; size_t v___x_4562_; lean_object* v___x_4563_; 
v___x_4561_ = ((size_t)0ULL);
v___x_4562_ = lean_usize_of_nat(v___x_4557_);
v___x_4563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4393_, v___x_4561_, v___x_4562_, v___x_4558_);
v___y_4533_ = v___x_4563_;
goto v___jp_4532_;
}
}
else
{
size_t v___x_4564_; size_t v___x_4565_; lean_object* v___x_4566_; 
v___x_4564_ = ((size_t)0ULL);
v___x_4565_ = lean_usize_of_nat(v___x_4557_);
v___x_4566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4393_, v___x_4564_, v___x_4565_, v___x_4558_);
v___y_4533_ = v___x_4566_;
goto v___jp_4532_;
}
}
v___jp_4400_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = lean_array_get(v___x_4399_, v___y_4402_, v___y_4401_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4402_);
v___x_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
return v___x_4404_;
}
v___jp_4406_:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; uint8_t v___x_4416_; 
v___x_4414_ = lean_array_get_borrowed(v___x_4399_, v___y_4409_, v_bestIdx_4405_);
v___x_4415_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4414_);
v___x_4416_ = lean_nat_dec_eq(v___x_4415_, v_bestIdx_4405_);
if (v___x_4416_ == 0)
{
lean_object* v___x_4417_; lean_object* v___x_4418_; uint8_t v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4417_ = lean_unsigned_to_nat(1u);
v___x_4418_ = lean_array_get_size(v___y_4409_);
v___x_4419_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4414_);
v___x_4420_ = lean_box(0);
v___x_4421_ = lean_box(v___x_4419_);
v___x_4422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4415_);
lean_ctor_set(v___x_4422_, 1, v___x_4421_);
v___x_4423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4423_, 0, v_bestIdx_4405_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
v___x_4424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4424_, 0, v___x_4420_);
lean_ctor_set(v___x_4424_, 1, v___x_4423_);
v___x_4425_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v___x_4418_, v___y_4409_, v___x_4417_, v___x_4424_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4480_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4428_ = v___x_4425_;
v_isShared_4429_ = v_isSharedCheck_4480_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4425_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4480_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v_fst_4430_; 
v_fst_4430_ = lean_ctor_get(v_a_4426_, 0);
if (lean_obj_tag(v_fst_4430_) == 0)
{
lean_object* v_snd_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4474_; 
lean_del_object(v___x_4428_);
v_snd_4431_ = lean_ctor_get(v_a_4426_, 1);
v_isSharedCheck_4474_ = !lean_is_exclusive(v_a_4426_);
if (v_isSharedCheck_4474_ == 0)
{
lean_object* v_unused_4475_; 
v_unused_4475_ = lean_ctor_get(v_a_4426_, 0);
lean_dec(v_unused_4475_);
v___x_4433_ = v_a_4426_;
v_isShared_4434_ = v_isSharedCheck_4474_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_snd_4431_);
lean_dec(v_a_4426_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4474_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v_fst_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4472_; 
v_fst_4435_ = lean_ctor_get(v_snd_4431_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v_snd_4431_);
if (v_isSharedCheck_4472_ == 0)
{
lean_object* v_unused_4473_; 
v_unused_4473_ = lean_ctor_get(v_snd_4431_, 1);
lean_dec(v_unused_4473_);
v___x_4437_ = v_snd_4431_;
v_isShared_4438_ = v_isSharedCheck_4472_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_fst_4435_);
lean_dec(v_snd_4431_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4472_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4439_; 
lean_inc_ref(v___y_4408_);
lean_inc(v___y_4413_);
lean_inc_ref(v___y_4412_);
lean_inc(v___y_4411_);
lean_inc_ref(v___y_4410_);
v___x_4439_ = lean_apply_5(v___y_4408_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, lean_box(0));
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_object* v_a_4440_; uint8_t v___x_4441_; 
v_a_4440_ = lean_ctor_get(v___x_4439_, 0);
lean_inc(v_a_4440_);
lean_dec_ref_known(v___x_4439_, 1);
v___x_4441_ = lean_unbox(v_a_4440_);
lean_dec(v_a_4440_);
if (v___x_4441_ == 0)
{
lean_del_object(v___x_4437_);
lean_del_object(v___x_4433_);
lean_dec(v___y_4407_);
v___y_4401_ = v_fst_4435_;
v___y_4402_ = v___y_4409_;
goto v___jp_4400_;
}
else
{
lean_object* v___x_4442_; lean_object* v_var_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4449_; 
v___x_4442_ = lean_array_get_borrowed(v___x_4399_, v___y_4409_, v_fst_4435_);
v_var_4443_ = lean_ctor_get(v___x_4442_, 0);
v___x_4444_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4443_);
v___x_4445_ = l_Nat_reprFast(v_var_4443_);
v___x_4446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4445_);
v___x_4447_ = l_Lean_MessageData_ofFormat(v___x_4446_);
if (v_isShared_4438_ == 0)
{
lean_ctor_set_tag(v___x_4437_, 7);
lean_ctor_set(v___x_4437_, 1, v___x_4447_);
lean_ctor_set(v___x_4437_, 0, v___x_4444_);
v___x_4449_ = v___x_4437_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v___x_4444_);
lean_ctor_set(v_reuseFailAlloc_4463_, 1, v___x_4447_);
v___x_4449_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
lean_object* v___x_4450_; lean_object* v___x_4452_; 
v___x_4450_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
if (v_isShared_4434_ == 0)
{
lean_ctor_set_tag(v___x_4433_, 7);
lean_ctor_set(v___x_4433_, 1, v___x_4450_);
lean_ctor_set(v___x_4433_, 0, v___x_4449_);
v___x_4452_ = v___x_4433_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4449_);
lean_ctor_set(v_reuseFailAlloc_4462_, 1, v___x_4450_);
v___x_4452_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
lean_object* v___x_4453_; 
v___x_4453_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4407_, v___x_4452_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
if (lean_obj_tag(v___x_4453_) == 0)
{
lean_dec_ref_known(v___x_4453_, 1);
v___y_4401_ = v_fst_4435_;
v___y_4402_ = v___y_4409_;
goto v___jp_4400_;
}
else
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
lean_dec(v_fst_4435_);
lean_dec_ref(v___y_4409_);
v_a_4454_ = lean_ctor_get(v___x_4453_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4456_ = v___x_4453_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v___x_4453_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
if (v_isShared_4457_ == 0)
{
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4454_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4471_; 
lean_del_object(v___x_4437_);
lean_dec(v_fst_4435_);
lean_del_object(v___x_4433_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4407_);
v_a_4464_ = lean_ctor_get(v___x_4439_, 0);
v_isSharedCheck_4471_ = !lean_is_exclusive(v___x_4439_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4466_ = v___x_4439_;
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_a_4464_);
lean_dec(v___x_4439_);
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
lean_object* v_val_4476_; lean_object* v___x_4478_; 
lean_inc_ref(v_fst_4430_);
lean_dec(v_a_4426_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4407_);
v_val_4476_ = lean_ctor_get(v_fst_4430_, 0);
lean_inc(v_val_4476_);
lean_dec_ref_known(v_fst_4430_, 1);
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v_val_4476_);
v___x_4478_ = v___x_4428_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_val_4476_);
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
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4407_);
v_a_4481_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4425_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4425_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
else
{
lean_object* v___x_4489_; 
lean_inc(v___x_4414_);
lean_dec(v___x_4415_);
lean_dec_ref(v___y_4409_);
lean_inc_ref(v___y_4408_);
lean_inc(v___y_4413_);
lean_inc_ref(v___y_4412_);
lean_inc(v___y_4411_);
lean_inc_ref(v___y_4410_);
v___x_4489_ = lean_apply_5(v___y_4408_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, lean_box(0));
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4523_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4492_ = v___x_4489_;
v_isShared_4493_ = v_isSharedCheck_4523_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4489_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4523_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
uint8_t v___x_4494_; 
v___x_4494_ = lean_unbox(v_a_4490_);
lean_dec(v_a_4490_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4496_; 
lean_dec(v___y_4407_);
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 0, v___x_4414_);
v___x_4496_ = v___x_4492_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4414_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
else
{
lean_object* v_var_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
lean_del_object(v___x_4492_);
v_var_4498_ = lean_ctor_get(v___x_4414_, 0);
v___x_4499_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4498_);
v___x_4500_ = l_Nat_reprFast(v_var_4498_);
v___x_4501_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4500_);
v___x_4502_ = l_Lean_MessageData_ofFormat(v___x_4501_);
v___x_4503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4499_);
lean_ctor_set(v___x_4503_, 1, v___x_4502_);
v___x_4504_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
v___x_4505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4503_);
lean_ctor_set(v___x_4505_, 1, v___x_4504_);
v___x_4506_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4407_, v___x_4505_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
if (lean_obj_tag(v___x_4506_) == 0)
{
lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4513_ == 0)
{
lean_object* v_unused_4514_; 
v_unused_4514_ = lean_ctor_get(v___x_4506_, 0);
lean_dec(v_unused_4514_);
v___x_4508_ = v___x_4506_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_dec(v___x_4506_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 0, v___x_4414_);
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4414_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
lean_dec(v___x_4414_);
v_a_4515_ = lean_ctor_get(v___x_4506_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4506_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4506_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
}
}
else
{
lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4531_; 
lean_dec(v___x_4414_);
lean_dec(v___y_4407_);
v_a_4524_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4526_ = v___x_4489_;
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4489_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4529_; 
if (v_isShared_4527_ == 0)
{
v___x_4529_ = v___x_4526_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4524_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
return v___x_4529_;
}
}
}
}
}
v___jp_4532_:
{
lean_object* v_cls_4534_; lean_object* v___f_4535_; lean_object* v___x_4536_; lean_object* v_a_4537_; uint8_t v___x_4538_; 
v_cls_4534_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___f_4535_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2));
v___x_4536_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4534_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_);
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4537_);
lean_dec_ref(v___x_4536_);
v___x_4538_ = lean_unbox(v_a_4537_);
lean_dec(v_a_4537_);
if (v___x_4538_ == 0)
{
v___y_4407_ = v_cls_4534_;
v___y_4408_ = v___f_4535_;
v___y_4409_ = v___y_4533_;
v___y_4410_ = v_a_4394_;
v___y_4411_ = v_a_4395_;
v___y_4412_ = v_a_4396_;
v___y_4413_ = v_a_4397_;
goto v___jp_4406_;
}
else
{
lean_object* v___x_4539_; size_t v_sz_4540_; size_t v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4539_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4);
v_sz_4540_ = lean_array_size(v___y_4533_);
v___x_4541_ = ((size_t)0ULL);
lean_inc_ref(v___y_4533_);
v___x_4542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_4540_, v___x_4541_, v___y_4533_);
v___x_4543_ = lean_array_to_list(v___x_4542_);
v___x_4544_ = lean_box(0);
v___x_4545_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v___x_4543_, v___x_4544_);
v___x_4546_ = l_Lean_MessageData_ofList(v___x_4545_);
v___x_4547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4539_);
lean_ctor_set(v___x_4547_, 1, v___x_4546_);
v___x_4548_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4534_, v___x_4547_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_dec_ref_known(v___x_4548_, 1);
v___y_4407_ = v_cls_4534_;
v___y_4408_ = v___f_4535_;
v___y_4409_ = v___y_4533_;
v___y_4410_ = v_a_4394_;
v___y_4411_ = v_a_4395_;
v___y_4412_ = v_a_4396_;
v___y_4413_ = v_a_4397_;
goto v___jp_4406_;
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
lean_dec_ref(v___y_4533_);
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4551_ = v___x_4548_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4548_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_4393_ = stack[0].m_obj;
lean_object* v_a_4394_ = stack[1].m_obj;
lean_object* v_a_4395_ = stack[2].m_obj;
lean_object* v_a_4396_ = stack[3].m_obj;
lean_object* v_a_4397_ = stack[4].m_obj;
lean_object* v_res_4567_;
v_res_4567_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_);
stack->m_obj
 = v_res_4567_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object* v_data_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_);
lean_dec(v_a_4572_);
lean_dec_ref(v_a_4571_);
lean_dec(v_a_4570_);
lean_dec_ref(v_a_4569_);
lean_dec_ref(v_data_4568_);
return v_res_4574_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object* v_upperBound_4575_, lean_object* v___y_4576_, lean_object* v_inst_4577_, lean_object* v_R_4578_, lean_object* v_a_4579_, lean_object* v_b_4580_, lean_object* v_c_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
lean_object* v___x_4587_; 
v___x_4587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4575_, v___y_4576_, v_a_4579_, v_b_4580_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_);
return v___x_4587_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_4575_ = stack[0].m_obj;
lean_object* v___y_4576_ = stack[1].m_obj;
lean_object* v_a_4579_ = stack[4].m_obj;
lean_object* v_b_4580_ = stack[5].m_obj;
lean_object* v___y_4582_ = stack[7].m_obj;
lean_object* v___y_4583_ = stack[8].m_obj;
lean_object* v___y_4584_ = stack[9].m_obj;
lean_object* v___y_4585_ = stack[10].m_obj;
lean_object* v_res_4588_;
v_res_4588_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_upperBound_4575_, v___y_4576_, lean_box(0), lean_box(0), v_a_4579_, v_b_4580_, lean_box(0), v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_);
stack->m_obj
 = v_res_4588_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object* v_upperBound_4589_, lean_object* v___y_4590_, lean_object* v_inst_4591_, lean_object* v_R_4592_, lean_object* v_a_4593_, lean_object* v_b_4594_, lean_object* v_c_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_){
_start:
{
lean_object* v_res_4601_; 
v_res_4601_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_upperBound_4589_, v___y_4590_, v_inst_4591_, v_R_4592_, v_a_4593_, v_b_4594_, v_c_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec_ref(v___y_4590_);
lean_dec(v_upperBound_4589_);
return v_res_4601_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(lean_object* v_snd_4602_, lean_object* v_fst_4603_, lean_object* v_as_x27_4604_, lean_object* v_b_4605_){
_start:
{
if (lean_obj_tag(v_as_x27_4604_) == 0)
{
lean_object* v___x_4607_; 
lean_dec_ref(v_fst_4603_);
v___x_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4607_, 0, v_b_4605_);
return v___x_4607_;
}
else
{
lean_object* v_head_4608_; lean_object* v_tail_4609_; lean_object* v_fst_4610_; lean_object* v_snd_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v_head_4608_ = lean_ctor_get(v_as_x27_4604_, 0);
v_tail_4609_ = lean_ctor_get(v_as_x27_4604_, 1);
v_fst_4610_ = lean_ctor_get(v_head_4608_, 0);
v_snd_4611_ = lean_ctor_get(v_head_4608_, 1);
v___x_4612_ = lean_int_neg(v_snd_4602_);
lean_inc(v_fst_4610_);
lean_inc_ref(v_fst_4603_);
lean_inc(v_snd_4611_);
v___x_4613_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_snd_4611_, v_fst_4603_, v___x_4612_, v_fst_4610_);
v___x_4614_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_4613_);
v___x_4615_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_b_4605_, v___x_4614_);
v_as_x27_4604_ = v_tail_4609_;
v_b_4605_ = v___x_4615_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_4602_ = stack[0].m_obj;
lean_object* v_fst_4603_ = stack[1].m_obj;
lean_object* v_as_x27_4604_ = stack[2].m_obj;
lean_object* v_b_4605_ = stack[3].m_obj;
lean_object* v_res_4617_;
v_res_4617_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4602_, v_fst_4603_, v_as_x27_4604_, v_b_4605_);
stack->m_obj
 = v_res_4617_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg___boxed(lean_object* v_snd_4618_, lean_object* v_fst_4619_, lean_object* v_as_x27_4620_, lean_object* v_b_4621_, lean_object* v___y_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4618_, v_fst_4619_, v_as_x27_4620_, v_b_4621_);
lean_dec(v_as_x27_4620_);
lean_dec(v_snd_4618_);
return v_res_4623_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(lean_object* v_upperBounds_4624_, lean_object* v_as_x27_4625_, lean_object* v_b_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_){
_start:
{
if (lean_obj_tag(v_as_x27_4625_) == 0)
{
lean_object* v___x_4632_; 
v___x_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4632_, 0, v_b_4626_);
return v___x_4632_;
}
else
{
lean_object* v_head_4633_; lean_object* v_tail_4634_; lean_object* v_fst_4635_; lean_object* v_snd_4636_; lean_object* v___x_4637_; lean_object* v_a_4638_; 
v_head_4633_ = lean_ctor_get(v_as_x27_4625_, 0);
v_tail_4634_ = lean_ctor_get(v_as_x27_4625_, 1);
v_fst_4635_ = lean_ctor_get(v_head_4633_, 0);
v_snd_4636_ = lean_ctor_get(v_head_4633_, 1);
lean_inc(v_fst_4635_);
v___x_4637_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4636_, v_fst_4635_, v_upperBounds_4624_, v_b_4626_);
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_a_4638_);
lean_dec_ref(v___x_4637_);
v_as_x27_4625_ = v_tail_4634_;
v_b_4626_ = v_a_4638_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBounds_4624_ = stack[0].m_obj;
lean_object* v_as_x27_4625_ = stack[1].m_obj;
lean_object* v_b_4626_ = stack[2].m_obj;
lean_object* v___y_4627_ = stack[3].m_obj;
lean_object* v___y_4628_ = stack[4].m_obj;
lean_object* v___y_4629_ = stack[5].m_obj;
lean_object* v___y_4630_ = stack[6].m_obj;
lean_object* v_res_4640_;
v_res_4640_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4624_, v_as_x27_4625_, v_b_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
stack->m_obj
 = v_res_4640_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg___boxed(lean_object* v_upperBounds_4641_, lean_object* v_as_x27_4642_, lean_object* v_b_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4641_, v_as_x27_4642_, v_b_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
lean_dec(v_as_x27_4642_);
lean_dec(v_upperBounds_4641_);
return v_res_4649_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(lean_object* v_as_x27_4650_, lean_object* v_b_4651_){
_start:
{
if (lean_obj_tag(v_as_x27_4650_) == 0)
{
lean_object* v___x_4653_; 
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v_b_4651_);
return v___x_4653_;
}
else
{
lean_object* v_head_4654_; lean_object* v_tail_4655_; lean_object* v___x_4656_; 
v_head_4654_ = lean_ctor_get(v_as_x27_4650_, 0);
v_tail_4655_ = lean_ctor_get(v_as_x27_4650_, 1);
lean_inc(v_head_4654_);
v___x_4656_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_b_4651_, v_head_4654_);
v_as_x27_4650_ = v_tail_4655_;
v_b_4651_ = v___x_4656_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_4650_ = stack[0].m_obj;
lean_object* v_b_4651_ = stack[1].m_obj;
lean_object* v_res_4658_;
v_res_4658_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4650_, v_b_4651_);
stack->m_obj
 = v_res_4658_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg___boxed(lean_object* v_as_x27_4659_, lean_object* v_b_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4659_, v_b_4660_);
lean_dec(v_as_x27_4659_);
return v_res_4662_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(lean_object* v_p_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
lean_object* v_data_4669_; lean_object* v___x_4670_; 
lean_inc_ref(v_p_4663_);
v_data_4669_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(v_p_4663_);
v___x_4670_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4669_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
lean_dec_ref(v_data_4669_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v_irrelevant_4672_; lean_object* v_lowerBounds_4673_; lean_object* v_upperBounds_4674_; lean_object* v_assumptions_4675_; lean_object* v_eliminations_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4691_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_a_4671_);
lean_dec_ref_known(v___x_4670_, 1);
v_irrelevant_4672_ = lean_ctor_get(v_a_4671_, 1);
lean_inc(v_irrelevant_4672_);
v_lowerBounds_4673_ = lean_ctor_get(v_a_4671_, 2);
lean_inc(v_lowerBounds_4673_);
v_upperBounds_4674_ = lean_ctor_get(v_a_4671_, 3);
lean_inc(v_upperBounds_4674_);
lean_dec(v_a_4671_);
v_assumptions_4675_ = lean_ctor_get(v_p_4663_, 0);
v_eliminations_4676_ = lean_ctor_get(v_p_4663_, 4);
v_isSharedCheck_4691_ = !lean_is_exclusive(v_p_4663_);
if (v_isSharedCheck_4691_ == 0)
{
lean_object* v_unused_4692_; lean_object* v_unused_4693_; lean_object* v_unused_4694_; lean_object* v_unused_4695_; lean_object* v_unused_4696_; 
v_unused_4692_ = lean_ctor_get(v_p_4663_, 6);
lean_dec(v_unused_4692_);
v_unused_4693_ = lean_ctor_get(v_p_4663_, 5);
lean_dec(v_unused_4693_);
v_unused_4694_ = lean_ctor_get(v_p_4663_, 3);
lean_dec(v_unused_4694_);
v_unused_4695_ = lean_ctor_get(v_p_4663_, 2);
lean_dec(v_unused_4695_);
v_unused_4696_ = lean_ctor_get(v_p_4663_, 1);
lean_dec(v_unused_4696_);
v___x_4678_ = v_p_4663_;
v_isShared_4679_ = v_isSharedCheck_4691_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_eliminations_4676_);
lean_inc(v_assumptions_4675_);
lean_dec(v_p_4663_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4691_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4680_; lean_object* v___x_4681_; uint8_t v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4686_; 
v___x_4680_ = lean_unsigned_to_nat(0u);
v___x_4681_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v___x_4682_ = 1;
v___x_4683_ = lean_box(0);
v___x_4684_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 6, v___x_4684_);
lean_ctor_set(v___x_4678_, 5, v___x_4683_);
lean_ctor_set(v___x_4678_, 3, v___x_4681_);
lean_ctor_set(v___x_4678_, 2, v___x_4681_);
lean_ctor_set(v___x_4678_, 1, v___x_4680_);
v___x_4686_ = v___x_4678_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_assumptions_4675_);
lean_ctor_set(v_reuseFailAlloc_4690_, 1, v___x_4680_);
lean_ctor_set(v_reuseFailAlloc_4690_, 2, v___x_4681_);
lean_ctor_set(v_reuseFailAlloc_4690_, 3, v___x_4681_);
lean_ctor_set(v_reuseFailAlloc_4690_, 4, v_eliminations_4676_);
lean_ctor_set(v_reuseFailAlloc_4690_, 5, v___x_4683_);
lean_ctor_set(v_reuseFailAlloc_4690_, 6, v___x_4684_);
v___x_4686_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
lean_object* v___x_4687_; lean_object* v_a_4688_; lean_object* v___x_4689_; 
lean_ctor_set_uint8(v___x_4686_, sizeof(void*)*7, v___x_4682_);
v___x_4687_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_irrelevant_4672_, v___x_4686_);
lean_dec(v_irrelevant_4672_);
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4688_);
lean_dec_ref(v___x_4687_);
v___x_4689_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4674_, v_lowerBounds_4673_, v_a_4688_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
lean_dec(v_lowerBounds_4673_);
lean_dec(v_upperBounds_4674_);
return v___x_4689_;
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_dec_ref(v_p_4663_);
v_a_4697_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4670_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4670_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_4663_ = stack[0].m_obj;
lean_object* v_a_4664_ = stack[1].m_obj;
lean_object* v_a_4665_ = stack[2].m_obj;
lean_object* v_a_4666_ = stack[3].m_obj;
lean_object* v_a_4667_ = stack[4].m_obj;
lean_object* v_res_4705_;
v_res_4705_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
stack->m_obj
 = v_res_4705_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin___boxed(lean_object* v_p_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_);
lean_dec(v_a_4710_);
lean_dec_ref(v_a_4709_);
lean_dec(v_a_4708_);
lean_dec_ref(v_a_4707_);
return v_res_4712_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(lean_object* v_snd_4713_, lean_object* v_fst_4714_, lean_object* v_as_4715_, lean_object* v_as_x27_4716_, lean_object* v_b_4717_, lean_object* v_a_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
lean_object* v___x_4724_; 
v___x_4724_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4713_, v_fst_4714_, v_as_x27_4716_, v_b_4717_);
return v___x_4724_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_4713_ = stack[0].m_obj;
lean_object* v_fst_4714_ = stack[1].m_obj;
lean_object* v_as_4715_ = stack[2].m_obj;
lean_object* v_as_x27_4716_ = stack[3].m_obj;
lean_object* v_b_4717_ = stack[4].m_obj;
lean_object* v___y_4719_ = stack[6].m_obj;
lean_object* v___y_4720_ = stack[7].m_obj;
lean_object* v___y_4721_ = stack[8].m_obj;
lean_object* v___y_4722_ = stack[9].m_obj;
lean_object* v_res_4725_;
v_res_4725_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(v_snd_4713_, v_fst_4714_, v_as_4715_, v_as_x27_4716_, v_b_4717_, lean_box(0), v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
stack->m_obj
 = v_res_4725_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___boxed(lean_object* v_snd_4726_, lean_object* v_fst_4727_, lean_object* v_as_4728_, lean_object* v_as_x27_4729_, lean_object* v_b_4730_, lean_object* v_a_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(v_snd_4726_, v_fst_4727_, v_as_4728_, v_as_x27_4729_, v_b_4730_, v_a_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec(v___y_4733_);
lean_dec_ref(v___y_4732_);
lean_dec(v_as_x27_4729_);
lean_dec(v_as_4728_);
lean_dec(v_snd_4726_);
return v_res_4737_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(lean_object* v_as_4738_, lean_object* v_as_x27_4739_, lean_object* v_b_4740_, lean_object* v_a_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_){
_start:
{
lean_object* v___x_4747_; 
v___x_4747_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4739_, v_b_4740_);
return v___x_4747_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4738_ = stack[0].m_obj;
lean_object* v_as_x27_4739_ = stack[1].m_obj;
lean_object* v_b_4740_ = stack[2].m_obj;
lean_object* v___y_4742_ = stack[4].m_obj;
lean_object* v___y_4743_ = stack[5].m_obj;
lean_object* v___y_4744_ = stack[6].m_obj;
lean_object* v___y_4745_ = stack[7].m_obj;
lean_object* v_res_4748_;
v_res_4748_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(v_as_4738_, v_as_x27_4739_, v_b_4740_, lean_box(0), v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
stack->m_obj
 = v_res_4748_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___boxed(lean_object* v_as_4749_, lean_object* v_as_x27_4750_, lean_object* v_b_4751_, lean_object* v_a_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(v_as_4749_, v_as_x27_4750_, v_b_4751_, v_a_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
lean_dec(v___y_4756_);
lean_dec_ref(v___y_4755_);
lean_dec(v___y_4754_);
lean_dec_ref(v___y_4753_);
lean_dec(v_as_x27_4750_);
lean_dec(v_as_4749_);
return v_res_4758_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(lean_object* v_upperBounds_4759_, lean_object* v_as_4760_, lean_object* v_as_x27_4761_, lean_object* v_b_4762_, lean_object* v_a_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_){
_start:
{
lean_object* v___x_4769_; 
v___x_4769_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4759_, v_as_x27_4761_, v_b_4762_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
return v___x_4769_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBounds_4759_ = stack[0].m_obj;
lean_object* v_as_4760_ = stack[1].m_obj;
lean_object* v_as_x27_4761_ = stack[2].m_obj;
lean_object* v_b_4762_ = stack[3].m_obj;
lean_object* v___y_4764_ = stack[5].m_obj;
lean_object* v___y_4765_ = stack[6].m_obj;
lean_object* v___y_4766_ = stack[7].m_obj;
lean_object* v___y_4767_ = stack[8].m_obj;
lean_object* v_res_4770_;
v_res_4770_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(v_upperBounds_4759_, v_as_4760_, v_as_x27_4761_, v_b_4762_, lean_box(0), v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
stack->m_obj
 = v_res_4770_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___boxed(lean_object* v_upperBounds_4771_, lean_object* v_as_4772_, lean_object* v_as_x27_4773_, lean_object* v_b_4774_, lean_object* v_a_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(v_upperBounds_4771_, v_as_4772_, v_as_x27_4773_, v_b_4774_, v_a_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
lean_dec(v___y_4779_);
lean_dec_ref(v___y_4778_);
lean_dec(v___y_4777_);
lean_dec_ref(v___y_4776_);
lean_dec(v_as_x27_4773_);
lean_dec(v_as_4772_);
lean_dec(v_upperBounds_4771_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object* v_x_4782_, lean_object* v_x_4783_){
_start:
{
if (lean_obj_tag(v_x_4783_) == 0)
{
lean_inc(v_x_4782_);
return v_x_4782_;
}
else
{
lean_object* v_key_4784_; lean_object* v_value_4785_; lean_object* v_tail_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v_key_4784_ = lean_ctor_get(v_x_4783_, 0);
v_value_4785_ = lean_ctor_get(v_x_4783_, 1);
v_tail_4786_ = lean_ctor_get(v_x_4783_, 2);
v___x_4787_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4782_, v_tail_4786_);
lean_inc(v_value_4785_);
lean_inc(v_key_4784_);
v___x_4788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4788_, 0, v_key_4784_);
lean_ctor_set(v___x_4788_, 1, v_value_4785_);
v___x_4789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4788_);
lean_ctor_set(v___x_4789_, 1, v___x_4787_);
return v___x_4789_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2___boxed(lean_object* v_x_4790_, lean_object* v_x_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4790_, v_x_4791_);
lean_dec(v_x_4791_);
lean_dec(v_x_4790_);
return v_res_4792_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object* v_as_4793_, size_t v_i_4794_, size_t v_stop_4795_, lean_object* v_b_4796_){
_start:
{
uint8_t v___x_4797_; 
v___x_4797_ = lean_usize_dec_eq(v_i_4794_, v_stop_4795_);
if (v___x_4797_ == 0)
{
size_t v___x_4798_; size_t v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4798_ = ((size_t)1ULL);
v___x_4799_ = lean_usize_sub(v_i_4794_, v___x_4798_);
v___x_4800_ = lean_array_uget_borrowed(v_as_4793_, v___x_4799_);
v___x_4801_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_b_4796_, v___x_4800_);
lean_dec(v_b_4796_);
v_i_4794_ = v___x_4799_;
v_b_4796_ = v___x_4801_;
goto _start;
}
else
{
return v_b_4796_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4793_ = stack[0].m_obj;
size_t v_i_4794_ = stack[1].m_num;
size_t v_stop_4795_ = stack[2].m_num;
lean_object* v_b_4796_ = stack[3].m_obj;
lean_object* v_res_4803_;
v_res_4803_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_as_4793_, v_i_4794_, v_stop_4795_, v_b_4796_);
stack->m_obj
 = v_res_4803_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object* v_as_4804_, lean_object* v_i_4805_, lean_object* v_stop_4806_, lean_object* v_b_4807_){
_start:
{
size_t v_i_boxed_4808_; size_t v_stop_boxed_4809_; lean_object* v_res_4810_; 
v_i_boxed_4808_ = lean_unbox_usize(v_i_4805_);
lean_dec(v_i_4805_);
v_stop_boxed_4809_ = lean_unbox_usize(v_stop_4806_);
lean_dec(v_stop_4806_);
v_res_4810_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_as_4804_, v_i_boxed_4808_, v_stop_boxed_4809_, v_b_4807_);
lean_dec_ref(v_as_4804_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object* v_a_4811_, lean_object* v_a_4812_){
_start:
{
if (lean_obj_tag(v_a_4811_) == 0)
{
lean_object* v___x_4813_; 
v___x_4813_ = l_List_reverse___redArg(v_a_4812_);
return v___x_4813_;
}
else
{
lean_object* v_head_4814_; lean_object* v_tail_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4932_; 
v_head_4814_ = lean_ctor_get(v_a_4811_, 0);
v_tail_4815_ = lean_ctor_get(v_a_4811_, 1);
v_isSharedCheck_4932_ = !lean_is_exclusive(v_a_4811_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4817_ = v_a_4811_;
v_isShared_4818_ = v_isSharedCheck_4932_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_tail_4815_);
lean_inc(v_head_4814_);
lean_dec(v_a_4811_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4932_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
lean_object* v___y_4820_; lean_object* v_snd_4825_; lean_object* v_constraint_4826_; lean_object* v_fst_4827_; lean_object* v_lowerBound_4828_; lean_object* v_upperBound_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___y_4834_; lean_object* v___y_4835_; 
v_snd_4825_ = lean_ctor_get(v_head_4814_, 1);
v_constraint_4826_ = lean_ctor_get(v_snd_4825_, 1);
lean_inc_ref(v_constraint_4826_);
v_fst_4827_ = lean_ctor_get(v_head_4814_, 0);
lean_inc(v_fst_4827_);
lean_dec(v_head_4814_);
v_lowerBound_4828_ = lean_ctor_get(v_constraint_4826_, 0);
lean_inc(v_lowerBound_4828_);
v_upperBound_4829_ = lean_ctor_get(v_constraint_4826_, 1);
lean_inc(v_upperBound_4829_);
lean_dec_ref(v_constraint_4826_);
v___x_4830_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_fst_4827_);
lean_dec(v_fst_4827_);
v___x_4831_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_4832_ = lean_string_append(v___x_4830_, v___x_4831_);
if (lean_obj_tag(v_lowerBound_4828_) == 0)
{
if (lean_obj_tag(v_upperBound_4829_) == 0)
{
lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4840_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_4841_ = lean_string_append(v___x_4832_, v___x_4840_);
v___y_4820_ = v___x_4841_;
goto v___jp_4819_;
}
else
{
lean_object* v_val_4842_; lean_object* v___x_4843_; lean_object* v___y_4845_; lean_object* v_intZero_4850_; uint8_t v_isNeg_4851_; 
v_val_4842_ = lean_ctor_get(v_upperBound_4829_, 0);
lean_inc(v_val_4842_);
lean_dec_ref_known(v_upperBound_4829_, 1);
v___x_4843_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_4850_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4851_ = lean_int_dec_lt(v_val_4842_, v_intZero_4850_);
if (v_isNeg_4851_ == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4853_; 
v_a_4852_ = lean_nat_abs(v_val_4842_);
lean_dec(v_val_4842_);
v___x_4853_ = l_Nat_reprFast(v_a_4852_);
v___y_4845_ = v___x_4853_;
goto v___jp_4844_;
}
else
{
lean_object* v_abs_4854_; lean_object* v_one_4855_; lean_object* v_a_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v_abs_4854_ = lean_nat_abs(v_val_4842_);
lean_dec(v_val_4842_);
v_one_4855_ = lean_unsigned_to_nat(1u);
v_a_4856_ = lean_nat_sub(v_abs_4854_, v_one_4855_);
lean_dec(v_abs_4854_);
v___x_4857_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4858_ = lean_nat_add(v_a_4856_, v_one_4855_);
lean_dec(v_a_4856_);
v___x_4859_ = l_Nat_reprFast(v___x_4858_);
v___x_4860_ = lean_string_append(v___x_4857_, v___x_4859_);
lean_dec_ref(v___x_4859_);
v___y_4845_ = v___x_4860_;
goto v___jp_4844_;
}
v___jp_4844_:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4846_ = lean_string_append(v___x_4843_, v___y_4845_);
lean_dec_ref(v___y_4845_);
v___x_4847_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4848_ = lean_string_append(v___x_4846_, v___x_4847_);
v___x_4849_ = lean_string_append(v___x_4832_, v___x_4848_);
lean_dec_ref(v___x_4848_);
v___y_4820_ = v___x_4849_;
goto v___jp_4819_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_4829_) == 0)
{
lean_object* v_val_4861_; lean_object* v___x_4862_; lean_object* v___y_4864_; lean_object* v_intZero_4869_; uint8_t v_isNeg_4870_; 
v_val_4861_ = lean_ctor_get(v_lowerBound_4828_, 0);
lean_inc(v_val_4861_);
lean_dec_ref_known(v_lowerBound_4828_, 1);
v___x_4862_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4869_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4870_ = lean_int_dec_lt(v_val_4861_, v_intZero_4869_);
if (v_isNeg_4870_ == 0)
{
lean_object* v_a_4871_; lean_object* v___x_4872_; 
v_a_4871_ = lean_nat_abs(v_val_4861_);
lean_dec(v_val_4861_);
v___x_4872_ = l_Nat_reprFast(v_a_4871_);
v___y_4864_ = v___x_4872_;
goto v___jp_4863_;
}
else
{
lean_object* v_abs_4873_; lean_object* v_one_4874_; lean_object* v_a_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v_abs_4873_ = lean_nat_abs(v_val_4861_);
lean_dec(v_val_4861_);
v_one_4874_ = lean_unsigned_to_nat(1u);
v_a_4875_ = lean_nat_sub(v_abs_4873_, v_one_4874_);
lean_dec(v_abs_4873_);
v___x_4876_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4877_ = lean_nat_add(v_a_4875_, v_one_4874_);
lean_dec(v_a_4875_);
v___x_4878_ = l_Nat_reprFast(v___x_4877_);
v___x_4879_ = lean_string_append(v___x_4876_, v___x_4878_);
lean_dec_ref(v___x_4878_);
v___y_4864_ = v___x_4879_;
goto v___jp_4863_;
}
v___jp_4863_:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4865_ = lean_string_append(v___x_4862_, v___y_4864_);
lean_dec_ref(v___y_4864_);
v___x_4866_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_4867_ = lean_string_append(v___x_4865_, v___x_4866_);
v___x_4868_ = lean_string_append(v___x_4832_, v___x_4867_);
lean_dec_ref(v___x_4867_);
v___y_4820_ = v___x_4868_;
goto v___jp_4819_;
}
}
else
{
lean_object* v_val_4880_; lean_object* v_val_4881_; uint8_t v___x_4882_; 
v_val_4880_ = lean_ctor_get(v_lowerBound_4828_, 0);
lean_inc(v_val_4880_);
lean_dec_ref_known(v_lowerBound_4828_, 1);
v_val_4881_ = lean_ctor_get(v_upperBound_4829_, 0);
lean_inc(v_val_4881_);
lean_dec_ref_known(v_upperBound_4829_, 1);
v___x_4882_ = lean_int_dec_lt(v_val_4881_, v_val_4880_);
if (v___x_4882_ == 0)
{
uint8_t v___x_4883_; 
v___x_4883_ = lean_int_dec_eq(v_val_4880_, v_val_4881_);
if (v___x_4883_ == 0)
{
lean_object* v___x_4884_; lean_object* v___y_4886_; lean_object* v_intZero_4901_; uint8_t v_isNeg_4902_; 
v___x_4884_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4901_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4902_ = lean_int_dec_lt(v_val_4880_, v_intZero_4901_);
if (v_isNeg_4902_ == 0)
{
lean_object* v_a_4903_; lean_object* v___x_4904_; 
v_a_4903_ = lean_nat_abs(v_val_4880_);
lean_dec(v_val_4880_);
v___x_4904_ = l_Nat_reprFast(v_a_4903_);
v___y_4886_ = v___x_4904_;
goto v___jp_4885_;
}
else
{
lean_object* v_abs_4905_; lean_object* v_one_4906_; lean_object* v_a_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; 
v_abs_4905_ = lean_nat_abs(v_val_4880_);
lean_dec(v_val_4880_);
v_one_4906_ = lean_unsigned_to_nat(1u);
v_a_4907_ = lean_nat_sub(v_abs_4905_, v_one_4906_);
lean_dec(v_abs_4905_);
v___x_4908_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4909_ = lean_nat_add(v_a_4907_, v_one_4906_);
lean_dec(v_a_4907_);
v___x_4910_ = l_Nat_reprFast(v___x_4909_);
v___x_4911_ = lean_string_append(v___x_4908_, v___x_4910_);
lean_dec_ref(v___x_4910_);
v___y_4886_ = v___x_4911_;
goto v___jp_4885_;
}
v___jp_4885_:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v_intZero_4890_; uint8_t v_isNeg_4891_; 
v___x_4887_ = lean_string_append(v___x_4884_, v___y_4886_);
lean_dec_ref(v___y_4886_);
v___x_4888_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_4889_ = lean_string_append(v___x_4887_, v___x_4888_);
v_intZero_4890_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4891_ = lean_int_dec_lt(v_val_4881_, v_intZero_4890_);
if (v_isNeg_4891_ == 0)
{
lean_object* v_a_4892_; lean_object* v___x_4893_; 
v_a_4892_ = lean_nat_abs(v_val_4881_);
lean_dec(v_val_4881_);
v___x_4893_ = l_Nat_reprFast(v_a_4892_);
v___y_4834_ = v___x_4889_;
v___y_4835_ = v___x_4893_;
goto v___jp_4833_;
}
else
{
lean_object* v_abs_4894_; lean_object* v_one_4895_; lean_object* v_a_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; 
v_abs_4894_ = lean_nat_abs(v_val_4881_);
lean_dec(v_val_4881_);
v_one_4895_ = lean_unsigned_to_nat(1u);
v_a_4896_ = lean_nat_sub(v_abs_4894_, v_one_4895_);
lean_dec(v_abs_4894_);
v___x_4897_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4898_ = lean_nat_add(v_a_4896_, v_one_4895_);
lean_dec(v_a_4896_);
v___x_4899_ = l_Nat_reprFast(v___x_4898_);
v___x_4900_ = lean_string_append(v___x_4897_, v___x_4899_);
lean_dec_ref(v___x_4899_);
v___y_4834_ = v___x_4889_;
v___y_4835_ = v___x_4900_;
goto v___jp_4833_;
}
}
}
else
{
lean_object* v___x_4912_; lean_object* v___y_4914_; lean_object* v_intZero_4919_; uint8_t v_isNeg_4920_; 
lean_dec(v_val_4881_);
v___x_4912_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_4919_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4920_ = lean_int_dec_lt(v_val_4880_, v_intZero_4919_);
if (v_isNeg_4920_ == 0)
{
lean_object* v_a_4921_; lean_object* v___x_4922_; 
v_a_4921_ = lean_nat_abs(v_val_4880_);
lean_dec(v_val_4880_);
v___x_4922_ = l_Nat_reprFast(v_a_4921_);
v___y_4914_ = v___x_4922_;
goto v___jp_4913_;
}
else
{
lean_object* v_abs_4923_; lean_object* v_one_4924_; lean_object* v_a_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v_abs_4923_ = lean_nat_abs(v_val_4880_);
lean_dec(v_val_4880_);
v_one_4924_ = lean_unsigned_to_nat(1u);
v_a_4925_ = lean_nat_sub(v_abs_4923_, v_one_4924_);
lean_dec(v_abs_4923_);
v___x_4926_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4927_ = lean_nat_add(v_a_4925_, v_one_4924_);
lean_dec(v_a_4925_);
v___x_4928_ = l_Nat_reprFast(v___x_4927_);
v___x_4929_ = lean_string_append(v___x_4926_, v___x_4928_);
lean_dec_ref(v___x_4928_);
v___y_4914_ = v___x_4929_;
goto v___jp_4913_;
}
v___jp_4913_:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4915_ = lean_string_append(v___x_4912_, v___y_4914_);
lean_dec_ref(v___y_4914_);
v___x_4916_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_4917_ = lean_string_append(v___x_4915_, v___x_4916_);
v___x_4918_ = lean_string_append(v___x_4832_, v___x_4917_);
lean_dec_ref(v___x_4917_);
v___y_4820_ = v___x_4918_;
goto v___jp_4819_;
}
}
}
else
{
lean_object* v___x_4930_; lean_object* v___x_4931_; 
lean_dec(v_val_4881_);
lean_dec(v_val_4880_);
v___x_4930_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_4931_ = lean_string_append(v___x_4832_, v___x_4930_);
v___y_4820_ = v___x_4931_;
goto v___jp_4819_;
}
}
}
v___jp_4819_:
{
lean_object* v___x_4822_; 
if (v_isShared_4818_ == 0)
{
lean_ctor_set(v___x_4817_, 1, v_a_4812_);
lean_ctor_set(v___x_4817_, 0, v___y_4820_);
v___x_4822_ = v___x_4817_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v___y_4820_);
lean_ctor_set(v_reuseFailAlloc_4824_, 1, v_a_4812_);
v___x_4822_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
v_a_4811_ = v_tail_4815_;
v_a_4812_ = v___x_4822_;
goto _start;
}
}
v___jp_4833_:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4836_ = lean_string_append(v___y_4834_, v___y_4835_);
lean_dec_ref(v___y_4835_);
v___x_4837_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4838_ = lean_string_append(v___x_4836_, v___x_4837_);
v___x_4839_ = lean_string_append(v___x_4832_, v___x_4838_);
lean_dec_ref(v___x_4838_);
v___y_4820_ = v___x_4839_;
goto v___jp_4819_;
}
}
}
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object* v_cls_4933_, lean_object* v_msg_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_){
_start:
{
lean_object* v_ref_4940_; lean_object* v___x_4941_; lean_object* v_a_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4987_; 
v_ref_4940_ = lean_ctor_get(v___y_4937_, 2);
v___x_4941_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_);
v_a_4942_ = lean_ctor_get(v___x_4941_, 0);
v_isSharedCheck_4987_ = !lean_is_exclusive(v___x_4941_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4944_ = v___x_4941_;
v_isShared_4945_ = v_isSharedCheck_4987_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_a_4942_);
lean_dec(v___x_4941_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4987_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
lean_object* v___x_4946_; lean_object* v_traceState_4947_; lean_object* v_env_4948_; lean_object* v_nextMacroScope_4949_; lean_object* v_ngen_4950_; lean_object* v_auxDeclNGen_4951_; lean_object* v_cache_4952_; lean_object* v_recordedDeps_4953_; lean_object* v_messages_4954_; lean_object* v_infoState_4955_; lean_object* v_snapshotTasks_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4986_; 
v___x_4946_ = lean_st_ref_take(v___y_4938_);
v_traceState_4947_ = lean_ctor_get(v___x_4946_, 4);
v_env_4948_ = lean_ctor_get(v___x_4946_, 0);
v_nextMacroScope_4949_ = lean_ctor_get(v___x_4946_, 1);
v_ngen_4950_ = lean_ctor_get(v___x_4946_, 2);
v_auxDeclNGen_4951_ = lean_ctor_get(v___x_4946_, 3);
v_cache_4952_ = lean_ctor_get(v___x_4946_, 5);
v_recordedDeps_4953_ = lean_ctor_get(v___x_4946_, 6);
v_messages_4954_ = lean_ctor_get(v___x_4946_, 7);
v_infoState_4955_ = lean_ctor_get(v___x_4946_, 8);
v_snapshotTasks_4956_ = lean_ctor_get(v___x_4946_, 9);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_4986_ == 0)
{
v___x_4958_ = v___x_4946_;
v_isShared_4959_ = v_isSharedCheck_4986_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_snapshotTasks_4956_);
lean_inc(v_infoState_4955_);
lean_inc(v_messages_4954_);
lean_inc(v_recordedDeps_4953_);
lean_inc(v_cache_4952_);
lean_inc(v_traceState_4947_);
lean_inc(v_auxDeclNGen_4951_);
lean_inc(v_ngen_4950_);
lean_inc(v_nextMacroScope_4949_);
lean_inc(v_env_4948_);
lean_dec(v___x_4946_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4986_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
uint64_t v_tid_4960_; lean_object* v_traces_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4985_; 
v_tid_4960_ = lean_ctor_get_uint64(v_traceState_4947_, sizeof(void*)*1);
v_traces_4961_ = lean_ctor_get(v_traceState_4947_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v_traceState_4947_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4963_ = v_traceState_4947_;
v_isShared_4964_ = v_isSharedCheck_4985_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_traces_4961_);
lean_dec(v_traceState_4947_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4985_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; double v___x_4967_; uint8_t v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4976_; 
v___x_4965_ = lean_box(0);
v___x_4966_ = lean_box(0);
v___x_4967_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4968_ = 0;
v___x_4969_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4970_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4970_, 0, v_cls_4933_);
lean_ctor_set(v___x_4970_, 1, v___x_4966_);
lean_ctor_set(v___x_4970_, 2, v___x_4969_);
lean_ctor_set_float(v___x_4970_, sizeof(void*)*3, v___x_4967_);
lean_ctor_set_float(v___x_4970_, sizeof(void*)*3 + 8, v___x_4967_);
lean_ctor_set_uint8(v___x_4970_, sizeof(void*)*3 + 16, v___x_4968_);
v___x_4971_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4972_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4972_, 0, v___x_4970_);
lean_ctor_set(v___x_4972_, 1, v_a_4942_);
lean_ctor_set(v___x_4972_, 2, v___x_4971_);
lean_inc(v_ref_4940_);
v___x_4973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4973_, 0, v_ref_4940_);
lean_ctor_set(v___x_4973_, 1, v___x_4972_);
v___x_4974_ = l_Lean_PersistentArray_push___redArg(v_traces_4961_, v___x_4973_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 0, v___x_4974_);
v___x_4976_ = v___x_4963_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v___x_4974_);
lean_ctor_set_uint64(v_reuseFailAlloc_4984_, sizeof(void*)*1, v_tid_4960_);
v___x_4976_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
lean_object* v___x_4978_; 
if (v_isShared_4959_ == 0)
{
lean_ctor_set(v___x_4958_, 4, v___x_4976_);
v___x_4978_ = v___x_4958_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_env_4948_);
lean_ctor_set(v_reuseFailAlloc_4983_, 1, v_nextMacroScope_4949_);
lean_ctor_set(v_reuseFailAlloc_4983_, 2, v_ngen_4950_);
lean_ctor_set(v_reuseFailAlloc_4983_, 3, v_auxDeclNGen_4951_);
lean_ctor_set(v_reuseFailAlloc_4983_, 4, v___x_4976_);
lean_ctor_set(v_reuseFailAlloc_4983_, 5, v_cache_4952_);
lean_ctor_set(v_reuseFailAlloc_4983_, 6, v_recordedDeps_4953_);
lean_ctor_set(v_reuseFailAlloc_4983_, 7, v_messages_4954_);
lean_ctor_set(v_reuseFailAlloc_4983_, 8, v_infoState_4955_);
lean_ctor_set(v_reuseFailAlloc_4983_, 9, v_snapshotTasks_4956_);
v___x_4978_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
lean_object* v___x_4979_; lean_object* v___x_4981_; 
v___x_4979_ = lean_st_ref_put(v___y_4938_, v___x_4978_);
if (v_isShared_4945_ == 0)
{
lean_ctor_set(v___x_4944_, 0, v___x_4965_);
v___x_4981_ = v___x_4944_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v___x_4965_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4933_ = stack[0].m_obj;
lean_object* v_msg_4934_ = stack[1].m_obj;
lean_object* v___y_4935_ = stack[2].m_obj;
lean_object* v___y_4936_ = stack[3].m_obj;
lean_object* v___y_4937_ = stack[4].m_obj;
lean_object* v___y_4938_ = stack[5].m_obj;
lean_object* v_res_4988_;
v_res_4988_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4933_, v_msg_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_);
stack->m_obj
 = v_res_4988_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg___boxed(lean_object* v_cls_4989_, lean_object* v_msg_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4989_, v_msg_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_);
lean_dec(v___y_4994_);
lean_dec_ref(v___y_4993_);
lean_dec(v___y_4992_);
lean_dec_ref(v___y_4991_);
return v_res_4996_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1(void){
_start:
{
lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___x_4998_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__0));
v___x_4999_ = l_Lean_stringToMessageData(v___x_4998_);
return v___x_4999_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1(void){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_5001_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__0));
v___x_5002_ = l_Lean_stringToMessageData(v___x_5001_);
return v___x_5002_;
}
}
lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega(lean_object* v_p_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, uint8_t v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v___y_5015_; lean_object* v___y_5016_; lean_object* v___y_5017_; uint8_t v___y_5018_; lean_object* v___y_5019_; lean_object* v___y_5020_; lean_object* v___y_5021_; lean_object* v___y_5022_; lean_object* v___y_5023_; lean_object* v_toCold_5029_; lean_object* v_options_5030_; uint8_t v_hasTrace_5031_; 
v_toCold_5029_ = lean_ctor_get(v_a_5011_, 0);
v_options_5030_ = lean_ctor_get(v_toCold_5029_, 2);
v_hasTrace_5031_ = lean_ctor_get_uint8(v_options_5030_, sizeof(void*)*1);
if (v_hasTrace_5031_ == 0)
{
v___y_5015_ = v_a_5004_;
v___y_5016_ = v_a_5005_;
v___y_5017_ = v_a_5006_;
v___y_5018_ = v_a_5007_;
v___y_5019_ = v_a_5008_;
v___y_5020_ = v_a_5009_;
v___y_5021_ = v_a_5010_;
v___y_5022_ = v_a_5011_;
v___y_5023_ = v_a_5012_;
goto v___jp_5014_;
}
else
{
lean_object* v_inheritedTraceOptions_5032_; lean_object* v_cls_5033_; lean_object* v___x_5034_; uint8_t v___x_5035_; 
v_inheritedTraceOptions_5032_ = lean_ctor_get(v_toCold_5029_, 11);
v_cls_5033_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_5034_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_5035_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5032_, v_options_5030_, v___x_5034_);
if (v___x_5035_ == 0)
{
v___y_5015_ = v_a_5004_;
v___y_5016_ = v_a_5005_;
v___y_5017_ = v_a_5006_;
v___y_5018_ = v_a_5007_;
v___y_5019_ = v_a_5008_;
v___y_5020_ = v_a_5009_;
v___y_5021_ = v_a_5010_;
v___y_5022_ = v_a_5011_;
v___y_5023_ = v_a_5012_;
goto v___jp_5014_;
}
else
{
lean_object* v_constraints_5036_; uint8_t v_possible_5037_; lean_object* v___x_5038_; lean_object* v___y_5040_; 
v_constraints_5036_ = lean_ctor_get(v_p_5003_, 2);
v_possible_5037_ = lean_ctor_get_uint8(v_p_5003_, sizeof(void*)*7);
v___x_5038_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1);
if (v_possible_5037_ == 0)
{
lean_object* v___x_5053_; 
v___x_5053_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
v___y_5040_ = v___x_5053_;
goto v___jp_5039_;
}
else
{
uint8_t v___x_5054_; 
v___x_5054_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_5003_);
if (v___x_5054_ == 0)
{
lean_object* v_buckets_5055_; lean_object* v___x_5056_; lean_object* v___y_5058_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; uint8_t v___x_5065_; 
v_buckets_5055_ = lean_ctor_get(v_constraints_5036_, 1);
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
v___y_5040_ = v___x_5061_;
goto v___jp_5039_;
}
}
else
{
lean_object* v___x_5069_; 
v___x_5069_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_5040_ = v___x_5069_;
goto v___jp_5039_;
}
}
v___jp_5039_:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5041_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5041_, 0, v___y_5040_);
v___x_5042_ = l_Lean_MessageData_ofFormat(v___x_5041_);
v___x_5043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5038_);
lean_ctor_set(v___x_5043_, 1, v___x_5042_);
v___x_5044_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5033_, v___x_5043_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_dec_ref_known(v___x_5044_, 1);
v___y_5015_ = v_a_5004_;
v___y_5016_ = v_a_5005_;
v___y_5017_ = v_a_5006_;
v___y_5018_ = v_a_5007_;
v___y_5019_ = v_a_5008_;
v___y_5020_ = v_a_5009_;
v___y_5021_ = v_a_5010_;
v___y_5022_ = v_a_5011_;
v___y_5023_ = v_a_5012_;
goto v___jp_5014_;
}
else
{
lean_object* v_a_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5052_; 
lean_dec_ref(v_p_5003_);
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5047_ = v___x_5044_;
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_a_5045_);
lean_dec(v___x_5044_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
}
}
}
v___jp_5014_:
{
uint8_t v_possible_5024_; 
v_possible_5024_ = lean_ctor_get_uint8(v_p_5003_, sizeof(void*)*7);
if (v_possible_5024_ == 0)
{
lean_object* v___x_5025_; 
v___x_5025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5025_, 0, v_p_5003_);
return v___x_5025_;
}
else
{
lean_object* v___x_5026_; 
v___x_5026_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_5003_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_);
if (lean_obj_tag(v___x_5026_) == 0)
{
lean_object* v_a_5027_; lean_object* v___x_5028_; 
v_a_5027_ = lean_ctor_get(v___x_5026_, 0);
lean_inc(v_a_5027_);
lean_dec_ref_known(v___x_5026_, 1);
v___x_5028_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_a_5027_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_);
return v___x_5028_;
}
else
{
return v___x_5026_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_runOmega_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_5003_ = stack[0].m_obj;
lean_object* v_a_5004_ = stack[1].m_obj;
lean_object* v_a_5005_ = stack[2].m_obj;
lean_object* v_a_5006_ = stack[3].m_obj;
uint8_t v_a_5007_ = stack[4].m_num;
lean_object* v_a_5008_ = stack[5].m_obj;
lean_object* v_a_5009_ = stack[6].m_obj;
lean_object* v_a_5010_ = stack[7].m_obj;
lean_object* v_a_5011_ = stack[8].m_obj;
lean_object* v_a_5012_ = stack[9].m_obj;
lean_object* v_res_5070_;
v_res_5070_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_p_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
stack->m_obj
 = v_res_5070_;
}
lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination(lean_object* v_p_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, uint8_t v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_){
_start:
{
lean_object* v___y_5083_; lean_object* v___y_5084_; lean_object* v___y_5085_; uint8_t v___y_5086_; lean_object* v___y_5087_; lean_object* v___y_5088_; lean_object* v___y_5089_; lean_object* v___y_5090_; lean_object* v___y_5091_; uint8_t v_possible_5095_; 
v_possible_5095_ = lean_ctor_get_uint8(v_p_5071_, sizeof(void*)*7);
if (v_possible_5095_ == 0)
{
lean_object* v___x_5096_; 
v___x_5096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5096_, 0, v_p_5071_);
return v___x_5096_;
}
else
{
lean_object* v_constraints_5097_; uint8_t v___x_5098_; 
v_constraints_5097_ = lean_ctor_get(v_p_5071_, 2);
v___x_5098_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_5071_);
if (v___x_5098_ == 0)
{
lean_object* v_toCold_5099_; lean_object* v_options_5100_; uint8_t v_hasTrace_5101_; 
v_toCold_5099_ = lean_ctor_get(v_a_5079_, 0);
v_options_5100_ = lean_ctor_get(v_toCold_5099_, 2);
v_hasTrace_5101_ = lean_ctor_get_uint8(v_options_5100_, sizeof(void*)*1);
if (v_hasTrace_5101_ == 0)
{
v___y_5083_ = v_a_5072_;
v___y_5084_ = v_a_5073_;
v___y_5085_ = v_a_5074_;
v___y_5086_ = v_a_5075_;
v___y_5087_ = v_a_5076_;
v___y_5088_ = v_a_5077_;
v___y_5089_ = v_a_5078_;
v___y_5090_ = v_a_5079_;
v___y_5091_ = v_a_5080_;
goto v___jp_5082_;
}
else
{
lean_object* v_inheritedTraceOptions_5102_; lean_object* v_cls_5103_; lean_object* v___x_5104_; uint8_t v___x_5105_; 
v_inheritedTraceOptions_5102_ = lean_ctor_get(v_toCold_5099_, 11);
v_cls_5103_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_5104_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_5105_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5102_, v_options_5100_, v___x_5104_);
if (v___x_5105_ == 0)
{
v___y_5083_ = v_a_5072_;
v___y_5084_ = v_a_5073_;
v___y_5085_ = v_a_5074_;
v___y_5086_ = v_a_5075_;
v___y_5087_ = v_a_5076_;
v___y_5088_ = v_a_5077_;
v___y_5089_ = v_a_5078_;
v___y_5090_ = v_a_5079_;
v___y_5091_ = v_a_5080_;
goto v___jp_5082_;
}
else
{
lean_object* v___x_5106_; lean_object* v___y_5108_; 
v___x_5106_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1);
if (v___x_5098_ == 0)
{
lean_object* v_buckets_5121_; lean_object* v___x_5122_; lean_object* v___y_5124_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; uint8_t v___x_5131_; 
v_buckets_5121_ = lean_ctor_get(v_constraints_5097_, 1);
v___x_5122_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5128_ = lean_box(0);
v___x_5129_ = lean_array_get_size(v_buckets_5121_);
v___x_5130_ = lean_unsigned_to_nat(0u);
v___x_5131_ = lean_nat_dec_lt(v___x_5130_, v___x_5129_);
if (v___x_5131_ == 0)
{
v___y_5124_ = v___x_5128_;
goto v___jp_5123_;
}
else
{
size_t v___x_5132_; size_t v___x_5133_; lean_object* v___x_5134_; 
v___x_5132_ = lean_usize_of_nat(v___x_5129_);
v___x_5133_ = ((size_t)0ULL);
v___x_5134_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5121_, v___x_5132_, v___x_5133_, v___x_5128_);
v___y_5124_ = v___x_5134_;
goto v___jp_5123_;
}
v___jp_5123_:
{
lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
v___x_5125_ = lean_box(0);
v___x_5126_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5124_, v___x_5125_);
v___x_5127_ = l_String_intercalate(v___x_5122_, v___x_5126_);
v___y_5108_ = v___x_5127_;
goto v___jp_5107_;
}
}
else
{
lean_object* v___x_5135_; 
v___x_5135_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_5108_ = v___x_5135_;
goto v___jp_5107_;
}
v___jp_5107_:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; 
v___x_5109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5109_, 0, v___y_5108_);
v___x_5110_ = l_Lean_MessageData_ofFormat(v___x_5109_);
v___x_5111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5111_, 0, v___x_5106_);
lean_ctor_set(v___x_5111_, 1, v___x_5110_);
v___x_5112_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5103_, v___x_5111_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
if (lean_obj_tag(v___x_5112_) == 0)
{
lean_dec_ref_known(v___x_5112_, 1);
v___y_5083_ = v_a_5072_;
v___y_5084_ = v_a_5073_;
v___y_5085_ = v_a_5074_;
v___y_5086_ = v_a_5075_;
v___y_5087_ = v_a_5076_;
v___y_5088_ = v_a_5077_;
v___y_5089_ = v_a_5078_;
v___y_5090_ = v_a_5079_;
v___y_5091_ = v_a_5080_;
goto v___jp_5082_;
}
else
{
lean_object* v_a_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5120_; 
lean_dec_ref(v_p_5071_);
v_a_5113_ = lean_ctor_get(v___x_5112_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v___x_5112_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5115_ = v___x_5112_;
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_a_5113_);
lean_dec(v___x_5112_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5118_; 
if (v_isShared_5116_ == 0)
{
v___x_5118_ = v___x_5115_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_a_5113_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5136_; 
v___x_5136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5136_, 0, v_p_5071_);
return v___x_5136_;
}
}
v___jp_5082_:
{
lean_object* v___x_5092_; 
v___x_5092_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_5071_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_);
if (lean_obj_tag(v___x_5092_) == 0)
{
lean_object* v_a_5093_; lean_object* v___x_5094_; 
v_a_5093_ = lean_ctor_get(v___x_5092_, 0);
lean_inc(v_a_5093_);
lean_dec_ref_known(v___x_5092_, 1);
v___x_5094_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_a_5093_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_);
return v___x_5094_;
}
else
{
return v___x_5092_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Omega_Problem_elimination_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_5071_ = stack[0].m_obj;
lean_object* v_a_5072_ = stack[1].m_obj;
lean_object* v_a_5073_ = stack[2].m_obj;
lean_object* v_a_5074_ = stack[3].m_obj;
uint8_t v_a_5075_ = stack[4].m_num;
lean_object* v_a_5076_ = stack[5].m_obj;
lean_object* v_a_5077_ = stack[6].m_obj;
lean_object* v_a_5078_ = stack[7].m_obj;
lean_object* v_a_5079_ = stack[8].m_obj;
lean_object* v_a_5080_ = stack[9].m_obj;
lean_object* v_res_5137_;
v_res_5137_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_p_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
stack->m_obj
 = v_res_5137_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___boxed(lean_object* v_p_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_){
_start:
{
uint8_t v_a_boxed_5149_; lean_object* v_res_5150_; 
v_a_boxed_5149_ = lean_unbox(v_a_5142_);
v_res_5150_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_p_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_boxed_5149_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_);
lean_dec(v_a_5147_);
lean_dec_ref(v_a_5146_);
lean_dec(v_a_5145_);
lean_dec_ref(v_a_5144_);
lean_dec(v_a_5143_);
lean_dec_ref(v_a_5141_);
lean_dec(v_a_5140_);
lean_dec(v_a_5139_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___boxed(lean_object* v_p_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_){
_start:
{
uint8_t v_a_boxed_5162_; lean_object* v_res_5163_; 
v_a_boxed_5162_ = lean_unbox(v_a_5155_);
v_res_5163_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_p_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_boxed_5162_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_);
lean_dec(v_a_5160_);
lean_dec_ref(v_a_5159_);
lean_dec(v_a_5158_);
lean_dec_ref(v_a_5157_);
lean_dec(v_a_5156_);
lean_dec_ref(v_a_5154_);
lean_dec(v_a_5153_);
lean_dec(v_a_5152_);
return v_res_5163_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(lean_object* v_cls_5164_, lean_object* v_msg_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, uint8_t v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_){
_start:
{
lean_object* v___x_5176_; 
v___x_5176_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5164_, v_msg_5165_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_);
return v___x_5176_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_5164_ = stack[0].m_obj;
lean_object* v_msg_5165_ = stack[1].m_obj;
lean_object* v___y_5166_ = stack[2].m_obj;
lean_object* v___y_5167_ = stack[3].m_obj;
lean_object* v___y_5168_ = stack[4].m_obj;
uint8_t v___y_5169_ = stack[5].m_num;
lean_object* v___y_5170_ = stack[6].m_obj;
lean_object* v___y_5171_ = stack[7].m_obj;
lean_object* v___y_5172_ = stack[8].m_obj;
lean_object* v___y_5173_ = stack[9].m_obj;
lean_object* v___y_5174_ = stack[10].m_obj;
lean_object* v_res_5177_;
v_res_5177_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(v_cls_5164_, v_msg_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_);
stack->m_obj
 = v_res_5177_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___boxed(lean_object* v_cls_5178_, lean_object* v_msg_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_){
_start:
{
uint8_t v___y_16669__boxed_5190_; lean_object* v_res_5191_; 
v___y_16669__boxed_5190_ = lean_unbox(v___y_5183_);
v_res_5191_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(v_cls_5178_, v_msg_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_16669__boxed_5190_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
lean_dec(v___y_5184_);
lean_dec_ref(v___y_5182_);
lean_dec(v___y_5181_);
lean_dec(v___y_5180_);
return v_res_5191_;
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
