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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl___redArg(lean_object* v_x_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_tag_nat(v_x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl___redArg___boxed(lean_object* v_x_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl___redArg(v_x_272_);
lean_dec_ref(v_x_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl(lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_x_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_tag_nat(v_x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl___boxed(lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_x_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Elab_Tactic_Omega_Justification_ctorIdx___impl(v_a_278_, v_a_279_, v_x_280_);
lean_dec_ref(v_x_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(lean_object* v_t_282_, lean_object* v_k_283_){
_start:
{
switch(lean_obj_tag(v_t_282_))
{
case 0:
{
lean_object* v_s_284_; lean_object* v_x_285_; lean_object* v_i_286_; lean_object* v___x_287_; 
v_s_284_ = lean_ctor_get(v_t_282_, 0);
lean_inc_ref(v_s_284_);
v_x_285_ = lean_ctor_get(v_t_282_, 1);
lean_inc(v_x_285_);
v_i_286_ = lean_ctor_get(v_t_282_, 2);
lean_inc(v_i_286_);
lean_dec_ref_known(v_t_282_, 3);
v___x_287_ = lean_apply_3(v_k_283_, v_s_284_, v_x_285_, v_i_286_);
return v___x_287_;
}
case 1:
{
lean_object* v_s_288_; lean_object* v_c_289_; lean_object* v_j_290_; lean_object* v___x_291_; 
v_s_288_ = lean_ctor_get(v_t_282_, 0);
lean_inc_ref(v_s_288_);
v_c_289_ = lean_ctor_get(v_t_282_, 1);
lean_inc(v_c_289_);
v_j_290_ = lean_ctor_get(v_t_282_, 2);
lean_inc_ref(v_j_290_);
lean_dec_ref_known(v_t_282_, 3);
v___x_291_ = lean_apply_3(v_k_283_, v_s_288_, v_c_289_, v_j_290_);
return v___x_291_;
}
case 2:
{
lean_object* v_s_292_; lean_object* v_t_293_; lean_object* v_c_294_; lean_object* v_j_295_; lean_object* v_k_296_; lean_object* v___x_297_; 
v_s_292_ = lean_ctor_get(v_t_282_, 0);
lean_inc_ref(v_s_292_);
v_t_293_ = lean_ctor_get(v_t_282_, 1);
lean_inc_ref(v_t_293_);
v_c_294_ = lean_ctor_get(v_t_282_, 2);
lean_inc(v_c_294_);
v_j_295_ = lean_ctor_get(v_t_282_, 3);
lean_inc_ref(v_j_295_);
v_k_296_ = lean_ctor_get(v_t_282_, 4);
lean_inc_ref(v_k_296_);
lean_dec_ref_known(v_t_282_, 5);
v___x_297_ = lean_apply_5(v_k_283_, v_s_292_, v_t_293_, v_c_294_, v_j_295_, v_k_296_);
return v___x_297_;
}
case 3:
{
lean_object* v_s_298_; lean_object* v_t_299_; lean_object* v_x_300_; lean_object* v_y_301_; lean_object* v_a_302_; lean_object* v_j_303_; lean_object* v_b_304_; lean_object* v_k_305_; lean_object* v___x_306_; 
v_s_298_ = lean_ctor_get(v_t_282_, 0);
lean_inc_ref(v_s_298_);
v_t_299_ = lean_ctor_get(v_t_282_, 1);
lean_inc_ref(v_t_299_);
v_x_300_ = lean_ctor_get(v_t_282_, 2);
lean_inc(v_x_300_);
v_y_301_ = lean_ctor_get(v_t_282_, 3);
lean_inc(v_y_301_);
v_a_302_ = lean_ctor_get(v_t_282_, 4);
lean_inc(v_a_302_);
v_j_303_ = lean_ctor_get(v_t_282_, 5);
lean_inc_ref(v_j_303_);
v_b_304_ = lean_ctor_get(v_t_282_, 6);
lean_inc(v_b_304_);
v_k_305_ = lean_ctor_get(v_t_282_, 7);
lean_inc_ref(v_k_305_);
lean_dec_ref_known(v_t_282_, 8);
v___x_306_ = lean_apply_8(v_k_283_, v_s_298_, v_t_299_, v_x_300_, v_y_301_, v_a_302_, v_j_303_, v_b_304_, v_k_305_);
return v___x_306_;
}
default: 
{
lean_object* v_m_307_; lean_object* v_r_308_; lean_object* v_i_309_; lean_object* v_x_310_; lean_object* v_j_311_; lean_object* v___x_312_; 
v_m_307_ = lean_ctor_get(v_t_282_, 0);
lean_inc(v_m_307_);
v_r_308_ = lean_ctor_get(v_t_282_, 1);
lean_inc(v_r_308_);
v_i_309_ = lean_ctor_get(v_t_282_, 2);
lean_inc(v_i_309_);
v_x_310_ = lean_ctor_get(v_t_282_, 3);
lean_inc(v_x_310_);
v_j_311_ = lean_ctor_get(v_t_282_, 4);
lean_inc_ref(v_j_311_);
lean_dec_ref_known(v_t_282_, 5);
v___x_312_ = lean_apply_5(v_k_283_, v_m_307_, v_r_308_, v_i_309_, v_x_310_, v_j_311_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim(lean_object* v_motive_313_, lean_object* v_ctorIdx_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_t_317_, lean_object* v_h_318_, lean_object* v_k_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_317_, v_k_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_ctorElim___boxed(lean_object* v_motive_321_, lean_object* v_ctorIdx_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_t_325_, lean_object* v_h_326_, lean_object* v_k_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim(v_motive_321_, v_ctorIdx_322_, v_a_323_, v_a_324_, v_t_325_, v_h_326_, v_k_327_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_ctorIdx_322_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim___redArg(lean_object* v_t_329_, lean_object* v_assumption_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_329_, v_assumption_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim(lean_object* v_motive_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_t_335_, lean_object* v_h_336_, lean_object* v_assumption_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_335_, v_assumption_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_assumption_elim___boxed(lean_object* v_motive_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_t_342_, lean_object* v_h_343_, lean_object* v_assumption_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Elab_Tactic_Omega_Justification_assumption_elim(v_motive_339_, v_a_340_, v_a_341_, v_t_342_, v_h_343_, v_assumption_344_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim___redArg(lean_object* v_t_346_, lean_object* v_tidy_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_346_, v_tidy_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim(lean_object* v_motive_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_t_352_, lean_object* v_h_353_, lean_object* v_tidy_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_352_, v_tidy_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_elim___boxed(lean_object* v_motive_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_t_359_, lean_object* v_h_360_, lean_object* v_tidy_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_elim(v_motive_356_, v_a_357_, v_a_358_, v_t_359_, v_h_360_, v_tidy_361_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim___redArg(lean_object* v_t_363_, lean_object* v_combine_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_363_, v_combine_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim(lean_object* v_motive_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_t_369_, lean_object* v_h_370_, lean_object* v_combine_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_369_, v_combine_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combine_elim___boxed(lean_object* v_motive_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_t_376_, lean_object* v_h_377_, lean_object* v_combine_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Elab_Tactic_Omega_Justification_combine_elim(v_motive_373_, v_a_374_, v_a_375_, v_t_376_, v_h_377_, v_combine_378_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim___redArg(lean_object* v_t_380_, lean_object* v_combo_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_380_, v_combo_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim(lean_object* v_motive_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_t_386_, lean_object* v_h_387_, lean_object* v_combo_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_386_, v_combo_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combo_elim___boxed(lean_object* v_motive_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_t_393_, lean_object* v_h_394_, lean_object* v_combo_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Elab_Tactic_Omega_Justification_combo_elim(v_motive_390_, v_a_391_, v_a_392_, v_t_393_, v_h_394_, v_combo_395_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim___redArg(lean_object* v_t_397_, lean_object* v_bmod_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_397_, v_bmod_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim(lean_object* v_motive_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_bmod_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Elab_Tactic_Omega_Justification_ctorElim___redArg(v_t_403_, v_bmod_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmod_elim___boxed(lean_object* v_motive_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_t_410_, lean_object* v_h_411_, lean_object* v_bmod_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Elab_Tactic_Omega_Justification_bmod_elim(v_motive_407_, v_a_408_, v_a_409_, v_t_410_, v_h_411_, v_bmod_412_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(lean_object* v_s_414_, lean_object* v_c_415_, lean_object* v_j_416_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_inc(v_c_415_);
lean_inc_ref(v_s_414_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_s_414_);
lean_ctor_set(v___x_417_, 1, v_c_415_);
lean_inc_ref(v___x_417_);
v___x_418_ = l_Lean_Omega_tidy_x3f(v___x_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v___x_419_; 
lean_dec_ref_known(v___x_417_, 2);
lean_dec_ref(v_j_416_);
lean_dec(v_c_415_);
lean_dec_ref(v_s_414_);
v___x_419_ = lean_box(0);
return v___x_419_;
}
else
{
lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_438_; 
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; 
v_unused_439_ = lean_ctor_get(v___x_418_, 0);
lean_dec(v_unused_439_);
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_438_;
goto v_resetjp_420_;
}
else
{
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_438_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v_fst_424_; lean_object* v_snd_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_437_; 
v___x_423_ = l_Lean_Omega_tidy(v___x_417_);
v_fst_424_ = lean_ctor_get(v___x_423_, 0);
v_snd_425_ = lean_ctor_get(v___x_423_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_437_ == 0)
{
v___x_427_ = v___x_423_;
v_isShared_428_ = v_isSharedCheck_437_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_snd_425_);
lean_inc(v_fst_424_);
lean_dec(v___x_423_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_437_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_429_, 0, v_s_414_);
lean_ctor_set(v___x_429_, 1, v_c_415_);
lean_ctor_set(v___x_429_, 2, v_j_416_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 1, v___x_429_);
lean_ctor_set(v___x_427_, 0, v_snd_425_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_snd_425_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_436_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v_fst_424_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_432_);
v___x_434_ = v___x_421_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(lean_object* v_s_440_, lean_object* v_replacement_441_, lean_object* v_a_442_, lean_object* v_b_443_){
_start:
{
lean_object* v_it_445_; lean_object* v_startPos_446_; lean_object* v_endPos_447_; lean_object* v_it_456_; 
switch(lean_obj_tag(v_a_442_))
{
case 0:
{
lean_object* v_pos_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_474_; 
v_pos_462_ = lean_ctor_get(v_a_442_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v_a_442_);
if (v_isSharedCheck_474_ == 0)
{
v___x_464_ = v_a_442_;
v_isShared_465_ = v_isSharedCheck_474_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_pos_462_);
lean_dec(v_a_442_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_474_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v_startInclusive_466_; lean_object* v_endExclusive_467_; lean_object* v___x_468_; uint8_t v_decide_469_; 
v_startInclusive_466_ = lean_ctor_get(v_s_440_, 1);
v_endExclusive_467_ = lean_ctor_get(v_s_440_, 2);
v___x_468_ = lean_nat_sub(v_endExclusive_467_, v_startInclusive_466_);
v_decide_469_ = lean_nat_dec_eq(v_pos_462_, v___x_468_);
lean_dec(v___x_468_);
if (v_decide_469_ == 0)
{
lean_object* v___x_471_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set_tag(v___x_464_, 1);
v___x_471_ = v___x_464_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_pos_462_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
v_it_456_ = v___x_471_;
goto v___jp_455_;
}
}
else
{
lean_object* v___x_473_; 
lean_del_object(v___x_464_);
lean_dec(v_pos_462_);
v___x_473_ = lean_box(3);
v_it_456_ = v___x_473_;
goto v___jp_455_;
}
}
}
case 1:
{
lean_object* v_pos_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_487_; 
v_pos_475_ = lean_ctor_get(v_a_442_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v_a_442_);
if (v_isSharedCheck_487_ == 0)
{
v___x_477_ = v_a_442_;
v_isShared_478_ = v_isSharedCheck_487_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_pos_475_);
lean_dec(v_a_442_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_487_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_str_479_; lean_object* v_startInclusive_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v_str_479_ = lean_ctor_get(v_s_440_, 0);
v_startInclusive_480_ = lean_ctor_get(v_s_440_, 1);
v___x_481_ = lean_nat_add(v_startInclusive_480_, v_pos_475_);
v___x_482_ = lean_string_utf8_next_fast(v_str_479_, v___x_481_);
lean_dec(v___x_481_);
v___x_483_ = lean_nat_sub(v___x_482_, v_startInclusive_480_);
lean_inc(v___x_483_);
if (v_isShared_478_ == 0)
{
lean_ctor_set_tag(v___x_477_, 0);
lean_ctor_set(v___x_477_, 0, v___x_483_);
v___x_485_ = v___x_477_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
v_it_445_ = v___x_485_;
v_startPos_446_ = v_pos_475_;
v_endPos_447_ = v___x_483_;
goto v___jp_444_;
}
}
}
case 2:
{
lean_object* v_needle_488_; lean_object* v_table_489_; lean_object* v_stackPos_490_; lean_object* v_needlePos_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_552_; 
v_needle_488_ = lean_ctor_get(v_a_442_, 0);
v_table_489_ = lean_ctor_get(v_a_442_, 1);
v_stackPos_490_ = lean_ctor_get(v_a_442_, 2);
v_needlePos_491_ = lean_ctor_get(v_a_442_, 3);
v_isSharedCheck_552_ = !lean_is_exclusive(v_a_442_);
if (v_isSharedCheck_552_ == 0)
{
v___x_493_ = v_a_442_;
v_isShared_494_ = v_isSharedCheck_552_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_needlePos_491_);
lean_inc(v_stackPos_490_);
lean_inc(v_table_489_);
lean_inc(v_needle_488_);
lean_dec(v_a_442_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_552_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v_str_495_; lean_object* v_startInclusive_496_; lean_object* v_endExclusive_497_; lean_object* v_str_498_; lean_object* v_startInclusive_499_; lean_object* v_endExclusive_500_; lean_object* v_basePos_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v_str_495_ = lean_ctor_get(v_needle_488_, 0);
v_startInclusive_496_ = lean_ctor_get(v_needle_488_, 1);
v_endExclusive_497_ = lean_ctor_get(v_needle_488_, 2);
v_str_498_ = lean_ctor_get(v_s_440_, 0);
v_startInclusive_499_ = lean_ctor_get(v_s_440_, 1);
v_endExclusive_500_ = lean_ctor_get(v_s_440_, 2);
v_basePos_501_ = lean_nat_sub(v_stackPos_490_, v_needlePos_491_);
v___x_502_ = lean_nat_sub(v_endExclusive_497_, v_startInclusive_496_);
v___x_503_ = lean_nat_add(v_basePos_501_, v___x_502_);
v___x_504_ = lean_nat_sub(v_endExclusive_500_, v_startInclusive_499_);
v___x_505_ = lean_nat_dec_le(v___x_503_, v___x_504_);
lean_dec(v___x_503_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
lean_dec(v___x_502_);
lean_del_object(v___x_493_);
lean_dec(v_needlePos_491_);
lean_dec(v_stackPos_490_);
lean_dec_ref(v_table_489_);
lean_dec_ref(v_needle_488_);
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_basePos_501_, v___x_506_);
v___x_508_ = lean_nat_dec_le(v___x_507_, v___x_504_);
lean_dec(v___x_507_);
if (v___x_508_ == 0)
{
lean_dec(v___x_504_);
lean_dec(v_basePos_501_);
lean_dec_ref(v_s_440_);
return v_b_443_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = l_String_Slice_pos_x21(v_s_440_, v_basePos_501_);
lean_dec(v_basePos_501_);
v___x_510_ = lean_box(3);
v_it_445_ = v___x_510_;
v_startPos_446_ = v___x_509_;
v_endPos_447_ = v___x_504_;
goto v___jp_444_;
}
}
else
{
lean_object* v___x_511_; uint8_t v_stackByte_512_; lean_object* v___x_513_; uint8_t v_patByte_514_; uint8_t v___x_515_; 
lean_dec(v___x_504_);
v___x_511_ = lean_nat_add(v_startInclusive_499_, v_stackPos_490_);
v_stackByte_512_ = lean_string_get_byte_fast(v_str_498_, v___x_511_);
v___x_513_ = lean_nat_add(v_startInclusive_496_, v_needlePos_491_);
v_patByte_514_ = lean_string_get_byte_fast(v_str_495_, v___x_513_);
v___x_515_ = lean_uint8_dec_eq(v_stackByte_512_, v_patByte_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; uint8_t v_decide_517_; 
lean_dec(v___x_502_);
v___x_516_ = lean_unsigned_to_nat(0u);
v_decide_517_ = lean_nat_dec_eq(v_needlePos_491_, v___x_516_);
if (v_decide_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v_newNeedlePos_520_; uint8_t v___x_521_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_sub(v_needlePos_491_, v___x_518_);
lean_dec(v_needlePos_491_);
v_newNeedlePos_520_ = lean_array_fget_borrowed(v_table_489_, v___x_519_);
lean_dec(v___x_519_);
v___x_521_ = lean_nat_dec_eq(v_newNeedlePos_520_, v___x_516_);
if (v___x_521_ == 0)
{
lean_object* v_oldBasePos_522_; lean_object* v___x_523_; lean_object* v_newBasePos_524_; lean_object* v___x_526_; 
lean_inc(v_newNeedlePos_520_);
v_oldBasePos_522_ = l_String_Slice_pos_x21(v_s_440_, v_basePos_501_);
lean_dec(v_basePos_501_);
v___x_523_ = lean_nat_sub(v_stackPos_490_, v_newNeedlePos_520_);
v_newBasePos_524_ = l_String_Slice_pos_x21(v_s_440_, v___x_523_);
lean_dec(v___x_523_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 3, v_newNeedlePos_520_);
v___x_526_ = v___x_493_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_needle_488_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_table_489_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_stackPos_490_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_newNeedlePos_520_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v_it_445_ = v___x_526_;
v_startPos_446_ = v_oldBasePos_522_;
v_endPos_447_ = v_newBasePos_524_;
goto v___jp_444_;
}
}
else
{
lean_object* v_basePos_528_; lean_object* v_nextStackPos_529_; lean_object* v___x_531_; 
v_basePos_528_ = l_String_Slice_pos_x21(v_s_440_, v_basePos_501_);
lean_dec(v_basePos_501_);
v_nextStackPos_529_ = l_String_Slice_posGE___redArg(v_s_440_, v_stackPos_490_);
lean_inc(v_nextStackPos_529_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 3, v___x_516_);
lean_ctor_set(v___x_493_, 2, v_nextStackPos_529_);
v___x_531_ = v___x_493_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_needle_488_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_table_489_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_nextStackPos_529_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v___x_516_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
v_it_445_ = v___x_531_;
v_startPos_446_ = v_basePos_528_;
v_endPos_447_ = v_nextStackPos_529_;
goto v___jp_444_;
}
}
}
else
{
lean_object* v_basePos_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v_nextStackPos_536_; lean_object* v___x_538_; 
lean_dec(v_basePos_501_);
lean_dec(v_needlePos_491_);
v_basePos_533_ = l_String_Slice_pos_x21(v_s_440_, v_stackPos_490_);
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_add(v_stackPos_490_, v___x_534_);
lean_dec(v_stackPos_490_);
v_nextStackPos_536_ = l_String_Slice_posGE___redArg(v_s_440_, v___x_535_);
lean_inc(v_nextStackPos_536_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 3, v___x_516_);
lean_ctor_set(v___x_493_, 2, v_nextStackPos_536_);
v___x_538_ = v___x_493_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_needle_488_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_table_489_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_nextStackPos_536_);
lean_ctor_set(v_reuseFailAlloc_539_, 3, v___x_516_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
v_it_445_ = v___x_538_;
v_startPos_446_ = v_basePos_533_;
v_endPos_447_ = v_nextStackPos_536_;
goto v___jp_444_;
}
}
}
else
{
lean_object* v___x_540_; lean_object* v_nextStackPos_541_; lean_object* v_nextNeedlePos_542_; uint8_t v_decide_543_; 
lean_dec(v_basePos_501_);
v___x_540_ = lean_unsigned_to_nat(1u);
v_nextStackPos_541_ = lean_nat_add(v_stackPos_490_, v___x_540_);
lean_dec(v_stackPos_490_);
v_nextNeedlePos_542_ = lean_nat_add(v_needlePos_491_, v___x_540_);
lean_dec(v_needlePos_491_);
v_decide_543_ = lean_nat_dec_eq(v_nextNeedlePos_542_, v___x_502_);
lean_dec(v___x_502_);
if (v_decide_543_ == 0)
{
lean_object* v___x_545_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 3, v_nextNeedlePos_542_);
lean_ctor_set(v___x_493_, 2, v_nextStackPos_541_);
v___x_545_ = v___x_493_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_needle_488_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_table_489_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_nextStackPos_541_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_nextNeedlePos_542_);
v___x_545_ = v_reuseFailAlloc_547_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
v_a_442_ = v___x_545_;
goto _start;
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_550_; 
lean_dec(v_nextNeedlePos_542_);
v___x_548_ = lean_unsigned_to_nat(0u);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 3, v___x_548_);
lean_ctor_set(v___x_493_, 2, v_nextStackPos_541_);
v___x_550_ = v___x_493_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_needle_488_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_table_489_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_nextStackPos_541_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
v_it_456_ = v___x_550_;
goto v___jp_455_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_440_);
return v_b_443_;
}
}
v___jp_444_:
{
lean_object* v___x_448_; lean_object* v_str_449_; lean_object* v_startInclusive_450_; lean_object* v_endExclusive_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
lean_inc_ref(v_s_440_);
v___x_448_ = l_String_Slice_slice_x21(v_s_440_, v_startPos_446_, v_endPos_447_);
lean_dec(v_endPos_447_);
lean_dec(v_startPos_446_);
v_str_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc_ref(v_str_449_);
v_startInclusive_450_ = lean_ctor_get(v___x_448_, 1);
lean_inc(v_startInclusive_450_);
v_endExclusive_451_ = lean_ctor_get(v___x_448_, 2);
lean_inc(v_endExclusive_451_);
lean_dec_ref(v___x_448_);
v___x_452_ = lean_string_utf8_extract_fast(v_str_449_, v_startInclusive_450_, v_endExclusive_451_);
lean_dec(v_endExclusive_451_);
lean_dec(v_startInclusive_450_);
lean_dec_ref(v_str_449_);
v___x_453_ = lean_string_append(v_b_443_, v___x_452_);
lean_dec_ref(v___x_452_);
v_a_442_ = v_it_445_;
v_b_443_ = v___x_453_;
goto _start;
}
v___jp_455_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_string_utf8_byte_size(v_replacement_441_);
v___x_459_ = lean_string_utf8_extract_fast(v_replacement_441_, v___x_457_, v___x_458_);
v___x_460_ = lean_string_append(v_b_443_, v___x_459_);
lean_dec_ref(v___x_459_);
v_a_442_ = v_it_456_;
v_b_443_ = v___x_460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg___boxed(lean_object* v_s_553_, lean_object* v_replacement_554_, lean_object* v_a_555_, lean_object* v_b_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_553_, v_replacement_554_, v_a_555_, v_b_556_);
lean_dec_ref(v_replacement_554_);
return v_res_557_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2));
v___x_565_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_564_);
return v___x_565_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__3);
v___x_568_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__2));
v___x_569_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_567_);
lean_ctor_set(v___x_569_, 2, v___x_566_);
lean_ctor_set(v___x_569_, 3, v___x_566_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(lean_object* v_s_570_, lean_object* v_replacement_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_573_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__4);
v___x_574_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_570_, v_replacement_571_, v___x_573_, v___x_572_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___boxed(lean_object* v_s_575_, lean_object* v_replacement_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v_s_575_, v_replacement_576_);
lean_dec_ref(v_replacement_576_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(lean_object* v_s_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__0));
v___x_582_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet___closed__1));
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_string_utf8_byte_size(v_s_580_);
v___x_585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_585_, 0, v_s_580_);
lean_ctor_set(v___x_585_, 1, v___x_583_);
lean_ctor_set(v___x_585_, 2, v___x_584_);
v___x_586_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v___x_585_, v___x_582_);
v___x_587_ = lean_string_append(v___x_581_, v___x_586_);
lean_dec_ref(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0(lean_object* v_s_588_, lean_object* v_pattern_589_, lean_object* v_replacement_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg(v_s_588_, v_replacement_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___boxed(lean_object* v_s_592_, lean_object* v_pattern_593_, lean_object* v_replacement_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0(v_s_592_, v_pattern_593_, v_replacement_594_);
lean_dec_ref(v_replacement_594_);
lean_dec_ref(v_pattern_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0(lean_object* v_s_596_, lean_object* v_replacement_597_, lean_object* v_inst_598_, lean_object* v_R_599_, lean_object* v_a_600_, lean_object* v_b_601_, lean_object* v_c_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___redArg(v_s_596_, v_replacement_597_, v_a_600_, v_b_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0___boxed(lean_object* v_s_604_, lean_object* v_replacement_605_, lean_object* v_inst_606_, lean_object* v_R_607_, lean_object* v_a_608_, lean_object* v_b_609_, lean_object* v_c_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0_spec__0(v_s_604_, v_replacement_605_, v_inst_606_, v_R_607_, v_a_608_, v_b_609_, v_c_610_);
lean_dec_ref(v_replacement_605_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
if (lean_obj_tag(v_x_614_) == 0)
{
return v_x_613_;
}
else
{
lean_object* v_head_615_; lean_object* v_tail_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_head_615_ = lean_ctor_get(v_x_614_, 0);
v_tail_616_ = lean_ctor_get(v_x_614_, 1);
v___x_617_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_618_ = lean_string_append(v_x_613_, v___x_617_);
v___x_619_ = l_Int_repr(v_head_615_);
v___x_620_ = lean_string_append(v___x_618_, v___x_619_);
lean_dec_ref(v___x_619_);
v_x_613_ = v___x_620_;
v_x_614_ = v_tail_616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___boxed(lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v_x_622_, v_x_623_);
lean_dec(v_x_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(lean_object* v_x_628_){
_start:
{
if (lean_obj_tag(v_x_628_) == 0)
{
lean_object* v___x_629_; 
v___x_629_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__0));
return v___x_629_;
}
else
{
lean_object* v_tail_630_; 
v_tail_630_ = lean_ctor_get(v_x_628_, 1);
if (lean_obj_tag(v_tail_630_) == 0)
{
lean_object* v_head_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_head_631_ = lean_ctor_get(v_x_628_, 0);
v___x_632_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v___x_633_ = l_Int_repr(v_head_631_);
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
lean_dec_ref(v___x_633_);
v___x_635_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_636_ = lean_string_append(v___x_634_, v___x_635_);
return v___x_636_;
}
else
{
lean_object* v_head_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint32_t v___x_642_; lean_object* v___x_643_; 
v_head_637_ = lean_ctor_get(v_x_628_, 0);
v___x_638_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v___x_639_ = l_Int_repr(v_head_637_);
v___x_640_ = lean_string_append(v___x_638_, v___x_639_);
lean_dec_ref(v___x_639_);
v___x_641_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0(v___x_640_, v_tail_630_);
v___x_642_ = 93;
v___x_643_ = lean_string_push(v___x_641_, v___x_642_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___boxed(lean_object* v_x_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_644_);
lean_dec(v_x_644_);
return v_res_645_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
if (lean_obj_tag(v_x_646_) == 0)
{
if (lean_obj_tag(v_x_647_) == 0)
{
uint8_t v___x_648_; 
v___x_648_ = 1;
return v___x_648_;
}
else
{
uint8_t v___x_649_; 
v___x_649_ = 0;
return v___x_649_;
}
}
else
{
if (lean_obj_tag(v_x_647_) == 0)
{
uint8_t v___x_650_; 
v___x_650_ = 0;
return v___x_650_;
}
else
{
lean_object* v_head_651_; lean_object* v_tail_652_; lean_object* v_head_653_; lean_object* v_tail_654_; uint8_t v___x_655_; 
v_head_651_ = lean_ctor_get(v_x_646_, 0);
v_tail_652_ = lean_ctor_get(v_x_646_, 1);
v_head_653_ = lean_ctor_get(v_x_647_, 0);
v_tail_654_ = lean_ctor_get(v_x_647_, 1);
v___x_655_ = lean_int_dec_eq(v_head_651_, v_head_653_);
if (v___x_655_ == 0)
{
return v___x_655_;
}
else
{
v_x_646_ = v_tail_652_;
v_x_647_ = v_tail_654_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1___boxed(lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
uint8_t v_res_659_; lean_object* v_r_660_; 
v_res_659_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_657_, v_x_658_);
lean_dec(v_x_658_);
lean_dec(v_x_657_);
v_r_660_ = lean_box(v_res_659_);
return v_r_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_toString(lean_object* v_s_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
switch(lean_obj_tag(v_x_680_))
{
case 0:
{
lean_object* v_i_681_; lean_object* v_lowerBound_682_; lean_object* v_upperBound_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___y_688_; lean_object* v___y_695_; lean_object* v___y_696_; 
v_i_681_ = lean_ctor_get(v_x_680_, 2);
lean_inc(v_i_681_);
lean_dec_ref_known(v_x_680_, 3);
v_lowerBound_682_ = lean_ctor_get(v_s_678_, 0);
lean_inc(v_lowerBound_682_);
v_upperBound_683_ = lean_ctor_get(v_s_678_, 1);
lean_inc(v_upperBound_683_);
lean_dec_ref(v_s_678_);
v___x_684_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_679_);
lean_dec(v_x_679_);
v___x_685_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_686_ = lean_string_append(v___x_684_, v___x_685_);
if (lean_obj_tag(v_lowerBound_682_) == 0)
{
if (lean_obj_tag(v_upperBound_683_) == 0)
{
lean_object* v___x_700_; 
v___x_700_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_688_ = v___x_700_;
goto v___jp_687_;
}
else
{
lean_object* v_val_701_; lean_object* v___x_702_; lean_object* v___y_704_; lean_object* v_intZero_708_; uint8_t v_isNeg_709_; 
v_val_701_ = lean_ctor_get(v_upperBound_683_, 0);
lean_inc(v_val_701_);
lean_dec_ref_known(v_upperBound_683_, 1);
v___x_702_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_708_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_709_ = lean_int_dec_lt(v_val_701_, v_intZero_708_);
if (v_isNeg_709_ == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; 
v_a_710_ = lean_nat_abs(v_val_701_);
lean_dec(v_val_701_);
v___x_711_ = l_Nat_reprFast(v_a_710_);
v___y_704_ = v___x_711_;
goto v___jp_703_;
}
else
{
lean_object* v_abs_712_; lean_object* v_one_713_; lean_object* v_a_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_abs_712_ = lean_nat_abs(v_val_701_);
lean_dec(v_val_701_);
v_one_713_ = lean_unsigned_to_nat(1u);
v_a_714_ = lean_nat_sub(v_abs_712_, v_one_713_);
lean_dec(v_abs_712_);
v___x_715_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_716_ = lean_nat_add(v_a_714_, v_one_713_);
lean_dec(v_a_714_);
v___x_717_ = l_Nat_reprFast(v___x_716_);
v___x_718_ = lean_string_append(v___x_715_, v___x_717_);
lean_dec_ref(v___x_717_);
v___y_704_ = v___x_718_;
goto v___jp_703_;
}
v___jp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_string_append(v___x_702_, v___y_704_);
lean_dec_ref(v___y_704_);
v___x_706_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_707_ = lean_string_append(v___x_705_, v___x_706_);
v___y_688_ = v___x_707_;
goto v___jp_687_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_683_) == 0)
{
lean_object* v_val_719_; lean_object* v___x_720_; lean_object* v___y_722_; lean_object* v_intZero_726_; uint8_t v_isNeg_727_; 
v_val_719_ = lean_ctor_get(v_lowerBound_682_, 0);
lean_inc(v_val_719_);
lean_dec_ref_known(v_lowerBound_682_, 1);
v___x_720_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_726_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_727_ = lean_int_dec_lt(v_val_719_, v_intZero_726_);
if (v_isNeg_727_ == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; 
v_a_728_ = lean_nat_abs(v_val_719_);
lean_dec(v_val_719_);
v___x_729_ = l_Nat_reprFast(v_a_728_);
v___y_722_ = v___x_729_;
goto v___jp_721_;
}
else
{
lean_object* v_abs_730_; lean_object* v_one_731_; lean_object* v_a_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_abs_730_ = lean_nat_abs(v_val_719_);
lean_dec(v_val_719_);
v_one_731_ = lean_unsigned_to_nat(1u);
v_a_732_ = lean_nat_sub(v_abs_730_, v_one_731_);
lean_dec(v_abs_730_);
v___x_733_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_734_ = lean_nat_add(v_a_732_, v_one_731_);
lean_dec(v_a_732_);
v___x_735_ = l_Nat_reprFast(v___x_734_);
v___x_736_ = lean_string_append(v___x_733_, v___x_735_);
lean_dec_ref(v___x_735_);
v___y_722_ = v___x_736_;
goto v___jp_721_;
}
v___jp_721_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = lean_string_append(v___x_720_, v___y_722_);
lean_dec_ref(v___y_722_);
v___x_724_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_725_ = lean_string_append(v___x_723_, v___x_724_);
v___y_688_ = v___x_725_;
goto v___jp_687_;
}
}
else
{
lean_object* v_val_737_; lean_object* v_val_738_; uint8_t v___x_739_; 
v_val_737_ = lean_ctor_get(v_lowerBound_682_, 0);
lean_inc(v_val_737_);
lean_dec_ref_known(v_lowerBound_682_, 1);
v_val_738_ = lean_ctor_get(v_upperBound_683_, 0);
lean_inc(v_val_738_);
lean_dec_ref_known(v_upperBound_683_, 1);
v___x_739_ = lean_int_dec_lt(v_val_738_, v_val_737_);
if (v___x_739_ == 0)
{
uint8_t v___x_740_; 
v___x_740_ = lean_int_dec_eq(v_val_737_, v_val_738_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___y_743_; lean_object* v_intZero_758_; uint8_t v_isNeg_759_; 
v___x_741_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_758_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_759_ = lean_int_dec_lt(v_val_737_, v_intZero_758_);
if (v_isNeg_759_ == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; 
v_a_760_ = lean_nat_abs(v_val_737_);
lean_dec(v_val_737_);
v___x_761_ = l_Nat_reprFast(v_a_760_);
v___y_743_ = v___x_761_;
goto v___jp_742_;
}
else
{
lean_object* v_abs_762_; lean_object* v_one_763_; lean_object* v_a_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_abs_762_ = lean_nat_abs(v_val_737_);
lean_dec(v_val_737_);
v_one_763_ = lean_unsigned_to_nat(1u);
v_a_764_ = lean_nat_sub(v_abs_762_, v_one_763_);
lean_dec(v_abs_762_);
v___x_765_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_766_ = lean_nat_add(v_a_764_, v_one_763_);
lean_dec(v_a_764_);
v___x_767_ = l_Nat_reprFast(v___x_766_);
v___x_768_ = lean_string_append(v___x_765_, v___x_767_);
lean_dec_ref(v___x_767_);
v___y_743_ = v___x_768_;
goto v___jp_742_;
}
v___jp_742_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v_intZero_747_; uint8_t v_isNeg_748_; 
v___x_744_ = lean_string_append(v___x_741_, v___y_743_);
lean_dec_ref(v___y_743_);
v___x_745_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_746_ = lean_string_append(v___x_744_, v___x_745_);
v_intZero_747_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_748_ = lean_int_dec_lt(v_val_738_, v_intZero_747_);
if (v_isNeg_748_ == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; 
v_a_749_ = lean_nat_abs(v_val_738_);
lean_dec(v_val_738_);
v___x_750_ = l_Nat_reprFast(v_a_749_);
v___y_695_ = v___x_746_;
v___y_696_ = v___x_750_;
goto v___jp_694_;
}
else
{
lean_object* v_abs_751_; lean_object* v_one_752_; lean_object* v_a_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_abs_751_ = lean_nat_abs(v_val_738_);
lean_dec(v_val_738_);
v_one_752_ = lean_unsigned_to_nat(1u);
v_a_753_ = lean_nat_sub(v_abs_751_, v_one_752_);
lean_dec(v_abs_751_);
v___x_754_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_755_ = lean_nat_add(v_a_753_, v_one_752_);
lean_dec(v_a_753_);
v___x_756_ = l_Nat_reprFast(v___x_755_);
v___x_757_ = lean_string_append(v___x_754_, v___x_756_);
lean_dec_ref(v___x_756_);
v___y_695_ = v___x_746_;
v___y_696_ = v___x_757_;
goto v___jp_694_;
}
}
}
else
{
lean_object* v___x_769_; lean_object* v___y_771_; lean_object* v_intZero_775_; uint8_t v_isNeg_776_; 
lean_dec(v_val_738_);
v___x_769_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_775_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_776_ = lean_int_dec_lt(v_val_737_, v_intZero_775_);
if (v_isNeg_776_ == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; 
v_a_777_ = lean_nat_abs(v_val_737_);
lean_dec(v_val_737_);
v___x_778_ = l_Nat_reprFast(v_a_777_);
v___y_771_ = v___x_778_;
goto v___jp_770_;
}
else
{
lean_object* v_abs_779_; lean_object* v_one_780_; lean_object* v_a_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_abs_779_ = lean_nat_abs(v_val_737_);
lean_dec(v_val_737_);
v_one_780_ = lean_unsigned_to_nat(1u);
v_a_781_ = lean_nat_sub(v_abs_779_, v_one_780_);
lean_dec(v_abs_779_);
v___x_782_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_783_ = lean_nat_add(v_a_781_, v_one_780_);
lean_dec(v_a_781_);
v___x_784_ = l_Nat_reprFast(v___x_783_);
v___x_785_ = lean_string_append(v___x_782_, v___x_784_);
lean_dec_ref(v___x_784_);
v___y_771_ = v___x_785_;
goto v___jp_770_;
}
v___jp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = lean_string_append(v___x_769_, v___y_771_);
lean_dec_ref(v___y_771_);
v___x_773_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_774_ = lean_string_append(v___x_772_, v___x_773_);
v___y_688_ = v___x_774_;
goto v___jp_687_;
}
}
}
else
{
lean_object* v___x_786_; 
lean_dec(v_val_738_);
lean_dec(v_val_737_);
v___x_786_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_688_ = v___x_786_;
goto v___jp_687_;
}
}
}
v___jp_687_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_689_ = lean_string_append(v___x_686_, v___y_688_);
lean_dec_ref(v___y_688_);
v___x_690_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__1));
v___x_691_ = lean_string_append(v___x_689_, v___x_690_);
v___x_692_ = l_Nat_reprFast(v_i_681_);
v___x_693_ = lean_string_append(v___x_691_, v___x_692_);
lean_dec_ref(v___x_692_);
return v___x_693_;
}
v___jp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = lean_string_append(v___y_695_, v___y_696_);
lean_dec_ref(v___y_696_);
v___x_698_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_699_ = lean_string_append(v___x_697_, v___x_698_);
v___y_688_ = v___x_699_;
goto v___jp_687_;
}
}
case 1:
{
lean_object* v_s_787_; lean_object* v_c_788_; lean_object* v_j_789_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; uint8_t v___y_847_; uint8_t v___x_910_; 
v_s_787_ = lean_ctor_get(v_x_680_, 0);
lean_inc_ref(v_s_787_);
v_c_788_ = lean_ctor_get(v_x_680_, 1);
lean_inc(v_c_788_);
v_j_789_ = lean_ctor_get(v_x_680_, 2);
lean_inc_ref(v_j_789_);
lean_dec_ref_known(v_x_680_, 3);
v___x_910_ = l_Lean_Omega_instBEqConstraint_beq(v_s_678_, v_s_787_);
if (v___x_910_ == 0)
{
v___y_847_ = v___x_910_;
goto v___jp_846_;
}
else
{
uint8_t v___x_911_; 
v___x_911_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_679_, v_c_788_);
v___y_847_ = v___x_911_;
goto v___jp_846_;
}
v___jp_790_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_793_ = lean_string_append(v___y_791_, v___y_792_);
lean_dec_ref(v___y_792_);
v___x_794_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__9));
v___x_795_ = lean_string_append(v___x_793_, v___x_794_);
v___x_796_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_787_, v_c_788_, v_j_789_);
v___x_797_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_796_);
v___x_798_ = lean_string_append(v___x_795_, v___x_797_);
lean_dec_ref(v___x_797_);
return v___x_798_;
}
v___jp_799_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
lean_inc_ref(v___y_800_);
v___x_803_ = lean_string_append(v___y_800_, v___y_802_);
lean_dec_ref(v___y_802_);
v___x_804_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_805_ = lean_string_append(v___x_803_, v___x_804_);
v___y_791_ = v___y_801_;
v___y_792_ = v___x_805_;
goto v___jp_790_;
}
v___jp_806_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_inc_ref(v___y_808_);
v___x_810_ = lean_string_append(v___y_808_, v___y_809_);
lean_dec_ref(v___y_809_);
v___x_811_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_812_ = lean_string_append(v___x_810_, v___x_811_);
v___y_791_ = v___y_807_;
v___y_792_ = v___x_812_;
goto v___jp_790_;
}
v___jp_813_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_string_append(v___y_814_, v___y_816_);
lean_dec_ref(v___y_816_);
v___x_818_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_819_ = lean_string_append(v___x_817_, v___x_818_);
v___y_791_ = v___y_815_;
v___y_792_ = v___x_819_;
goto v___jp_790_;
}
v___jp_820_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v_intZero_828_; uint8_t v_isNeg_829_; 
lean_inc_ref(v___y_821_);
v___x_825_ = lean_string_append(v___y_821_, v___y_824_);
lean_dec_ref(v___y_824_);
v___x_826_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_827_ = lean_string_append(v___x_825_, v___x_826_);
v_intZero_828_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_829_ = lean_int_dec_lt(v___y_822_, v_intZero_828_);
if (v_isNeg_829_ == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; 
v_a_830_ = lean_nat_abs(v___y_822_);
lean_dec(v___y_822_);
v___x_831_ = l_Nat_reprFast(v_a_830_);
v___y_814_ = v___x_827_;
v___y_815_ = v___y_823_;
v___y_816_ = v___x_831_;
goto v___jp_813_;
}
else
{
lean_object* v_abs_832_; lean_object* v_one_833_; lean_object* v_a_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_abs_832_ = lean_nat_abs(v___y_822_);
lean_dec(v___y_822_);
v_one_833_ = lean_unsigned_to_nat(1u);
v_a_834_ = lean_nat_sub(v_abs_832_, v_one_833_);
lean_dec(v_abs_832_);
v___x_835_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_836_ = lean_nat_add(v_a_834_, v_one_833_);
lean_dec(v_a_834_);
v___x_837_ = l_Nat_reprFast(v___x_836_);
v___x_838_ = lean_string_append(v___x_835_, v___x_837_);
lean_dec_ref(v___x_837_);
v___y_814_ = v___x_827_;
v___y_815_ = v___y_823_;
v___y_816_ = v___x_838_;
goto v___jp_813_;
}
}
v___jp_839_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_inc_ref(v___y_840_);
v___x_843_ = lean_string_append(v___y_840_, v___y_842_);
lean_dec_ref(v___y_842_);
v___x_844_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_845_ = lean_string_append(v___x_843_, v___x_844_);
v___y_791_ = v___y_841_;
v___y_792_ = v___x_845_;
goto v___jp_790_;
}
v___jp_846_:
{
if (v___y_847_ == 0)
{
lean_object* v_lowerBound_848_; lean_object* v_upperBound_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_lowerBound_848_ = lean_ctor_get(v_s_678_, 0);
lean_inc(v_lowerBound_848_);
v_upperBound_849_ = lean_ctor_get(v_s_678_, 1);
lean_inc(v_upperBound_849_);
lean_dec_ref(v_s_678_);
v___x_850_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_679_);
lean_dec(v_x_679_);
v___x_851_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_852_ = lean_string_append(v___x_850_, v___x_851_);
if (lean_obj_tag(v_lowerBound_848_) == 0)
{
if (lean_obj_tag(v_upperBound_849_) == 0)
{
lean_object* v___x_853_; 
v___x_853_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_791_ = v___x_852_;
v___y_792_ = v___x_853_;
goto v___jp_790_;
}
else
{
lean_object* v_val_854_; lean_object* v___x_855_; lean_object* v_intZero_856_; uint8_t v_isNeg_857_; 
v_val_854_ = lean_ctor_get(v_upperBound_849_, 0);
lean_inc(v_val_854_);
lean_dec_ref_known(v_upperBound_849_, 1);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_856_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_857_ = lean_int_dec_lt(v_val_854_, v_intZero_856_);
if (v_isNeg_857_ == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; 
v_a_858_ = lean_nat_abs(v_val_854_);
lean_dec(v_val_854_);
v___x_859_ = l_Nat_reprFast(v_a_858_);
v___y_800_ = v___x_855_;
v___y_801_ = v___x_852_;
v___y_802_ = v___x_859_;
goto v___jp_799_;
}
else
{
lean_object* v_abs_860_; lean_object* v_one_861_; lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_abs_860_ = lean_nat_abs(v_val_854_);
lean_dec(v_val_854_);
v_one_861_ = lean_unsigned_to_nat(1u);
v_a_862_ = lean_nat_sub(v_abs_860_, v_one_861_);
lean_dec(v_abs_860_);
v___x_863_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_864_ = lean_nat_add(v_a_862_, v_one_861_);
lean_dec(v_a_862_);
v___x_865_ = l_Nat_reprFast(v___x_864_);
v___x_866_ = lean_string_append(v___x_863_, v___x_865_);
lean_dec_ref(v___x_865_);
v___y_800_ = v___x_855_;
v___y_801_ = v___x_852_;
v___y_802_ = v___x_866_;
goto v___jp_799_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_849_) == 0)
{
lean_object* v_val_867_; lean_object* v___x_868_; lean_object* v_intZero_869_; uint8_t v_isNeg_870_; 
v_val_867_ = lean_ctor_get(v_lowerBound_848_, 0);
lean_inc(v_val_867_);
lean_dec_ref_known(v_lowerBound_848_, 1);
v___x_868_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_869_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_870_ = lean_int_dec_lt(v_val_867_, v_intZero_869_);
if (v_isNeg_870_ == 0)
{
lean_object* v_a_871_; lean_object* v___x_872_; 
v_a_871_ = lean_nat_abs(v_val_867_);
lean_dec(v_val_867_);
v___x_872_ = l_Nat_reprFast(v_a_871_);
v___y_807_ = v___x_852_;
v___y_808_ = v___x_868_;
v___y_809_ = v___x_872_;
goto v___jp_806_;
}
else
{
lean_object* v_abs_873_; lean_object* v_one_874_; lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_abs_873_ = lean_nat_abs(v_val_867_);
lean_dec(v_val_867_);
v_one_874_ = lean_unsigned_to_nat(1u);
v_a_875_ = lean_nat_sub(v_abs_873_, v_one_874_);
lean_dec(v_abs_873_);
v___x_876_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_877_ = lean_nat_add(v_a_875_, v_one_874_);
lean_dec(v_a_875_);
v___x_878_ = l_Nat_reprFast(v___x_877_);
v___x_879_ = lean_string_append(v___x_876_, v___x_878_);
lean_dec_ref(v___x_878_);
v___y_807_ = v___x_852_;
v___y_808_ = v___x_868_;
v___y_809_ = v___x_879_;
goto v___jp_806_;
}
}
else
{
lean_object* v_val_880_; lean_object* v_val_881_; uint8_t v___x_882_; 
v_val_880_ = lean_ctor_get(v_lowerBound_848_, 0);
lean_inc(v_val_880_);
lean_dec_ref_known(v_lowerBound_848_, 1);
v_val_881_ = lean_ctor_get(v_upperBound_849_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v_upperBound_849_, 1);
v___x_882_ = lean_int_dec_lt(v_val_881_, v_val_880_);
if (v___x_882_ == 0)
{
uint8_t v___x_883_; 
v___x_883_ = lean_int_dec_eq(v_val_880_, v_val_881_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v_intZero_885_; uint8_t v_isNeg_886_; 
v___x_884_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_885_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_886_ = lean_int_dec_lt(v_val_880_, v_intZero_885_);
if (v_isNeg_886_ == 0)
{
lean_object* v_a_887_; lean_object* v___x_888_; 
v_a_887_ = lean_nat_abs(v_val_880_);
lean_dec(v_val_880_);
v___x_888_ = l_Nat_reprFast(v_a_887_);
v___y_821_ = v___x_884_;
v___y_822_ = v_val_881_;
v___y_823_ = v___x_852_;
v___y_824_ = v___x_888_;
goto v___jp_820_;
}
else
{
lean_object* v_abs_889_; lean_object* v_one_890_; lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_abs_889_ = lean_nat_abs(v_val_880_);
lean_dec(v_val_880_);
v_one_890_ = lean_unsigned_to_nat(1u);
v_a_891_ = lean_nat_sub(v_abs_889_, v_one_890_);
lean_dec(v_abs_889_);
v___x_892_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_893_ = lean_nat_add(v_a_891_, v_one_890_);
lean_dec(v_a_891_);
v___x_894_ = l_Nat_reprFast(v___x_893_);
v___x_895_ = lean_string_append(v___x_892_, v___x_894_);
lean_dec_ref(v___x_894_);
v___y_821_ = v___x_884_;
v___y_822_ = v_val_881_;
v___y_823_ = v___x_852_;
v___y_824_ = v___x_895_;
goto v___jp_820_;
}
}
else
{
lean_object* v___x_896_; lean_object* v_intZero_897_; uint8_t v_isNeg_898_; 
lean_dec(v_val_881_);
v___x_896_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_897_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_898_ = lean_int_dec_lt(v_val_880_, v_intZero_897_);
if (v_isNeg_898_ == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; 
v_a_899_ = lean_nat_abs(v_val_880_);
lean_dec(v_val_880_);
v___x_900_ = l_Nat_reprFast(v_a_899_);
v___y_840_ = v___x_896_;
v___y_841_ = v___x_852_;
v___y_842_ = v___x_900_;
goto v___jp_839_;
}
else
{
lean_object* v_abs_901_; lean_object* v_one_902_; lean_object* v_a_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_abs_901_ = lean_nat_abs(v_val_880_);
lean_dec(v_val_880_);
v_one_902_ = lean_unsigned_to_nat(1u);
v_a_903_ = lean_nat_sub(v_abs_901_, v_one_902_);
lean_dec(v_abs_901_);
v___x_904_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_905_ = lean_nat_add(v_a_903_, v_one_902_);
lean_dec(v_a_903_);
v___x_906_ = l_Nat_reprFast(v___x_905_);
v___x_907_ = lean_string_append(v___x_904_, v___x_906_);
lean_dec_ref(v___x_906_);
v___y_840_ = v___x_896_;
v___y_841_ = v___x_852_;
v___y_842_ = v___x_907_;
goto v___jp_839_;
}
}
}
else
{
lean_object* v___x_908_; 
lean_dec(v_val_881_);
lean_dec(v_val_880_);
v___x_908_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_791_ = v___x_852_;
v___y_792_ = v___x_908_;
goto v___jp_790_;
}
}
}
}
else
{
lean_dec(v_x_679_);
lean_dec_ref(v_s_678_);
v_s_678_ = v_s_787_;
v_x_679_ = v_c_788_;
v_x_680_ = v_j_789_;
goto _start;
}
}
}
case 2:
{
lean_object* v_s_912_; lean_object* v_t_913_; lean_object* v_j_914_; lean_object* v_k_915_; lean_object* v_lowerBound_916_; lean_object* v_upperBound_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___y_922_; lean_object* v___y_935_; lean_object* v___y_936_; 
v_s_912_ = lean_ctor_get(v_x_680_, 0);
lean_inc_ref(v_s_912_);
v_t_913_ = lean_ctor_get(v_x_680_, 1);
lean_inc_ref(v_t_913_);
v_j_914_ = lean_ctor_get(v_x_680_, 3);
lean_inc_ref(v_j_914_);
v_k_915_ = lean_ctor_get(v_x_680_, 4);
lean_inc_ref(v_k_915_);
lean_dec_ref_known(v_x_680_, 5);
v_lowerBound_916_ = lean_ctor_get(v_s_678_, 0);
lean_inc(v_lowerBound_916_);
v_upperBound_917_ = lean_ctor_get(v_s_678_, 1);
lean_inc(v_upperBound_917_);
lean_dec_ref(v_s_678_);
v___x_918_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_679_);
v___x_919_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_920_ = lean_string_append(v___x_918_, v___x_919_);
if (lean_obj_tag(v_lowerBound_916_) == 0)
{
if (lean_obj_tag(v_upperBound_917_) == 0)
{
lean_object* v___x_940_; 
v___x_940_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_922_ = v___x_940_;
goto v___jp_921_;
}
else
{
lean_object* v_val_941_; lean_object* v___x_942_; lean_object* v___y_944_; lean_object* v_intZero_948_; uint8_t v_isNeg_949_; 
v_val_941_ = lean_ctor_get(v_upperBound_917_, 0);
lean_inc(v_val_941_);
lean_dec_ref_known(v_upperBound_917_, 1);
v___x_942_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_948_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_949_ = lean_int_dec_lt(v_val_941_, v_intZero_948_);
if (v_isNeg_949_ == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; 
v_a_950_ = lean_nat_abs(v_val_941_);
lean_dec(v_val_941_);
v___x_951_ = l_Nat_reprFast(v_a_950_);
v___y_944_ = v___x_951_;
goto v___jp_943_;
}
else
{
lean_object* v_abs_952_; lean_object* v_one_953_; lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_abs_952_ = lean_nat_abs(v_val_941_);
lean_dec(v_val_941_);
v_one_953_ = lean_unsigned_to_nat(1u);
v_a_954_ = lean_nat_sub(v_abs_952_, v_one_953_);
lean_dec(v_abs_952_);
v___x_955_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_956_ = lean_nat_add(v_a_954_, v_one_953_);
lean_dec(v_a_954_);
v___x_957_ = l_Nat_reprFast(v___x_956_);
v___x_958_ = lean_string_append(v___x_955_, v___x_957_);
lean_dec_ref(v___x_957_);
v___y_944_ = v___x_958_;
goto v___jp_943_;
}
v___jp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = lean_string_append(v___x_942_, v___y_944_);
lean_dec_ref(v___y_944_);
v___x_946_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_947_ = lean_string_append(v___x_945_, v___x_946_);
v___y_922_ = v___x_947_;
goto v___jp_921_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_917_) == 0)
{
lean_object* v_val_959_; lean_object* v___x_960_; lean_object* v___y_962_; lean_object* v_intZero_966_; uint8_t v_isNeg_967_; 
v_val_959_ = lean_ctor_get(v_lowerBound_916_, 0);
lean_inc(v_val_959_);
lean_dec_ref_known(v_lowerBound_916_, 1);
v___x_960_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_966_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_967_ = lean_int_dec_lt(v_val_959_, v_intZero_966_);
if (v_isNeg_967_ == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; 
v_a_968_ = lean_nat_abs(v_val_959_);
lean_dec(v_val_959_);
v___x_969_ = l_Nat_reprFast(v_a_968_);
v___y_962_ = v___x_969_;
goto v___jp_961_;
}
else
{
lean_object* v_abs_970_; lean_object* v_one_971_; lean_object* v_a_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_abs_970_ = lean_nat_abs(v_val_959_);
lean_dec(v_val_959_);
v_one_971_ = lean_unsigned_to_nat(1u);
v_a_972_ = lean_nat_sub(v_abs_970_, v_one_971_);
lean_dec(v_abs_970_);
v___x_973_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_974_ = lean_nat_add(v_a_972_, v_one_971_);
lean_dec(v_a_972_);
v___x_975_ = l_Nat_reprFast(v___x_974_);
v___x_976_ = lean_string_append(v___x_973_, v___x_975_);
lean_dec_ref(v___x_975_);
v___y_962_ = v___x_976_;
goto v___jp_961_;
}
v___jp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_963_ = lean_string_append(v___x_960_, v___y_962_);
lean_dec_ref(v___y_962_);
v___x_964_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_965_ = lean_string_append(v___x_963_, v___x_964_);
v___y_922_ = v___x_965_;
goto v___jp_921_;
}
}
else
{
lean_object* v_val_977_; lean_object* v_val_978_; uint8_t v___x_979_; 
v_val_977_ = lean_ctor_get(v_lowerBound_916_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_lowerBound_916_, 1);
v_val_978_ = lean_ctor_get(v_upperBound_917_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v_upperBound_917_, 1);
v___x_979_ = lean_int_dec_lt(v_val_978_, v_val_977_);
if (v___x_979_ == 0)
{
uint8_t v___x_980_; 
v___x_980_ = lean_int_dec_eq(v_val_977_, v_val_978_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___y_983_; lean_object* v_intZero_998_; uint8_t v_isNeg_999_; 
v___x_981_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_998_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_999_ = lean_int_dec_lt(v_val_977_, v_intZero_998_);
if (v_isNeg_999_ == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; 
v_a_1000_ = lean_nat_abs(v_val_977_);
lean_dec(v_val_977_);
v___x_1001_ = l_Nat_reprFast(v_a_1000_);
v___y_983_ = v___x_1001_;
goto v___jp_982_;
}
else
{
lean_object* v_abs_1002_; lean_object* v_one_1003_; lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_abs_1002_ = lean_nat_abs(v_val_977_);
lean_dec(v_val_977_);
v_one_1003_ = lean_unsigned_to_nat(1u);
v_a_1004_ = lean_nat_sub(v_abs_1002_, v_one_1003_);
lean_dec(v_abs_1002_);
v___x_1005_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1006_ = lean_nat_add(v_a_1004_, v_one_1003_);
lean_dec(v_a_1004_);
v___x_1007_ = l_Nat_reprFast(v___x_1006_);
v___x_1008_ = lean_string_append(v___x_1005_, v___x_1007_);
lean_dec_ref(v___x_1007_);
v___y_983_ = v___x_1008_;
goto v___jp_982_;
}
v___jp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_intZero_987_; uint8_t v_isNeg_988_; 
v___x_984_ = lean_string_append(v___x_981_, v___y_983_);
lean_dec_ref(v___y_983_);
v___x_985_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_986_ = lean_string_append(v___x_984_, v___x_985_);
v_intZero_987_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_988_ = lean_int_dec_lt(v_val_978_, v_intZero_987_);
if (v_isNeg_988_ == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; 
v_a_989_ = lean_nat_abs(v_val_978_);
lean_dec(v_val_978_);
v___x_990_ = l_Nat_reprFast(v_a_989_);
v___y_935_ = v___x_986_;
v___y_936_ = v___x_990_;
goto v___jp_934_;
}
else
{
lean_object* v_abs_991_; lean_object* v_one_992_; lean_object* v_a_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_abs_991_ = lean_nat_abs(v_val_978_);
lean_dec(v_val_978_);
v_one_992_ = lean_unsigned_to_nat(1u);
v_a_993_ = lean_nat_sub(v_abs_991_, v_one_992_);
lean_dec(v_abs_991_);
v___x_994_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_995_ = lean_nat_add(v_a_993_, v_one_992_);
lean_dec(v_a_993_);
v___x_996_ = l_Nat_reprFast(v___x_995_);
v___x_997_ = lean_string_append(v___x_994_, v___x_996_);
lean_dec_ref(v___x_996_);
v___y_935_ = v___x_986_;
v___y_936_ = v___x_997_;
goto v___jp_934_;
}
}
}
else
{
lean_object* v___x_1009_; lean_object* v___y_1011_; lean_object* v_intZero_1015_; uint8_t v_isNeg_1016_; 
lean_dec(v_val_978_);
v___x_1009_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1015_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1016_ = lean_int_dec_lt(v_val_977_, v_intZero_1015_);
if (v_isNeg_1016_ == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_nat_abs(v_val_977_);
lean_dec(v_val_977_);
v___x_1018_ = l_Nat_reprFast(v_a_1017_);
v___y_1011_ = v___x_1018_;
goto v___jp_1010_;
}
else
{
lean_object* v_abs_1019_; lean_object* v_one_1020_; lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_abs_1019_ = lean_nat_abs(v_val_977_);
lean_dec(v_val_977_);
v_one_1020_ = lean_unsigned_to_nat(1u);
v_a_1021_ = lean_nat_sub(v_abs_1019_, v_one_1020_);
lean_dec(v_abs_1019_);
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1023_ = lean_nat_add(v_a_1021_, v_one_1020_);
lean_dec(v_a_1021_);
v___x_1024_ = l_Nat_reprFast(v___x_1023_);
v___x_1025_ = lean_string_append(v___x_1022_, v___x_1024_);
lean_dec_ref(v___x_1024_);
v___y_1011_ = v___x_1025_;
goto v___jp_1010_;
}
v___jp_1010_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_string_append(v___x_1009_, v___y_1011_);
lean_dec_ref(v___y_1011_);
v___x_1013_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1014_ = lean_string_append(v___x_1012_, v___x_1013_);
v___y_922_ = v___x_1014_;
goto v___jp_921_;
}
}
}
else
{
lean_object* v___x_1026_; 
lean_dec(v_val_978_);
lean_dec(v_val_977_);
v___x_1026_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_922_ = v___x_1026_;
goto v___jp_921_;
}
}
}
v___jp_921_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_923_ = lean_string_append(v___x_920_, v___y_922_);
lean_dec_ref(v___y_922_);
v___x_924_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__10));
v___x_925_ = lean_string_append(v___x_923_, v___x_924_);
lean_inc(v_x_679_);
v___x_926_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_912_, v_x_679_, v_j_914_);
v___x_927_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_926_);
v___x_928_ = lean_string_append(v___x_925_, v___x_927_);
lean_dec_ref(v___x_927_);
v___x_929_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_930_ = lean_string_append(v___x_928_, v___x_929_);
v___x_931_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_913_, v_x_679_, v_k_915_);
v___x_932_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_931_);
v___x_933_ = lean_string_append(v___x_930_, v___x_932_);
lean_dec_ref(v___x_932_);
return v___x_933_;
}
v___jp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_string_append(v___y_935_, v___y_936_);
lean_dec_ref(v___y_936_);
v___x_938_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_939_ = lean_string_append(v___x_937_, v___x_938_);
v___y_922_ = v___x_939_;
goto v___jp_921_;
}
}
case 3:
{
lean_object* v_s_1027_; lean_object* v_t_1028_; lean_object* v_x_1029_; lean_object* v_y_1030_; lean_object* v_a_1031_; lean_object* v_j_1032_; lean_object* v_b_1033_; lean_object* v_k_1034_; lean_object* v_lowerBound_1035_; lean_object* v_upperBound_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___y_1041_; lean_object* v___y_1062_; lean_object* v___y_1063_; 
v_s_1027_ = lean_ctor_get(v_x_680_, 0);
lean_inc_ref(v_s_1027_);
v_t_1028_ = lean_ctor_get(v_x_680_, 1);
lean_inc_ref(v_t_1028_);
v_x_1029_ = lean_ctor_get(v_x_680_, 2);
lean_inc(v_x_1029_);
v_y_1030_ = lean_ctor_get(v_x_680_, 3);
lean_inc(v_y_1030_);
v_a_1031_ = lean_ctor_get(v_x_680_, 4);
lean_inc(v_a_1031_);
v_j_1032_ = lean_ctor_get(v_x_680_, 5);
lean_inc_ref(v_j_1032_);
v_b_1033_ = lean_ctor_get(v_x_680_, 6);
lean_inc(v_b_1033_);
v_k_1034_ = lean_ctor_get(v_x_680_, 7);
lean_inc_ref(v_k_1034_);
lean_dec_ref_known(v_x_680_, 8);
v_lowerBound_1035_ = lean_ctor_get(v_s_678_, 0);
lean_inc(v_lowerBound_1035_);
v_upperBound_1036_ = lean_ctor_get(v_s_678_, 1);
lean_inc(v_upperBound_1036_);
lean_dec_ref(v_s_678_);
v___x_1037_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_679_);
lean_dec(v_x_679_);
v___x_1038_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1039_ = lean_string_append(v___x_1037_, v___x_1038_);
if (lean_obj_tag(v_lowerBound_1035_) == 0)
{
if (lean_obj_tag(v_upperBound_1036_) == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1041_ = v___x_1067_;
goto v___jp_1040_;
}
else
{
lean_object* v_val_1068_; lean_object* v___x_1069_; lean_object* v___y_1071_; lean_object* v_intZero_1075_; uint8_t v_isNeg_1076_; 
v_val_1068_ = lean_ctor_get(v_upperBound_1036_, 0);
lean_inc(v_val_1068_);
lean_dec_ref_known(v_upperBound_1036_, 1);
v___x_1069_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1075_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1076_ = lean_int_dec_lt(v_val_1068_, v_intZero_1075_);
if (v_isNeg_1076_ == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1078_; 
v_a_1077_ = lean_nat_abs(v_val_1068_);
lean_dec(v_val_1068_);
v___x_1078_ = l_Nat_reprFast(v_a_1077_);
v___y_1071_ = v___x_1078_;
goto v___jp_1070_;
}
else
{
lean_object* v_abs_1079_; lean_object* v_one_1080_; lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_abs_1079_ = lean_nat_abs(v_val_1068_);
lean_dec(v_val_1068_);
v_one_1080_ = lean_unsigned_to_nat(1u);
v_a_1081_ = lean_nat_sub(v_abs_1079_, v_one_1080_);
lean_dec(v_abs_1079_);
v___x_1082_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1083_ = lean_nat_add(v_a_1081_, v_one_1080_);
lean_dec(v_a_1081_);
v___x_1084_ = l_Nat_reprFast(v___x_1083_);
v___x_1085_ = lean_string_append(v___x_1082_, v___x_1084_);
lean_dec_ref(v___x_1084_);
v___y_1071_ = v___x_1085_;
goto v___jp_1070_;
}
v___jp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = lean_string_append(v___x_1069_, v___y_1071_);
lean_dec_ref(v___y_1071_);
v___x_1073_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1074_ = lean_string_append(v___x_1072_, v___x_1073_);
v___y_1041_ = v___x_1074_;
goto v___jp_1040_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1036_) == 0)
{
lean_object* v_val_1086_; lean_object* v___x_1087_; lean_object* v___y_1089_; lean_object* v_intZero_1093_; uint8_t v_isNeg_1094_; 
v_val_1086_ = lean_ctor_get(v_lowerBound_1035_, 0);
lean_inc(v_val_1086_);
lean_dec_ref_known(v_lowerBound_1035_, 1);
v___x_1087_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1093_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1094_ = lean_int_dec_lt(v_val_1086_, v_intZero_1093_);
if (v_isNeg_1094_ == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1096_; 
v_a_1095_ = lean_nat_abs(v_val_1086_);
lean_dec(v_val_1086_);
v___x_1096_ = l_Nat_reprFast(v_a_1095_);
v___y_1089_ = v___x_1096_;
goto v___jp_1088_;
}
else
{
lean_object* v_abs_1097_; lean_object* v_one_1098_; lean_object* v_a_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_abs_1097_ = lean_nat_abs(v_val_1086_);
lean_dec(v_val_1086_);
v_one_1098_ = lean_unsigned_to_nat(1u);
v_a_1099_ = lean_nat_sub(v_abs_1097_, v_one_1098_);
lean_dec(v_abs_1097_);
v___x_1100_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1101_ = lean_nat_add(v_a_1099_, v_one_1098_);
lean_dec(v_a_1099_);
v___x_1102_ = l_Nat_reprFast(v___x_1101_);
v___x_1103_ = lean_string_append(v___x_1100_, v___x_1102_);
lean_dec_ref(v___x_1102_);
v___y_1089_ = v___x_1103_;
goto v___jp_1088_;
}
v___jp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1090_ = lean_string_append(v___x_1087_, v___y_1089_);
lean_dec_ref(v___y_1089_);
v___x_1091_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1092_ = lean_string_append(v___x_1090_, v___x_1091_);
v___y_1041_ = v___x_1092_;
goto v___jp_1040_;
}
}
else
{
lean_object* v_val_1104_; lean_object* v_val_1105_; uint8_t v___x_1106_; 
v_val_1104_ = lean_ctor_get(v_lowerBound_1035_, 0);
lean_inc(v_val_1104_);
lean_dec_ref_known(v_lowerBound_1035_, 1);
v_val_1105_ = lean_ctor_get(v_upperBound_1036_, 0);
lean_inc(v_val_1105_);
lean_dec_ref_known(v_upperBound_1036_, 1);
v___x_1106_ = lean_int_dec_lt(v_val_1105_, v_val_1104_);
if (v___x_1106_ == 0)
{
uint8_t v___x_1107_; 
v___x_1107_ = lean_int_dec_eq(v_val_1104_, v_val_1105_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___y_1110_; lean_object* v_intZero_1125_; uint8_t v_isNeg_1126_; 
v___x_1108_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1125_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1126_ = lean_int_dec_lt(v_val_1104_, v_intZero_1125_);
if (v_isNeg_1126_ == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1128_; 
v_a_1127_ = lean_nat_abs(v_val_1104_);
lean_dec(v_val_1104_);
v___x_1128_ = l_Nat_reprFast(v_a_1127_);
v___y_1110_ = v___x_1128_;
goto v___jp_1109_;
}
else
{
lean_object* v_abs_1129_; lean_object* v_one_1130_; lean_object* v_a_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_abs_1129_ = lean_nat_abs(v_val_1104_);
lean_dec(v_val_1104_);
v_one_1130_ = lean_unsigned_to_nat(1u);
v_a_1131_ = lean_nat_sub(v_abs_1129_, v_one_1130_);
lean_dec(v_abs_1129_);
v___x_1132_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1133_ = lean_nat_add(v_a_1131_, v_one_1130_);
lean_dec(v_a_1131_);
v___x_1134_ = l_Nat_reprFast(v___x_1133_);
v___x_1135_ = lean_string_append(v___x_1132_, v___x_1134_);
lean_dec_ref(v___x_1134_);
v___y_1110_ = v___x_1135_;
goto v___jp_1109_;
}
v___jp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v_intZero_1114_; uint8_t v_isNeg_1115_; 
v___x_1111_ = lean_string_append(v___x_1108_, v___y_1110_);
lean_dec_ref(v___y_1110_);
v___x_1112_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1113_ = lean_string_append(v___x_1111_, v___x_1112_);
v_intZero_1114_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1115_ = lean_int_dec_lt(v_val_1105_, v_intZero_1114_);
if (v_isNeg_1115_ == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
v_a_1116_ = lean_nat_abs(v_val_1105_);
lean_dec(v_val_1105_);
v___x_1117_ = l_Nat_reprFast(v_a_1116_);
v___y_1062_ = v___x_1113_;
v___y_1063_ = v___x_1117_;
goto v___jp_1061_;
}
else
{
lean_object* v_abs_1118_; lean_object* v_one_1119_; lean_object* v_a_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_abs_1118_ = lean_nat_abs(v_val_1105_);
lean_dec(v_val_1105_);
v_one_1119_ = lean_unsigned_to_nat(1u);
v_a_1120_ = lean_nat_sub(v_abs_1118_, v_one_1119_);
lean_dec(v_abs_1118_);
v___x_1121_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1122_ = lean_nat_add(v_a_1120_, v_one_1119_);
lean_dec(v_a_1120_);
v___x_1123_ = l_Nat_reprFast(v___x_1122_);
v___x_1124_ = lean_string_append(v___x_1121_, v___x_1123_);
lean_dec_ref(v___x_1123_);
v___y_1062_ = v___x_1113_;
v___y_1063_ = v___x_1124_;
goto v___jp_1061_;
}
}
}
else
{
lean_object* v___x_1136_; lean_object* v___y_1138_; lean_object* v_intZero_1142_; uint8_t v_isNeg_1143_; 
lean_dec(v_val_1105_);
v___x_1136_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1142_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1143_ = lean_int_dec_lt(v_val_1104_, v_intZero_1142_);
if (v_isNeg_1143_ == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1145_; 
v_a_1144_ = lean_nat_abs(v_val_1104_);
lean_dec(v_val_1104_);
v___x_1145_ = l_Nat_reprFast(v_a_1144_);
v___y_1138_ = v___x_1145_;
goto v___jp_1137_;
}
else
{
lean_object* v_abs_1146_; lean_object* v_one_1147_; lean_object* v_a_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_abs_1146_ = lean_nat_abs(v_val_1104_);
lean_dec(v_val_1104_);
v_one_1147_ = lean_unsigned_to_nat(1u);
v_a_1148_ = lean_nat_sub(v_abs_1146_, v_one_1147_);
lean_dec(v_abs_1146_);
v___x_1149_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1150_ = lean_nat_add(v_a_1148_, v_one_1147_);
lean_dec(v_a_1148_);
v___x_1151_ = l_Nat_reprFast(v___x_1150_);
v___x_1152_ = lean_string_append(v___x_1149_, v___x_1151_);
lean_dec_ref(v___x_1151_);
v___y_1138_ = v___x_1152_;
goto v___jp_1137_;
}
v___jp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = lean_string_append(v___x_1136_, v___y_1138_);
lean_dec_ref(v___y_1138_);
v___x_1140_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1141_ = lean_string_append(v___x_1139_, v___x_1140_);
v___y_1041_ = v___x_1141_;
goto v___jp_1040_;
}
}
}
else
{
lean_object* v___x_1153_; 
lean_dec(v_val_1105_);
lean_dec(v_val_1104_);
v___x_1153_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1041_ = v___x_1153_;
goto v___jp_1040_;
}
}
}
v___jp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1042_ = lean_string_append(v___x_1039_, v___y_1041_);
lean_dec_ref(v___y_1041_);
v___x_1043_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__11));
v___x_1044_ = lean_string_append(v___x_1042_, v___x_1043_);
v___x_1045_ = l_Int_repr(v_a_1031_);
lean_dec(v_a_1031_);
v___x_1046_ = lean_string_append(v___x_1044_, v___x_1045_);
lean_dec_ref(v___x_1045_);
v___x_1047_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__12));
v___x_1048_ = lean_string_append(v___x_1046_, v___x_1047_);
v___x_1049_ = l_Int_repr(v_b_1033_);
lean_dec(v_b_1033_);
v___x_1050_ = lean_string_append(v___x_1048_, v___x_1049_);
lean_dec_ref(v___x_1049_);
v___x_1051_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__13));
v___x_1052_ = lean_string_append(v___x_1050_, v___x_1051_);
v___x_1053_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_1027_, v_x_1029_, v_j_1032_);
v___x_1054_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1053_);
v___x_1055_ = lean_string_append(v___x_1052_, v___x_1054_);
lean_dec_ref(v___x_1054_);
v___x_1056_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_1057_ = lean_string_append(v___x_1055_, v___x_1056_);
v___x_1058_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_1028_, v_y_1030_, v_k_1034_);
v___x_1059_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1058_);
v___x_1060_ = lean_string_append(v___x_1057_, v___x_1059_);
lean_dec_ref(v___x_1059_);
return v___x_1060_;
}
v___jp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = lean_string_append(v___y_1062_, v___y_1063_);
lean_dec_ref(v___y_1063_);
v___x_1065_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1066_ = lean_string_append(v___x_1064_, v___x_1065_);
v___y_1041_ = v___x_1066_;
goto v___jp_1040_;
}
}
default: 
{
lean_object* v_m_1154_; lean_object* v_r_1155_; lean_object* v_i_1156_; lean_object* v_x_1157_; lean_object* v_j_1158_; lean_object* v_lowerBound_1159_; lean_object* v_upperBound_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___y_1165_; lean_object* v___y_1182_; lean_object* v___y_1183_; 
v_m_1154_ = lean_ctor_get(v_x_680_, 0);
lean_inc(v_m_1154_);
v_r_1155_ = lean_ctor_get(v_x_680_, 1);
lean_inc(v_r_1155_);
v_i_1156_ = lean_ctor_get(v_x_680_, 2);
lean_inc(v_i_1156_);
v_x_1157_ = lean_ctor_get(v_x_680_, 3);
lean_inc(v_x_1157_);
v_j_1158_ = lean_ctor_get(v_x_680_, 4);
lean_inc_ref(v_j_1158_);
lean_dec_ref_known(v_x_680_, 5);
v_lowerBound_1159_ = lean_ctor_get(v_s_678_, 0);
lean_inc(v_lowerBound_1159_);
v_upperBound_1160_ = lean_ctor_get(v_s_678_, 1);
lean_inc(v_upperBound_1160_);
lean_dec_ref(v_s_678_);
v___x_1161_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_679_);
lean_dec(v_x_679_);
v___x_1162_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1163_ = lean_string_append(v___x_1161_, v___x_1162_);
if (lean_obj_tag(v_lowerBound_1159_) == 0)
{
if (lean_obj_tag(v_upperBound_1160_) == 0)
{
lean_object* v___x_1187_; 
v___x_1187_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1165_ = v___x_1187_;
goto v___jp_1164_;
}
else
{
lean_object* v_val_1188_; lean_object* v___x_1189_; lean_object* v___y_1191_; lean_object* v_intZero_1195_; uint8_t v_isNeg_1196_; 
v_val_1188_ = lean_ctor_get(v_upperBound_1160_, 0);
lean_inc(v_val_1188_);
lean_dec_ref_known(v_upperBound_1160_, 1);
v___x_1189_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1195_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1196_ = lean_int_dec_lt(v_val_1188_, v_intZero_1195_);
if (v_isNeg_1196_ == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; 
v_a_1197_ = lean_nat_abs(v_val_1188_);
lean_dec(v_val_1188_);
v___x_1198_ = l_Nat_reprFast(v_a_1197_);
v___y_1191_ = v___x_1198_;
goto v___jp_1190_;
}
else
{
lean_object* v_abs_1199_; lean_object* v_one_1200_; lean_object* v_a_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_abs_1199_ = lean_nat_abs(v_val_1188_);
lean_dec(v_val_1188_);
v_one_1200_ = lean_unsigned_to_nat(1u);
v_a_1201_ = lean_nat_sub(v_abs_1199_, v_one_1200_);
lean_dec(v_abs_1199_);
v___x_1202_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1203_ = lean_nat_add(v_a_1201_, v_one_1200_);
lean_dec(v_a_1201_);
v___x_1204_ = l_Nat_reprFast(v___x_1203_);
v___x_1205_ = lean_string_append(v___x_1202_, v___x_1204_);
lean_dec_ref(v___x_1204_);
v___y_1191_ = v___x_1205_;
goto v___jp_1190_;
}
v___jp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = lean_string_append(v___x_1189_, v___y_1191_);
lean_dec_ref(v___y_1191_);
v___x_1193_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1194_ = lean_string_append(v___x_1192_, v___x_1193_);
v___y_1165_ = v___x_1194_;
goto v___jp_1164_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1160_) == 0)
{
lean_object* v_val_1206_; lean_object* v___x_1207_; lean_object* v___y_1209_; lean_object* v_intZero_1213_; uint8_t v_isNeg_1214_; 
v_val_1206_ = lean_ctor_get(v_lowerBound_1159_, 0);
lean_inc(v_val_1206_);
lean_dec_ref_known(v_lowerBound_1159_, 1);
v___x_1207_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1213_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1214_ = lean_int_dec_lt(v_val_1206_, v_intZero_1213_);
if (v_isNeg_1214_ == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1216_; 
v_a_1215_ = lean_nat_abs(v_val_1206_);
lean_dec(v_val_1206_);
v___x_1216_ = l_Nat_reprFast(v_a_1215_);
v___y_1209_ = v___x_1216_;
goto v___jp_1208_;
}
else
{
lean_object* v_abs_1217_; lean_object* v_one_1218_; lean_object* v_a_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_abs_1217_ = lean_nat_abs(v_val_1206_);
lean_dec(v_val_1206_);
v_one_1218_ = lean_unsigned_to_nat(1u);
v_a_1219_ = lean_nat_sub(v_abs_1217_, v_one_1218_);
lean_dec(v_abs_1217_);
v___x_1220_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1221_ = lean_nat_add(v_a_1219_, v_one_1218_);
lean_dec(v_a_1219_);
v___x_1222_ = l_Nat_reprFast(v___x_1221_);
v___x_1223_ = lean_string_append(v___x_1220_, v___x_1222_);
lean_dec_ref(v___x_1222_);
v___y_1209_ = v___x_1223_;
goto v___jp_1208_;
}
v___jp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = lean_string_append(v___x_1207_, v___y_1209_);
lean_dec_ref(v___y_1209_);
v___x_1211_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1212_ = lean_string_append(v___x_1210_, v___x_1211_);
v___y_1165_ = v___x_1212_;
goto v___jp_1164_;
}
}
else
{
lean_object* v_val_1224_; lean_object* v_val_1225_; uint8_t v___x_1226_; 
v_val_1224_ = lean_ctor_get(v_lowerBound_1159_, 0);
lean_inc(v_val_1224_);
lean_dec_ref_known(v_lowerBound_1159_, 1);
v_val_1225_ = lean_ctor_get(v_upperBound_1160_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v_upperBound_1160_, 1);
v___x_1226_ = lean_int_dec_lt(v_val_1225_, v_val_1224_);
if (v___x_1226_ == 0)
{
uint8_t v___x_1227_; 
v___x_1227_ = lean_int_dec_eq(v_val_1224_, v_val_1225_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; lean_object* v___y_1230_; lean_object* v_intZero_1245_; uint8_t v_isNeg_1246_; 
v___x_1228_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1245_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1246_ = lean_int_dec_lt(v_val_1224_, v_intZero_1245_);
if (v_isNeg_1246_ == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; 
v_a_1247_ = lean_nat_abs(v_val_1224_);
lean_dec(v_val_1224_);
v___x_1248_ = l_Nat_reprFast(v_a_1247_);
v___y_1230_ = v___x_1248_;
goto v___jp_1229_;
}
else
{
lean_object* v_abs_1249_; lean_object* v_one_1250_; lean_object* v_a_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_abs_1249_ = lean_nat_abs(v_val_1224_);
lean_dec(v_val_1224_);
v_one_1250_ = lean_unsigned_to_nat(1u);
v_a_1251_ = lean_nat_sub(v_abs_1249_, v_one_1250_);
lean_dec(v_abs_1249_);
v___x_1252_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1253_ = lean_nat_add(v_a_1251_, v_one_1250_);
lean_dec(v_a_1251_);
v___x_1254_ = l_Nat_reprFast(v___x_1253_);
v___x_1255_ = lean_string_append(v___x_1252_, v___x_1254_);
lean_dec_ref(v___x_1254_);
v___y_1230_ = v___x_1255_;
goto v___jp_1229_;
}
v___jp_1229_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_intZero_1234_; uint8_t v_isNeg_1235_; 
v___x_1231_ = lean_string_append(v___x_1228_, v___y_1230_);
lean_dec_ref(v___y_1230_);
v___x_1232_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1233_ = lean_string_append(v___x_1231_, v___x_1232_);
v_intZero_1234_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1235_ = lean_int_dec_lt(v_val_1225_, v_intZero_1234_);
if (v_isNeg_1235_ == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1237_; 
v_a_1236_ = lean_nat_abs(v_val_1225_);
lean_dec(v_val_1225_);
v___x_1237_ = l_Nat_reprFast(v_a_1236_);
v___y_1182_ = v___x_1233_;
v___y_1183_ = v___x_1237_;
goto v___jp_1181_;
}
else
{
lean_object* v_abs_1238_; lean_object* v_one_1239_; lean_object* v_a_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_abs_1238_ = lean_nat_abs(v_val_1225_);
lean_dec(v_val_1225_);
v_one_1239_ = lean_unsigned_to_nat(1u);
v_a_1240_ = lean_nat_sub(v_abs_1238_, v_one_1239_);
lean_dec(v_abs_1238_);
v___x_1241_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1242_ = lean_nat_add(v_a_1240_, v_one_1239_);
lean_dec(v_a_1240_);
v___x_1243_ = l_Nat_reprFast(v___x_1242_);
v___x_1244_ = lean_string_append(v___x_1241_, v___x_1243_);
lean_dec_ref(v___x_1243_);
v___y_1182_ = v___x_1233_;
v___y_1183_ = v___x_1244_;
goto v___jp_1181_;
}
}
}
else
{
lean_object* v___x_1256_; lean_object* v___y_1258_; lean_object* v_intZero_1262_; uint8_t v_isNeg_1263_; 
lean_dec(v_val_1225_);
v___x_1256_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1262_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1263_ = lean_int_dec_lt(v_val_1224_, v_intZero_1262_);
if (v_isNeg_1263_ == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; 
v_a_1264_ = lean_nat_abs(v_val_1224_);
lean_dec(v_val_1224_);
v___x_1265_ = l_Nat_reprFast(v_a_1264_);
v___y_1258_ = v___x_1265_;
goto v___jp_1257_;
}
else
{
lean_object* v_abs_1266_; lean_object* v_one_1267_; lean_object* v_a_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_abs_1266_ = lean_nat_abs(v_val_1224_);
lean_dec(v_val_1224_);
v_one_1267_ = lean_unsigned_to_nat(1u);
v_a_1268_ = lean_nat_sub(v_abs_1266_, v_one_1267_);
lean_dec(v_abs_1266_);
v___x_1269_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1270_ = lean_nat_add(v_a_1268_, v_one_1267_);
lean_dec(v_a_1268_);
v___x_1271_ = l_Nat_reprFast(v___x_1270_);
v___x_1272_ = lean_string_append(v___x_1269_, v___x_1271_);
lean_dec_ref(v___x_1271_);
v___y_1258_ = v___x_1272_;
goto v___jp_1257_;
}
v___jp_1257_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_string_append(v___x_1256_, v___y_1258_);
lean_dec_ref(v___y_1258_);
v___x_1260_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1261_ = lean_string_append(v___x_1259_, v___x_1260_);
v___y_1165_ = v___x_1261_;
goto v___jp_1164_;
}
}
}
else
{
lean_object* v___x_1273_; 
lean_dec(v_val_1225_);
lean_dec(v_val_1224_);
v___x_1273_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1165_ = v___x_1273_;
goto v___jp_1164_;
}
}
}
v___jp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1166_ = lean_string_append(v___x_1163_, v___y_1165_);
lean_dec_ref(v___y_1165_);
v___x_1167_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__14));
v___x_1168_ = lean_string_append(v___x_1166_, v___x_1167_);
v___x_1169_ = l_Nat_reprFast(v_m_1154_);
v___x_1170_ = lean_string_append(v___x_1168_, v___x_1169_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__15));
v___x_1172_ = lean_string_append(v___x_1170_, v___x_1171_);
v___x_1173_ = l_Nat_reprFast(v_i_1156_);
v___x_1174_ = lean_string_append(v___x_1172_, v___x_1173_);
lean_dec_ref(v___x_1173_);
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__16));
v___x_1176_ = lean_string_append(v___x_1174_, v___x_1175_);
v___x_1177_ = l_Lean_Omega_Constraint_exact(v_r_1155_);
v___x_1178_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v___x_1177_, v_x_1157_, v_j_1158_);
v___x_1179_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1178_);
v___x_1180_ = lean_string_append(v___x_1176_, v___x_1179_);
lean_dec_ref(v___x_1179_);
return v___x_1180_;
}
v___jp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = lean_string_append(v___y_1182_, v___y_1183_);
lean_dec_ref(v___y_1183_);
v___x_1185_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1186_ = lean_string_append(v___x_1184_, v___x_1185_);
v___y_1165_ = v___x_1186_;
goto v___jp_1164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_instToString(lean_object* v_s_1274_, lean_object* v_x_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Justification_toString), 3, 2);
lean_closure_set(v___x_1276_, 0, v_s_1274_);
lean_closure_set(v___x_1276_, 1, v_x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(lean_object* v_nilFn_1277_, lean_object* v_consFn_1278_, lean_object* v_x_1279_){
_start:
{
if (lean_obj_tag(v_x_1279_) == 0)
{
lean_dec_ref(v_consFn_1278_);
lean_inc_ref(v_nilFn_1277_);
return v_nilFn_1277_;
}
else
{
lean_object* v_head_1280_; lean_object* v_tail_1281_; lean_object* v___y_1283_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v_head_1280_ = lean_ctor_get(v_x_1279_, 0);
v_tail_1281_ = lean_ctor_get(v_x_1279_, 1);
v___x_1286_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1287_ = lean_int_dec_le(v___x_1286_, v_head_1280_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1288_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1289_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1290_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1291_ = lean_int_neg(v_head_1280_);
v___x_1292_ = l_Int_toNat(v___x_1291_);
lean_dec(v___x_1291_);
v___x_1293_ = l_Lean_instToExprInt_mkNat(v___x_1292_);
v___x_1294_ = l_Lean_mkApp3(v___x_1288_, v___x_1289_, v___x_1290_, v___x_1293_);
v___y_1283_ = v___x_1294_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = l_Int_toNat(v_head_1280_);
v___x_1296_ = l_Lean_instToExprInt_mkNat(v___x_1295_);
v___y_1283_ = v___x_1296_;
goto v___jp_1282_;
}
v___jp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_inc_ref(v_consFn_1278_);
v___x_1284_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1277_, v_consFn_1278_, v_tail_1281_);
v___x_1285_ = l_Lean_mkAppB(v_consFn_1278_, v___y_1283_, v___x_1284_);
return v___x_1285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0___boxed(lean_object* v_nilFn_1297_, lean_object* v_consFn_1298_, lean_object* v_x_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1297_, v_consFn_1298_, v_x_1299_);
lean_dec(v_x_1299_);
lean_dec_ref(v_nilFn_1297_);
return v_res_1300_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1));
v___x_1308_ = l_Lean_Expr_const___override(v___x_1307_, v___x_1306_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof(lean_object* v_s_1309_, lean_object* v_x_1310_, lean_object* v_v_1311_, lean_object* v_prf_1312_){
_start:
{
lean_object* v___x_1313_; lean_object* v___y_1315_; lean_object* v_lowerBound_1320_; lean_object* v_upperBound_1321_; lean_object* v___x_1322_; lean_object* v_type_1323_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1331_; 
v___x_1313_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2);
v_lowerBound_1320_ = lean_ctor_get(v_s_1309_, 0);
v_upperBound_1321_ = lean_ctor_get(v_s_1309_, 1);
v___x_1322_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1323_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1320_) == 0)
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1331_ = v___x_1347_;
goto v___jp_1330_;
}
else
{
lean_object* v_val_1348_; lean_object* v___x_1349_; lean_object* v___y_1351_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v_val_1348_ = lean_ctor_get(v_lowerBound_1320_, 0);
v___x_1349_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1353_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1354_ = lean_int_dec_le(v___x_1353_, v_val_1348_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1355_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1356_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1357_ = lean_int_neg(v_val_1348_);
v___x_1358_ = l_Int_toNat(v___x_1357_);
lean_dec(v___x_1357_);
v___x_1359_ = l_Lean_instToExprInt_mkNat(v___x_1358_);
v___x_1360_ = l_Lean_mkApp3(v___x_1355_, v_type_1323_, v___x_1356_, v___x_1359_);
v___y_1351_ = v___x_1360_;
goto v___jp_1350_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = l_Int_toNat(v_val_1348_);
v___x_1362_ = l_Lean_instToExprInt_mkNat(v___x_1361_);
v___y_1351_ = v___x_1362_;
goto v___jp_1350_;
}
v___jp_1350_:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_mkAppB(v___x_1349_, v_type_1323_, v___y_1351_);
v___y_1331_ = v___x_1352_;
goto v___jp_1330_;
}
}
v___jp_1314_:
{
lean_object* v_nil_1316_; lean_object* v_cons_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v_nil_1316_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1317_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1318_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1316_, v_cons_1317_, v_x_1310_);
v___x_1319_ = l_Lean_mkApp4(v___x_1313_, v___y_1315_, v___x_1318_, v_v_1311_, v_prf_1312_);
return v___x_1319_;
}
v___jp_1324_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_inc_ref(v___y_1325_);
v___x_1328_ = l_Lean_mkAppB(v___y_1325_, v_type_1323_, v___y_1327_);
v___x_1329_ = l_Lean_Expr_app___override(v___y_1326_, v___x_1328_);
v___y_1315_ = v___x_1329_;
goto v___jp_1314_;
}
v___jp_1330_:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Expr_app___override(v___x_1322_, v___y_1331_);
if (lean_obj_tag(v_upperBound_1321_) == 0)
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1334_ = l_Lean_Expr_app___override(v___x_1332_, v___x_1333_);
v___y_1315_ = v___x_1334_;
goto v___jp_1314_;
}
else
{
lean_object* v_val_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v_val_1335_ = lean_ctor_get(v_upperBound_1321_, 0);
v___x_1336_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1337_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1338_ = lean_int_dec_le(v___x_1337_, v_val_1335_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1339_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1340_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1341_ = lean_int_neg(v_val_1335_);
v___x_1342_ = l_Int_toNat(v___x_1341_);
lean_dec(v___x_1341_);
v___x_1343_ = l_Lean_instToExprInt_mkNat(v___x_1342_);
v___x_1344_ = l_Lean_mkApp3(v___x_1339_, v_type_1323_, v___x_1340_, v___x_1343_);
v___y_1325_ = v___x_1336_;
v___y_1326_ = v___x_1332_;
v___y_1327_ = v___x_1344_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = l_Int_toNat(v_val_1335_);
v___x_1346_ = l_Lean_instToExprInt_mkNat(v___x_1345_);
v___y_1325_ = v___x_1336_;
v___y_1326_ = v___x_1332_;
v___y_1327_ = v___x_1346_;
goto v___jp_1324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___boxed(lean_object* v_s_1363_, lean_object* v_x_1364_, lean_object* v_v_1365_, lean_object* v_prf_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1363_, v_x_1364_, v_v_1365_, v_prf_1366_);
lean_dec(v_x_1364_);
lean_dec_ref(v_s_1363_);
return v_res_1367_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1));
v___x_1376_ = l_Lean_Expr_const___override(v___x_1375_, v___x_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof(lean_object* v_s_1377_, lean_object* v_t_1378_, lean_object* v_x_1379_, lean_object* v_v_1380_, lean_object* v_ps_1381_, lean_object* v_pt_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1434_; lean_object* v_lowerBound_1452_; lean_object* v_upperBound_1453_; lean_object* v___x_1454_; lean_object* v_type_1455_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1463_; 
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2);
v_lowerBound_1452_ = lean_ctor_get(v_s_1377_, 0);
v_upperBound_1453_ = lean_ctor_get(v_s_1377_, 1);
v___x_1454_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1455_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1452_) == 0)
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1463_ = v___x_1479_;
goto v___jp_1462_;
}
else
{
lean_object* v_val_1480_; lean_object* v___x_1481_; lean_object* v___y_1483_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v_val_1480_ = lean_ctor_get(v_lowerBound_1452_, 0);
v___x_1481_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1485_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1486_ = lean_int_dec_le(v___x_1485_, v_val_1480_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1487_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1488_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1489_ = lean_int_neg(v_val_1480_);
v___x_1490_ = l_Int_toNat(v___x_1489_);
lean_dec(v___x_1489_);
v___x_1491_ = l_Lean_instToExprInt_mkNat(v___x_1490_);
v___x_1492_ = l_Lean_mkApp3(v___x_1487_, v_type_1455_, v___x_1488_, v___x_1491_);
v___y_1483_ = v___x_1492_;
goto v___jp_1482_;
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = l_Int_toNat(v_val_1480_);
v___x_1494_ = l_Lean_instToExprInt_mkNat(v___x_1493_);
v___y_1483_ = v___x_1494_;
goto v___jp_1482_;
}
v___jp_1482_:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_mkAppB(v___x_1481_, v_type_1455_, v___y_1483_);
v___y_1463_ = v___x_1484_;
goto v___jp_1462_;
}
}
v___jp_1385_:
{
lean_object* v_nil_1388_; lean_object* v_cons_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_nil_1388_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1389_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1390_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1388_, v_cons_1389_, v_x_1379_);
v___x_1391_ = l_Lean_mkApp6(v___x_1384_, v___y_1386_, v___y_1387_, v___x_1390_, v_v_1380_, v_ps_1381_, v_pt_1382_);
return v___x_1391_;
}
v___jp_1392_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_inc_ref(v___y_1396_);
v___x_1398_ = l_Lean_mkAppB(v___y_1396_, v___y_1395_, v___y_1397_);
v___x_1399_ = l_Lean_Expr_app___override(v___y_1393_, v___x_1398_);
v___y_1386_ = v___y_1394_;
v___y_1387_ = v___x_1399_;
goto v___jp_1385_;
}
v___jp_1400_:
{
lean_object* v_upperBound_1406_; lean_object* v___x_1407_; 
v_upperBound_1406_ = lean_ctor_get(v_t_1378_, 1);
lean_inc_ref(v___y_1404_);
v___x_1407_ = l_Lean_Expr_app___override(v___y_1404_, v___y_1405_);
if (lean_obj_tag(v_upperBound_1406_) == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1409_ = l_Lean_Expr_app___override(v___x_1408_, v___y_1403_);
v___x_1410_ = l_Lean_Expr_app___override(v___x_1407_, v___x_1409_);
v___y_1386_ = v___y_1401_;
v___y_1387_ = v___x_1410_;
goto v___jp_1385_;
}
else
{
lean_object* v_val_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_val_1411_ = lean_ctor_get(v_upperBound_1406_, 0);
v___x_1412_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1413_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1414_ = lean_int_dec_le(v___x_1413_, v_val_1411_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1415_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1416_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1402_);
v___x_1417_ = l_Lean_Name_mkStr2(v___y_1402_, v___x_1416_);
v___x_1418_ = l_Lean_Expr_const___override(v___x_1417_, v___x_1383_);
v___x_1419_ = lean_int_neg(v_val_1411_);
v___x_1420_ = l_Int_toNat(v___x_1419_);
lean_dec(v___x_1419_);
v___x_1421_ = l_Lean_instToExprInt_mkNat(v___x_1420_);
lean_inc_ref(v___y_1403_);
v___x_1422_ = l_Lean_mkApp3(v___x_1415_, v___y_1403_, v___x_1418_, v___x_1421_);
v___y_1393_ = v___x_1407_;
v___y_1394_ = v___y_1401_;
v___y_1395_ = v___y_1403_;
v___y_1396_ = v___x_1412_;
v___y_1397_ = v___x_1422_;
goto v___jp_1392_;
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = l_Int_toNat(v_val_1411_);
v___x_1424_ = l_Lean_instToExprInt_mkNat(v___x_1423_);
v___y_1393_ = v___x_1407_;
v___y_1394_ = v___y_1401_;
v___y_1395_ = v___y_1403_;
v___y_1396_ = v___x_1412_;
v___y_1397_ = v___x_1424_;
goto v___jp_1392_;
}
}
}
v___jp_1425_:
{
lean_object* v___x_1432_; 
lean_inc_ref(v___y_1429_);
lean_inc_ref(v___y_1426_);
v___x_1432_ = l_Lean_mkAppB(v___y_1426_, v___y_1429_, v___y_1431_);
v___y_1401_ = v___y_1427_;
v___y_1402_ = v___y_1428_;
v___y_1403_ = v___y_1429_;
v___y_1404_ = v___y_1430_;
v___y_1405_ = v___x_1432_;
goto v___jp_1400_;
}
v___jp_1433_:
{
lean_object* v_lowerBound_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v_type_1438_; 
v_lowerBound_1435_ = lean_ctor_get(v_t_1378_, 0);
v___x_1436_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1437_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1438_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1435_) == 0)
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1401_ = v___y_1434_;
v___y_1402_ = v___x_1437_;
v___y_1403_ = v_type_1438_;
v___y_1404_ = v___x_1436_;
v___y_1405_ = v___x_1439_;
goto v___jp_1400_;
}
else
{
lean_object* v_val_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v_val_1440_ = lean_ctor_get(v_lowerBound_1435_, 0);
v___x_1441_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1442_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1443_ = lean_int_dec_le(v___x_1442_, v_val_1440_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1444_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1445_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1446_ = lean_int_neg(v_val_1440_);
v___x_1447_ = l_Int_toNat(v___x_1446_);
lean_dec(v___x_1446_);
v___x_1448_ = l_Lean_instToExprInt_mkNat(v___x_1447_);
v___x_1449_ = l_Lean_mkApp3(v___x_1444_, v_type_1438_, v___x_1445_, v___x_1448_);
v___y_1426_ = v___x_1441_;
v___y_1427_ = v___y_1434_;
v___y_1428_ = v___x_1437_;
v___y_1429_ = v_type_1438_;
v___y_1430_ = v___x_1436_;
v___y_1431_ = v___x_1449_;
goto v___jp_1425_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = l_Int_toNat(v_val_1440_);
v___x_1451_ = l_Lean_instToExprInt_mkNat(v___x_1450_);
v___y_1426_ = v___x_1441_;
v___y_1427_ = v___y_1434_;
v___y_1428_ = v___x_1437_;
v___y_1429_ = v_type_1438_;
v___y_1430_ = v___x_1436_;
v___y_1431_ = v___x_1451_;
goto v___jp_1425_;
}
}
}
v___jp_1456_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_inc_ref(v___y_1457_);
v___x_1460_ = l_Lean_mkAppB(v___y_1457_, v_type_1455_, v___y_1459_);
v___x_1461_ = l_Lean_Expr_app___override(v___y_1458_, v___x_1460_);
v___y_1434_ = v___x_1461_;
goto v___jp_1433_;
}
v___jp_1462_:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Expr_app___override(v___x_1454_, v___y_1463_);
if (lean_obj_tag(v_upperBound_1453_) == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1466_ = l_Lean_Expr_app___override(v___x_1464_, v___x_1465_);
v___y_1434_ = v___x_1466_;
goto v___jp_1433_;
}
else
{
lean_object* v_val_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v_val_1467_ = lean_ctor_get(v_upperBound_1453_, 0);
v___x_1468_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1469_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1470_ = lean_int_dec_le(v___x_1469_, v_val_1467_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1471_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1472_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1473_ = lean_int_neg(v_val_1467_);
v___x_1474_ = l_Int_toNat(v___x_1473_);
lean_dec(v___x_1473_);
v___x_1475_ = l_Lean_instToExprInt_mkNat(v___x_1474_);
v___x_1476_ = l_Lean_mkApp3(v___x_1471_, v_type_1455_, v___x_1472_, v___x_1475_);
v___y_1457_ = v___x_1468_;
v___y_1458_ = v___x_1464_;
v___y_1459_ = v___x_1476_;
goto v___jp_1456_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = l_Int_toNat(v_val_1467_);
v___x_1478_ = l_Lean_instToExprInt_mkNat(v___x_1477_);
v___y_1457_ = v___x_1468_;
v___y_1458_ = v___x_1464_;
v___y_1459_ = v___x_1478_;
goto v___jp_1456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___boxed(lean_object* v_s_1495_, lean_object* v_t_1496_, lean_object* v_x_1497_, lean_object* v_v_1498_, lean_object* v_ps_1499_, lean_object* v_pt_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1495_, v_t_1496_, v_x_1497_, v_v_1498_, v_ps_1499_, v_pt_1500_);
lean_dec(v_x_1497_);
lean_dec_ref(v_t_1496_);
lean_dec_ref(v_s_1495_);
return v_res_1501_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = lean_box(0);
v___x_1508_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1));
v___x_1509_ = l_Lean_Expr_const___override(v___x_1508_, v___x_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof(lean_object* v_s_1510_, lean_object* v_t_1511_, lean_object* v_a_1512_, lean_object* v_x_1513_, lean_object* v_b_1514_, lean_object* v_y_1515_, lean_object* v_v_1516_, lean_object* v_px_1517_, lean_object* v_py_1518_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1605_; lean_object* v_lowerBound_1623_; lean_object* v_upperBound_1624_; lean_object* v___x_1625_; lean_object* v_type_1626_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1634_; 
v___x_1519_ = lean_box(0);
v___x_1520_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2);
v_lowerBound_1623_ = lean_ctor_get(v_s_1510_, 0);
v_upperBound_1624_ = lean_ctor_get(v_s_1510_, 1);
v___x_1625_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1626_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1623_) == 0)
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1634_ = v___x_1650_;
goto v___jp_1633_;
}
else
{
lean_object* v_val_1651_; lean_object* v___x_1652_; lean_object* v___y_1654_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v_val_1651_ = lean_ctor_get(v_lowerBound_1623_, 0);
v___x_1652_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1656_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1657_ = lean_int_dec_le(v___x_1656_, v_val_1651_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1658_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1659_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1660_ = lean_int_neg(v_val_1651_);
v___x_1661_ = l_Int_toNat(v___x_1660_);
lean_dec(v___x_1660_);
v___x_1662_ = l_Lean_instToExprInt_mkNat(v___x_1661_);
v___x_1663_ = l_Lean_mkApp3(v___x_1658_, v_type_1626_, v___x_1659_, v___x_1662_);
v___y_1654_ = v___x_1663_;
goto v___jp_1653_;
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = l_Int_toNat(v_val_1651_);
v___x_1665_ = l_Lean_instToExprInt_mkNat(v___x_1664_);
v___y_1654_ = v___x_1665_;
goto v___jp_1653_;
}
v___jp_1653_:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_mkAppB(v___x_1652_, v_type_1626_, v___y_1654_);
v___y_1634_ = v___x_1655_;
goto v___jp_1633_;
}
}
v___jp_1521_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v___y_1527_, v___y_1526_, v_y_1515_);
v___x_1530_ = l_Lean_mkApp9(v___x_1520_, v___y_1523_, v___y_1522_, v___y_1524_, v___y_1525_, v___y_1528_, v___x_1529_, v_v_1516_, v_px_1517_, v_py_1518_);
return v___x_1530_;
}
v___jp_1531_:
{
lean_object* v_type_1535_; lean_object* v_nil_1536_; lean_object* v_cons_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v_type_1535_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_nil_1536_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1537_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1538_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1536_, v_cons_1537_, v_x_1513_);
v___x_1539_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1540_ = lean_int_dec_le(v___x_1539_, v_b_1514_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1541_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1542_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1543_ = lean_int_neg(v_b_1514_);
v___x_1544_ = l_Int_toNat(v___x_1543_);
lean_dec(v___x_1543_);
v___x_1545_ = l_Lean_instToExprInt_mkNat(v___x_1544_);
v___x_1546_ = l_Lean_mkApp3(v___x_1541_, v_type_1535_, v___x_1542_, v___x_1545_);
v___y_1522_ = v___y_1532_;
v___y_1523_ = v___y_1533_;
v___y_1524_ = v___y_1534_;
v___y_1525_ = v___x_1538_;
v___y_1526_ = v_cons_1537_;
v___y_1527_ = v_nil_1536_;
v___y_1528_ = v___x_1546_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = l_Int_toNat(v_b_1514_);
v___x_1548_ = l_Lean_instToExprInt_mkNat(v___x_1547_);
v___y_1522_ = v___y_1532_;
v___y_1523_ = v___y_1533_;
v___y_1524_ = v___y_1534_;
v___y_1525_ = v___x_1538_;
v___y_1526_ = v_cons_1537_;
v___y_1527_ = v_nil_1536_;
v___y_1528_ = v___x_1548_;
goto v___jp_1521_;
}
}
v___jp_1549_:
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1553_ = lean_int_dec_le(v___x_1552_, v_a_1512_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1554_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1555_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1556_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1557_ = lean_int_neg(v_a_1512_);
v___x_1558_ = l_Int_toNat(v___x_1557_);
lean_dec(v___x_1557_);
v___x_1559_ = l_Lean_instToExprInt_mkNat(v___x_1558_);
v___x_1560_ = l_Lean_mkApp3(v___x_1554_, v___x_1555_, v___x_1556_, v___x_1559_);
v___y_1532_ = v___y_1551_;
v___y_1533_ = v___y_1550_;
v___y_1534_ = v___x_1560_;
goto v___jp_1531_;
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = l_Int_toNat(v_a_1512_);
v___x_1562_ = l_Lean_instToExprInt_mkNat(v___x_1561_);
v___y_1532_ = v___y_1551_;
v___y_1533_ = v___y_1550_;
v___y_1534_ = v___x_1562_;
goto v___jp_1531_;
}
}
v___jp_1563_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_inc_ref(v___y_1564_);
v___x_1569_ = l_Lean_mkAppB(v___y_1564_, v___y_1565_, v___y_1568_);
v___x_1570_ = l_Lean_Expr_app___override(v___y_1567_, v___x_1569_);
v___y_1550_ = v___y_1566_;
v___y_1551_ = v___x_1570_;
goto v___jp_1549_;
}
v___jp_1571_:
{
lean_object* v_upperBound_1577_; lean_object* v___x_1578_; 
v_upperBound_1577_ = lean_ctor_get(v_t_1511_, 1);
lean_inc_ref(v___y_1573_);
v___x_1578_ = l_Lean_Expr_app___override(v___y_1573_, v___y_1576_);
if (lean_obj_tag(v_upperBound_1577_) == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1580_ = l_Lean_Expr_app___override(v___x_1579_, v___y_1572_);
v___x_1581_ = l_Lean_Expr_app___override(v___x_1578_, v___x_1580_);
v___y_1550_ = v___y_1575_;
v___y_1551_ = v___x_1581_;
goto v___jp_1549_;
}
else
{
lean_object* v_val_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v_val_1582_ = lean_ctor_get(v_upperBound_1577_, 0);
v___x_1583_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1584_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1585_ = lean_int_dec_le(v___x_1584_, v_val_1582_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1586_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1587_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1574_);
v___x_1588_ = l_Lean_Name_mkStr2(v___y_1574_, v___x_1587_);
v___x_1589_ = l_Lean_Expr_const___override(v___x_1588_, v___x_1519_);
v___x_1590_ = lean_int_neg(v_val_1582_);
v___x_1591_ = l_Int_toNat(v___x_1590_);
lean_dec(v___x_1590_);
v___x_1592_ = l_Lean_instToExprInt_mkNat(v___x_1591_);
lean_inc_ref(v___y_1572_);
v___x_1593_ = l_Lean_mkApp3(v___x_1586_, v___y_1572_, v___x_1589_, v___x_1592_);
v___y_1564_ = v___x_1583_;
v___y_1565_ = v___y_1572_;
v___y_1566_ = v___y_1575_;
v___y_1567_ = v___x_1578_;
v___y_1568_ = v___x_1593_;
goto v___jp_1563_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = l_Int_toNat(v_val_1582_);
v___x_1595_ = l_Lean_instToExprInt_mkNat(v___x_1594_);
v___y_1564_ = v___x_1583_;
v___y_1565_ = v___y_1572_;
v___y_1566_ = v___y_1575_;
v___y_1567_ = v___x_1578_;
v___y_1568_ = v___x_1595_;
goto v___jp_1563_;
}
}
}
v___jp_1596_:
{
lean_object* v___x_1603_; 
lean_inc_ref(v___y_1597_);
lean_inc_ref(v___y_1599_);
v___x_1603_ = l_Lean_mkAppB(v___y_1599_, v___y_1597_, v___y_1602_);
v___y_1572_ = v___y_1597_;
v___y_1573_ = v___y_1598_;
v___y_1574_ = v___y_1600_;
v___y_1575_ = v___y_1601_;
v___y_1576_ = v___x_1603_;
goto v___jp_1571_;
}
v___jp_1604_:
{
lean_object* v_lowerBound_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v_type_1609_; 
v_lowerBound_1606_ = lean_ctor_get(v_t_1511_, 0);
v___x_1607_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1608_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1609_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1606_) == 0)
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1572_ = v_type_1609_;
v___y_1573_ = v___x_1607_;
v___y_1574_ = v___x_1608_;
v___y_1575_ = v___y_1605_;
v___y_1576_ = v___x_1610_;
goto v___jp_1571_;
}
else
{
lean_object* v_val_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v_val_1611_ = lean_ctor_get(v_lowerBound_1606_, 0);
v___x_1612_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1613_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1614_ = lean_int_dec_le(v___x_1613_, v_val_1611_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1615_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1616_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1617_ = lean_int_neg(v_val_1611_);
v___x_1618_ = l_Int_toNat(v___x_1617_);
lean_dec(v___x_1617_);
v___x_1619_ = l_Lean_instToExprInt_mkNat(v___x_1618_);
v___x_1620_ = l_Lean_mkApp3(v___x_1615_, v_type_1609_, v___x_1616_, v___x_1619_);
v___y_1597_ = v_type_1609_;
v___y_1598_ = v___x_1607_;
v___y_1599_ = v___x_1612_;
v___y_1600_ = v___x_1608_;
v___y_1601_ = v___y_1605_;
v___y_1602_ = v___x_1620_;
goto v___jp_1596_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = l_Int_toNat(v_val_1611_);
v___x_1622_ = l_Lean_instToExprInt_mkNat(v___x_1621_);
v___y_1597_ = v_type_1609_;
v___y_1598_ = v___x_1607_;
v___y_1599_ = v___x_1612_;
v___y_1600_ = v___x_1608_;
v___y_1601_ = v___y_1605_;
v___y_1602_ = v___x_1622_;
goto v___jp_1596_;
}
}
}
v___jp_1627_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_inc_ref(v___y_1628_);
v___x_1631_ = l_Lean_mkAppB(v___y_1628_, v_type_1626_, v___y_1630_);
v___x_1632_ = l_Lean_Expr_app___override(v___y_1629_, v___x_1631_);
v___y_1605_ = v___x_1632_;
goto v___jp_1604_;
}
v___jp_1633_:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Expr_app___override(v___x_1625_, v___y_1634_);
if (lean_obj_tag(v_upperBound_1624_) == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1637_ = l_Lean_Expr_app___override(v___x_1635_, v___x_1636_);
v___y_1605_ = v___x_1637_;
goto v___jp_1604_;
}
else
{
lean_object* v_val_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v_val_1638_ = lean_ctor_get(v_upperBound_1624_, 0);
v___x_1639_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1640_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1641_ = lean_int_dec_le(v___x_1640_, v_val_1638_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1642_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1643_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1644_ = lean_int_neg(v_val_1638_);
v___x_1645_ = l_Int_toNat(v___x_1644_);
lean_dec(v___x_1644_);
v___x_1646_ = l_Lean_instToExprInt_mkNat(v___x_1645_);
v___x_1647_ = l_Lean_mkApp3(v___x_1642_, v_type_1626_, v___x_1643_, v___x_1646_);
v___y_1628_ = v___x_1639_;
v___y_1629_ = v___x_1635_;
v___y_1630_ = v___x_1647_;
goto v___jp_1627_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = l_Int_toNat(v_val_1638_);
v___x_1649_ = l_Lean_instToExprInt_mkNat(v___x_1648_);
v___y_1628_ = v___x_1639_;
v___y_1629_ = v___x_1635_;
v___y_1630_ = v___x_1649_;
goto v___jp_1627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___boxed(lean_object* v_s_1666_, lean_object* v_t_1667_, lean_object* v_a_1668_, lean_object* v_x_1669_, lean_object* v_b_1670_, lean_object* v_y_1671_, lean_object* v_v_1672_, lean_object* v_px_1673_, lean_object* v_py_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1666_, v_t_1667_, v_a_1668_, v_x_1669_, v_b_1670_, v_y_1671_, v_v_1672_, v_px_1673_, v_py_1674_);
lean_dec(v_y_1671_);
lean_dec(v_b_1670_);
lean_dec(v_x_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_t_1667_);
lean_dec_ref(v_s_1666_);
return v_res_1675_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_1682_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2));
v___x_1683_ = l_Lean_Expr_const___override(v___x_1682_, v___x_1681_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = lean_box(0);
v___x_1688_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5));
v___x_1689_ = l_Lean_Expr_const___override(v___x_1688_, v___x_1687_);
return v___x_1689_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = lean_box(0);
v___x_1694_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8));
v___x_1695_ = l_Lean_Expr_const___override(v___x_1694_, v___x_1693_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = lean_box(0);
v___x_1704_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12));
v___x_1705_ = l_Lean_Expr_const___override(v___x_1704_, v___x_1703_);
return v___x_1705_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_box(0);
v___x_1713_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15));
v___x_1714_ = l_Lean_Expr_const___override(v___x_1713_, v___x_1712_);
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = lean_box(0);
v___x_1721_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18));
v___x_1722_ = l_Lean_Expr_const___override(v___x_1721_, v___x_1720_);
return v___x_1722_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = lean_box(0);
v___x_1729_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21));
v___x_1730_ = l_Lean_Expr_const___override(v___x_1729_, v___x_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof(lean_object* v_m_1731_, lean_object* v_r_1732_, lean_object* v_i_1733_, lean_object* v_x_1734_, lean_object* v_v_1735_, lean_object* v_w_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_m_1742_; lean_object* v___y_1744_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_m_1742_ = l_Lean_mkNatLit(v_m_1731_);
v___x_1772_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1773_ = lean_int_dec_le(v___x_1772_, v_r_1732_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1774_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1775_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1776_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1777_ = lean_int_neg(v_r_1732_);
v___x_1778_ = l_Int_toNat(v___x_1777_);
lean_dec(v___x_1777_);
v___x_1779_ = l_Lean_instToExprInt_mkNat(v___x_1778_);
v___x_1780_ = l_Lean_mkApp3(v___x_1774_, v___x_1775_, v___x_1776_, v___x_1779_);
v___y_1744_ = v___x_1780_;
goto v___jp_1743_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = l_Int_toNat(v_r_1732_);
v___x_1782_ = l_Lean_instToExprInt_mkNat(v___x_1781_);
v___y_1744_ = v___x_1782_;
goto v___jp_1743_;
}
v___jp_1743_:
{
lean_object* v_i_1745_; lean_object* v_nil_1746_; lean_object* v_cons_1747_; lean_object* v_x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_i_1745_ = l_Lean_mkNatLit(v_i_1733_);
v_nil_1746_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1747_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v_x_1748_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1746_, v_cons_1747_, v_x_1734_);
v___x_1749_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3);
v___x_1750_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6);
v___x_1751_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9);
v___x_1752_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13);
lean_inc_ref(v_x_1748_);
v___x_1753_ = l_Lean_Expr_app___override(v___x_1752_, v_x_1748_);
lean_inc_ref(v_i_1745_);
v___x_1754_ = l_Lean_mkApp4(v___x_1749_, v___x_1750_, v___x_1751_, v___x_1753_, v_i_1745_);
v___x_1755_ = l_Lean_Meta_mkDecideProof(v___x_1754_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1755_, 1);
v___x_1757_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16);
lean_inc_ref(v_i_1745_);
lean_inc_ref_n(v_v_1735_, 2);
v___x_1758_ = l_Lean_mkAppB(v___x_1757_, v_v_1735_, v_i_1745_);
v___x_1759_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc_ref(v_x_1748_);
lean_inc_ref(v_m_1742_);
v___x_1760_ = l_Lean_mkApp3(v___x_1759_, v_m_1742_, v_x_1748_, v_v_1735_);
v___x_1761_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v___x_1758_, v___x_1760_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1771_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1771_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1771_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1766_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22);
v___x_1767_ = l_Lean_mkApp8(v___x_1766_, v_m_1742_, v___y_1744_, v_i_1745_, v_x_1748_, v_v_1735_, v_a_1756_, v_a_1762_, v_w_1736_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1767_);
v___x_1769_ = v___x_1764_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
else
{
lean_dec(v_a_1756_);
lean_dec_ref(v_x_1748_);
lean_dec_ref(v_i_1745_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v_m_1742_);
lean_dec_ref(v_w_1736_);
lean_dec_ref(v_v_1735_);
return v___x_1761_;
}
}
else
{
lean_dec_ref(v_x_1748_);
lean_dec_ref(v_i_1745_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v_m_1742_);
lean_dec_ref(v_w_1736_);
lean_dec_ref(v_v_1735_);
return v___x_1755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___boxed(lean_object* v_m_1783_, lean_object* v_r_1784_, lean_object* v_i_1785_, lean_object* v_x_1786_, lean_object* v_v_1787_, lean_object* v_w_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1783_, v_r_1784_, v_i_1785_, v_x_1786_, v_v_1787_, v_w_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
lean_dec(v_x_1786_);
lean_dec(v_r_1784_);
return v_res_1794_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0(void){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_instMonadEIO___redArg();
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0);
v___x_1797_ = l_StateRefT_x27_instMonad___redArg(v___x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(lean_object* v_c_1802_, lean_object* v_v_1803_, lean_object* v_assumptions_1804_, lean_object* v_x_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, uint8_t v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v___x_1816_; lean_object* v_toApplicative_1817_; lean_object* v_toFunctor_1818_; lean_object* v_toSeq_1819_; lean_object* v_toSeqLeft_1820_; lean_object* v_toSeqRight_1821_; lean_object* v___f_1822_; lean_object* v___f_1823_; lean_object* v___f_1824_; lean_object* v___f_1825_; lean_object* v___x_1826_; lean_object* v___f_1827_; lean_object* v___f_1828_; lean_object* v___f_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v_toApplicative_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1928_; 
v___x_1816_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1);
v_toApplicative_1817_ = lean_ctor_get(v___x_1816_, 0);
v_toFunctor_1818_ = lean_ctor_get(v_toApplicative_1817_, 0);
v_toSeq_1819_ = lean_ctor_get(v_toApplicative_1817_, 2);
v_toSeqLeft_1820_ = lean_ctor_get(v_toApplicative_1817_, 3);
v_toSeqRight_1821_ = lean_ctor_get(v_toApplicative_1817_, 4);
v___f_1822_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2));
v___f_1823_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1818_, 2);
v___f_1824_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1824_, 0, v_toFunctor_1818_);
v___f_1825_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1825_, 0, v_toFunctor_1818_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___f_1824_);
lean_ctor_set(v___x_1826_, 1, v___f_1825_);
lean_inc(v_toSeqRight_1821_);
v___f_1827_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1827_, 0, v_toSeqRight_1821_);
lean_inc(v_toSeqLeft_1820_);
v___f_1828_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1828_, 0, v_toSeqLeft_1820_);
lean_inc(v_toSeq_1819_);
v___f_1829_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1829_, 0, v_toSeq_1819_);
v___x_1830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1826_);
lean_ctor_set(v___x_1830_, 1, v___f_1822_);
lean_ctor_set(v___x_1830_, 2, v___f_1829_);
lean_ctor_set(v___x_1830_, 3, v___f_1828_);
lean_ctor_set(v___x_1830_, 4, v___f_1827_);
v___x_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
lean_ctor_set(v___x_1831_, 1, v___f_1823_);
v___x_1832_ = l_StateRefT_x27_instMonad___redArg(v___x_1831_);
v_toApplicative_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; 
v_unused_1929_ = lean_ctor_get(v___x_1832_, 1);
lean_dec(v_unused_1929_);
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1928_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_toApplicative_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1928_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v_toFunctor_1837_; lean_object* v_toSeq_1838_; lean_object* v_toSeqLeft_1839_; lean_object* v_toSeqRight_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1926_; 
v_toFunctor_1837_ = lean_ctor_get(v_toApplicative_1833_, 0);
v_toSeq_1838_ = lean_ctor_get(v_toApplicative_1833_, 2);
v_toSeqLeft_1839_ = lean_ctor_get(v_toApplicative_1833_, 3);
v_toSeqRight_1840_ = lean_ctor_get(v_toApplicative_1833_, 4);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_toApplicative_1833_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v_toApplicative_1833_, 1);
lean_dec(v_unused_1927_);
v___x_1842_ = v_toApplicative_1833_;
v_isShared_1843_ = v_isSharedCheck_1926_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_toSeqRight_1840_);
lean_inc(v_toSeqLeft_1839_);
lean_inc(v_toSeq_1838_);
lean_inc(v_toFunctor_1837_);
lean_dec(v_toApplicative_1833_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1926_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___f_1844_; lean_object* v___f_1845_; lean_object* v___f_1846_; lean_object* v___f_1847_; lean_object* v___x_1848_; lean_object* v___f_1849_; lean_object* v___f_1850_; lean_object* v___f_1851_; lean_object* v___x_1853_; 
v___f_1844_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4));
v___f_1845_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5));
lean_inc_ref(v_toFunctor_1837_);
v___f_1846_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1846_, 0, v_toFunctor_1837_);
v___f_1847_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1847_, 0, v_toFunctor_1837_);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___f_1846_);
lean_ctor_set(v___x_1848_, 1, v___f_1847_);
v___f_1849_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1849_, 0, v_toSeqRight_1840_);
v___f_1850_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1850_, 0, v_toSeqLeft_1839_);
v___f_1851_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1851_, 0, v_toSeq_1838_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 4, v___f_1849_);
lean_ctor_set(v___x_1842_, 3, v___f_1850_);
lean_ctor_set(v___x_1842_, 2, v___f_1851_);
lean_ctor_set(v___x_1842_, 1, v___f_1844_);
lean_ctor_set(v___x_1842_, 0, v___x_1848_);
v___x_1853_ = v___x_1842_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___f_1844_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v___f_1851_);
lean_ctor_set(v_reuseFailAlloc_1925_, 3, v___f_1850_);
lean_ctor_set(v_reuseFailAlloc_1925_, 4, v___f_1849_);
v___x_1853_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 1, v___f_1845_);
lean_ctor_set(v___x_1835_, 0, v___x_1853_);
v___x_1855_ = v___x_1835_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___f_1845_);
v___x_1855_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1856_ = l_StateRefT_x27_instMonad___redArg(v___x_1855_);
v___x_1857_ = l_ReaderT_instMonad___redArg(v___x_1856_);
v___x_1858_ = l_ReaderT_instMonad___redArg(v___x_1857_);
v___x_1859_ = l_StateRefT_x27_instMonad___redArg(v___x_1858_);
v___x_1860_ = l_StateRefT_x27_instMonad___redArg(v___x_1859_);
switch(lean_obj_tag(v_x_1805_))
{
case 0:
{
lean_object* v_i_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_3464__overap_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
lean_dec_ref(v_v_1803_);
v_i_1861_ = lean_ctor_get(v_x_1805_, 2);
lean_inc(v_i_1861_);
lean_dec_ref_known(v_x_1805_, 3);
v___x_1862_ = l_Lean_instInhabitedExpr;
v___x_1863_ = l_instInhabitedOfMonad___redArg(v___x_1860_, v___x_1862_);
v___x_3464__overap_1864_ = lean_array_get(v___x_1863_, v_assumptions_1804_, v_i_1861_);
lean_dec(v_i_1861_);
lean_dec(v___x_1863_);
v___x_1865_ = lean_box(v_a_1809_);
lean_inc(v_a_1814_);
lean_inc_ref(v_a_1813_);
lean_inc(v_a_1812_);
lean_inc_ref(v_a_1811_);
lean_inc(v_a_1810_);
lean_inc_ref(v_a_1808_);
lean_inc(v_a_1807_);
lean_inc(v_a_1806_);
v___x_1866_ = lean_apply_10(v___x_3464__overap_1864_, v_a_1806_, v_a_1807_, v_a_1808_, v___x_1865_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, lean_box(0));
return v___x_1866_;
}
case 1:
{
lean_object* v_s_1867_; lean_object* v_c_1868_; lean_object* v_j_1869_; lean_object* v___x_1870_; 
lean_dec_ref(v___x_1860_);
v_s_1867_ = lean_ctor_get(v_x_1805_, 0);
lean_inc_ref(v_s_1867_);
v_c_1868_ = lean_ctor_get(v_x_1805_, 1);
lean_inc(v_c_1868_);
v_j_1869_ = lean_ctor_get(v_x_1805_, 2);
lean_inc_ref(v_j_1869_);
lean_dec_ref_known(v_x_1805_, 3);
lean_inc_ref(v_v_1803_);
v___x_1870_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1868_, v_v_1803_, v_assumptions_1804_, v_j_1869_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1879_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1879_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1879_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1875_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1867_, v_c_1868_, v_v_1803_, v_a_1871_);
lean_dec(v_c_1868_);
lean_dec_ref(v_s_1867_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1875_);
v___x_1877_ = v___x_1873_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
else
{
lean_dec(v_c_1868_);
lean_dec_ref(v_s_1867_);
lean_dec_ref(v_v_1803_);
return v___x_1870_;
}
}
case 2:
{
lean_object* v_s_1880_; lean_object* v_t_1881_; lean_object* v_j_1882_; lean_object* v_k_1883_; lean_object* v___x_1884_; 
lean_dec_ref(v___x_1860_);
v_s_1880_ = lean_ctor_get(v_x_1805_, 0);
lean_inc_ref(v_s_1880_);
v_t_1881_ = lean_ctor_get(v_x_1805_, 1);
lean_inc_ref(v_t_1881_);
v_j_1882_ = lean_ctor_get(v_x_1805_, 3);
lean_inc_ref(v_j_1882_);
v_k_1883_ = lean_ctor_get(v_x_1805_, 4);
lean_inc_ref(v_k_1883_);
lean_dec_ref_known(v_x_1805_, 5);
lean_inc_ref(v_v_1803_);
v___x_1884_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1802_, v_v_1803_, v_assumptions_1804_, v_j_1882_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1886_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
lean_inc_ref(v_v_1803_);
v___x_1886_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1802_, v_v_1803_, v_assumptions_1804_, v_k_1883_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1895_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1880_, v_t_1881_, v_c_1802_, v_v_1803_, v_a_1885_, v_a_1887_);
lean_dec_ref(v_t_1881_);
lean_dec_ref(v_s_1880_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1891_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
else
{
lean_dec(v_a_1885_);
lean_dec_ref(v_t_1881_);
lean_dec_ref(v_s_1880_);
lean_dec_ref(v_v_1803_);
return v___x_1886_;
}
}
else
{
lean_dec_ref(v_k_1883_);
lean_dec_ref(v_t_1881_);
lean_dec_ref(v_s_1880_);
lean_dec_ref(v_v_1803_);
return v___x_1884_;
}
}
case 3:
{
lean_object* v_s_1896_; lean_object* v_t_1897_; lean_object* v_x_1898_; lean_object* v_y_1899_; lean_object* v_a_1900_; lean_object* v_j_1901_; lean_object* v_b_1902_; lean_object* v_k_1903_; lean_object* v___x_1904_; 
lean_dec_ref(v___x_1860_);
v_s_1896_ = lean_ctor_get(v_x_1805_, 0);
lean_inc_ref(v_s_1896_);
v_t_1897_ = lean_ctor_get(v_x_1805_, 1);
lean_inc_ref(v_t_1897_);
v_x_1898_ = lean_ctor_get(v_x_1805_, 2);
lean_inc(v_x_1898_);
v_y_1899_ = lean_ctor_get(v_x_1805_, 3);
lean_inc(v_y_1899_);
v_a_1900_ = lean_ctor_get(v_x_1805_, 4);
lean_inc(v_a_1900_);
v_j_1901_ = lean_ctor_get(v_x_1805_, 5);
lean_inc_ref(v_j_1901_);
v_b_1902_ = lean_ctor_get(v_x_1805_, 6);
lean_inc(v_b_1902_);
v_k_1903_ = lean_ctor_get(v_x_1805_, 7);
lean_inc_ref(v_k_1903_);
lean_dec_ref_known(v_x_1805_, 8);
lean_inc_ref(v_v_1803_);
v___x_1904_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1898_, v_v_1803_, v_assumptions_1804_, v_j_1901_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
lean_inc_ref(v_v_1803_);
v___x_1906_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_y_1899_, v_v_1803_, v_assumptions_1804_, v_k_1903_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1915_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1911_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1896_, v_t_1897_, v_a_1900_, v_x_1898_, v_b_1902_, v_y_1899_, v_v_1803_, v_a_1905_, v_a_1907_);
lean_dec(v_y_1899_);
lean_dec(v_b_1902_);
lean_dec(v_x_1898_);
lean_dec(v_a_1900_);
lean_dec_ref(v_t_1897_);
lean_dec_ref(v_s_1896_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1911_);
v___x_1913_ = v___x_1909_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
else
{
lean_dec(v_a_1905_);
lean_dec(v_b_1902_);
lean_dec(v_a_1900_);
lean_dec(v_y_1899_);
lean_dec(v_x_1898_);
lean_dec_ref(v_t_1897_);
lean_dec_ref(v_s_1896_);
lean_dec_ref(v_v_1803_);
return v___x_1906_;
}
}
else
{
lean_dec_ref(v_k_1903_);
lean_dec(v_b_1902_);
lean_dec(v_a_1900_);
lean_dec(v_y_1899_);
lean_dec(v_x_1898_);
lean_dec_ref(v_t_1897_);
lean_dec_ref(v_s_1896_);
lean_dec_ref(v_v_1803_);
return v___x_1904_;
}
}
default: 
{
lean_object* v_m_1916_; lean_object* v_r_1917_; lean_object* v_i_1918_; lean_object* v_x_1919_; lean_object* v_j_1920_; lean_object* v___x_1921_; 
lean_dec_ref(v___x_1860_);
v_m_1916_ = lean_ctor_get(v_x_1805_, 0);
lean_inc(v_m_1916_);
v_r_1917_ = lean_ctor_get(v_x_1805_, 1);
lean_inc(v_r_1917_);
v_i_1918_ = lean_ctor_get(v_x_1805_, 2);
lean_inc(v_i_1918_);
v_x_1919_ = lean_ctor_get(v_x_1805_, 3);
lean_inc(v_x_1919_);
v_j_1920_ = lean_ctor_get(v_x_1805_, 4);
lean_inc_ref(v_j_1920_);
lean_dec_ref_known(v_x_1805_, 5);
lean_inc_ref(v_v_1803_);
v___x_1921_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1919_, v_v_1803_, v_assumptions_1804_, v_j_1920_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___x_1923_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1916_, v_r_1917_, v_i_1918_, v_x_1919_, v_v_1803_, v_a_1922_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
lean_dec(v_x_1919_);
lean_dec(v_r_1917_);
return v___x_1923_;
}
else
{
lean_dec(v_x_1919_);
lean_dec(v_i_1918_);
lean_dec(v_r_1917_);
lean_dec(v_m_1916_);
lean_dec_ref(v_v_1803_);
return v___x_1921_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___boxed(lean_object* v_c_1930_, lean_object* v_v_1931_, lean_object* v_assumptions_1932_, lean_object* v_x_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
uint8_t v_a_boxed_1944_; lean_object* v_res_1945_; 
v_a_boxed_1944_ = lean_unbox(v_a_1937_);
v_res_1945_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1930_, v_v_1931_, v_assumptions_1932_, v_x_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_boxed_1944_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1936_);
lean_dec(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_assumptions_1932_);
lean_dec(v_c_1930_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof(lean_object* v_s_1946_, lean_object* v_c_1947_, lean_object* v_v_1948_, lean_object* v_assumptions_1949_, lean_object* v_x_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, uint8_t v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1947_, v_v_1948_, v_assumptions_1949_, v_x_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___boxed(lean_object* v_s_1962_, lean_object* v_c_1963_, lean_object* v_v_1964_, lean_object* v_assumptions_1965_, lean_object* v_x_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
uint8_t v_a_boxed_1977_; lean_object* v_res_1978_; 
v_a_boxed_1977_ = lean_unbox(v_a_1970_);
v_res_1978_ = l_Lean_Elab_Tactic_Omega_Justification_proof(v_s_1962_, v_c_1963_, v_v_1964_, v_assumptions_1965_, v_x_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_boxed_1977_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec_ref(v_assumptions_1965_);
lean_dec(v_c_1963_);
lean_dec_ref(v_s_1962_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_instToString___lam__0(lean_object* v_f_1979_){
_start:
{
lean_object* v_coeffs_1980_; lean_object* v_constraint_1981_; lean_object* v_justification_1982_; lean_object* v___x_1983_; 
v_coeffs_1980_ = lean_ctor_get(v_f_1979_, 0);
lean_inc(v_coeffs_1980_);
v_constraint_1981_ = lean_ctor_get(v_f_1979_, 1);
lean_inc_ref(v_constraint_1981_);
v_justification_1982_ = lean_ctor_get(v_f_1979_, 2);
lean_inc_ref(v_justification_1982_);
lean_dec_ref(v_f_1979_);
v___x_1983_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_1981_, v_coeffs_1980_, v_justification_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_tidy(lean_object* v_f_1986_){
_start:
{
lean_object* v_coeffs_1987_; lean_object* v_constraint_1988_; lean_object* v_justification_1989_; lean_object* v___x_1990_; 
v_coeffs_1987_ = lean_ctor_get(v_f_1986_, 0);
v_constraint_1988_ = lean_ctor_get(v_f_1986_, 1);
v_justification_1989_ = lean_ctor_get(v_f_1986_, 2);
lean_inc_ref(v_justification_1989_);
lean_inc(v_coeffs_1987_);
lean_inc_ref(v_constraint_1988_);
v___x_1990_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(v_constraint_1988_, v_coeffs_1987_, v_justification_1989_);
if (lean_obj_tag(v___x_1990_) == 0)
{
return v_f_1986_;
}
else
{
lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2002_; 
v_isSharedCheck_2002_ = !lean_is_exclusive(v_f_1986_);
if (v_isSharedCheck_2002_ == 0)
{
lean_object* v_unused_2003_; lean_object* v_unused_2004_; lean_object* v_unused_2005_; 
v_unused_2003_ = lean_ctor_get(v_f_1986_, 2);
lean_dec(v_unused_2003_);
v_unused_2004_ = lean_ctor_get(v_f_1986_, 1);
lean_dec(v_unused_2004_);
v_unused_2005_ = lean_ctor_get(v_f_1986_, 0);
lean_dec(v_unused_2005_);
v___x_1992_ = v_f_1986_;
v_isShared_1993_ = v_isSharedCheck_2002_;
goto v_resetjp_1991_;
}
else
{
lean_dec(v_f_1986_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2002_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v_val_1994_; lean_object* v_snd_1995_; lean_object* v_fst_1996_; lean_object* v_fst_1997_; lean_object* v_snd_1998_; lean_object* v___x_2000_; 
v_val_1994_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_val_1994_);
lean_dec_ref_known(v___x_1990_, 1);
v_snd_1995_ = lean_ctor_get(v_val_1994_, 1);
lean_inc(v_snd_1995_);
v_fst_1996_ = lean_ctor_get(v_val_1994_, 0);
lean_inc(v_fst_1996_);
lean_dec(v_val_1994_);
v_fst_1997_ = lean_ctor_get(v_snd_1995_, 0);
lean_inc(v_fst_1997_);
v_snd_1998_ = lean_ctor_get(v_snd_1995_, 1);
lean_inc(v_snd_1998_);
lean_dec(v_snd_1995_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 2, v_snd_1998_);
lean_ctor_set(v___x_1992_, 1, v_fst_1996_);
lean_ctor_set(v___x_1992_, 0, v_fst_1997_);
v___x_2000_ = v___x_1992_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_fst_1997_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_fst_1996_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_snd_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_combo(lean_object* v_a_2006_, lean_object* v_f_2007_, lean_object* v_b_2008_, lean_object* v_g_2009_){
_start:
{
lean_object* v_coeffs_2010_; lean_object* v_constraint_2011_; lean_object* v_justification_2012_; lean_object* v_coeffs_2013_; lean_object* v_constraint_2014_; lean_object* v_justification_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2025_; 
v_coeffs_2010_ = lean_ctor_get(v_f_2007_, 0);
lean_inc(v_coeffs_2010_);
v_constraint_2011_ = lean_ctor_get(v_f_2007_, 1);
lean_inc_ref(v_constraint_2011_);
v_justification_2012_ = lean_ctor_get(v_f_2007_, 2);
lean_inc_ref(v_justification_2012_);
lean_dec_ref(v_f_2007_);
v_coeffs_2013_ = lean_ctor_get(v_g_2009_, 0);
v_constraint_2014_ = lean_ctor_get(v_g_2009_, 1);
v_justification_2015_ = lean_ctor_get(v_g_2009_, 2);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_g_2009_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2017_ = v_g_2009_;
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_justification_2015_);
lean_inc(v_constraint_2014_);
lean_inc(v_coeffs_2013_);
lean_dec(v_g_2009_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
lean_inc(v_coeffs_2013_);
lean_inc(v_coeffs_2010_);
v___x_2019_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_2006_, v_b_2008_, v_coeffs_2010_, v_coeffs_2013_);
lean_inc_ref(v_constraint_2014_);
lean_inc(v_b_2008_);
lean_inc_ref(v_constraint_2011_);
lean_inc(v_a_2006_);
v___x_2020_ = l_Lean_Omega_Constraint_combo(v_a_2006_, v_constraint_2011_, v_b_2008_, v_constraint_2014_);
v___x_2021_ = lean_alloc_ctor(3, 8, 0);
lean_ctor_set(v___x_2021_, 0, v_constraint_2011_);
lean_ctor_set(v___x_2021_, 1, v_constraint_2014_);
lean_ctor_set(v___x_2021_, 2, v_coeffs_2010_);
lean_ctor_set(v___x_2021_, 3, v_coeffs_2013_);
lean_ctor_set(v___x_2021_, 4, v_a_2006_);
lean_ctor_set(v___x_2021_, 5, v_justification_2012_);
lean_ctor_set(v___x_2021_, 6, v_b_2008_);
lean_ctor_set(v___x_2021_, 7, v_justification_2015_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 2, v___x_2021_);
lean_ctor_set(v___x_2017_, 1, v___x_2020_);
lean_ctor_set(v___x_2017_, 0, v___x_2019_);
v___x_2023_ = v___x_2017_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__10));
v___x_2052_ = l_Lean_mkAtom(v___x_2051_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11);
v___x_2054_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2055_ = lean_array_push(v___x_2054_, v___x_2053_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2056_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12);
v___x_2057_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9));
v___x_2058_ = lean_box(2);
v___x_2059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v___x_2057_);
lean_ctor_set(v___x_2059_, 2, v___x_2056_);
return v___x_2059_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13);
v___x_2061_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2062_ = lean_array_push(v___x_2061_, v___x_2060_);
return v___x_2062_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2063_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14);
v___x_2064_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7));
v___x_2065_ = lean_box(2);
v___x_2066_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v___x_2064_);
lean_ctor_set(v___x_2066_, 2, v___x_2063_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2067_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15);
v___x_2068_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2069_ = lean_array_push(v___x_2068_, v___x_2067_);
return v___x_2069_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2070_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16);
v___x_2071_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5));
v___x_2072_ = lean_box(2);
v___x_2073_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
lean_ctor_set(v___x_2073_, 1, v___x_2071_);
lean_ctor_set(v___x_2073_, 2, v___x_2070_);
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17);
v___x_2075_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2076_ = lean_array_push(v___x_2075_, v___x_2074_);
return v___x_2076_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2077_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18);
v___x_2078_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2));
v___x_2079_ = lean_box(2);
v___x_2080_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v___x_2078_);
lean_ctor_set(v___x_2080_, 2, v___x_2077_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam(void){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19);
return v___x_2081_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_isEmpty(lean_object* v_p_2082_){
_start:
{
lean_object* v_constraints_2083_; lean_object* v_size_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v_constraints_2083_ = lean_ctor_get(v_p_2082_, 2);
v_size_2084_ = lean_ctor_get(v_constraints_2083_, 0);
v___x_2085_ = lean_unsigned_to_nat(0u);
v___x_2086_ = lean_nat_dec_eq(v_size_2084_, v___x_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_isEmpty___boxed(lean_object* v_p_2087_){
_start:
{
uint8_t v_res_2088_; lean_object* v_r_2089_; 
v_res_2088_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2087_);
lean_dec_ref(v_p_2087_);
v_r_2089_ = lean_box(v_res_2088_);
return v_r_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object* v_a_2090_, lean_object* v_b_2091_, lean_object* v_d_2092_){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2093_, 0, v_a_2090_);
lean_ctor_set(v___x_2093_, 1, v_b_2091_);
v___x_2094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v_d_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object* v___x_2095_, lean_object* v_x_2096_){
_start:
{
lean_object* v_snd_2097_; lean_object* v_constraint_2098_; lean_object* v_fst_2099_; lean_object* v_lowerBound_2100_; lean_object* v_upperBound_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___y_2106_; lean_object* v___y_2107_; 
v_snd_2097_ = lean_ctor_get(v_x_2096_, 1);
v_constraint_2098_ = lean_ctor_get(v_snd_2097_, 1);
lean_inc_ref(v_constraint_2098_);
v_fst_2099_ = lean_ctor_get(v_x_2096_, 0);
lean_inc(v_fst_2099_);
lean_dec_ref(v_x_2096_);
v_lowerBound_2100_ = lean_ctor_get(v_constraint_2098_, 0);
lean_inc(v_lowerBound_2100_);
v_upperBound_2101_ = lean_ctor_get(v_constraint_2098_, 1);
lean_inc(v_upperBound_2101_);
lean_dec_ref(v_constraint_2098_);
v___x_2102_ = l_List_toString___redArg(v___x_2095_, v_fst_2099_);
v___x_2103_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_2104_ = lean_string_append(v___x_2102_, v___x_2103_);
if (lean_obj_tag(v_lowerBound_2100_) == 0)
{
if (lean_obj_tag(v_upperBound_2101_) == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_2113_ = lean_string_append(v___x_2104_, v___x_2112_);
return v___x_2113_;
}
else
{
lean_object* v_val_2114_; lean_object* v___x_2115_; lean_object* v___y_2117_; lean_object* v_intZero_2122_; uint8_t v_isNeg_2123_; 
v_val_2114_ = lean_ctor_get(v_upperBound_2101_, 0);
lean_inc(v_val_2114_);
lean_dec_ref_known(v_upperBound_2101_, 1);
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
if (lean_obj_tag(v_upperBound_2101_) == 0)
{
lean_object* v_val_2133_; lean_object* v___x_2134_; lean_object* v___y_2136_; lean_object* v_intZero_2141_; uint8_t v_isNeg_2142_; 
v_val_2133_ = lean_ctor_get(v_lowerBound_2100_, 0);
lean_inc(v_val_2133_);
lean_dec_ref_known(v_lowerBound_2100_, 1);
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
v_val_2152_ = lean_ctor_get(v_lowerBound_2100_, 0);
lean_inc(v_val_2152_);
lean_dec_ref_known(v_lowerBound_2100_, 1);
v_val_2153_ = lean_ctor_get(v_upperBound_2101_, 0);
lean_inc(v_val_2153_);
lean_dec_ref_known(v_upperBound_2101_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2(lean_object* v___x_2204_, lean_object* v___f_2205_, lean_object* v_l_2206_, lean_object* v_acc_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2204_, v___f_2205_, v_acc_2207_, v_l_2206_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3(lean_object* v___f_2230_, lean_object* v___f_2231_, lean_object* v_p_2232_){
_start:
{
uint8_t v_possible_2233_; 
v_possible_2233_ = lean_ctor_get_uint8(v_p_2232_, sizeof(void*)*7);
if (v_possible_2233_ == 0)
{
lean_object* v___x_2234_; 
lean_dec_ref(v_p_2232_);
lean_dec_ref(v___f_2231_);
lean_dec_ref(v___f_2230_);
v___x_2234_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
return v___x_2234_;
}
else
{
lean_object* v_constraints_2235_; uint8_t v___x_2236_; 
v_constraints_2235_ = lean_ctor_get(v_p_2232_, 2);
lean_inc_ref(v_constraints_2235_);
v___x_2236_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2232_);
lean_dec_ref(v_p_2232_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; lean_object* v_buckets_2238_; lean_object* v___x_2239_; lean_object* v___y_2241_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v___x_2237_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10));
v_buckets_2238_ = lean_ctor_get(v_constraints_2235_, 1);
lean_inc_ref(v_buckets_2238_);
lean_dec_ref(v_constraints_2235_);
v___x_2239_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_2245_ = lean_box(0);
v___x_2246_ = lean_array_get_size(v_buckets_2238_);
v___x_2247_ = lean_unsigned_to_nat(0u);
v___x_2248_ = lean_nat_dec_lt(v___x_2247_, v___x_2246_);
if (v___x_2248_ == 0)
{
lean_dec_ref(v_buckets_2238_);
lean_dec_ref(v___f_2231_);
v___y_2241_ = v___x_2245_;
goto v___jp_2240_;
}
else
{
lean_object* v___f_2249_; size_t v___x_2250_; size_t v___x_2251_; lean_object* v___x_2252_; 
v___f_2249_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2), 4, 2);
lean_closure_set(v___f_2249_, 0, v___x_2237_);
lean_closure_set(v___f_2249_, 1, v___f_2231_);
v___x_2250_ = lean_usize_of_nat(v___x_2246_);
v___x_2251_ = ((size_t)0ULL);
v___x_2252_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2237_, v___f_2249_, v_buckets_2238_, v___x_2250_, v___x_2251_, v___x_2245_);
v___y_2241_ = v___x_2252_;
goto v___jp_2240_;
}
v___jp_2240_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = lean_box(0);
v___x_2243_ = l_List_mapTR_loop___redArg(v___f_2230_, v___y_2241_, v___x_2242_);
v___x_2244_ = l_String_intercalate(v___x_2239_, v___x_2243_);
return v___x_2244_;
}
}
else
{
lean_object* v___x_2253_; 
lean_dec_ref(v_constraints_2235_);
lean_dec_ref(v___f_2231_);
lean_dec_ref(v___f_2230_);
v___x_2253_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
return v___x_2253_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2268_ = lean_box(0);
v___x_2269_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1));
v___x_2270_ = l_Lean_Expr_const___override(v___x_2269_, v___x_2268_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = lean_box(0);
v___x_2277_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5));
v___x_2278_ = l_Lean_Expr_const___override(v___x_2277_, v___x_2276_);
return v___x_2278_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = lean_box(0);
v___x_2286_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8));
v___x_2287_ = l_Lean_Expr_const___override(v___x_2286_, v___x_2285_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse(lean_object* v_s_2288_, lean_object* v_x_2289_, lean_object* v_j_2290_, lean_object* v_assumptions_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, uint8_t v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2293_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc_n(v_a_2303_, 2);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_2289_, v_a_2303_, v_assumptions_2291_, v_j_2290_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2306_; lean_object* v_lowerBound_2307_; lean_object* v_upperBound_2308_; lean_object* v_nil_2309_; lean_object* v_cons_2310_; lean_object* v___x_2311_; lean_object* v___y_2313_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___x_2336_; lean_object* v___y_2338_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v___x_2306_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_lowerBound_2307_ = lean_ctor_get(v_s_2288_, 0);
v_upperBound_2308_ = lean_ctor_get(v_s_2288_, 1);
v_nil_2309_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2310_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2311_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2309_, v_cons_2310_, v_x_2289_);
v___x_2336_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
if (lean_obj_tag(v_lowerBound_2307_) == 0)
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_2338_ = v___x_2354_;
goto v___jp_2337_;
}
else
{
lean_object* v_val_2355_; lean_object* v___x_2356_; lean_object* v___y_2358_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v_val_2355_ = lean_ctor_get(v_lowerBound_2307_, 0);
v___x_2356_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2360_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2361_ = lean_int_dec_le(v___x_2360_, v_val_2355_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2362_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2363_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2364_ = lean_int_neg(v_val_2355_);
v___x_2365_ = l_Int_toNat(v___x_2364_);
lean_dec(v___x_2364_);
v___x_2366_ = l_Lean_instToExprInt_mkNat(v___x_2365_);
v___x_2367_ = l_Lean_mkApp3(v___x_2362_, v___x_2306_, v___x_2363_, v___x_2366_);
v___y_2358_ = v___x_2367_;
goto v___jp_2357_;
}
else
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = l_Int_toNat(v_val_2355_);
v___x_2369_ = l_Lean_instToExprInt_mkNat(v___x_2368_);
v___y_2358_ = v___x_2369_;
goto v___jp_2357_;
}
v___jp_2357_:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_mkAppB(v___x_2356_, v___x_2306_, v___y_2358_);
v___y_2338_ = v___x_2359_;
goto v___jp_2337_;
}
}
v___jp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2314_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2);
lean_inc_ref(v___y_2313_);
v___x_2315_ = l_Lean_Expr_app___override(v___x_2314_, v___y_2313_);
v___x_2316_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6);
v___x_2317_ = l_Lean_Meta_mkEq(v___x_2315_, v___x_2316_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2319_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
v___x_2319_ = l_Lean_Meta_mkDecideProof(v_a_2318_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2329_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2329_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2329_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2324_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9);
v___x_2325_ = l_Lean_mkApp5(v___x_2324_, v___y_2313_, v_a_2320_, v___x_2311_, v_a_2303_, v_a_2305_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2325_);
v___x_2327_ = v___x_2322_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
else
{
lean_dec_ref(v___y_2313_);
lean_dec_ref(v___x_2311_);
lean_dec(v_a_2305_);
lean_dec(v_a_2303_);
return v___x_2319_;
}
}
else
{
lean_dec_ref(v___y_2313_);
lean_dec_ref(v___x_2311_);
lean_dec(v_a_2305_);
lean_dec(v_a_2303_);
return v___x_2317_;
}
}
v___jp_2330_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_inc_ref(v___y_2331_);
v___x_2334_ = l_Lean_mkAppB(v___y_2331_, v___x_2306_, v___y_2333_);
v___x_2335_ = l_Lean_Expr_app___override(v___y_2332_, v___x_2334_);
v___y_2313_ = v___x_2335_;
goto v___jp_2312_;
}
v___jp_2337_:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Expr_app___override(v___x_2336_, v___y_2338_);
if (lean_obj_tag(v_upperBound_2308_) == 0)
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_2341_ = l_Lean_Expr_app___override(v___x_2339_, v___x_2340_);
v___y_2313_ = v___x_2341_;
goto v___jp_2312_;
}
else
{
lean_object* v_val_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v_val_2342_ = lean_ctor_get(v_upperBound_2308_, 0);
v___x_2343_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2344_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2345_ = lean_int_dec_le(v___x_2344_, v_val_2342_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2346_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2347_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2348_ = lean_int_neg(v_val_2342_);
v___x_2349_ = l_Int_toNat(v___x_2348_);
lean_dec(v___x_2348_);
v___x_2350_ = l_Lean_instToExprInt_mkNat(v___x_2349_);
v___x_2351_ = l_Lean_mkApp3(v___x_2346_, v___x_2306_, v___x_2347_, v___x_2350_);
v___y_2331_ = v___x_2343_;
v___y_2332_ = v___x_2339_;
v___y_2333_ = v___x_2351_;
goto v___jp_2330_;
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = l_Int_toNat(v_val_2342_);
v___x_2353_ = l_Lean_instToExprInt_mkNat(v___x_2352_);
v___y_2331_ = v___x_2343_;
v___y_2332_ = v___x_2339_;
v___y_2333_ = v___x_2353_;
goto v___jp_2330_;
}
}
}
}
else
{
lean_dec(v_a_2303_);
return v___x_2304_;
}
}
else
{
lean_dec_ref(v_j_2290_);
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed(lean_object* v_s_2370_, lean_object* v_x_2371_, lean_object* v_j_2372_, lean_object* v_assumptions_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
uint8_t v_a_boxed_2384_; lean_object* v_res_2385_; 
v_a_boxed_2384_ = lean_unbox(v_a_2377_);
v_res_2385_ = l_Lean_Elab_Tactic_Omega_Problem_proveFalse(v_s_2370_, v_x_2371_, v_j_2372_, v_assumptions_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_boxed_2384_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_assumptions_2373_);
lean_dec(v_x_2371_);
lean_dec_ref(v_s_2370_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0(lean_object* v_constraint_2386_, lean_object* v_coeffs_2387_, lean_object* v_justification_2388_, lean_object* v_x_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_2386_, v_coeffs_2387_, v_justification_2388_);
return v___x_2390_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(lean_object* v_a_2391_, lean_object* v_x_2392_){
_start:
{
if (lean_obj_tag(v_x_2392_) == 0)
{
uint8_t v___x_2393_; 
v___x_2393_ = 0;
return v___x_2393_;
}
else
{
lean_object* v_key_2394_; lean_object* v_tail_2395_; uint8_t v___x_2396_; 
v_key_2394_ = lean_ctor_get(v_x_2392_, 0);
v_tail_2395_ = lean_ctor_get(v_x_2392_, 2);
v___x_2396_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2394_, v_a_2391_);
if (v___x_2396_ == 0)
{
v_x_2392_ = v_tail_2395_;
goto _start;
}
else
{
return v___x_2396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg___boxed(lean_object* v_a_2398_, lean_object* v_x_2399_){
_start:
{
uint8_t v_res_2400_; lean_object* v_r_2401_; 
v_res_2400_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2398_, v_x_2399_);
lean_dec(v_x_2399_);
lean_dec(v_a_2398_);
v_r_2401_ = lean_box(v_res_2400_);
return v_r_2401_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(uint64_t v_x_2402_, lean_object* v_x_2403_){
_start:
{
if (lean_obj_tag(v_x_2403_) == 0)
{
return v_x_2402_;
}
else
{
lean_object* v_head_2404_; lean_object* v_tail_2405_; lean_object* v_intZero_2406_; uint8_t v_isNeg_2407_; 
v_head_2404_ = lean_ctor_get(v_x_2403_, 0);
v_tail_2405_ = lean_ctor_get(v_x_2403_, 1);
v_intZero_2406_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2407_ = lean_int_dec_lt(v_head_2404_, v_intZero_2406_);
if (v_isNeg_2407_ == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint64_t v___x_2411_; uint64_t v___x_2412_; 
v_a_2408_ = lean_nat_abs(v_head_2404_);
v___x_2409_ = lean_unsigned_to_nat(2u);
v___x_2410_ = lean_nat_mul(v___x_2409_, v_a_2408_);
lean_dec(v_a_2408_);
v___x_2411_ = lean_uint64_of_nat(v___x_2410_);
lean_dec(v___x_2410_);
v___x_2412_ = lean_uint64_mix_hash(v_x_2402_, v___x_2411_);
v_x_2402_ = v___x_2412_;
v_x_2403_ = v_tail_2405_;
goto _start;
}
else
{
lean_object* v_abs_2414_; lean_object* v_one_2415_; lean_object* v_a_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint64_t v___x_2420_; uint64_t v___x_2421_; 
v_abs_2414_ = lean_nat_abs(v_head_2404_);
v_one_2415_ = lean_unsigned_to_nat(1u);
v_a_2416_ = lean_nat_sub(v_abs_2414_, v_one_2415_);
lean_dec(v_abs_2414_);
v___x_2417_ = lean_unsigned_to_nat(2u);
v___x_2418_ = lean_nat_mul(v___x_2417_, v_a_2416_);
lean_dec(v_a_2416_);
v___x_2419_ = lean_nat_add(v___x_2418_, v_one_2415_);
lean_dec(v___x_2418_);
v___x_2420_ = lean_uint64_of_nat(v___x_2419_);
lean_dec(v___x_2419_);
v___x_2421_ = lean_uint64_mix_hash(v_x_2402_, v___x_2420_);
v_x_2402_ = v___x_2421_;
v_x_2403_ = v_tail_2405_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0___boxed(lean_object* v_x_2423_, lean_object* v_x_2424_){
_start:
{
uint64_t v_x_806__boxed_2425_; uint64_t v_res_2426_; lean_object* v_r_2427_; 
v_x_806__boxed_2425_ = lean_unbox_uint64(v_x_2423_);
lean_dec_ref(v_x_2423_);
v_res_2426_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v_x_806__boxed_2425_, v_x_2424_);
lean_dec(v_x_2424_);
v_r_2427_ = lean_box_uint64(v_res_2426_);
return v_r_2427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_2428_, lean_object* v_x_2429_){
_start:
{
if (lean_obj_tag(v_x_2429_) == 0)
{
return v_x_2428_;
}
else
{
lean_object* v_key_2430_; lean_object* v_value_2431_; lean_object* v_tail_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2456_; 
v_key_2430_ = lean_ctor_get(v_x_2429_, 0);
v_value_2431_ = lean_ctor_get(v_x_2429_, 1);
v_tail_2432_ = lean_ctor_get(v_x_2429_, 2);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_x_2429_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2434_ = v_x_2429_;
v_isShared_2435_ = v_isSharedCheck_2456_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_tail_2432_);
lean_inc(v_value_2431_);
lean_inc(v_key_2430_);
lean_dec(v_x_2429_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2456_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; uint64_t v___x_2437_; uint64_t v___x_2438_; uint64_t v___x_2439_; uint64_t v___x_2440_; uint64_t v_fold_2441_; uint64_t v___x_2442_; uint64_t v___x_2443_; uint64_t v___x_2444_; size_t v___x_2445_; size_t v___x_2446_; size_t v___x_2447_; size_t v___x_2448_; size_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2436_ = lean_array_get_size(v_x_2428_);
v___x_2437_ = 7ULL;
v___x_2438_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2437_, v_key_2430_);
v___x_2439_ = 32ULL;
v___x_2440_ = lean_uint64_shift_right(v___x_2438_, v___x_2439_);
v_fold_2441_ = lean_uint64_xor(v___x_2438_, v___x_2440_);
v___x_2442_ = 16ULL;
v___x_2443_ = lean_uint64_shift_right(v_fold_2441_, v___x_2442_);
v___x_2444_ = lean_uint64_xor(v_fold_2441_, v___x_2443_);
v___x_2445_ = lean_uint64_to_usize(v___x_2444_);
v___x_2446_ = lean_usize_of_nat(v___x_2436_);
v___x_2447_ = ((size_t)1ULL);
v___x_2448_ = lean_usize_sub(v___x_2446_, v___x_2447_);
v___x_2449_ = lean_usize_land(v___x_2445_, v___x_2448_);
v___x_2450_ = lean_array_uget_borrowed(v_x_2428_, v___x_2449_);
lean_inc(v___x_2450_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 2, v___x_2450_);
v___x_2452_ = v___x_2434_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_key_2430_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_value_2431_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_array_uset(v_x_2428_, v___x_2449_, v___x_2452_);
v_x_2428_ = v___x_2453_;
v_x_2429_ = v_tail_2432_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(lean_object* v_i_2457_, lean_object* v_source_2458_, lean_object* v_target_2459_){
_start:
{
lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2460_ = lean_array_get_size(v_source_2458_);
v___x_2461_ = lean_nat_dec_lt(v_i_2457_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_dec_ref(v_source_2458_);
lean_dec(v_i_2457_);
return v_target_2459_;
}
else
{
lean_object* v_es_2462_; lean_object* v___x_2463_; lean_object* v_source_2464_; lean_object* v_target_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_es_2462_ = lean_array_fget(v_source_2458_, v_i_2457_);
v___x_2463_ = lean_box(0);
v_source_2464_ = lean_array_fset(v_source_2458_, v_i_2457_, v___x_2463_);
v_target_2465_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_target_2459_, v_es_2462_);
v___x_2466_ = lean_unsigned_to_nat(1u);
v___x_2467_ = lean_nat_add(v_i_2457_, v___x_2466_);
lean_dec(v_i_2457_);
v_i_2457_ = v___x_2467_;
v_source_2458_ = v_source_2464_;
v_target_2459_ = v_target_2465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(lean_object* v_data_2469_){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v_nbuckets_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2470_ = lean_array_get_size(v_data_2469_);
v___x_2471_ = lean_unsigned_to_nat(2u);
v_nbuckets_2472_ = lean_nat_mul(v___x_2470_, v___x_2471_);
v___x_2473_ = lean_unsigned_to_nat(0u);
v___x_2474_ = lean_box(0);
v___x_2475_ = lean_mk_array(v_nbuckets_2472_, v___x_2474_);
v___x_2476_ = lean_array_propagate_mark(v_data_2469_, v___x_2475_);
v___x_2477_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v___x_2473_, v_data_2469_, v___x_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(lean_object* v_m_2478_, lean_object* v_a_2479_, lean_object* v_b_2480_){
_start:
{
lean_object* v_size_2481_; lean_object* v_buckets_2482_; lean_object* v___x_2483_; uint64_t v___x_2484_; uint64_t v___x_2485_; uint64_t v___x_2486_; uint64_t v___x_2487_; uint64_t v_fold_2488_; uint64_t v___x_2489_; uint64_t v___x_2490_; uint64_t v___x_2491_; size_t v___x_2492_; size_t v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; lean_object* v_bkt_2497_; uint8_t v___x_2498_; 
v_size_2481_ = lean_ctor_get(v_m_2478_, 0);
v_buckets_2482_ = lean_ctor_get(v_m_2478_, 1);
v___x_2483_ = lean_array_get_size(v_buckets_2482_);
v___x_2484_ = 7ULL;
v___x_2485_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2484_, v_a_2479_);
v___x_2486_ = 32ULL;
v___x_2487_ = lean_uint64_shift_right(v___x_2485_, v___x_2486_);
v_fold_2488_ = lean_uint64_xor(v___x_2485_, v___x_2487_);
v___x_2489_ = 16ULL;
v___x_2490_ = lean_uint64_shift_right(v_fold_2488_, v___x_2489_);
v___x_2491_ = lean_uint64_xor(v_fold_2488_, v___x_2490_);
v___x_2492_ = lean_uint64_to_usize(v___x_2491_);
v___x_2493_ = lean_usize_of_nat(v___x_2483_);
v___x_2494_ = ((size_t)1ULL);
v___x_2495_ = lean_usize_sub(v___x_2493_, v___x_2494_);
v___x_2496_ = lean_usize_land(v___x_2492_, v___x_2495_);
v_bkt_2497_ = lean_array_uget_borrowed(v_buckets_2482_, v___x_2496_);
v___x_2498_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2479_, v_bkt_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2519_; 
lean_inc_ref(v_buckets_2482_);
lean_inc(v_size_2481_);
v_isSharedCheck_2519_ = !lean_is_exclusive(v_m_2478_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; lean_object* v_unused_2521_; 
v_unused_2520_ = lean_ctor_get(v_m_2478_, 1);
lean_dec(v_unused_2520_);
v_unused_2521_ = lean_ctor_get(v_m_2478_, 0);
lean_dec(v_unused_2521_);
v___x_2500_ = v_m_2478_;
v_isShared_2501_ = v_isSharedCheck_2519_;
goto v_resetjp_2499_;
}
else
{
lean_dec(v_m_2478_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2519_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v_size_x27_2503_; lean_object* v___x_2504_; lean_object* v_buckets_x27_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2502_ = lean_unsigned_to_nat(1u);
v_size_x27_2503_ = lean_nat_add(v_size_2481_, v___x_2502_);
lean_dec(v_size_2481_);
lean_inc(v_bkt_2497_);
v___x_2504_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2504_, 0, v_a_2479_);
lean_ctor_set(v___x_2504_, 1, v_b_2480_);
lean_ctor_set(v___x_2504_, 2, v_bkt_2497_);
v_buckets_x27_2505_ = lean_array_uset(v_buckets_2482_, v___x_2496_, v___x_2504_);
v___x_2506_ = lean_unsigned_to_nat(4u);
v___x_2507_ = lean_nat_mul(v_size_x27_2503_, v___x_2506_);
v___x_2508_ = lean_unsigned_to_nat(3u);
v___x_2509_ = lean_nat_div(v___x_2507_, v___x_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_array_get_size(v_buckets_x27_2505_);
v___x_2511_ = lean_nat_dec_le(v___x_2509_, v___x_2510_);
lean_dec(v___x_2509_);
if (v___x_2511_ == 0)
{
lean_object* v_val_2512_; lean_object* v___x_2514_; 
v_val_2512_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2505_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 1, v_val_2512_);
lean_ctor_set(v___x_2500_, 0, v_size_x27_2503_);
v___x_2514_ = v___x_2500_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_size_x27_2503_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_val_2512_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
else
{
lean_object* v___x_2517_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 1, v_buckets_x27_2505_);
lean_ctor_set(v___x_2500_, 0, v_size_x27_2503_);
v___x_2517_ = v___x_2500_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_size_x27_2503_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_buckets_x27_2505_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
else
{
lean_dec(v_b_2480_);
lean_dec(v_a_2479_);
return v_m_2478_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(lean_object* v_a_2522_, lean_object* v_b_2523_, lean_object* v_x_2524_){
_start:
{
if (lean_obj_tag(v_x_2524_) == 0)
{
lean_dec(v_b_2523_);
lean_dec(v_a_2522_);
return v_x_2524_;
}
else
{
lean_object* v_key_2525_; lean_object* v_value_2526_; lean_object* v_tail_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2539_; 
v_key_2525_ = lean_ctor_get(v_x_2524_, 0);
v_value_2526_ = lean_ctor_get(v_x_2524_, 1);
v_tail_2527_ = lean_ctor_get(v_x_2524_, 2);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_x_2524_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2529_ = v_x_2524_;
v_isShared_2530_ = v_isSharedCheck_2539_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_tail_2527_);
lean_inc(v_value_2526_);
lean_inc(v_key_2525_);
lean_dec(v_x_2524_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2539_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
uint8_t v___x_2531_; 
v___x_2531_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2525_, v_a_2522_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2532_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2522_, v_b_2523_, v_tail_2527_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 2, v___x_2532_);
v___x_2534_ = v___x_2529_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_key_2525_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_value_2526_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
else
{
lean_object* v___x_2537_; 
lean_dec(v_value_2526_);
lean_dec(v_key_2525_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v_b_2523_);
lean_ctor_set(v___x_2529_, 0, v_a_2522_);
v___x_2537_ = v___x_2529_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2522_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_b_2523_);
lean_ctor_set(v_reuseFailAlloc_2538_, 2, v_tail_2527_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(lean_object* v_m_2540_, lean_object* v_a_2541_, lean_object* v_b_2542_){
_start:
{
lean_object* v_size_2543_; lean_object* v_buckets_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2588_; 
v_size_2543_ = lean_ctor_get(v_m_2540_, 0);
v_buckets_2544_ = lean_ctor_get(v_m_2540_, 1);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_m_2540_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2546_ = v_m_2540_;
v_isShared_2547_ = v_isSharedCheck_2588_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_buckets_2544_);
lean_inc(v_size_2543_);
lean_dec(v_m_2540_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2588_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; uint64_t v___x_2549_; uint64_t v___x_2550_; uint64_t v___x_2551_; uint64_t v___x_2552_; uint64_t v_fold_2553_; uint64_t v___x_2554_; uint64_t v___x_2555_; uint64_t v___x_2556_; size_t v___x_2557_; size_t v___x_2558_; size_t v___x_2559_; size_t v___x_2560_; size_t v___x_2561_; lean_object* v_bkt_2562_; uint8_t v___x_2563_; 
v___x_2548_ = lean_array_get_size(v_buckets_2544_);
v___x_2549_ = 7ULL;
v___x_2550_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2549_, v_a_2541_);
v___x_2551_ = 32ULL;
v___x_2552_ = lean_uint64_shift_right(v___x_2550_, v___x_2551_);
v_fold_2553_ = lean_uint64_xor(v___x_2550_, v___x_2552_);
v___x_2554_ = 16ULL;
v___x_2555_ = lean_uint64_shift_right(v_fold_2553_, v___x_2554_);
v___x_2556_ = lean_uint64_xor(v_fold_2553_, v___x_2555_);
v___x_2557_ = lean_uint64_to_usize(v___x_2556_);
v___x_2558_ = lean_usize_of_nat(v___x_2548_);
v___x_2559_ = ((size_t)1ULL);
v___x_2560_ = lean_usize_sub(v___x_2558_, v___x_2559_);
v___x_2561_ = lean_usize_land(v___x_2557_, v___x_2560_);
v_bkt_2562_ = lean_array_uget_borrowed(v_buckets_2544_, v___x_2561_);
v___x_2563_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2541_, v_bkt_2562_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v_size_x27_2565_; lean_object* v___x_2566_; lean_object* v_buckets_x27_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2564_ = lean_unsigned_to_nat(1u);
v_size_x27_2565_ = lean_nat_add(v_size_2543_, v___x_2564_);
lean_dec(v_size_2543_);
lean_inc(v_bkt_2562_);
v___x_2566_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2566_, 0, v_a_2541_);
lean_ctor_set(v___x_2566_, 1, v_b_2542_);
lean_ctor_set(v___x_2566_, 2, v_bkt_2562_);
v_buckets_x27_2567_ = lean_array_uset(v_buckets_2544_, v___x_2561_, v___x_2566_);
v___x_2568_ = lean_unsigned_to_nat(4u);
v___x_2569_ = lean_nat_mul(v_size_x27_2565_, v___x_2568_);
v___x_2570_ = lean_unsigned_to_nat(3u);
v___x_2571_ = lean_nat_div(v___x_2569_, v___x_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_array_get_size(v_buckets_x27_2567_);
v___x_2573_ = lean_nat_dec_le(v___x_2571_, v___x_2572_);
lean_dec(v___x_2571_);
if (v___x_2573_ == 0)
{
lean_object* v_val_2574_; lean_object* v___x_2576_; 
v_val_2574_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2567_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 1, v_val_2574_);
lean_ctor_set(v___x_2546_, 0, v_size_x27_2565_);
v___x_2576_ = v___x_2546_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_size_x27_2565_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_val_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
else
{
lean_object* v___x_2579_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 1, v_buckets_x27_2567_);
lean_ctor_set(v___x_2546_, 0, v_size_x27_2565_);
v___x_2579_ = v___x_2546_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_size_x27_2565_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_buckets_x27_2567_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
else
{
lean_object* v___x_2581_; lean_object* v_buckets_x27_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
lean_inc(v_bkt_2562_);
v___x_2581_ = lean_box(0);
v_buckets_x27_2582_ = lean_array_uset(v_buckets_2544_, v___x_2561_, v___x_2581_);
v___x_2583_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2541_, v_b_2542_, v_bkt_2562_);
v___x_2584_ = lean_array_uset(v_buckets_x27_2582_, v___x_2561_, v___x_2583_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 1, v___x_2584_);
v___x_2586_ = v___x_2546_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_size_2543_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(lean_object* v_p_2589_, lean_object* v_x_2590_){
_start:
{
lean_object* v_coeffs_2591_; lean_object* v_constraint_2592_; lean_object* v_justification_2593_; uint8_t v___x_2594_; 
v_coeffs_2591_ = lean_ctor_get(v_x_2590_, 0);
lean_inc(v_coeffs_2591_);
v_constraint_2592_ = lean_ctor_get(v_x_2590_, 1);
lean_inc_ref(v_constraint_2592_);
v_justification_2593_ = lean_ctor_get(v_x_2590_, 2);
v___x_2594_ = l_Lean_Omega_Constraint_isImpossible(v_constraint_2592_);
if (v___x_2594_ == 0)
{
lean_object* v_assumptions_2595_; lean_object* v_numVars_2596_; lean_object* v_constraints_2597_; lean_object* v_equalities_2598_; lean_object* v_eliminations_2599_; uint8_t v_possible_2600_; lean_object* v_proveFalse_x3f_2601_; lean_object* v_explanation_x3f_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2620_; 
v_assumptions_2595_ = lean_ctor_get(v_p_2589_, 0);
v_numVars_2596_ = lean_ctor_get(v_p_2589_, 1);
v_constraints_2597_ = lean_ctor_get(v_p_2589_, 2);
v_equalities_2598_ = lean_ctor_get(v_p_2589_, 3);
v_eliminations_2599_ = lean_ctor_get(v_p_2589_, 4);
v_possible_2600_ = lean_ctor_get_uint8(v_p_2589_, sizeof(void*)*7);
v_proveFalse_x3f_2601_ = lean_ctor_get(v_p_2589_, 5);
v_explanation_x3f_2602_ = lean_ctor_get(v_p_2589_, 6);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_p_2589_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2604_ = v_p_2589_;
v_isShared_2605_ = v_isSharedCheck_2620_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_explanation_x3f_2602_);
lean_inc(v_proveFalse_x3f_2601_);
lean_inc(v_eliminations_2599_);
lean_inc(v_equalities_2598_);
lean_inc(v_constraints_2597_);
lean_inc(v_numVars_2596_);
lean_inc(v_assumptions_2595_);
lean_dec(v_p_2589_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2620_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___y_2607_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = l_List_lengthTR___redArg(v_coeffs_2591_);
v___x_2619_ = lean_nat_dec_le(v_numVars_2596_, v___x_2618_);
if (v___x_2619_ == 0)
{
lean_dec(v___x_2618_);
v___y_2607_ = v_numVars_2596_;
goto v___jp_2606_;
}
else
{
lean_dec(v_numVars_2596_);
v___y_2607_ = v___x_2618_;
goto v___jp_2606_;
}
v___jp_2606_:
{
lean_object* v___x_2608_; uint8_t v___x_2609_; 
lean_inc(v_coeffs_2591_);
v___x_2608_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_constraints_2597_, v_coeffs_2591_, v_x_2590_);
v___x_2609_ = l_Lean_Omega_Constraint_isExact(v_constraint_2592_);
lean_dec_ref(v_constraint_2592_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2611_; 
lean_dec(v_coeffs_2591_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 2, v___x_2608_);
lean_ctor_set(v___x_2604_, 1, v___y_2607_);
v___x_2611_ = v___x_2604_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_assumptions_2595_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v___y_2607_);
lean_ctor_set(v_reuseFailAlloc_2612_, 2, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2612_, 3, v_equalities_2598_);
lean_ctor_set(v_reuseFailAlloc_2612_, 4, v_eliminations_2599_);
lean_ctor_set(v_reuseFailAlloc_2612_, 5, v_proveFalse_x3f_2601_);
lean_ctor_set(v_reuseFailAlloc_2612_, 6, v_explanation_x3f_2602_);
lean_ctor_set_uint8(v_reuseFailAlloc_2612_, sizeof(void*)*7, v_possible_2600_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
else
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2616_; 
v___x_2613_ = lean_box(0);
v___x_2614_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_equalities_2598_, v_coeffs_2591_, v___x_2613_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 3, v___x_2614_);
lean_ctor_set(v___x_2604_, 2, v___x_2608_);
lean_ctor_set(v___x_2604_, 1, v___y_2607_);
v___x_2616_ = v___x_2604_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_assumptions_2595_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___y_2607_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2617_, 3, v___x_2614_);
lean_ctor_set(v_reuseFailAlloc_2617_, 4, v_eliminations_2599_);
lean_ctor_set(v_reuseFailAlloc_2617_, 5, v_proveFalse_x3f_2601_);
lean_ctor_set(v_reuseFailAlloc_2617_, 6, v_explanation_x3f_2602_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*7, v_possible_2600_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
else
{
lean_object* v_assumptions_2621_; lean_object* v_numVars_2622_; lean_object* v_constraints_2623_; lean_object* v_equalities_2624_; lean_object* v_eliminations_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2637_; 
lean_inc_ref(v_justification_2593_);
lean_dec_ref(v_x_2590_);
v_assumptions_2621_ = lean_ctor_get(v_p_2589_, 0);
v_numVars_2622_ = lean_ctor_get(v_p_2589_, 1);
v_constraints_2623_ = lean_ctor_get(v_p_2589_, 2);
v_equalities_2624_ = lean_ctor_get(v_p_2589_, 3);
v_eliminations_2625_ = lean_ctor_get(v_p_2589_, 4);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_p_2589_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; lean_object* v_unused_2639_; 
v_unused_2638_ = lean_ctor_get(v_p_2589_, 6);
lean_dec(v_unused_2638_);
v_unused_2639_ = lean_ctor_get(v_p_2589_, 5);
lean_dec(v_unused_2639_);
v___x_2627_ = v_p_2589_;
v_isShared_2628_ = v_isSharedCheck_2637_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_eliminations_2625_);
lean_inc(v_equalities_2624_);
lean_inc(v_constraints_2623_);
lean_inc(v_numVars_2622_);
lean_inc(v_assumptions_2621_);
lean_dec(v_p_2589_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2637_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___f_2629_; uint8_t v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
lean_inc_ref(v_justification_2593_);
lean_inc(v_coeffs_2591_);
lean_inc_ref(v_constraint_2592_);
v___f_2629_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0), 4, 3);
lean_closure_set(v___f_2629_, 0, v_constraint_2592_);
lean_closure_set(v___f_2629_, 1, v_coeffs_2591_);
lean_closure_set(v___f_2629_, 2, v_justification_2593_);
v___x_2630_ = 0;
lean_inc_ref(v_assumptions_2621_);
v___x_2631_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed), 14, 4);
lean_closure_set(v___x_2631_, 0, v_constraint_2592_);
lean_closure_set(v___x_2631_, 1, v_coeffs_2591_);
lean_closure_set(v___x_2631_, 2, v_justification_2593_);
lean_closure_set(v___x_2631_, 3, v_assumptions_2621_);
v___x_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
v___x_2633_ = lean_mk_thunk(v___f_2629_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 6, v___x_2633_);
lean_ctor_set(v___x_2627_, 5, v___x_2632_);
v___x_2635_ = v___x_2627_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_assumptions_2621_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_numVars_2622_);
lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_constraints_2623_);
lean_ctor_set(v_reuseFailAlloc_2636_, 3, v_equalities_2624_);
lean_ctor_set(v_reuseFailAlloc_2636_, 4, v_eliminations_2625_);
lean_ctor_set(v_reuseFailAlloc_2636_, 5, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2636_, 6, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*7, v___x_2630_);
return v___x_2635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0(lean_object* v_00_u03b2_2640_, lean_object* v_m_2641_, lean_object* v_a_2642_, lean_object* v_b_2643_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_m_2641_, v_a_2642_, v_b_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1(lean_object* v_00_u03b2_2645_, lean_object* v_m_2646_, lean_object* v_a_2647_, lean_object* v_b_2648_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_m_2646_, v_a_2647_, v_b_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_object* v_00_u03b2_2650_, lean_object* v_a_2651_, lean_object* v_x_2652_){
_start:
{
uint8_t v___x_2653_; 
v___x_2653_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2651_, v_x_2652_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2654_, lean_object* v_a_2655_, lean_object* v_x_2656_){
_start:
{
uint8_t v_res_2657_; lean_object* v_r_2658_; 
v_res_2657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(v_00_u03b2_2654_, v_a_2655_, v_x_2656_);
lean_dec(v_x_2656_);
lean_dec(v_a_2655_);
v_r_2658_ = lean_box(v_res_2657_);
return v_r_2658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2(lean_object* v_00_u03b2_2659_, lean_object* v_data_2660_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_data_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3(lean_object* v_00_u03b2_2662_, lean_object* v_a_2663_, lean_object* v_b_2664_, lean_object* v_x_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2663_, v_b_2664_, v_x_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2667_, lean_object* v_i_2668_, lean_object* v_source_2669_, lean_object* v_target_2670_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v_i_2668_, v_source_2669_, v_target_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2672_, lean_object* v_x_2673_, lean_object* v_x_2674_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_x_2673_, v_x_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(lean_object* v_a_2676_, lean_object* v_x_2677_){
_start:
{
if (lean_obj_tag(v_x_2677_) == 0)
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_box(0);
return v___x_2678_;
}
else
{
lean_object* v_key_2679_; lean_object* v_value_2680_; lean_object* v_tail_2681_; uint8_t v___x_2682_; 
v_key_2679_ = lean_ctor_get(v_x_2677_, 0);
v_value_2680_ = lean_ctor_get(v_x_2677_, 1);
v_tail_2681_ = lean_ctor_get(v_x_2677_, 2);
v___x_2682_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2679_, v_a_2676_);
if (v___x_2682_ == 0)
{
v_x_2677_ = v_tail_2681_;
goto _start;
}
else
{
lean_object* v___x_2684_; 
lean_inc(v_value_2680_);
v___x_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2684_, 0, v_value_2680_);
return v___x_2684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg___boxed(lean_object* v_a_2685_, lean_object* v_x_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2685_, v_x_2686_);
lean_dec(v_x_2686_);
lean_dec(v_a_2685_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(lean_object* v_m_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_buckets_2690_; lean_object* v___x_2691_; uint64_t v___x_2692_; uint64_t v___x_2693_; uint64_t v___x_2694_; uint64_t v___x_2695_; uint64_t v_fold_2696_; uint64_t v___x_2697_; uint64_t v___x_2698_; uint64_t v___x_2699_; size_t v___x_2700_; size_t v___x_2701_; size_t v___x_2702_; size_t v___x_2703_; size_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v_buckets_2690_ = lean_ctor_get(v_m_2688_, 1);
v___x_2691_ = lean_array_get_size(v_buckets_2690_);
v___x_2692_ = 7ULL;
v___x_2693_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2692_, v_a_2689_);
v___x_2694_ = 32ULL;
v___x_2695_ = lean_uint64_shift_right(v___x_2693_, v___x_2694_);
v_fold_2696_ = lean_uint64_xor(v___x_2693_, v___x_2695_);
v___x_2697_ = 16ULL;
v___x_2698_ = lean_uint64_shift_right(v_fold_2696_, v___x_2697_);
v___x_2699_ = lean_uint64_xor(v_fold_2696_, v___x_2698_);
v___x_2700_ = lean_uint64_to_usize(v___x_2699_);
v___x_2701_ = lean_usize_of_nat(v___x_2691_);
v___x_2702_ = ((size_t)1ULL);
v___x_2703_ = lean_usize_sub(v___x_2701_, v___x_2702_);
v___x_2704_ = lean_usize_land(v___x_2700_, v___x_2703_);
v___x_2705_ = lean_array_uget_borrowed(v_buckets_2690_, v___x_2704_);
v___x_2706_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2689_, v___x_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg___boxed(lean_object* v_m_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2707_, v_a_2708_);
lean_dec(v_a_2708_);
lean_dec_ref(v_m_2707_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addConstraint(lean_object* v_p_2710_, lean_object* v_x_2711_){
_start:
{
uint8_t v_possible_2712_; 
v_possible_2712_ = lean_ctor_get_uint8(v_p_2710_, sizeof(void*)*7);
if (v_possible_2712_ == 0)
{
lean_dec_ref(v_x_2711_);
return v_p_2710_;
}
else
{
lean_object* v_coeffs_2713_; lean_object* v_constraint_2714_; lean_object* v_justification_2715_; lean_object* v_constraints_2716_; lean_object* v___x_2717_; 
v_coeffs_2713_ = lean_ctor_get(v_x_2711_, 0);
v_constraint_2714_ = lean_ctor_get(v_x_2711_, 1);
v_justification_2715_ = lean_ctor_get(v_x_2711_, 2);
v_constraints_2716_ = lean_ctor_get(v_p_2710_, 2);
v___x_2717_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2716_, v_coeffs_2713_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_lowerBound_2718_; 
v_lowerBound_2718_ = lean_ctor_get(v_constraint_2714_, 0);
if (lean_obj_tag(v_lowerBound_2718_) == 0)
{
lean_object* v_upperBound_2719_; 
v_upperBound_2719_ = lean_ctor_get(v_constraint_2714_, 1);
if (lean_obj_tag(v_upperBound_2719_) == 0)
{
lean_dec_ref(v_x_2711_);
return v_p_2710_;
}
else
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2710_, v_x_2711_);
return v___x_2720_;
}
}
else
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2710_, v_x_2711_);
return v___x_2721_;
}
}
else
{
lean_object* v_val_2722_; lean_object* v_coeffs_2723_; lean_object* v_constraint_2724_; lean_object* v_justification_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2740_; 
v_val_2722_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_val_2722_);
lean_dec_ref_known(v___x_2717_, 1);
v_coeffs_2723_ = lean_ctor_get(v_val_2722_, 0);
v_constraint_2724_ = lean_ctor_get(v_val_2722_, 1);
v_justification_2725_ = lean_ctor_get(v_val_2722_, 2);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_val_2722_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2727_ = v_val_2722_;
v_isShared_2728_ = v_isSharedCheck_2740_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_justification_2725_);
lean_inc(v_constraint_2724_);
lean_inc(v_coeffs_2723_);
lean_dec(v_val_2722_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2740_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___x_2729_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc(v_coeffs_2713_);
v___x_2730_ = l_instDecidableEqList___redArg(v___x_2729_, v_coeffs_2713_, v_coeffs_2723_);
if (v___x_2730_ == 0)
{
lean_del_object(v___x_2727_);
lean_dec_ref(v_justification_2725_);
lean_dec_ref(v_constraint_2724_);
lean_dec_ref(v_x_2711_);
return v_p_2710_;
}
else
{
lean_object* v_r_2731_; uint8_t v___x_2732_; 
lean_inc_ref_n(v_constraint_2724_, 2);
lean_inc_ref(v_constraint_2714_);
v_r_2731_ = l_Lean_Omega_Constraint_combine(v_constraint_2714_, v_constraint_2724_);
lean_inc_ref(v_r_2731_);
v___x_2732_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2731_, v_constraint_2724_);
if (v___x_2732_ == 0)
{
uint8_t v___x_2733_; 
lean_inc_ref(v_constraint_2714_);
lean_inc_ref(v_r_2731_);
v___x_2733_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2731_, v_constraint_2714_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
lean_inc_ref(v_justification_2715_);
lean_inc_ref(v_constraint_2714_);
lean_inc_n(v_coeffs_2713_, 2);
lean_dec_ref(v_x_2711_);
v___x_2734_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_2734_, 0, v_constraint_2714_);
lean_ctor_set(v___x_2734_, 1, v_constraint_2724_);
lean_ctor_set(v___x_2734_, 2, v_coeffs_2713_);
lean_ctor_set(v___x_2734_, 3, v_justification_2715_);
lean_ctor_set(v___x_2734_, 4, v_justification_2725_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 2, v___x_2734_);
lean_ctor_set(v___x_2727_, 1, v_r_2731_);
lean_ctor_set(v___x_2727_, 0, v_coeffs_2713_);
v___x_2736_ = v___x_2727_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_coeffs_2713_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_r_2731_);
lean_ctor_set(v_reuseFailAlloc_2738_, 2, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2710_, v___x_2736_);
return v___x_2737_;
}
}
else
{
lean_object* v___x_2739_; 
lean_dec_ref(v_r_2731_);
lean_del_object(v___x_2727_);
lean_dec_ref(v_justification_2725_);
lean_dec_ref(v_constraint_2724_);
v___x_2739_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2710_, v_x_2711_);
return v___x_2739_;
}
}
else
{
lean_dec_ref(v_r_2731_);
lean_del_object(v___x_2727_);
lean_dec_ref(v_justification_2725_);
lean_dec_ref(v_constraint_2724_);
lean_dec_ref(v_x_2711_);
return v_p_2710_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(lean_object* v_00_u03b2_2741_, lean_object* v_m_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2742_, v_a_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___boxed(lean_object* v_00_u03b2_2745_, lean_object* v_m_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(v_00_u03b2_2745_, v_m_2746_, v_a_2747_);
lean_dec(v_a_2747_);
lean_dec_ref(v_m_2746_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(lean_object* v_00_u03b2_2749_, lean_object* v_a_2750_, lean_object* v_x_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2750_, v_x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2753_, lean_object* v_a_2754_, lean_object* v_x_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(v_00_u03b2_2753_, v_a_2754_, v_x_2755_);
lean_dec(v_x_2755_);
lean_dec(v_a_2754_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(lean_object* v_x_2757_, lean_object* v_x_2758_){
_start:
{
if (lean_obj_tag(v_x_2758_) == 0)
{
return v_x_2757_;
}
else
{
if (lean_obj_tag(v_x_2757_) == 0)
{
lean_object* v_key_2759_; lean_object* v_tail_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v_key_2759_ = lean_ctor_get(v_x_2758_, 0);
lean_inc_n(v_key_2759_, 2);
v_tail_2760_ = lean_ctor_get(v_x_2758_, 2);
lean_inc(v_tail_2760_);
lean_dec_ref_known(v_x_2758_, 3);
v___x_2761_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2759_);
v___x_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2762_, 0, v_key_2759_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
v_x_2757_ = v___x_2763_;
v_x_2758_ = v_tail_2760_;
goto _start;
}
else
{
lean_object* v_val_2765_; lean_object* v_key_2766_; lean_object* v_tail_2767_; lean_object* v_fst_2768_; lean_object* v_snd_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2790_; 
v_val_2765_ = lean_ctor_get(v_x_2757_, 0);
lean_inc(v_val_2765_);
v_key_2766_ = lean_ctor_get(v_x_2758_, 0);
lean_inc(v_key_2766_);
v_tail_2767_ = lean_ctor_get(v_x_2758_, 2);
lean_inc(v_tail_2767_);
lean_dec_ref_known(v_x_2758_, 3);
v_fst_2768_ = lean_ctor_get(v_val_2765_, 0);
v_snd_2769_ = lean_ctor_get(v_val_2765_, 1);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_val_2765_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2771_ = v_val_2765_;
v_isShared_2772_ = v_isSharedCheck_2790_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_snd_2769_);
lean_inc(v_fst_2768_);
lean_dec(v_val_2765_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2790_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; uint8_t v___x_2774_; 
v___x_2773_ = lean_unsigned_to_nat(2u);
v___x_2774_ = lean_nat_dec_le(v___x_2773_, v_snd_2769_);
if (v___x_2774_ == 0)
{
lean_del_object(v___x_2771_);
lean_dec(v_snd_2769_);
lean_dec(v_fst_2768_);
lean_dec(v_key_2766_);
v_x_2758_ = v_tail_2767_;
goto _start;
}
else
{
lean_object* v_m_x27_2776_; uint8_t v___x_2783_; 
lean_inc(v_key_2766_);
v_m_x27_2776_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2766_);
v___x_2783_ = lean_nat_dec_lt(v_m_x27_2776_, v_snd_2769_);
if (v___x_2783_ == 0)
{
uint8_t v___x_2784_; 
v___x_2784_ = lean_nat_dec_eq(v_m_x27_2776_, v_snd_2769_);
lean_dec(v_snd_2769_);
if (v___x_2784_ == 0)
{
lean_dec(v_m_x27_2776_);
lean_del_object(v___x_2771_);
lean_dec(v_fst_2768_);
lean_dec(v_key_2766_);
v_x_2758_ = v_tail_2767_;
goto _start;
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
lean_inc(v_key_2766_);
v___x_2786_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_key_2766_);
v___x_2787_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_fst_2768_);
v___x_2788_ = lean_nat_dec_lt(v___x_2786_, v___x_2787_);
lean_dec(v___x_2787_);
lean_dec(v___x_2786_);
if (v___x_2788_ == 0)
{
lean_dec(v_m_x27_2776_);
lean_del_object(v___x_2771_);
lean_dec(v_key_2766_);
v_x_2758_ = v_tail_2767_;
goto _start;
}
else
{
lean_dec_ref_known(v_x_2757_, 1);
goto v___jp_2777_;
}
}
}
else
{
lean_dec(v_snd_2769_);
lean_dec(v_fst_2768_);
lean_dec_ref_known(v_x_2757_, 1);
goto v___jp_2777_;
}
v___jp_2777_:
{
lean_object* v___x_2779_; 
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 1, v_m_x27_2776_);
lean_ctor_set(v___x_2771_, 0, v_key_2766_);
v___x_2779_ = v___x_2771_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_key_2766_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_m_x27_2776_);
v___x_2779_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
v_x_2757_ = v___x_2780_;
v_x_2758_ = v_tail_2767_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(lean_object* v_as_2791_, size_t v_i_2792_, size_t v_stop_2793_, lean_object* v_b_2794_){
_start:
{
uint8_t v___x_2795_; 
v___x_2795_ = lean_usize_dec_eq(v_i_2792_, v_stop_2793_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; lean_object* v___x_2797_; size_t v___x_2798_; size_t v___x_2799_; 
v___x_2796_ = lean_array_uget_borrowed(v_as_2791_, v_i_2792_);
lean_inc(v___x_2796_);
v___x_2797_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(v_b_2794_, v___x_2796_);
v___x_2798_ = ((size_t)1ULL);
v___x_2799_ = lean_usize_add(v_i_2792_, v___x_2798_);
v_i_2792_ = v___x_2799_;
v_b_2794_ = v___x_2797_;
goto _start;
}
else
{
return v_b_2794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1___boxed(lean_object* v_as_2801_, lean_object* v_i_2802_, lean_object* v_stop_2803_, lean_object* v_b_2804_){
_start:
{
size_t v_i_boxed_2805_; size_t v_stop_boxed_2806_; lean_object* v_res_2807_; 
v_i_boxed_2805_ = lean_unbox_usize(v_i_2802_);
lean_dec(v_i_2802_);
v_stop_boxed_2806_ = lean_unbox_usize(v_stop_2803_);
lean_dec(v_stop_2803_);
v_res_2807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_as_2801_, v_i_boxed_2805_, v_stop_boxed_2806_, v_b_2804_);
lean_dec_ref(v_as_2801_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality(lean_object* v_p_2808_){
_start:
{
lean_object* v_equalities_2809_; lean_object* v_buckets_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; 
v_equalities_2809_ = lean_ctor_get(v_p_2808_, 3);
v_buckets_2810_ = lean_ctor_get(v_equalities_2809_, 1);
v___x_2811_ = lean_box(0);
v___x_2812_ = lean_unsigned_to_nat(0u);
v___x_2813_ = lean_array_get_size(v_buckets_2810_);
v___x_2814_ = lean_nat_dec_lt(v___x_2812_, v___x_2813_);
if (v___x_2814_ == 0)
{
return v___x_2811_;
}
else
{
size_t v___x_2815_; size_t v___x_2816_; lean_object* v___x_2817_; 
v___x_2815_ = ((size_t)0ULL);
v___x_2816_ = lean_usize_of_nat(v___x_2813_);
v___x_2817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2810_, v___x_2815_, v___x_2816_, v___x_2811_);
return v___x_2817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality___boxed(lean_object* v_p_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_2818_);
lean_dec_ref(v_p_2818_);
return v_res_2819_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = lean_unsigned_to_nat(1u);
v___x_2821_ = lean_nat_to_int(v___x_2820_);
return v___x_2821_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2823_ = lean_int_neg(v___x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(lean_object* v_as_2824_, size_t v_i_2825_, size_t v_stop_2826_, lean_object* v_b_2827_){
_start:
{
uint8_t v___x_2828_; 
v___x_2828_ = lean_usize_dec_eq(v_i_2825_, v_stop_2826_);
if (v___x_2828_ == 0)
{
size_t v___x_2829_; size_t v___x_2830_; lean_object* v___x_2831_; lean_object* v_snd_2832_; lean_object* v_fst_2833_; lean_object* v_fst_2834_; lean_object* v_snd_2835_; lean_object* v_coeffs_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2829_ = ((size_t)1ULL);
v___x_2830_ = lean_usize_sub(v_i_2825_, v___x_2829_);
v___x_2831_ = lean_array_uget_borrowed(v_as_2824_, v___x_2830_);
v_snd_2832_ = lean_ctor_get(v___x_2831_, 1);
v_fst_2833_ = lean_ctor_get(v___x_2831_, 0);
v_fst_2834_ = lean_ctor_get(v_snd_2832_, 0);
v_snd_2835_ = lean_ctor_get(v_snd_2832_, 1);
v_coeffs_2836_ = lean_ctor_get(v_b_2827_, 0);
lean_inc(v_fst_2834_);
v___x_2837_ = l_Lean_Omega_IntList_get(v_coeffs_2836_, v_fst_2834_);
v___x_2838_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2839_ = lean_int_dec_eq(v___x_2837_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2840_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2841_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2842_ = lean_int_mul(v___x_2841_, v_snd_2835_);
v___x_2843_ = lean_int_mul(v___x_2842_, v___x_2837_);
lean_dec(v___x_2837_);
lean_dec(v___x_2842_);
lean_inc(v_fst_2833_);
v___x_2844_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v___x_2843_, v_fst_2833_, v___x_2840_, v_b_2827_);
v_i_2825_ = v___x_2830_;
v_b_2827_ = v___x_2844_;
goto _start;
}
else
{
lean_dec(v___x_2837_);
v_i_2825_ = v___x_2830_;
goto _start;
}
}
else
{
return v_b_2827_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___boxed(lean_object* v_as_2847_, lean_object* v_i_2848_, lean_object* v_stop_2849_, lean_object* v_b_2850_){
_start:
{
size_t v_i_boxed_2851_; size_t v_stop_boxed_2852_; lean_object* v_res_2853_; 
v_i_boxed_2851_ = lean_unbox_usize(v_i_2848_);
lean_dec(v_i_2848_);
v_stop_boxed_2852_ = lean_unbox_usize(v_stop_2849_);
lean_dec(v_stop_2849_);
v_res_2853_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v_as_2847_, v_i_boxed_2851_, v_stop_boxed_2852_, v_b_2850_);
lean_dec_ref(v_as_2847_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(lean_object* v_init_2854_, lean_object* v_l_2855_){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2856_ = lean_array_mk(v_l_2855_);
v___x_2857_ = lean_array_get_size(v___x_2856_);
v___x_2858_ = lean_unsigned_to_nat(0u);
v___x_2859_ = lean_nat_dec_lt(v___x_2858_, v___x_2857_);
if (v___x_2859_ == 0)
{
lean_dec_ref(v___x_2856_);
return v_init_2854_;
}
else
{
size_t v___x_2860_; size_t v___x_2861_; lean_object* v___x_2862_; 
v___x_2860_ = lean_usize_of_nat(v___x_2857_);
v___x_2861_ = ((size_t)0ULL);
v___x_2862_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(v___x_2856_, v___x_2860_, v___x_2861_, v_init_2854_);
lean_dec_ref(v___x_2856_);
return v___x_2862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(lean_object* v_p_2863_, lean_object* v_f_2864_){
_start:
{
lean_object* v_eliminations_2865_; lean_object* v___x_2866_; 
v_eliminations_2865_ = lean_ctor_get(v_p_2863_, 4);
lean_inc(v_eliminations_2865_);
lean_dec_ref(v_p_2863_);
v___x_2866_ = l_List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0(v_f_2864_, v_eliminations_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___lam__0(lean_object* v_x_2867_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(lean_object* v___y_2869_, lean_object* v_sign_2870_, lean_object* v_val_2871_, lean_object* v_x_2872_, lean_object* v_x_2873_){
_start:
{
if (lean_obj_tag(v_x_2873_) == 0)
{
lean_dec_ref(v_val_2871_);
lean_dec(v___y_2869_);
return v_x_2872_;
}
else
{
lean_object* v_key_2874_; lean_object* v_value_2875_; lean_object* v_tail_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; 
v_key_2874_ = lean_ctor_get(v_x_2873_, 0);
lean_inc(v_key_2874_);
v_value_2875_ = lean_ctor_get(v_x_2873_, 1);
lean_inc(v_value_2875_);
v_tail_2876_ = lean_ctor_get(v_x_2873_, 2);
lean_inc(v_tail_2876_);
lean_dec_ref_known(v_x_2873_, 3);
lean_inc(v___y_2869_);
v___x_2877_ = l_Lean_Omega_IntList_get(v_key_2874_, v___y_2869_);
lean_dec(v_key_2874_);
v___x_2878_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2879_ = lean_int_dec_eq(v___x_2877_, v___x_2878_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v_k_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2880_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2881_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2882_ = lean_int_mul(v___x_2881_, v_sign_2870_);
v_k_2883_ = lean_int_mul(v___x_2882_, v___x_2877_);
lean_dec(v___x_2877_);
lean_dec(v___x_2882_);
lean_inc_ref(v_val_2871_);
v___x_2884_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_k_2883_, v_val_2871_, v___x_2880_, v_value_2875_);
v___x_2885_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_2884_);
v___x_2886_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2872_, v___x_2885_);
v_x_2872_ = v___x_2886_;
v_x_2873_ = v_tail_2876_;
goto _start;
}
else
{
lean_object* v___x_2888_; 
lean_dec(v___x_2877_);
v___x_2888_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2872_, v_value_2875_);
v_x_2872_ = v___x_2888_;
v_x_2873_ = v_tail_2876_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0___boxed(lean_object* v___y_2890_, lean_object* v_sign_2891_, lean_object* v_val_2892_, lean_object* v_x_2893_, lean_object* v_x_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2890_, v_sign_2891_, v_val_2892_, v_x_2893_, v_x_2894_);
lean_dec(v_sign_2891_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object* v___y_2896_, lean_object* v_sign_2897_, lean_object* v_val_2898_, lean_object* v_as_2899_, size_t v_i_2900_, size_t v_stop_2901_, lean_object* v_b_2902_){
_start:
{
uint8_t v___x_2903_; 
v___x_2903_ = lean_usize_dec_eq(v_i_2900_, v_stop_2901_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; lean_object* v___x_2905_; size_t v___x_2906_; size_t v___x_2907_; 
v___x_2904_ = lean_array_uget_borrowed(v_as_2899_, v_i_2900_);
lean_inc(v___x_2904_);
lean_inc_ref(v_val_2898_);
lean_inc(v___y_2896_);
v___x_2905_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2896_, v_sign_2897_, v_val_2898_, v_b_2902_, v___x_2904_);
v___x_2906_ = ((size_t)1ULL);
v___x_2907_ = lean_usize_add(v_i_2900_, v___x_2906_);
v_i_2900_ = v___x_2907_;
v_b_2902_ = v___x_2905_;
goto _start;
}
else
{
lean_dec_ref(v_val_2898_);
lean_dec(v___y_2896_);
return v_b_2902_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1___boxed(lean_object* v___y_2909_, lean_object* v_sign_2910_, lean_object* v_val_2911_, lean_object* v_as_2912_, lean_object* v_i_2913_, lean_object* v_stop_2914_, lean_object* v_b_2915_){
_start:
{
size_t v_i_boxed_2916_; size_t v_stop_boxed_2917_; lean_object* v_res_2918_; 
v_i_boxed_2916_ = lean_unbox_usize(v_i_2913_);
lean_dec(v_i_2913_);
v_stop_boxed_2917_ = lean_unbox_usize(v_stop_2914_);
lean_dec(v_stop_2914_);
v_res_2918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2909_, v_sign_2910_, v_val_2911_, v_as_2912_, v_i_boxed_2916_, v_stop_boxed_2917_, v_b_2915_);
lean_dec_ref(v_as_2912_);
lean_dec(v_sign_2910_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
if (lean_obj_tag(v_a_2919_) == 0)
{
lean_object* v___x_2921_; 
lean_dec(v_a_2920_);
v___x_2921_ = lean_box(0);
return v___x_2921_;
}
else
{
lean_object* v_head_2922_; lean_object* v_tail_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v_head_2922_ = lean_ctor_get(v_a_2919_, 0);
v_tail_2923_ = lean_ctor_get(v_a_2919_, 1);
v___x_2924_ = lean_nat_abs(v_head_2922_);
v___x_2925_ = lean_unsigned_to_nat(1u);
v___x_2926_ = lean_nat_dec_eq(v___x_2924_, v___x_2925_);
lean_dec(v___x_2924_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_nat_add(v_a_2920_, v___x_2925_);
lean_dec(v_a_2920_);
v_a_2919_ = v_tail_2923_;
v_a_2920_ = v___x_2927_;
goto _start;
}
else
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2929_, 0, v_a_2920_);
return v___x_2929_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2___boxed(lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(v_a_2930_, v_a_2931_);
lean_dec(v_a_2930_);
return v_res_2932_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = lean_box(0);
v___x_2935_ = lean_unsigned_to_nat(16u);
v___x_2936_ = lean_mk_array(v___x_2935_, v___x_2934_);
return v___x_2936_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2937_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1);
v___x_2938_ = lean_unsigned_to_nat(0u);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
lean_ctor_set(v___x_2939_, 1, v___x_2937_);
return v___x_2939_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3(void){
_start:
{
lean_object* v___f_2940_; lean_object* v___x_2941_; 
v___f_2940_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0));
v___x_2941_ = lean_mk_thunk(v___f_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(lean_object* v_p_2942_, lean_object* v_c_2943_){
_start:
{
lean_object* v___y_2945_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = lean_unsigned_to_nat(0u);
v___x_2989_ = l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(v_c_2943_, v___x_2988_);
if (lean_obj_tag(v___x_2989_) == 0)
{
v___y_2945_ = v___x_2988_;
goto v___jp_2944_;
}
else
{
lean_object* v_val_2990_; 
v_val_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_val_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___y_2945_ = v_val_2990_;
goto v___jp_2944_;
}
v___jp_2944_:
{
lean_object* v_assumptions_2946_; lean_object* v_constraints_2947_; lean_object* v_eliminations_2948_; lean_object* v___x_2949_; 
v_assumptions_2946_ = lean_ctor_get(v_p_2942_, 0);
v_constraints_2947_ = lean_ctor_get(v_p_2942_, 2);
lean_inc_ref(v_constraints_2947_);
v_eliminations_2948_ = lean_ctor_get(v_p_2942_, 4);
v___x_2949_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2947_, v_c_2943_);
if (lean_obj_tag(v___x_2949_) == 1)
{
lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2980_; 
lean_inc(v_eliminations_2948_);
lean_inc_ref(v_assumptions_2946_);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_p_2942_);
if (v_isSharedCheck_2980_ == 0)
{
lean_object* v_unused_2981_; lean_object* v_unused_2982_; lean_object* v_unused_2983_; lean_object* v_unused_2984_; lean_object* v_unused_2985_; lean_object* v_unused_2986_; lean_object* v_unused_2987_; 
v_unused_2981_ = lean_ctor_get(v_p_2942_, 6);
lean_dec(v_unused_2981_);
v_unused_2982_ = lean_ctor_get(v_p_2942_, 5);
lean_dec(v_unused_2982_);
v_unused_2983_ = lean_ctor_get(v_p_2942_, 4);
lean_dec(v_unused_2983_);
v_unused_2984_ = lean_ctor_get(v_p_2942_, 3);
lean_dec(v_unused_2984_);
v_unused_2985_ = lean_ctor_get(v_p_2942_, 2);
lean_dec(v_unused_2985_);
v_unused_2986_ = lean_ctor_get(v_p_2942_, 1);
lean_dec(v_unused_2986_);
v_unused_2987_ = lean_ctor_get(v_p_2942_, 0);
lean_dec(v_unused_2987_);
v___x_2951_ = v_p_2942_;
v_isShared_2952_ = v_isSharedCheck_2980_;
goto v_resetjp_2950_;
}
else
{
lean_dec(v_p_2942_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2980_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v_val_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v_buckets_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2978_; 
v_val_2953_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_val_2953_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2954_ = lean_unsigned_to_nat(0u);
v___x_2955_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v_buckets_2956_ = lean_ctor_get(v_constraints_2947_, 1);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_constraints_2947_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; 
v_unused_2979_ = lean_ctor_get(v_constraints_2947_, 0);
lean_dec(v_unused_2979_);
v___x_2958_ = v_constraints_2947_;
v_isShared_2959_ = v_isSharedCheck_2978_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_buckets_2956_);
lean_dec(v_constraints_2947_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2978_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; lean_object* v_sign_2961_; lean_object* v___x_2963_; 
lean_inc_n(v___y_2945_, 2);
v___x_2960_ = l_Lean_Omega_IntList_get(v_c_2943_, v___y_2945_);
v_sign_2961_ = l_Int_sign(v___x_2960_);
lean_dec(v___x_2960_);
lean_inc(v_sign_2961_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 1, v_sign_2961_);
lean_ctor_set(v___x_2958_, 0, v___y_2945_);
v___x_2963_ = v___x_2958_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___y_2945_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_sign_2961_);
v___x_2963_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v_init_2970_; 
lean_inc(v_val_2953_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v_val_2953_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v_eliminations_2948_);
v___x_2966_ = 1;
v___x_2967_ = lean_box(0);
v___x_2968_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 6, v___x_2968_);
lean_ctor_set(v___x_2951_, 5, v___x_2967_);
lean_ctor_set(v___x_2951_, 4, v___x_2965_);
lean_ctor_set(v___x_2951_, 3, v___x_2955_);
lean_ctor_set(v___x_2951_, 2, v___x_2955_);
lean_ctor_set(v___x_2951_, 1, v___x_2954_);
v_init_2970_ = v___x_2951_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_assumptions_2946_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_2976_, 5, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_2976_, 6, v___x_2968_);
v_init_2970_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
lean_ctor_set_uint8(v_init_2970_, sizeof(void*)*7, v___x_2966_);
v___x_2971_ = lean_array_get_size(v_buckets_2956_);
v___x_2972_ = lean_nat_dec_lt(v___x_2954_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_dec(v_sign_2961_);
lean_dec_ref(v_buckets_2956_);
lean_dec(v_val_2953_);
lean_dec(v___y_2945_);
return v_init_2970_;
}
else
{
size_t v___x_2973_; size_t v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = ((size_t)0ULL);
v___x_2974_ = lean_usize_of_nat(v___x_2971_);
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2945_, v_sign_2961_, v_val_2953_, v_buckets_2956_, v___x_2973_, v___x_2974_, v_init_2970_);
lean_dec_ref(v_buckets_2956_);
lean_dec(v_sign_2961_);
return v___x_2975_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2949_);
lean_dec_ref(v_constraints_2947_);
lean_dec(v___y_2945_);
return v_p_2942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___boxed(lean_object* v_p_2991_, lean_object* v_c_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_2991_, v_c_2992_);
lean_dec(v_c_2992_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(lean_object* v_msgData_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v___x_3000_; lean_object* v_env_3001_; uint8_t v___x_3002_; lean_object* v_env_3003_; lean_object* v___x_3004_; lean_object* v_toCold_3005_; lean_object* v_mctx_3006_; lean_object* v_lctx_3007_; lean_object* v_options_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3000_ = lean_st_ref_get(v___y_2998_);
v_env_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc_ref(v_env_3001_);
lean_dec(v___x_3000_);
v___x_3002_ = 0;
v_env_3003_ = l_Lean_Environment_setRecordingDeps(v_env_3001_, v___x_3002_);
v___x_3004_ = lean_st_ref_get(v___y_2996_);
v_toCold_3005_ = lean_ctor_get(v___y_2997_, 0);
v_mctx_3006_ = lean_ctor_get(v___x_3004_, 0);
lean_inc_ref(v_mctx_3006_);
lean_dec(v___x_3004_);
v_lctx_3007_ = lean_ctor_get(v___y_2995_, 2);
v_options_3008_ = lean_ctor_get(v_toCold_3005_, 2);
lean_inc_ref(v_options_3008_);
lean_inc_ref(v_lctx_3007_);
v___x_3009_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3009_, 0, v_env_3003_);
lean_ctor_set(v___x_3009_, 1, v_mctx_3006_);
lean_ctor_set(v___x_3009_, 2, v_lctx_3007_);
lean_ctor_set(v___x_3009_, 3, v_options_3008_);
v___x_3010_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v_msgData_2994_);
v___x_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0___boxed(lean_object* v_msgData_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msgData_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(lean_object* v_msg_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_ref_3025_; lean_object* v___x_3026_; lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3035_; 
v_ref_3025_ = lean_ctor_get(v___y_3022_, 2);
v___x_3026_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3029_ = v___x_3026_;
v_isShared_3030_ = v_isSharedCheck_3035_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3026_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3035_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; lean_object* v___x_3033_; 
lean_inc(v_ref_3025_);
v___x_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3031_, 0, v_ref_3025_);
lean_ctor_set(v___x_3031_, 1, v_a_3027_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set_tag(v___x_3029_, 1);
lean_ctor_set(v___x_3029_, 0, v___x_3031_);
v___x_3033_ = v___x_3029_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3031_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg___boxed(lean_object* v_msg_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
return v_res_3042_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0));
v___x_3045_ = l_Lean_stringToMessageData(v___x_3044_);
return v___x_3045_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2));
v___x_3048_ = l_Lean_stringToMessageData(v___x_3047_);
return v___x_3048_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4));
v___x_3051_ = l_Lean_stringToMessageData(v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(lean_object* v_p_3052_, lean_object* v_c_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, uint8_t v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v_constraints_3064_; lean_object* v___x_3065_; 
v_constraints_3064_ = lean_ctor_get(v_p_3052_, 2);
v___x_3065_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_3064_, v_c_3053_);
if (lean_obj_tag(v___x_3065_) == 1)
{
lean_object* v_val_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3165_; 
v_val_3066_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3068_ = v___x_3065_;
v_isShared_3069_ = v_isSharedCheck_3165_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_val_3066_);
lean_dec(v___x_3065_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3165_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v_constraint_3070_; lean_object* v_lowerBound_3071_; 
v_constraint_3070_ = lean_ctor_get(v_val_3066_, 1);
v_lowerBound_3071_ = lean_ctor_get(v_constraint_3070_, 0);
lean_inc(v_lowerBound_3071_);
if (lean_obj_tag(v_lowerBound_3071_) == 1)
{
lean_object* v_upperBound_3072_; 
lean_del_object(v___x_3068_);
v_upperBound_3072_ = lean_ctor_get(v_constraint_3070_, 1);
lean_inc(v_upperBound_3072_);
if (lean_obj_tag(v_upperBound_3072_) == 1)
{
lean_object* v_coeffs_3073_; lean_object* v_justification_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3152_; 
v_coeffs_3073_ = lean_ctor_get(v_val_3066_, 0);
v_justification_3074_ = lean_ctor_get(v_val_3066_, 2);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_val_3066_);
if (v_isSharedCheck_3152_ == 0)
{
lean_object* v_unused_3153_; 
v_unused_3153_ = lean_ctor_get(v_val_3066_, 1);
lean_dec(v_unused_3153_);
v___x_3076_ = v_val_3066_;
v_isShared_3077_ = v_isSharedCheck_3152_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_justification_3074_);
lean_inc(v_coeffs_3073_);
lean_dec(v_val_3066_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3152_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v_val_3078_; lean_object* v_val_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v_m_3082_; lean_object* v___x_3083_; 
v_val_3078_ = lean_ctor_get(v_lowerBound_3071_, 0);
lean_inc(v_val_3078_);
lean_dec_ref_known(v_lowerBound_3071_, 1);
v_val_3079_ = lean_ctor_get(v_upperBound_3072_, 0);
lean_inc(v_val_3079_);
lean_dec_ref_known(v_upperBound_3072_, 1);
lean_inc(v_c_3053_);
v___x_3080_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_c_3053_);
v___x_3081_ = lean_unsigned_to_nat(1u);
v_m_3082_ = lean_nat_add(v___x_3080_, v___x_3081_);
lean_dec(v___x_3080_);
v___x_3083_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3055_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v_nil_3087_; lean_object* v_cons_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
v___x_3085_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc(v_m_3082_);
v___x_3086_ = l_Lean_mkNatLit(v_m_3082_);
v_nil_3087_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3088_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3089_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3087_, v_cons_3088_, v_c_3053_);
lean_dec(v_c_3053_);
v___x_3090_ = l_Lean_mkApp3(v___x_3085_, v___x_3086_, v___x_3089_, v_a_3084_);
v___x_3091_ = l_Lean_Elab_Tactic_Omega_lookup(v___x_3090_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3135_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3135_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3135_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v_fst_3096_; lean_object* v_snd_3097_; uint8_t v___x_3110_; 
v_fst_3096_ = lean_ctor_get(v_a_3092_, 0);
lean_inc(v_fst_3096_);
v_snd_3097_ = lean_ctor_get(v_a_3092_, 1);
lean_inc(v_snd_3097_);
lean_dec(v_a_3092_);
v___x_3110_ = lean_int_dec_eq(v_val_3079_, v_val_3078_);
lean_dec(v_val_3079_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_dec(v_snd_3097_);
lean_dec(v_fst_3096_);
lean_del_object(v___x_3094_);
lean_dec(v_m_3082_);
lean_dec(v_val_3078_);
lean_del_object(v___x_3076_);
lean_dec_ref(v_justification_3074_);
lean_dec(v_coeffs_3073_);
lean_dec_ref(v_p_3052_);
v___x_3111_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1);
v___x_3112_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3111_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3112_;
}
else
{
if (lean_obj_tag(v_snd_3097_) == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec(v_fst_3096_);
lean_del_object(v___x_3094_);
lean_dec(v_m_3082_);
lean_dec(v_val_3078_);
lean_del_object(v___x_3076_);
lean_dec_ref(v_justification_3074_);
lean_dec(v_coeffs_3073_);
lean_dec_ref(v_p_3052_);
v___x_3113_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3);
v___x_3114_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3113_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
else
{
lean_object* v_val_3123_; uint8_t v___x_3124_; 
v_val_3123_ = lean_ctor_get(v_snd_3097_, 0);
lean_inc(v_val_3123_);
lean_dec_ref_known(v_snd_3097_, 1);
v___x_3124_ = l_List_isEmpty___redArg(v_val_3123_);
lean_dec(v_val_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec(v_fst_3096_);
lean_del_object(v___x_3094_);
lean_dec(v_m_3082_);
lean_dec(v_val_3078_);
lean_del_object(v___x_3076_);
lean_dec_ref(v_justification_3074_);
lean_dec(v_coeffs_3073_);
lean_dec_ref(v_p_3052_);
v___x_3125_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5);
v___x_3126_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3125_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3126_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3126_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
else
{
goto v___jp_3098_;
}
}
}
v___jp_3098_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
lean_inc(v_coeffs_3073_);
lean_inc_n(v_m_3082_, 2);
v___x_3099_ = l_Lean_Omega_bmod__coeffs(v_m_3082_, v_fst_3096_, v_coeffs_3073_);
v___x_3100_ = l_Int_bmod(v_val_3078_, v_m_3082_);
v___x_3101_ = l_Lean_Omega_Constraint_exact(v___x_3100_);
v___x_3102_ = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(v___x_3102_, 0, v_m_3082_);
lean_ctor_set(v___x_3102_, 1, v_val_3078_);
lean_ctor_set(v___x_3102_, 2, v_fst_3096_);
lean_ctor_set(v___x_3102_, 3, v_coeffs_3073_);
lean_ctor_set(v___x_3102_, 4, v_justification_3074_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 2, v___x_3102_);
lean_ctor_set(v___x_3076_, 1, v___x_3101_);
lean_ctor_set(v___x_3076_, 0, v___x_3099_);
v___x_3104_ = v___x_3076_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3099_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3105_; lean_object* v___x_3107_; 
v___x_3105_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_3052_, v___x_3104_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3105_);
v___x_3107_ = v___x_3094_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3105_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec(v_m_3082_);
lean_dec(v_val_3079_);
lean_dec(v_val_3078_);
lean_del_object(v___x_3076_);
lean_dec_ref(v_justification_3074_);
lean_dec(v_coeffs_3073_);
lean_dec_ref(v_p_3052_);
v_a_3136_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3091_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3091_);
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
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_m_3082_);
lean_dec(v_val_3079_);
lean_dec(v_val_3078_);
lean_del_object(v___x_3076_);
lean_dec_ref(v_justification_3074_);
lean_dec(v_coeffs_3073_);
lean_dec(v_c_3053_);
lean_dec_ref(v_p_3052_);
v_a_3144_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3083_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3083_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
else
{
lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v_upperBound_3072_);
lean_dec(v_val_3066_);
lean_dec(v_c_3053_);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_lowerBound_3071_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; 
v_unused_3161_ = lean_ctor_get(v_lowerBound_3071_, 0);
lean_dec(v_unused_3161_);
v___x_3155_ = v_lowerBound_3071_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_dec(v_lowerBound_3071_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set_tag(v___x_3155_, 0);
lean_ctor_set(v___x_3155_, 0, v_p_3052_);
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_p_3052_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
else
{
lean_object* v___x_3163_; 
lean_dec(v_lowerBound_3071_);
lean_dec(v_val_3066_);
lean_dec(v_c_3053_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set_tag(v___x_3068_, 0);
lean_ctor_set(v___x_3068_, 0, v_p_3052_);
v___x_3163_ = v___x_3068_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_p_3052_);
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
else
{
lean_object* v___x_3166_; 
lean_dec(v___x_3065_);
lean_dec(v_c_3053_);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_p_3052_);
return v___x_3166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___boxed(lean_object* v_p_3167_, lean_object* v_c_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
uint8_t v_a_boxed_3179_; lean_object* v_res_3180_; 
v_a_boxed_3179_ = lean_unbox(v_a_3172_);
v_res_3180_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3167_, v_c_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_boxed_3179_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_a_3175_);
lean_dec_ref(v_a_3174_);
lean_dec(v_a_3173_);
lean_dec_ref(v_a_3171_);
lean_dec(v_a_3170_);
lean_dec(v_a_3169_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_object* v_00_u03b1_3181_, lean_object* v_msg_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, uint8_t v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3182_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___boxed(lean_object* v_00_u03b1_3194_, lean_object* v_msg_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
uint8_t v___y_8992__boxed_3206_; lean_object* v_res_3207_; 
v___y_8992__boxed_3206_ = lean_unbox(v___y_3199_);
v_res_3207_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(v_00_u03b1_3194_, v_msg_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_8992__boxed_3206_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec(v___y_3196_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality(lean_object* v_p_3208_, lean_object* v_c_3209_, lean_object* v_m_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, uint8_t v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v___x_3221_; uint8_t v___x_3222_; 
v___x_3221_ = lean_unsigned_to_nat(1u);
v___x_3222_ = lean_nat_dec_eq(v_m_3210_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; 
v___x_3223_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3208_, v_c_3209_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_);
return v___x_3223_;
}
else
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_3208_, v_c_3209_);
lean_dec(v_c_3209_);
v___x_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
return v___x_3225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality___boxed(lean_object* v_p_3226_, lean_object* v_c_3227_, lean_object* v_m_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_){
_start:
{
uint8_t v_a_boxed_3239_; lean_object* v_res_3240_; 
v_a_boxed_3239_ = lean_unbox(v_a_3232_);
v_res_3240_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3226_, v_c_3227_, v_m_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_boxed_3239_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3231_);
lean_dec(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec(v_m_3228_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(lean_object* v_p_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, uint8_t v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
uint8_t v_possible_3252_; 
v_possible_3252_ = lean_ctor_get_uint8(v_p_3241_, sizeof(void*)*7);
if (v_possible_3252_ == 0)
{
lean_object* v___x_3253_; 
v___x_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3253_, 0, v_p_3241_);
return v___x_3253_;
}
else
{
lean_object* v___x_3254_; 
v___x_3254_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_3241_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v___x_3255_; 
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v_p_3241_);
return v___x_3255_;
}
else
{
lean_object* v_val_3256_; lean_object* v_fst_3257_; lean_object* v_snd_3258_; lean_object* v___x_3259_; 
v_val_3256_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_val_3256_);
lean_dec_ref_known(v___x_3254_, 1);
v_fst_3257_ = lean_ctor_get(v_val_3256_, 0);
lean_inc(v_fst_3257_);
v_snd_3258_ = lean_ctor_get(v_val_3256_, 1);
lean_inc(v_snd_3258_);
lean_dec(v_val_3256_);
v___x_3259_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3241_, v_fst_3257_, v_snd_3258_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
lean_dec(v_snd_3258_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3259_, 1);
v_p_3241_ = v_a_3260_;
goto _start;
}
else
{
return v___x_3259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities___boxed(lean_object* v_p_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_){
_start:
{
uint8_t v_a_boxed_3273_; lean_object* v_res_3274_; 
v_a_boxed_3273_ = lean_unbox(v_a_3266_);
v_res_3274_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_boxed_3273_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
lean_dec(v_a_3271_);
lean_dec_ref(v_a_3270_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3268_);
lean_dec(v_a_3267_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec(v_a_3263_);
return v_res_3274_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = lean_box(0);
v___x_3282_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1));
v___x_3283_ = l_Lean_Expr_const___override(v___x_3282_, v___x_3281_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object* v_c_3284_, lean_object* v_x_3285_, lean_object* v_p_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, uint8_t v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3288_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
v___x_3299_ = lean_box(v_a_3290_);
lean_inc(v_a_3295_);
lean_inc_ref(v_a_3294_);
lean_inc(v_a_3293_);
lean_inc_ref(v_a_3292_);
lean_inc(v_a_3291_);
lean_inc_ref(v_a_3289_);
lean_inc(v_a_3288_);
lean_inc(v_a_3287_);
v___x_3300_ = lean_apply_10(v_p_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v___x_3299_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, lean_box(0));
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3326_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3326_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3326_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; lean_object* v___y_3307_; lean_object* v___x_3315_; uint8_t v___x_3316_; 
v___x_3305_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2);
v___x_3315_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3316_ = lean_int_dec_le(v___x_3315_, v_c_3284_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3317_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3318_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3319_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3320_ = lean_int_neg(v_c_3284_);
v___x_3321_ = l_Int_toNat(v___x_3320_);
lean_dec(v___x_3320_);
v___x_3322_ = l_Lean_instToExprInt_mkNat(v___x_3321_);
v___x_3323_ = l_Lean_mkApp3(v___x_3317_, v___x_3318_, v___x_3319_, v___x_3322_);
v___y_3307_ = v___x_3323_;
goto v___jp_3306_;
}
else
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = l_Int_toNat(v_c_3284_);
v___x_3325_ = l_Lean_instToExprInt_mkNat(v___x_3324_);
v___y_3307_ = v___x_3325_;
goto v___jp_3306_;
}
v___jp_3306_:
{
lean_object* v_nil_3308_; lean_object* v_cons_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3313_; 
v_nil_3308_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3309_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3310_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3308_, v_cons_3309_, v_x_3285_);
v___x_3311_ = l_Lean_mkApp4(v___x_3305_, v___y_3307_, v___x_3310_, v_a_3298_, v_a_3301_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3311_);
v___x_3313_ = v___x_3303_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
else
{
lean_dec(v_a_3298_);
return v___x_3300_;
}
}
else
{
lean_dec_ref(v_p_3286_);
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object* v_c_3327_, lean_object* v_x_3328_, lean_object* v_p_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
uint8_t v_a_boxed_3340_; lean_object* v_res_3341_; 
v_a_boxed_3340_ = lean_unbox(v_a_3333_);
v_res_3341_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(v_c_3327_, v_x_3328_, v_p_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_boxed_3340_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
lean_dec(v_a_3334_);
lean_dec_ref(v_a_3332_);
lean_dec(v_a_3331_);
lean_dec(v_a_3330_);
lean_dec(v_x_3328_);
lean_dec(v_c_3327_);
return v_res_3341_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = lean_box(0);
v___x_3349_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1));
v___x_3350_ = l_Lean_Expr_const___override(v___x_3349_, v___x_3348_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(lean_object* v_c_3351_, lean_object* v_x_3352_, lean_object* v_p_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, uint8_t v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_){
_start:
{
lean_object* v___x_3364_; 
v___x_3364_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3355_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3364_, 1);
v___x_3366_ = lean_box(v_a_3357_);
lean_inc(v_a_3362_);
lean_inc_ref(v_a_3361_);
lean_inc(v_a_3360_);
lean_inc_ref(v_a_3359_);
lean_inc(v_a_3358_);
lean_inc_ref(v_a_3356_);
lean_inc(v_a_3355_);
lean_inc(v_a_3354_);
v___x_3367_ = lean_apply_10(v_p_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v___x_3366_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, lean_box(0));
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3393_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3370_ = v___x_3367_;
v_isShared_3371_ = v_isSharedCheck_3393_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3367_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3393_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; lean_object* v___y_3374_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3372_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2);
v___x_3382_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3383_ = lean_int_dec_le(v___x_3382_, v_c_3351_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3384_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3385_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3386_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3387_ = lean_int_neg(v_c_3351_);
v___x_3388_ = l_Int_toNat(v___x_3387_);
lean_dec(v___x_3387_);
v___x_3389_ = l_Lean_instToExprInt_mkNat(v___x_3388_);
v___x_3390_ = l_Lean_mkApp3(v___x_3384_, v___x_3385_, v___x_3386_, v___x_3389_);
v___y_3374_ = v___x_3390_;
goto v___jp_3373_;
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = l_Int_toNat(v_c_3351_);
v___x_3392_ = l_Lean_instToExprInt_mkNat(v___x_3391_);
v___y_3374_ = v___x_3392_;
goto v___jp_3373_;
}
v___jp_3373_:
{
lean_object* v_nil_3375_; lean_object* v_cons_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3380_; 
v_nil_3375_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3376_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3377_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3375_, v_cons_3376_, v_x_3352_);
v___x_3378_ = l_Lean_mkApp4(v___x_3372_, v___y_3374_, v___x_3377_, v_a_3365_, v_a_3368_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3378_);
v___x_3380_ = v___x_3370_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
else
{
lean_dec(v_a_3365_);
return v___x_3367_;
}
}
else
{
lean_dec_ref(v_p_3353_);
return v___x_3364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed(lean_object* v_c_3394_, lean_object* v_x_3395_, lean_object* v_p_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
uint8_t v_a_boxed_3407_; lean_object* v_res_3408_; 
v_a_boxed_3407_ = lean_unbox(v_a_3400_);
v_res_3408_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(v_c_3394_, v_x_3395_, v_p_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_boxed_3407_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3402_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3399_);
lean_dec(v_a_3398_);
lean_dec(v_a_3397_);
lean_dec(v_x_3395_);
lean_dec(v_c_3394_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(lean_object* v_prf_x3f_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, uint8_t v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
if (lean_obj_tag(v_prf_x3f_3409_) == 0)
{
lean_object* v___x_3420_; uint8_t v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3420_ = lean_box(0);
v___x_3421_ = 0;
v___x_3422_ = lean_box(0);
v___x_3423_ = l_Lean_Meta_mkFreshExprMVar(v___x_3420_, v___x_3421_, v___x_3422_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; uint8_t v___x_3425_; lean_object* v___x_3426_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
v___x_3425_ = 0;
v___x_3426_ = l_Lean_Meta_mkSorry(v_a_3424_, v___x_3425_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
return v___x_3426_;
}
else
{
return v___x_3423_;
}
}
else
{
lean_object* v_val_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v_val_3427_ = lean_ctor_get(v_prf_x3f_3409_, 0);
lean_inc(v_val_3427_);
lean_dec_ref_known(v_prf_x3f_3409_, 1);
v___x_3428_ = lean_box(v___y_3413_);
lean_inc(v___y_3418_);
lean_inc_ref(v___y_3417_);
lean_inc(v___y_3416_);
lean_inc_ref(v___y_3415_);
lean_inc(v___y_3414_);
lean_inc_ref(v___y_3412_);
lean_inc(v___y_3411_);
lean_inc(v___y_3410_);
v___x_3429_ = lean_apply_10(v_val_3427_, v___y_3410_, v___y_3411_, v___y_3412_, v___x_3428_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, lean_box(0));
return v___x_3429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed(lean_object* v_prf_x3f_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
uint8_t v___y_833__boxed_3441_; lean_object* v_res_3442_; 
v___y_833__boxed_3441_ = lean_unbox(v___y_3434_);
v_res_3442_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(v_prf_x3f_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_833__boxed_3441_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec(v___y_3431_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality(lean_object* v_p_3443_, lean_object* v_const_3444_, lean_object* v_coeffs_3445_, lean_object* v_prf_x3f_3446_){
_start:
{
lean_object* v_assumptions_3447_; lean_object* v_numVars_3448_; lean_object* v_constraints_3449_; lean_object* v_equalities_3450_; lean_object* v_eliminations_3451_; uint8_t v_possible_3452_; lean_object* v_proveFalse_x3f_3453_; lean_object* v_explanation_x3f_3454_; lean_object* v_prf_3455_; lean_object* v_i_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v_p_x27_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v_f_3465_; lean_object* v_f_3466_; lean_object* v_f_3467_; lean_object* v___x_3468_; 
v_assumptions_3447_ = lean_ctor_get(v_p_3443_, 0);
v_numVars_3448_ = lean_ctor_get(v_p_3443_, 1);
v_constraints_3449_ = lean_ctor_get(v_p_3443_, 2);
v_equalities_3450_ = lean_ctor_get(v_p_3443_, 3);
v_eliminations_3451_ = lean_ctor_get(v_p_3443_, 4);
v_possible_3452_ = lean_ctor_get_uint8(v_p_3443_, sizeof(void*)*7);
v_proveFalse_x3f_3453_ = lean_ctor_get(v_p_3443_, 5);
v_explanation_x3f_3454_ = lean_ctor_get(v_p_3443_, 6);
v_prf_3455_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3455_, 0, v_prf_x3f_3446_);
v_i_3456_ = lean_array_get_size(v_assumptions_3447_);
lean_inc_n(v_coeffs_3445_, 2);
lean_inc(v_const_3444_);
v___x_3457_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed), 13, 3);
lean_closure_set(v___x_3457_, 0, v_const_3444_);
lean_closure_set(v___x_3457_, 1, v_coeffs_3445_);
lean_closure_set(v___x_3457_, 2, v_prf_3455_);
lean_inc_ref(v_assumptions_3447_);
v___x_3458_ = lean_array_push(v_assumptions_3447_, v___x_3457_);
lean_inc_ref(v_explanation_x3f_3454_);
lean_inc(v_proveFalse_x3f_3453_);
lean_inc(v_eliminations_3451_);
lean_inc_ref(v_equalities_3450_);
lean_inc_ref(v_constraints_3449_);
lean_inc(v_numVars_3448_);
v_p_x27_3459_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3459_, 0, v___x_3458_);
lean_ctor_set(v_p_x27_3459_, 1, v_numVars_3448_);
lean_ctor_set(v_p_x27_3459_, 2, v_constraints_3449_);
lean_ctor_set(v_p_x27_3459_, 3, v_equalities_3450_);
lean_ctor_set(v_p_x27_3459_, 4, v_eliminations_3451_);
lean_ctor_set(v_p_x27_3459_, 5, v_proveFalse_x3f_3453_);
lean_ctor_set(v_p_x27_3459_, 6, v_explanation_x3f_3454_);
lean_ctor_set_uint8(v_p_x27_3459_, sizeof(void*)*7, v_possible_3452_);
v___x_3460_ = lean_int_neg(v_const_3444_);
lean_dec(v_const_3444_);
v___x_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
v___x_3462_ = lean_box(0);
v___x_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3461_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
lean_inc_ref(v___x_3463_);
v___x_3464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
lean_ctor_set(v___x_3464_, 1, v_coeffs_3445_);
lean_ctor_set(v___x_3464_, 2, v_i_3456_);
v_f_3465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3465_, 0, v_coeffs_3445_);
lean_ctor_set(v_f_3465_, 1, v___x_3463_);
lean_ctor_set(v_f_3465_, 2, v___x_3464_);
v_f_3466_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3443_, v_f_3465_);
v_f_3467_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3466_);
v___x_3468_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3459_, v_f_3467_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality(lean_object* v_p_3469_, lean_object* v_const_3470_, lean_object* v_coeffs_3471_, lean_object* v_prf_x3f_3472_){
_start:
{
lean_object* v_assumptions_3473_; lean_object* v_numVars_3474_; lean_object* v_constraints_3475_; lean_object* v_equalities_3476_; lean_object* v_eliminations_3477_; uint8_t v_possible_3478_; lean_object* v_proveFalse_x3f_3479_; lean_object* v_explanation_x3f_3480_; lean_object* v_prf_3481_; lean_object* v_i_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v_p_x27_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v_f_3490_; lean_object* v_f_3491_; lean_object* v_f_3492_; lean_object* v___x_3493_; 
v_assumptions_3473_ = lean_ctor_get(v_p_3469_, 0);
v_numVars_3474_ = lean_ctor_get(v_p_3469_, 1);
v_constraints_3475_ = lean_ctor_get(v_p_3469_, 2);
v_equalities_3476_ = lean_ctor_get(v_p_3469_, 3);
v_eliminations_3477_ = lean_ctor_get(v_p_3469_, 4);
v_possible_3478_ = lean_ctor_get_uint8(v_p_3469_, sizeof(void*)*7);
v_proveFalse_x3f_3479_ = lean_ctor_get(v_p_3469_, 5);
v_explanation_x3f_3480_ = lean_ctor_get(v_p_3469_, 6);
v_prf_3481_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3481_, 0, v_prf_x3f_3472_);
v_i_3482_ = lean_array_get_size(v_assumptions_3473_);
lean_inc_n(v_coeffs_3471_, 2);
lean_inc(v_const_3470_);
v___x_3483_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed), 13, 3);
lean_closure_set(v___x_3483_, 0, v_const_3470_);
lean_closure_set(v___x_3483_, 1, v_coeffs_3471_);
lean_closure_set(v___x_3483_, 2, v_prf_3481_);
lean_inc_ref(v_assumptions_3473_);
v___x_3484_ = lean_array_push(v_assumptions_3473_, v___x_3483_);
lean_inc_ref(v_explanation_x3f_3480_);
lean_inc(v_proveFalse_x3f_3479_);
lean_inc(v_eliminations_3477_);
lean_inc_ref(v_equalities_3476_);
lean_inc_ref(v_constraints_3475_);
lean_inc(v_numVars_3474_);
v_p_x27_3485_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3485_, 0, v___x_3484_);
lean_ctor_set(v_p_x27_3485_, 1, v_numVars_3474_);
lean_ctor_set(v_p_x27_3485_, 2, v_constraints_3475_);
lean_ctor_set(v_p_x27_3485_, 3, v_equalities_3476_);
lean_ctor_set(v_p_x27_3485_, 4, v_eliminations_3477_);
lean_ctor_set(v_p_x27_3485_, 5, v_proveFalse_x3f_3479_);
lean_ctor_set(v_p_x27_3485_, 6, v_explanation_x3f_3480_);
lean_ctor_set_uint8(v_p_x27_3485_, sizeof(void*)*7, v_possible_3478_);
v___x_3486_ = lean_int_neg(v_const_3470_);
lean_dec(v_const_3470_);
v___x_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
lean_inc_ref(v___x_3487_);
v___x_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
lean_inc_ref(v___x_3488_);
v___x_3489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
lean_ctor_set(v___x_3489_, 1, v_coeffs_3471_);
lean_ctor_set(v___x_3489_, 2, v_i_3482_);
v_f_3490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3490_, 0, v_coeffs_3471_);
lean_ctor_set(v_f_3490_, 1, v___x_3488_);
lean_ctor_set(v_f_3490_, 2, v___x_3489_);
v_f_3491_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3469_, v_f_3490_);
v_f_3492_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3491_);
v___x_3493_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3485_, v_f_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(lean_object* v_x_3494_, lean_object* v_x_3495_){
_start:
{
if (lean_obj_tag(v_x_3495_) == 0)
{
return v_x_3494_;
}
else
{
lean_object* v_head_3496_; lean_object* v_snd_3497_; lean_object* v_tail_3498_; lean_object* v_fst_3499_; lean_object* v_fst_3500_; lean_object* v_snd_3501_; lean_object* v___x_3502_; 
v_head_3496_ = lean_ctor_get(v_x_3495_, 0);
lean_inc(v_head_3496_);
v_snd_3497_ = lean_ctor_get(v_head_3496_, 1);
lean_inc(v_snd_3497_);
v_tail_3498_ = lean_ctor_get(v_x_3495_, 1);
lean_inc(v_tail_3498_);
lean_dec_ref_known(v_x_3495_, 2);
v_fst_3499_ = lean_ctor_get(v_head_3496_, 0);
lean_inc(v_fst_3499_);
lean_dec(v_head_3496_);
v_fst_3500_ = lean_ctor_get(v_snd_3497_, 0);
lean_inc(v_fst_3500_);
v_snd_3501_ = lean_ctor_get(v_snd_3497_, 1);
lean_inc(v_snd_3501_);
lean_dec(v_snd_3497_);
v___x_3502_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality(v_x_3494_, v_fst_3499_, v_fst_3500_, v_snd_3501_);
v_x_3494_ = v___x_3502_;
v_x_3495_ = v_tail_3498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequalities(lean_object* v_p_3504_, lean_object* v_ineqs_3505_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(v_p_3504_, v_ineqs_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(lean_object* v_x_3507_, lean_object* v_x_3508_){
_start:
{
if (lean_obj_tag(v_x_3508_) == 0)
{
return v_x_3507_;
}
else
{
lean_object* v_head_3509_; lean_object* v_snd_3510_; lean_object* v_tail_3511_; lean_object* v_fst_3512_; lean_object* v_fst_3513_; lean_object* v_snd_3514_; lean_object* v___x_3515_; 
v_head_3509_ = lean_ctor_get(v_x_3508_, 0);
lean_inc(v_head_3509_);
v_snd_3510_ = lean_ctor_get(v_head_3509_, 1);
lean_inc(v_snd_3510_);
v_tail_3511_ = lean_ctor_get(v_x_3508_, 1);
lean_inc(v_tail_3511_);
lean_dec_ref_known(v_x_3508_, 2);
v_fst_3512_ = lean_ctor_get(v_head_3509_, 0);
lean_inc(v_fst_3512_);
lean_dec(v_head_3509_);
v_fst_3513_ = lean_ctor_get(v_snd_3510_, 0);
lean_inc(v_fst_3513_);
v_snd_3514_ = lean_ctor_get(v_snd_3510_, 1);
lean_inc(v_snd_3514_);
lean_dec(v_snd_3510_);
v___x_3515_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality(v_x_3507_, v_fst_3512_, v_fst_3513_, v_snd_3514_);
v_x_3507_ = v___x_3515_;
v_x_3508_ = v_tail_3511_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEqualities(lean_object* v_p_3517_, lean_object* v_eqs_3518_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(v_p_3517_, v_eqs_3518_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0(lean_object* v___x_3526_, lean_object* v_x_3527_){
_start:
{
lean_object* v_constraint_3528_; lean_object* v_coeffs_3529_; lean_object* v_lowerBound_3530_; lean_object* v_upperBound_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___y_3536_; lean_object* v___y_3537_; 
v_constraint_3528_ = lean_ctor_get(v_x_3527_, 1);
lean_inc_ref(v_constraint_3528_);
v_coeffs_3529_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_coeffs_3529_);
lean_dec_ref(v_x_3527_);
v_lowerBound_3530_ = lean_ctor_get(v_constraint_3528_, 0);
lean_inc(v_lowerBound_3530_);
v_upperBound_3531_ = lean_ctor_get(v_constraint_3528_, 1);
lean_inc(v_upperBound_3531_);
lean_dec_ref(v_constraint_3528_);
v___x_3532_ = l_List_toString___redArg(v___x_3526_, v_coeffs_3529_);
v___x_3533_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3534_ = lean_string_append(v___x_3532_, v___x_3533_);
if (lean_obj_tag(v_lowerBound_3530_) == 0)
{
if (lean_obj_tag(v_upperBound_3531_) == 0)
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3543_ = lean_string_append(v___x_3534_, v___x_3542_);
return v___x_3543_;
}
else
{
lean_object* v_val_3544_; lean_object* v___x_3545_; lean_object* v___y_3547_; lean_object* v_intZero_3552_; uint8_t v_isNeg_3553_; 
v_val_3544_ = lean_ctor_get(v_upperBound_3531_, 0);
lean_inc(v_val_3544_);
lean_dec_ref_known(v_upperBound_3531_, 1);
v___x_3545_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3552_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3553_ = lean_int_dec_lt(v_val_3544_, v_intZero_3552_);
if (v_isNeg_3553_ == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3555_; 
v_a_3554_ = lean_nat_abs(v_val_3544_);
lean_dec(v_val_3544_);
v___x_3555_ = l_Nat_reprFast(v_a_3554_);
v___y_3547_ = v___x_3555_;
goto v___jp_3546_;
}
else
{
lean_object* v_abs_3556_; lean_object* v_one_3557_; lean_object* v_a_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v_abs_3556_ = lean_nat_abs(v_val_3544_);
lean_dec(v_val_3544_);
v_one_3557_ = lean_unsigned_to_nat(1u);
v_a_3558_ = lean_nat_sub(v_abs_3556_, v_one_3557_);
lean_dec(v_abs_3556_);
v___x_3559_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3560_ = lean_nat_add(v_a_3558_, v_one_3557_);
lean_dec(v_a_3558_);
v___x_3561_ = l_Nat_reprFast(v___x_3560_);
v___x_3562_ = lean_string_append(v___x_3559_, v___x_3561_);
lean_dec_ref(v___x_3561_);
v___y_3547_ = v___x_3562_;
goto v___jp_3546_;
}
v___jp_3546_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3548_ = lean_string_append(v___x_3545_, v___y_3547_);
lean_dec_ref(v___y_3547_);
v___x_3549_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3550_ = lean_string_append(v___x_3548_, v___x_3549_);
v___x_3551_ = lean_string_append(v___x_3534_, v___x_3550_);
lean_dec_ref(v___x_3550_);
return v___x_3551_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3531_) == 0)
{
lean_object* v_val_3563_; lean_object* v___x_3564_; lean_object* v___y_3566_; lean_object* v_intZero_3571_; uint8_t v_isNeg_3572_; 
v_val_3563_ = lean_ctor_get(v_lowerBound_3530_, 0);
lean_inc(v_val_3563_);
lean_dec_ref_known(v_lowerBound_3530_, 1);
v___x_3564_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3571_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3572_ = lean_int_dec_lt(v_val_3563_, v_intZero_3571_);
if (v_isNeg_3572_ == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3574_; 
v_a_3573_ = lean_nat_abs(v_val_3563_);
lean_dec(v_val_3563_);
v___x_3574_ = l_Nat_reprFast(v_a_3573_);
v___y_3566_ = v___x_3574_;
goto v___jp_3565_;
}
else
{
lean_object* v_abs_3575_; lean_object* v_one_3576_; lean_object* v_a_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v_abs_3575_ = lean_nat_abs(v_val_3563_);
lean_dec(v_val_3563_);
v_one_3576_ = lean_unsigned_to_nat(1u);
v_a_3577_ = lean_nat_sub(v_abs_3575_, v_one_3576_);
lean_dec(v_abs_3575_);
v___x_3578_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3579_ = lean_nat_add(v_a_3577_, v_one_3576_);
lean_dec(v_a_3577_);
v___x_3580_ = l_Nat_reprFast(v___x_3579_);
v___x_3581_ = lean_string_append(v___x_3578_, v___x_3580_);
lean_dec_ref(v___x_3580_);
v___y_3566_ = v___x_3581_;
goto v___jp_3565_;
}
v___jp_3565_:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3567_ = lean_string_append(v___x_3564_, v___y_3566_);
lean_dec_ref(v___y_3566_);
v___x_3568_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3569_ = lean_string_append(v___x_3567_, v___x_3568_);
v___x_3570_ = lean_string_append(v___x_3534_, v___x_3569_);
lean_dec_ref(v___x_3569_);
return v___x_3570_;
}
}
else
{
lean_object* v_val_3582_; lean_object* v_val_3583_; uint8_t v___x_3584_; 
v_val_3582_ = lean_ctor_get(v_lowerBound_3530_, 0);
lean_inc(v_val_3582_);
lean_dec_ref_known(v_lowerBound_3530_, 1);
v_val_3583_ = lean_ctor_get(v_upperBound_3531_, 0);
lean_inc(v_val_3583_);
lean_dec_ref_known(v_upperBound_3531_, 1);
v___x_3584_ = lean_int_dec_lt(v_val_3583_, v_val_3582_);
if (v___x_3584_ == 0)
{
uint8_t v___x_3585_; 
v___x_3585_ = lean_int_dec_eq(v_val_3582_, v_val_3583_);
if (v___x_3585_ == 0)
{
lean_object* v___x_3586_; lean_object* v___y_3588_; lean_object* v_intZero_3603_; uint8_t v_isNeg_3604_; 
v___x_3586_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3603_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3604_ = lean_int_dec_lt(v_val_3582_, v_intZero_3603_);
if (v_isNeg_3604_ == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3606_; 
v_a_3605_ = lean_nat_abs(v_val_3582_);
lean_dec(v_val_3582_);
v___x_3606_ = l_Nat_reprFast(v_a_3605_);
v___y_3588_ = v___x_3606_;
goto v___jp_3587_;
}
else
{
lean_object* v_abs_3607_; lean_object* v_one_3608_; lean_object* v_a_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v_abs_3607_ = lean_nat_abs(v_val_3582_);
lean_dec(v_val_3582_);
v_one_3608_ = lean_unsigned_to_nat(1u);
v_a_3609_ = lean_nat_sub(v_abs_3607_, v_one_3608_);
lean_dec(v_abs_3607_);
v___x_3610_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3611_ = lean_nat_add(v_a_3609_, v_one_3608_);
lean_dec(v_a_3609_);
v___x_3612_ = l_Nat_reprFast(v___x_3611_);
v___x_3613_ = lean_string_append(v___x_3610_, v___x_3612_);
lean_dec_ref(v___x_3612_);
v___y_3588_ = v___x_3613_;
goto v___jp_3587_;
}
v___jp_3587_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v_intZero_3592_; uint8_t v_isNeg_3593_; 
v___x_3589_ = lean_string_append(v___x_3586_, v___y_3588_);
lean_dec_ref(v___y_3588_);
v___x_3590_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3591_ = lean_string_append(v___x_3589_, v___x_3590_);
v_intZero_3592_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3593_ = lean_int_dec_lt(v_val_3583_, v_intZero_3592_);
if (v_isNeg_3593_ == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3595_; 
v_a_3594_ = lean_nat_abs(v_val_3583_);
lean_dec(v_val_3583_);
v___x_3595_ = l_Nat_reprFast(v_a_3594_);
v___y_3536_ = v___x_3591_;
v___y_3537_ = v___x_3595_;
goto v___jp_3535_;
}
else
{
lean_object* v_abs_3596_; lean_object* v_one_3597_; lean_object* v_a_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_abs_3596_ = lean_nat_abs(v_val_3583_);
lean_dec(v_val_3583_);
v_one_3597_ = lean_unsigned_to_nat(1u);
v_a_3598_ = lean_nat_sub(v_abs_3596_, v_one_3597_);
lean_dec(v_abs_3596_);
v___x_3599_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3600_ = lean_nat_add(v_a_3598_, v_one_3597_);
lean_dec(v_a_3598_);
v___x_3601_ = l_Nat_reprFast(v___x_3600_);
v___x_3602_ = lean_string_append(v___x_3599_, v___x_3601_);
lean_dec_ref(v___x_3601_);
v___y_3536_ = v___x_3591_;
v___y_3537_ = v___x_3602_;
goto v___jp_3535_;
}
}
}
else
{
lean_object* v___x_3614_; lean_object* v___y_3616_; lean_object* v_intZero_3621_; uint8_t v_isNeg_3622_; 
lean_dec(v_val_3583_);
v___x_3614_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3621_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3622_ = lean_int_dec_lt(v_val_3582_, v_intZero_3621_);
if (v_isNeg_3622_ == 0)
{
lean_object* v_a_3623_; lean_object* v___x_3624_; 
v_a_3623_ = lean_nat_abs(v_val_3582_);
lean_dec(v_val_3582_);
v___x_3624_ = l_Nat_reprFast(v_a_3623_);
v___y_3616_ = v___x_3624_;
goto v___jp_3615_;
}
else
{
lean_object* v_abs_3625_; lean_object* v_one_3626_; lean_object* v_a_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v_abs_3625_ = lean_nat_abs(v_val_3582_);
lean_dec(v_val_3582_);
v_one_3626_ = lean_unsigned_to_nat(1u);
v_a_3627_ = lean_nat_sub(v_abs_3625_, v_one_3626_);
lean_dec(v_abs_3625_);
v___x_3628_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3629_ = lean_nat_add(v_a_3627_, v_one_3626_);
lean_dec(v_a_3627_);
v___x_3630_ = l_Nat_reprFast(v___x_3629_);
v___x_3631_ = lean_string_append(v___x_3628_, v___x_3630_);
lean_dec_ref(v___x_3630_);
v___y_3616_ = v___x_3631_;
goto v___jp_3615_;
}
v___jp_3615_:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3617_ = lean_string_append(v___x_3614_, v___y_3616_);
lean_dec_ref(v___y_3616_);
v___x_3618_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3619_ = lean_string_append(v___x_3617_, v___x_3618_);
v___x_3620_ = lean_string_append(v___x_3534_, v___x_3619_);
lean_dec_ref(v___x_3619_);
return v___x_3620_;
}
}
}
else
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
lean_dec(v_val_3583_);
lean_dec(v_val_3582_);
v___x_3632_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3633_ = lean_string_append(v___x_3534_, v___x_3632_);
return v___x_3633_;
}
}
}
v___jp_3535_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3538_ = lean_string_append(v___y_3536_, v___y_3537_);
lean_dec_ref(v___y_3537_);
v___x_3539_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3540_ = lean_string_append(v___x_3538_, v___x_3539_);
v___x_3541_ = lean_string_append(v___x_3534_, v___x_3540_);
lean_dec_ref(v___x_3540_);
return v___x_3541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1(lean_object* v___x_3634_, lean_object* v_x_3635_){
_start:
{
lean_object* v_fst_3636_; lean_object* v_constraint_3637_; lean_object* v_coeffs_3638_; lean_object* v_lowerBound_3639_; lean_object* v_upperBound_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___y_3645_; lean_object* v___y_3646_; 
v_fst_3636_ = lean_ctor_get(v_x_3635_, 0);
lean_inc(v_fst_3636_);
lean_dec_ref(v_x_3635_);
v_constraint_3637_ = lean_ctor_get(v_fst_3636_, 1);
lean_inc_ref(v_constraint_3637_);
v_coeffs_3638_ = lean_ctor_get(v_fst_3636_, 0);
lean_inc(v_coeffs_3638_);
lean_dec(v_fst_3636_);
v_lowerBound_3639_ = lean_ctor_get(v_constraint_3637_, 0);
lean_inc(v_lowerBound_3639_);
v_upperBound_3640_ = lean_ctor_get(v_constraint_3637_, 1);
lean_inc(v_upperBound_3640_);
lean_dec_ref(v_constraint_3637_);
v___x_3641_ = l_List_toString___redArg(v___x_3634_, v_coeffs_3638_);
v___x_3642_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3643_ = lean_string_append(v___x_3641_, v___x_3642_);
if (lean_obj_tag(v_lowerBound_3639_) == 0)
{
if (lean_obj_tag(v_upperBound_3640_) == 0)
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3652_ = lean_string_append(v___x_3643_, v___x_3651_);
return v___x_3652_;
}
else
{
lean_object* v_val_3653_; lean_object* v___x_3654_; lean_object* v___y_3656_; lean_object* v_intZero_3661_; uint8_t v_isNeg_3662_; 
v_val_3653_ = lean_ctor_get(v_upperBound_3640_, 0);
lean_inc(v_val_3653_);
lean_dec_ref_known(v_upperBound_3640_, 1);
v___x_3654_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3661_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3662_ = lean_int_dec_lt(v_val_3653_, v_intZero_3661_);
if (v_isNeg_3662_ == 0)
{
lean_object* v_a_3663_; lean_object* v___x_3664_; 
v_a_3663_ = lean_nat_abs(v_val_3653_);
lean_dec(v_val_3653_);
v___x_3664_ = l_Nat_reprFast(v_a_3663_);
v___y_3656_ = v___x_3664_;
goto v___jp_3655_;
}
else
{
lean_object* v_abs_3665_; lean_object* v_one_3666_; lean_object* v_a_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v_abs_3665_ = lean_nat_abs(v_val_3653_);
lean_dec(v_val_3653_);
v_one_3666_ = lean_unsigned_to_nat(1u);
v_a_3667_ = lean_nat_sub(v_abs_3665_, v_one_3666_);
lean_dec(v_abs_3665_);
v___x_3668_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3669_ = lean_nat_add(v_a_3667_, v_one_3666_);
lean_dec(v_a_3667_);
v___x_3670_ = l_Nat_reprFast(v___x_3669_);
v___x_3671_ = lean_string_append(v___x_3668_, v___x_3670_);
lean_dec_ref(v___x_3670_);
v___y_3656_ = v___x_3671_;
goto v___jp_3655_;
}
v___jp_3655_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3657_ = lean_string_append(v___x_3654_, v___y_3656_);
lean_dec_ref(v___y_3656_);
v___x_3658_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3659_ = lean_string_append(v___x_3657_, v___x_3658_);
v___x_3660_ = lean_string_append(v___x_3643_, v___x_3659_);
lean_dec_ref(v___x_3659_);
return v___x_3660_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3640_) == 0)
{
lean_object* v_val_3672_; lean_object* v___x_3673_; lean_object* v___y_3675_; lean_object* v_intZero_3680_; uint8_t v_isNeg_3681_; 
v_val_3672_ = lean_ctor_get(v_lowerBound_3639_, 0);
lean_inc(v_val_3672_);
lean_dec_ref_known(v_lowerBound_3639_, 1);
v___x_3673_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3680_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3681_ = lean_int_dec_lt(v_val_3672_, v_intZero_3680_);
if (v_isNeg_3681_ == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3683_; 
v_a_3682_ = lean_nat_abs(v_val_3672_);
lean_dec(v_val_3672_);
v___x_3683_ = l_Nat_reprFast(v_a_3682_);
v___y_3675_ = v___x_3683_;
goto v___jp_3674_;
}
else
{
lean_object* v_abs_3684_; lean_object* v_one_3685_; lean_object* v_a_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v_abs_3684_ = lean_nat_abs(v_val_3672_);
lean_dec(v_val_3672_);
v_one_3685_ = lean_unsigned_to_nat(1u);
v_a_3686_ = lean_nat_sub(v_abs_3684_, v_one_3685_);
lean_dec(v_abs_3684_);
v___x_3687_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3688_ = lean_nat_add(v_a_3686_, v_one_3685_);
lean_dec(v_a_3686_);
v___x_3689_ = l_Nat_reprFast(v___x_3688_);
v___x_3690_ = lean_string_append(v___x_3687_, v___x_3689_);
lean_dec_ref(v___x_3689_);
v___y_3675_ = v___x_3690_;
goto v___jp_3674_;
}
v___jp_3674_:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3676_ = lean_string_append(v___x_3673_, v___y_3675_);
lean_dec_ref(v___y_3675_);
v___x_3677_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3678_ = lean_string_append(v___x_3676_, v___x_3677_);
v___x_3679_ = lean_string_append(v___x_3643_, v___x_3678_);
lean_dec_ref(v___x_3678_);
return v___x_3679_;
}
}
else
{
lean_object* v_val_3691_; lean_object* v_val_3692_; uint8_t v___x_3693_; 
v_val_3691_ = lean_ctor_get(v_lowerBound_3639_, 0);
lean_inc(v_val_3691_);
lean_dec_ref_known(v_lowerBound_3639_, 1);
v_val_3692_ = lean_ctor_get(v_upperBound_3640_, 0);
lean_inc(v_val_3692_);
lean_dec_ref_known(v_upperBound_3640_, 1);
v___x_3693_ = lean_int_dec_lt(v_val_3692_, v_val_3691_);
if (v___x_3693_ == 0)
{
uint8_t v___x_3694_; 
v___x_3694_ = lean_int_dec_eq(v_val_3691_, v_val_3692_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3695_; lean_object* v___y_3697_; lean_object* v_intZero_3712_; uint8_t v_isNeg_3713_; 
v___x_3695_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3712_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3713_ = lean_int_dec_lt(v_val_3691_, v_intZero_3712_);
if (v_isNeg_3713_ == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; 
v_a_3714_ = lean_nat_abs(v_val_3691_);
lean_dec(v_val_3691_);
v___x_3715_ = l_Nat_reprFast(v_a_3714_);
v___y_3697_ = v___x_3715_;
goto v___jp_3696_;
}
else
{
lean_object* v_abs_3716_; lean_object* v_one_3717_; lean_object* v_a_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v_abs_3716_ = lean_nat_abs(v_val_3691_);
lean_dec(v_val_3691_);
v_one_3717_ = lean_unsigned_to_nat(1u);
v_a_3718_ = lean_nat_sub(v_abs_3716_, v_one_3717_);
lean_dec(v_abs_3716_);
v___x_3719_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3720_ = lean_nat_add(v_a_3718_, v_one_3717_);
lean_dec(v_a_3718_);
v___x_3721_ = l_Nat_reprFast(v___x_3720_);
v___x_3722_ = lean_string_append(v___x_3719_, v___x_3721_);
lean_dec_ref(v___x_3721_);
v___y_3697_ = v___x_3722_;
goto v___jp_3696_;
}
v___jp_3696_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v_intZero_3701_; uint8_t v_isNeg_3702_; 
v___x_3698_ = lean_string_append(v___x_3695_, v___y_3697_);
lean_dec_ref(v___y_3697_);
v___x_3699_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3700_ = lean_string_append(v___x_3698_, v___x_3699_);
v_intZero_3701_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3702_ = lean_int_dec_lt(v_val_3692_, v_intZero_3701_);
if (v_isNeg_3702_ == 0)
{
lean_object* v_a_3703_; lean_object* v___x_3704_; 
v_a_3703_ = lean_nat_abs(v_val_3692_);
lean_dec(v_val_3692_);
v___x_3704_ = l_Nat_reprFast(v_a_3703_);
v___y_3645_ = v___x_3700_;
v___y_3646_ = v___x_3704_;
goto v___jp_3644_;
}
else
{
lean_object* v_abs_3705_; lean_object* v_one_3706_; lean_object* v_a_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v_abs_3705_ = lean_nat_abs(v_val_3692_);
lean_dec(v_val_3692_);
v_one_3706_ = lean_unsigned_to_nat(1u);
v_a_3707_ = lean_nat_sub(v_abs_3705_, v_one_3706_);
lean_dec(v_abs_3705_);
v___x_3708_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3709_ = lean_nat_add(v_a_3707_, v_one_3706_);
lean_dec(v_a_3707_);
v___x_3710_ = l_Nat_reprFast(v___x_3709_);
v___x_3711_ = lean_string_append(v___x_3708_, v___x_3710_);
lean_dec_ref(v___x_3710_);
v___y_3645_ = v___x_3700_;
v___y_3646_ = v___x_3711_;
goto v___jp_3644_;
}
}
}
else
{
lean_object* v___x_3723_; lean_object* v___y_3725_; lean_object* v_intZero_3730_; uint8_t v_isNeg_3731_; 
lean_dec(v_val_3692_);
v___x_3723_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3730_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3731_ = lean_int_dec_lt(v_val_3691_, v_intZero_3730_);
if (v_isNeg_3731_ == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3733_; 
v_a_3732_ = lean_nat_abs(v_val_3691_);
lean_dec(v_val_3691_);
v___x_3733_ = l_Nat_reprFast(v_a_3732_);
v___y_3725_ = v___x_3733_;
goto v___jp_3724_;
}
else
{
lean_object* v_abs_3734_; lean_object* v_one_3735_; lean_object* v_a_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v_abs_3734_ = lean_nat_abs(v_val_3691_);
lean_dec(v_val_3691_);
v_one_3735_ = lean_unsigned_to_nat(1u);
v_a_3736_ = lean_nat_sub(v_abs_3734_, v_one_3735_);
lean_dec(v_abs_3734_);
v___x_3737_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3738_ = lean_nat_add(v_a_3736_, v_one_3735_);
lean_dec(v_a_3736_);
v___x_3739_ = l_Nat_reprFast(v___x_3738_);
v___x_3740_ = lean_string_append(v___x_3737_, v___x_3739_);
lean_dec_ref(v___x_3739_);
v___y_3725_ = v___x_3740_;
goto v___jp_3724_;
}
v___jp_3724_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3726_ = lean_string_append(v___x_3723_, v___y_3725_);
lean_dec_ref(v___y_3725_);
v___x_3727_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3728_ = lean_string_append(v___x_3726_, v___x_3727_);
v___x_3729_ = lean_string_append(v___x_3643_, v___x_3728_);
lean_dec_ref(v___x_3728_);
return v___x_3729_;
}
}
}
else
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
lean_dec(v_val_3692_);
lean_dec(v_val_3691_);
v___x_3741_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3742_ = lean_string_append(v___x_3643_, v___x_3741_);
return v___x_3742_;
}
}
}
v___jp_3644_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3647_ = lean_string_append(v___y_3645_, v___y_3646_);
lean_dec_ref(v___y_3646_);
v___x_3648_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3649_ = lean_string_append(v___x_3647_, v___x_3648_);
v___x_3650_ = lean_string_append(v___x_3643_, v___x_3649_);
lean_dec_ref(v___x_3649_);
return v___x_3650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2(lean_object* v___f_3747_, lean_object* v___f_3748_, lean_object* v___f_3749_, lean_object* v_d_3750_){
_start:
{
lean_object* v_var_3751_; lean_object* v_irrelevant_3752_; lean_object* v_lowerBounds_3753_; lean_object* v_upperBounds_3754_; lean_object* v___x_3755_; lean_object* v_irrelevant_3756_; lean_object* v_lowerBounds_3757_; lean_object* v_upperBounds_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v_var_3751_ = lean_ctor_get(v_d_3750_, 0);
lean_inc(v_var_3751_);
v_irrelevant_3752_ = lean_ctor_get(v_d_3750_, 1);
lean_inc(v_irrelevant_3752_);
v_lowerBounds_3753_ = lean_ctor_get(v_d_3750_, 2);
lean_inc(v_lowerBounds_3753_);
v_upperBounds_3754_ = lean_ctor_get(v_d_3750_, 3);
lean_inc(v_upperBounds_3754_);
lean_dec_ref(v_d_3750_);
v___x_3755_ = lean_box(0);
v_irrelevant_3756_ = l_List_mapTR_loop___redArg(v___f_3747_, v_irrelevant_3752_, v___x_3755_);
lean_inc_ref(v___f_3748_);
v_lowerBounds_3757_ = l_List_mapTR_loop___redArg(v___f_3748_, v_lowerBounds_3753_, v___x_3755_);
v_upperBounds_3758_ = l_List_mapTR_loop___redArg(v___f_3748_, v_upperBounds_3754_, v___x_3755_);
v___x_3759_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0));
v___x_3760_ = l_Nat_reprFast(v_var_3751_);
v___x_3761_ = lean_string_append(v___x_3759_, v___x_3760_);
lean_dec_ref(v___x_3760_);
v___x_3762_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_3763_ = lean_string_append(v___x_3761_, v___x_3762_);
v___x_3764_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1));
lean_inc_ref_n(v___f_3749_, 2);
v___x_3765_ = l_List_toString___redArg(v___f_3749_, v_irrelevant_3756_);
v___x_3766_ = lean_string_append(v___x_3764_, v___x_3765_);
lean_dec_ref(v___x_3765_);
v___x_3767_ = lean_string_append(v___x_3766_, v___x_3762_);
v___x_3768_ = lean_string_append(v___x_3763_, v___x_3767_);
lean_dec_ref(v___x_3767_);
v___x_3769_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2));
v___x_3770_ = l_List_toString___redArg(v___f_3749_, v_lowerBounds_3757_);
v___x_3771_ = lean_string_append(v___x_3769_, v___x_3770_);
lean_dec_ref(v___x_3770_);
v___x_3772_ = lean_string_append(v___x_3771_, v___x_3762_);
v___x_3773_ = lean_string_append(v___x_3768_, v___x_3772_);
lean_dec_ref(v___x_3772_);
v___x_3774_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3));
v___x_3775_ = l_List_toString___redArg(v___f_3749_, v_upperBounds_3758_);
v___x_3776_ = lean_string_append(v___x_3774_, v___x_3775_);
lean_dec_ref(v___x_3775_);
v___x_3777_ = lean_string_append(v___x_3773_, v___x_3776_);
lean_dec_ref(v___x_3776_);
return v___x_3777_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(lean_object* v_d_3788_){
_start:
{
lean_object* v_lowerBounds_3789_; lean_object* v_upperBounds_3790_; uint8_t v___x_3791_; 
v_lowerBounds_3789_ = lean_ctor_get(v_d_3788_, 2);
v_upperBounds_3790_ = lean_ctor_get(v_d_3788_, 3);
v___x_3791_ = l_List_isEmpty___redArg(v_lowerBounds_3789_);
if (v___x_3791_ == 0)
{
return v___x_3791_;
}
else
{
uint8_t v___x_3792_; 
v___x_3792_ = l_List_isEmpty___redArg(v_upperBounds_3790_);
return v___x_3792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty___boxed(lean_object* v_d_3793_){
_start:
{
uint8_t v_res_3794_; lean_object* v_r_3795_; 
v_res_3794_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v_d_3793_);
lean_dec_ref(v_d_3793_);
v_r_3795_ = lean_box(v_res_3794_);
return v_r_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(lean_object* v_d_3796_){
_start:
{
lean_object* v_lowerBounds_3797_; lean_object* v_upperBounds_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v_lowerBounds_3797_ = lean_ctor_get(v_d_3796_, 2);
v_upperBounds_3798_ = lean_ctor_get(v_d_3796_, 3);
v___x_3799_ = l_List_lengthTR___redArg(v_lowerBounds_3797_);
v___x_3800_ = l_List_lengthTR___redArg(v_upperBounds_3798_);
v___x_3801_ = lean_nat_mul(v___x_3799_, v___x_3800_);
lean_dec(v___x_3800_);
lean_dec(v___x_3799_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size___boxed(lean_object* v_d_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_d_3802_);
lean_dec_ref(v_d_3802_);
return v_res_3803_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(lean_object* v_d_3804_){
_start:
{
uint8_t v_lowerExact_3805_; 
v_lowerExact_3805_ = lean_ctor_get_uint8(v_d_3804_, sizeof(void*)*4);
if (v_lowerExact_3805_ == 0)
{
uint8_t v_upperExact_3806_; 
v_upperExact_3806_ = lean_ctor_get_uint8(v_d_3804_, sizeof(void*)*4 + 1);
return v_upperExact_3806_;
}
else
{
return v_lowerExact_3805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact___boxed(lean_object* v_d_3807_){
_start:
{
uint8_t v_res_3808_; lean_object* v_r_3809_; 
v_res_3808_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_d_3807_);
lean_dec_ref(v_d_3807_);
v_r_3809_ = lean_box(v_res_3808_);
return v_r_3809_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(lean_object* v_x_3810_, lean_object* v_x_3811_){
_start:
{
if (lean_obj_tag(v_x_3811_) == 0)
{
return v_x_3810_;
}
else
{
lean_object* v_head_3812_; lean_object* v_tail_3813_; lean_object* v___x_3814_; uint8_t v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v_head_3812_ = lean_ctor_get(v_x_3811_, 0);
v_tail_3813_ = lean_ctor_get(v_x_3811_, 1);
v___x_3814_ = lean_box(0);
v___x_3815_ = 1;
lean_inc(v_head_3812_);
v___x_3816_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3816_, 0, v_head_3812_);
lean_ctor_set(v___x_3816_, 1, v___x_3814_);
lean_ctor_set(v___x_3816_, 2, v___x_3814_);
lean_ctor_set(v___x_3816_, 3, v___x_3814_);
lean_ctor_set_uint8(v___x_3816_, sizeof(void*)*4, v___x_3815_);
lean_ctor_set_uint8(v___x_3816_, sizeof(void*)*4 + 1, v___x_3815_);
v___x_3817_ = lean_array_push(v_x_3810_, v___x_3816_);
v_x_3810_ = v___x_3817_;
v_x_3811_ = v_tail_3813_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2___boxed(lean_object* v_x_3819_, lean_object* v_x_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v_x_3819_, v_x_3820_);
lean_dec(v_x_3820_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object* v___x_3822_, lean_object* v_b_3823_, lean_object* v___x_3824_, uint8_t v___x_3825_, lean_object* v_____r_3826_, lean_object* v_d_x27_3827_){
_start:
{
lean_object* v_upperBound_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3855_; 
v_upperBound_3828_ = lean_ctor_get(v___x_3822_, 1);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3855_ == 0)
{
lean_object* v_unused_3856_; 
v_unused_3856_ = lean_ctor_get(v___x_3822_, 0);
lean_dec(v_unused_3856_);
v___x_3830_ = v___x_3822_;
v_isShared_3831_ = v_isSharedCheck_3855_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_upperBound_3828_);
lean_dec(v___x_3822_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3855_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
if (lean_obj_tag(v_upperBound_3828_) == 0)
{
lean_del_object(v___x_3830_);
lean_dec(v___x_3824_);
lean_dec_ref(v_b_3823_);
return v_d_x27_3827_;
}
else
{
lean_object* v_var_3832_; lean_object* v_irrelevant_3833_; lean_object* v_lowerBounds_3834_; lean_object* v_upperBounds_3835_; uint8_t v_lowerExact_3836_; uint8_t v_upperExact_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3854_; 
lean_dec_ref_known(v_upperBound_3828_, 1);
v_var_3832_ = lean_ctor_get(v_d_x27_3827_, 0);
v_irrelevant_3833_ = lean_ctor_get(v_d_x27_3827_, 1);
v_lowerBounds_3834_ = lean_ctor_get(v_d_x27_3827_, 2);
v_upperBounds_3835_ = lean_ctor_get(v_d_x27_3827_, 3);
v_lowerExact_3836_ = lean_ctor_get_uint8(v_d_x27_3827_, sizeof(void*)*4);
v_upperExact_3837_ = lean_ctor_get_uint8(v_d_x27_3827_, sizeof(void*)*4 + 1);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_d_x27_3827_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3839_ = v_d_x27_3827_;
v_isShared_3840_ = v_isSharedCheck_3854_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_upperBounds_3835_);
lean_inc(v_lowerBounds_3834_);
lean_inc(v_irrelevant_3833_);
lean_inc(v_var_3832_);
lean_dec(v_d_x27_3827_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3854_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
lean_inc(v___x_3824_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 1, v___x_3824_);
lean_ctor_set(v___x_3830_, 0, v_b_3823_);
v___x_3842_ = v___x_3830_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_b_3823_);
lean_ctor_set(v_reuseFailAlloc_3853_, 1, v___x_3824_);
v___x_3842_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3843_; 
v___x_3843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
lean_ctor_set(v___x_3843_, 1, v_upperBounds_3835_);
if (v_upperExact_3837_ == 0)
{
lean_object* v___x_3845_; 
lean_dec(v___x_3824_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 3, v___x_3843_);
v___x_3845_ = v___x_3839_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_var_3832_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v_irrelevant_3833_);
lean_ctor_set(v_reuseFailAlloc_3846_, 2, v_lowerBounds_3834_);
lean_ctor_set(v_reuseFailAlloc_3846_, 3, v___x_3843_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, sizeof(void*)*4, v_lowerExact_3836_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_ctor_set_uint8(v___x_3845_, sizeof(void*)*4 + 1, v___x_3825_);
return v___x_3845_;
}
}
else
{
lean_object* v___x_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; lean_object* v___x_3851_; 
v___x_3847_ = lean_nat_abs(v___x_3824_);
lean_dec(v___x_3824_);
v___x_3848_ = lean_unsigned_to_nat(1u);
v___x_3849_ = lean_nat_dec_eq(v___x_3847_, v___x_3848_);
lean_dec(v___x_3847_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 3, v___x_3843_);
v___x_3851_ = v___x_3839_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_var_3832_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v_irrelevant_3833_);
lean_ctor_set(v_reuseFailAlloc_3852_, 2, v_lowerBounds_3834_);
lean_ctor_set(v_reuseFailAlloc_3852_, 3, v___x_3843_);
lean_ctor_set_uint8(v_reuseFailAlloc_3852_, sizeof(void*)*4, v_lowerExact_3836_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_ctor_set_uint8(v___x_3851_, sizeof(void*)*4 + 1, v___x_3849_);
return v___x_3851_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0___boxed(lean_object* v___x_3857_, lean_object* v_b_3858_, lean_object* v___x_3859_, lean_object* v___x_3860_, lean_object* v_____r_3861_, lean_object* v_d_x27_3862_){
_start:
{
uint8_t v___x_1958__boxed_3863_; lean_object* v_res_3864_; 
v___x_1958__boxed_3863_ = lean_unbox(v___x_3860_);
v_res_3864_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3857_, v_b_3858_, v___x_3859_, v___x_1958__boxed_3863_, v_____r_3861_, v_d_x27_3862_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(lean_object* v_upperBound_3865_, lean_object* v_coeffs_3866_, lean_object* v_constraint_3867_, lean_object* v_b_3868_, lean_object* v_a_3869_, lean_object* v_b_3870_){
_start:
{
lean_object* v_a_3872_; uint8_t v___x_3876_; 
v___x_3876_ = lean_nat_dec_lt(v_a_3869_, v_upperBound_3865_);
if (v___x_3876_ == 0)
{
lean_dec(v_a_3869_);
lean_dec_ref(v_b_3868_);
lean_dec_ref(v_constraint_3867_);
return v_b_3870_;
}
else
{
lean_object* v___x_3877_; uint8_t v___x_3878_; 
v___x_3877_ = lean_array_get_size(v_b_3870_);
v___x_3878_ = lean_nat_dec_lt(v_a_3869_, v___x_3877_);
if (v___x_3878_ == 0)
{
v_a_3872_ = v_b_3870_;
goto v___jp_3871_;
}
else
{
lean_object* v___x_3879_; lean_object* v_v_3880_; lean_object* v___x_3881_; lean_object* v_xs_x27_3882_; lean_object* v___y_3884_; lean_object* v___x_3886_; uint8_t v___x_3887_; 
lean_inc(v_a_3869_);
v___x_3879_ = l_Lean_Omega_IntList_get(v_coeffs_3866_, v_a_3869_);
v_v_3880_ = lean_array_fget(v_b_3870_, v_a_3869_);
v___x_3881_ = lean_box(0);
v_xs_x27_3882_ = lean_array_fset(v_b_3870_, v_a_3869_, v___x_3881_);
v___x_3886_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3887_ = lean_int_dec_eq(v___x_3879_, v___x_3886_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; lean_object* v_lowerBound_3889_; 
lean_inc_ref(v_constraint_3867_);
lean_inc(v___x_3879_);
v___x_3888_ = l_Lean_Omega_Constraint_scale(v___x_3879_, v_constraint_3867_);
v_lowerBound_3889_ = lean_ctor_get(v___x_3888_, 0);
if (lean_obj_tag(v_lowerBound_3889_) == 0)
{
lean_object* v___x_3890_; 
lean_inc_ref(v_b_3868_);
v___x_3890_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3888_, v_b_3868_, v___x_3879_, v___x_3887_, v___x_3881_, v_v_3880_);
v___y_3884_ = v___x_3890_;
goto v___jp_3883_;
}
else
{
lean_object* v_var_3891_; lean_object* v_irrelevant_3892_; lean_object* v_lowerBounds_3893_; lean_object* v_upperBounds_3894_; uint8_t v_lowerExact_3895_; uint8_t v_upperExact_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3911_; 
v_var_3891_ = lean_ctor_get(v_v_3880_, 0);
v_irrelevant_3892_ = lean_ctor_get(v_v_3880_, 1);
v_lowerBounds_3893_ = lean_ctor_get(v_v_3880_, 2);
v_upperBounds_3894_ = lean_ctor_get(v_v_3880_, 3);
v_lowerExact_3895_ = lean_ctor_get_uint8(v_v_3880_, sizeof(void*)*4);
v_upperExact_3896_ = lean_ctor_get_uint8(v_v_3880_, sizeof(void*)*4 + 1);
v_isSharedCheck_3911_ = !lean_is_exclusive(v_v_3880_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3898_ = v_v_3880_;
v_isShared_3899_ = v_isSharedCheck_3911_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_upperBounds_3894_);
lean_inc(v_lowerBounds_3893_);
lean_inc(v_irrelevant_3892_);
lean_inc(v_var_3891_);
lean_dec(v_v_3880_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3911_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; uint8_t v___y_3903_; 
lean_inc(v___x_3879_);
lean_inc_ref(v_b_3868_);
v___x_3900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3900_, 0, v_b_3868_);
lean_ctor_set(v___x_3900_, 1, v___x_3879_);
v___x_3901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
lean_ctor_set(v___x_3901_, 1, v_lowerBounds_3893_);
if (v_lowerExact_3895_ == 0)
{
v___y_3903_ = v___x_3887_;
goto v___jp_3902_;
}
else
{
lean_object* v___x_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; 
v___x_3908_ = lean_nat_abs(v___x_3879_);
v___x_3909_ = lean_unsigned_to_nat(1u);
v___x_3910_ = lean_nat_dec_eq(v___x_3908_, v___x_3909_);
lean_dec(v___x_3908_);
v___y_3903_ = v___x_3910_;
goto v___jp_3902_;
}
v___jp_3902_:
{
lean_object* v___x_3905_; 
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 2, v___x_3901_);
v___x_3905_ = v___x_3898_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_var_3891_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_irrelevant_3892_);
lean_ctor_set(v_reuseFailAlloc_3907_, 2, v___x_3901_);
lean_ctor_set(v_reuseFailAlloc_3907_, 3, v_upperBounds_3894_);
lean_ctor_set_uint8(v_reuseFailAlloc_3907_, sizeof(void*)*4 + 1, v_upperExact_3896_);
v___x_3905_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; 
lean_ctor_set_uint8(v___x_3905_, sizeof(void*)*4, v___y_3903_);
lean_inc_ref(v_b_3868_);
v___x_3906_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v___x_3888_, v_b_3868_, v___x_3879_, v___x_3887_, v___x_3881_, v___x_3905_);
v___y_3884_ = v___x_3906_;
goto v___jp_3883_;
}
}
}
}
}
else
{
lean_object* v_var_3912_; lean_object* v_irrelevant_3913_; lean_object* v_lowerBounds_3914_; lean_object* v_upperBounds_3915_; uint8_t v_lowerExact_3916_; uint8_t v_upperExact_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3925_; 
lean_dec(v___x_3879_);
v_var_3912_ = lean_ctor_get(v_v_3880_, 0);
v_irrelevant_3913_ = lean_ctor_get(v_v_3880_, 1);
v_lowerBounds_3914_ = lean_ctor_get(v_v_3880_, 2);
v_upperBounds_3915_ = lean_ctor_get(v_v_3880_, 3);
v_lowerExact_3916_ = lean_ctor_get_uint8(v_v_3880_, sizeof(void*)*4);
v_upperExact_3917_ = lean_ctor_get_uint8(v_v_3880_, sizeof(void*)*4 + 1);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_v_3880_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3919_ = v_v_3880_;
v_isShared_3920_ = v_isSharedCheck_3925_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_upperBounds_3915_);
lean_inc(v_lowerBounds_3914_);
lean_inc(v_irrelevant_3913_);
lean_inc(v_var_3912_);
lean_dec(v_v_3880_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3925_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3921_; lean_object* v___x_3923_; 
lean_inc_ref(v_b_3868_);
v___x_3921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3921_, 0, v_b_3868_);
lean_ctor_set(v___x_3921_, 1, v_irrelevant_3913_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 1, v___x_3921_);
v___x_3923_ = v___x_3919_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_var_3912_);
lean_ctor_set(v_reuseFailAlloc_3924_, 1, v___x_3921_);
lean_ctor_set(v_reuseFailAlloc_3924_, 2, v_lowerBounds_3914_);
lean_ctor_set(v_reuseFailAlloc_3924_, 3, v_upperBounds_3915_);
lean_ctor_set_uint8(v_reuseFailAlloc_3924_, sizeof(void*)*4, v_lowerExact_3916_);
lean_ctor_set_uint8(v_reuseFailAlloc_3924_, sizeof(void*)*4 + 1, v_upperExact_3917_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
v___y_3884_ = v___x_3923_;
goto v___jp_3883_;
}
}
}
v___jp_3883_:
{
lean_object* v___x_3885_; 
v___x_3885_ = lean_array_fset(v_xs_x27_3882_, v_a_3869_, v___y_3884_);
v_a_3872_ = v___x_3885_;
goto v___jp_3871_;
}
}
}
v___jp_3871_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = lean_unsigned_to_nat(1u);
v___x_3874_ = lean_nat_add(v_a_3869_, v___x_3873_);
lean_dec(v_a_3869_);
v_a_3869_ = v___x_3874_;
v_b_3870_ = v_a_3872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___boxed(lean_object* v_upperBound_3926_, lean_object* v_coeffs_3927_, lean_object* v_constraint_3928_, lean_object* v_b_3929_, lean_object* v_a_3930_, lean_object* v_b_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3926_, v_coeffs_3927_, v_constraint_3928_, v_b_3929_, v_a_3930_, v_b_3931_);
lean_dec(v_coeffs_3927_);
lean_dec(v_upperBound_3926_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(lean_object* v_n_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_){
_start:
{
if (lean_obj_tag(v_a_3934_) == 0)
{
lean_object* v___x_3936_; 
v___x_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3936_, 0, v_a_3935_);
return v___x_3936_;
}
else
{
lean_object* v_value_3937_; lean_object* v_tail_3938_; lean_object* v_coeffs_3939_; lean_object* v_constraint_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v_value_3937_ = lean_ctor_get(v_a_3934_, 1);
lean_inc(v_value_3937_);
v_tail_3938_ = lean_ctor_get(v_a_3934_, 2);
lean_inc(v_tail_3938_);
lean_dec_ref_known(v_a_3934_, 3);
v_coeffs_3939_ = lean_ctor_get(v_value_3937_, 0);
lean_inc(v_coeffs_3939_);
v_constraint_3940_ = lean_ctor_get(v_value_3937_, 1);
lean_inc_ref(v_constraint_3940_);
v___x_3941_ = lean_unsigned_to_nat(0u);
v___x_3942_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_n_3933_, v_coeffs_3939_, v_constraint_3940_, v_value_3937_, v___x_3941_, v_a_3935_);
lean_dec(v_coeffs_3939_);
v_a_3934_ = v_tail_3938_;
v_a_3935_ = v___x_3942_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1___boxed(lean_object* v_n_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3944_, v_a_3945_, v_a_3946_);
lean_dec(v_n_3944_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(lean_object* v_n_3948_, lean_object* v_as_3949_, size_t v_sz_3950_, size_t v_i_3951_, lean_object* v_b_3952_){
_start:
{
uint8_t v___x_3953_; 
v___x_3953_ = lean_usize_dec_lt(v_i_3951_, v_sz_3950_);
if (v___x_3953_ == 0)
{
return v_b_3952_;
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3955_; 
v_a_3954_ = lean_array_uget_borrowed(v_as_3949_, v_i_3951_);
lean_inc(v_a_3954_);
v___x_3955_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3948_, v_a_3954_, v_b_3952_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref_known(v___x_3955_, 1);
return v_a_3956_;
}
else
{
lean_object* v_a_3957_; size_t v___x_3958_; size_t v___x_3959_; 
v_a_3957_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3957_);
lean_dec_ref_known(v___x_3955_, 1);
v___x_3958_ = ((size_t)1ULL);
v___x_3959_ = lean_usize_add(v_i_3951_, v___x_3958_);
v_i_3951_ = v___x_3959_;
v_b_3952_ = v_a_3957_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3___boxed(lean_object* v_n_3961_, lean_object* v_as_3962_, lean_object* v_sz_3963_, lean_object* v_i_3964_, lean_object* v_b_3965_){
_start:
{
size_t v_sz_boxed_3966_; size_t v_i_boxed_3967_; lean_object* v_res_3968_; 
v_sz_boxed_3966_ = lean_unbox_usize(v_sz_3963_);
lean_dec(v_sz_3963_);
v_i_boxed_3967_ = lean_unbox_usize(v_i_3964_);
lean_dec(v_i_3964_);
v_res_3968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_n_3961_, v_as_3962_, v_sz_boxed_3966_, v_i_boxed_3967_, v_b_3965_);
lean_dec_ref(v_as_3962_);
lean_dec(v_n_3961_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(lean_object* v_p_3971_){
_start:
{
lean_object* v_constraints_3972_; lean_object* v_numVars_3973_; lean_object* v_buckets_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v_data_3977_; size_t v_sz_3978_; size_t v___x_3979_; lean_object* v___x_3980_; 
v_constraints_3972_ = lean_ctor_get(v_p_3971_, 2);
lean_inc_ref(v_constraints_3972_);
v_numVars_3973_ = lean_ctor_get(v_p_3971_, 1);
lean_inc_n(v_numVars_3973_, 2);
lean_dec_ref(v_p_3971_);
v_buckets_3974_ = lean_ctor_get(v_constraints_3972_, 1);
lean_inc_ref(v_buckets_3974_);
lean_dec_ref(v_constraints_3972_);
v___x_3975_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_3976_ = l_List_range(v_numVars_3973_);
v_data_3977_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v___x_3975_, v___x_3976_);
lean_dec(v___x_3976_);
v_sz_3978_ = lean_array_size(v_buckets_3974_);
v___x_3979_ = ((size_t)0ULL);
v___x_3980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_numVars_3973_, v_buckets_3974_, v_sz_3978_, v___x_3979_, v_data_3977_);
lean_dec_ref(v_buckets_3974_);
lean_dec(v_numVars_3973_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(lean_object* v_upperBound_3981_, lean_object* v_coeffs_3982_, lean_object* v_constraint_3983_, lean_object* v_b_3984_, lean_object* v_inst_3985_, lean_object* v_R_3986_, lean_object* v_a_3987_, lean_object* v_b_3988_, lean_object* v_c_3989_){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3981_, v_coeffs_3982_, v_constraint_3983_, v_b_3984_, v_a_3987_, v_b_3988_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___boxed(lean_object* v_upperBound_3991_, lean_object* v_coeffs_3992_, lean_object* v_constraint_3993_, lean_object* v_b_3994_, lean_object* v_inst_3995_, lean_object* v_R_3996_, lean_object* v_a_3997_, lean_object* v_b_3998_, lean_object* v_c_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(v_upperBound_3991_, v_coeffs_3992_, v_constraint_3993_, v_b_3994_, v_inst_3995_, v_R_3996_, v_a_3997_, v_b_3998_, v_c_3999_);
lean_dec(v_coeffs_3992_);
lean_dec(v_upperBound_3991_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(lean_object* v_cls_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v_toCold_4010_; lean_object* v_options_4011_; uint8_t v_hasTrace_4012_; 
v_toCold_4010_ = lean_ctor_get(v___y_4007_, 0);
v_options_4011_ = lean_ctor_get(v_toCold_4010_, 2);
v_hasTrace_4012_ = lean_ctor_get_uint8(v_options_4011_, sizeof(void*)*1);
if (v_hasTrace_4012_ == 0)
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
lean_dec(v_cls_4004_);
v___x_4013_ = lean_box(v_hasTrace_4012_);
v___x_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
return v___x_4014_;
}
else
{
lean_object* v_inheritedTraceOptions_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; uint8_t v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
v_inheritedTraceOptions_4015_ = lean_ctor_get(v_toCold_4010_, 11);
v___x_4016_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4017_ = l_Lean_Name_append(v___x_4016_, v_cls_4004_);
v___x_4018_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4015_, v_options_4011_, v___x_4017_);
lean_dec(v___x_4017_);
v___x_4019_ = lean_box(v___x_4018_);
v___x_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
return v___x_4020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___boxed(lean_object* v_cls_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(lean_object* v___x_4028_, lean_object* v_fst_4029_, lean_object* v_snd_4030_, lean_object* v_fst_4031_, lean_object* v_____r_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4028_);
v___x_4039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4039_, 0, v_fst_4029_);
lean_ctor_set(v___x_4039_, 1, v_snd_4030_);
v___x_4040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4040_, 0, v_fst_4031_);
lean_ctor_set(v___x_4040_, 1, v___x_4039_);
v___x_4041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4038_);
lean_ctor_set(v___x_4041_, 1, v___x_4040_);
v___x_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
return v___x_4043_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0___boxed(lean_object* v___x_4044_, lean_object* v_fst_4045_, lean_object* v_snd_4046_, lean_object* v_fst_4047_, lean_object* v_____r_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4044_, v_fst_4045_, v_snd_4046_, v_fst_4047_, v_____r_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
return v_res_4054_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4055_; double v___x_4056_; 
v___x_4055_ = lean_unsigned_to_nat(0u);
v___x_4056_ = lean_float_of_nat(v___x_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(lean_object* v_cls_4059_, lean_object* v_msg_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v_ref_4066_; lean_object* v___x_4067_; lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4113_; 
v_ref_4066_ = lean_ctor_get(v___y_4063_, 2);
v___x_4067_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4070_ = v___x_4067_;
v_isShared_4071_ = v_isSharedCheck_4113_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4067_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4113_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4072_; lean_object* v_traceState_4073_; lean_object* v_env_4074_; lean_object* v_nextMacroScope_4075_; lean_object* v_ngen_4076_; lean_object* v_auxDeclNGen_4077_; lean_object* v_cache_4078_; lean_object* v_recordedDeps_4079_; lean_object* v_messages_4080_; lean_object* v_infoState_4081_; lean_object* v_snapshotTasks_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4112_; 
v___x_4072_ = lean_st_ref_take(v___y_4064_);
v_traceState_4073_ = lean_ctor_get(v___x_4072_, 4);
v_env_4074_ = lean_ctor_get(v___x_4072_, 0);
v_nextMacroScope_4075_ = lean_ctor_get(v___x_4072_, 1);
v_ngen_4076_ = lean_ctor_get(v___x_4072_, 2);
v_auxDeclNGen_4077_ = lean_ctor_get(v___x_4072_, 3);
v_cache_4078_ = lean_ctor_get(v___x_4072_, 5);
v_recordedDeps_4079_ = lean_ctor_get(v___x_4072_, 6);
v_messages_4080_ = lean_ctor_get(v___x_4072_, 7);
v_infoState_4081_ = lean_ctor_get(v___x_4072_, 8);
v_snapshotTasks_4082_ = lean_ctor_get(v___x_4072_, 9);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4084_ = v___x_4072_;
v_isShared_4085_ = v_isSharedCheck_4112_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_snapshotTasks_4082_);
lean_inc(v_infoState_4081_);
lean_inc(v_messages_4080_);
lean_inc(v_recordedDeps_4079_);
lean_inc(v_cache_4078_);
lean_inc(v_traceState_4073_);
lean_inc(v_auxDeclNGen_4077_);
lean_inc(v_ngen_4076_);
lean_inc(v_nextMacroScope_4075_);
lean_inc(v_env_4074_);
lean_dec(v___x_4072_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4112_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
uint64_t v_tid_4086_; lean_object* v_traces_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4111_; 
v_tid_4086_ = lean_ctor_get_uint64(v_traceState_4073_, sizeof(void*)*1);
v_traces_4087_ = lean_ctor_get(v_traceState_4073_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v_traceState_4073_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4089_ = v_traceState_4073_;
v_isShared_4090_ = v_isSharedCheck_4111_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_traces_4087_);
lean_dec(v_traceState_4073_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4111_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; double v___x_4093_; uint8_t v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4102_; 
v___x_4091_ = lean_box(0);
v___x_4092_ = lean_box(0);
v___x_4093_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4094_ = 0;
v___x_4095_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4096_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4096_, 0, v_cls_4059_);
lean_ctor_set(v___x_4096_, 1, v___x_4092_);
lean_ctor_set(v___x_4096_, 2, v___x_4095_);
lean_ctor_set_float(v___x_4096_, sizeof(void*)*3, v___x_4093_);
lean_ctor_set_float(v___x_4096_, sizeof(void*)*3 + 8, v___x_4093_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*3 + 16, v___x_4094_);
v___x_4097_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4098_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4096_);
lean_ctor_set(v___x_4098_, 1, v_a_4068_);
lean_ctor_set(v___x_4098_, 2, v___x_4097_);
lean_inc(v_ref_4066_);
v___x_4099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4099_, 0, v_ref_4066_);
lean_ctor_set(v___x_4099_, 1, v___x_4098_);
v___x_4100_ = l_Lean_PersistentArray_push___redArg(v_traces_4087_, v___x_4099_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v___x_4100_);
v___x_4102_ = v___x_4089_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4100_);
lean_ctor_set_uint64(v_reuseFailAlloc_4110_, sizeof(void*)*1, v_tid_4086_);
v___x_4102_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
lean_object* v___x_4104_; 
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 4, v___x_4102_);
v___x_4104_ = v___x_4084_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_env_4074_);
lean_ctor_set(v_reuseFailAlloc_4109_, 1, v_nextMacroScope_4075_);
lean_ctor_set(v_reuseFailAlloc_4109_, 2, v_ngen_4076_);
lean_ctor_set(v_reuseFailAlloc_4109_, 3, v_auxDeclNGen_4077_);
lean_ctor_set(v_reuseFailAlloc_4109_, 4, v___x_4102_);
lean_ctor_set(v_reuseFailAlloc_4109_, 5, v_cache_4078_);
lean_ctor_set(v_reuseFailAlloc_4109_, 6, v_recordedDeps_4079_);
lean_ctor_set(v_reuseFailAlloc_4109_, 7, v_messages_4080_);
lean_ctor_set(v_reuseFailAlloc_4109_, 8, v_infoState_4081_);
lean_ctor_set(v_reuseFailAlloc_4109_, 9, v_snapshotTasks_4082_);
v___x_4104_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_object* v___x_4105_; lean_object* v___x_4107_; 
v___x_4105_ = lean_st_ref_put(v___y_4064_, v___x_4104_);
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 0, v___x_4091_);
v___x_4107_ = v___x_4070_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4091_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___boxed(lean_object* v_cls_4114_, lean_object* v_msg_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4114_, v_msg_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
return v_res_4121_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v_cls_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v_cls_4122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4123_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4124_ = l_Lean_Name_append(v___x_4123_, v_cls_4122_);
return v___x_4124_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__1));
v___x_4127_ = l_Lean_stringToMessageData(v___x_4126_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(lean_object* v_upperBound_4128_, lean_object* v___y_4129_, lean_object* v_a_4130_, lean_object* v_b_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_a_4138_; lean_object* v___y_4143_; uint8_t v___x_4162_; 
v___x_4162_ = lean_nat_dec_lt(v_a_4130_, v_upperBound_4128_);
if (v___x_4162_ == 0)
{
lean_object* v___x_4163_; 
lean_dec(v_a_4130_);
v___x_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4163_, 0, v_b_4131_);
return v___x_4163_;
}
else
{
lean_object* v_snd_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4235_; 
v_snd_4164_ = lean_ctor_get(v_b_4131_, 1);
v_isSharedCheck_4235_ = !lean_is_exclusive(v_b_4131_);
if (v_isSharedCheck_4235_ == 0)
{
lean_object* v_unused_4236_; 
v_unused_4236_ = lean_ctor_get(v_b_4131_, 0);
lean_dec(v_unused_4236_);
v___x_4166_ = v_b_4131_;
v_isShared_4167_ = v_isSharedCheck_4235_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_snd_4164_);
lean_dec(v_b_4131_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4235_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v_snd_4168_; lean_object* v_fst_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4234_; 
v_snd_4168_ = lean_ctor_get(v_snd_4164_, 1);
v_fst_4169_ = lean_ctor_get(v_snd_4164_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v_snd_4164_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4171_ = v_snd_4164_;
v_isShared_4172_ = v_isSharedCheck_4234_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_snd_4168_);
lean_inc(v_fst_4169_);
lean_dec(v_snd_4164_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4234_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v_fst_4173_; lean_object* v_snd_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4233_; 
v_fst_4173_ = lean_ctor_get(v_snd_4168_, 0);
v_snd_4174_ = lean_ctor_get(v_snd_4168_, 1);
v_isSharedCheck_4233_ = !lean_is_exclusive(v_snd_4168_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4176_ = v_snd_4168_;
v_isShared_4177_ = v_isSharedCheck_4233_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_snd_4174_);
lean_inc(v_fst_4173_);
lean_dec(v_snd_4168_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4233_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4178_; lean_object* v_bestIdx_4189_; lean_object* v_cls_4190_; lean_object* v___x_4191_; uint8_t v___x_4195_; lean_object* v___x_4196_; uint8_t v___x_4197_; uint8_t v___y_4227_; 
v___x_4178_ = lean_box(0);
v_bestIdx_4189_ = lean_unsigned_to_nat(0u);
v_cls_4190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4191_ = lean_array_fget_borrowed(v___y_4129_, v_a_4130_);
v___x_4195_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4191_);
v___x_4196_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4191_);
v___x_4197_ = lean_nat_dec_eq(v___x_4196_, v_bestIdx_4189_);
if (v___x_4197_ == 0)
{
uint8_t v___x_4232_; 
v___x_4232_ = lean_unbox(v_snd_4174_);
if (v___x_4232_ == 0)
{
if (v___x_4195_ == 0)
{
goto v___jp_4229_;
}
else
{
lean_del_object(v___x_4176_);
lean_del_object(v___x_4171_);
lean_del_object(v___x_4166_);
goto v___jp_4198_;
}
}
else
{
goto v___jp_4229_;
}
}
else
{
lean_del_object(v___x_4176_);
lean_del_object(v___x_4171_);
lean_del_object(v___x_4166_);
goto v___jp_4198_;
}
v___jp_4179_:
{
lean_object* v___x_4181_; 
if (v_isShared_4177_ == 0)
{
v___x_4181_ = v___x_4176_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_fst_4173_);
lean_ctor_set(v_reuseFailAlloc_4188_, 1, v_snd_4174_);
v___x_4181_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
lean_object* v___x_4183_; 
if (v_isShared_4172_ == 0)
{
lean_ctor_set(v___x_4171_, 1, v___x_4181_);
v___x_4183_ = v___x_4171_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_fst_4169_);
lean_ctor_set(v_reuseFailAlloc_4187_, 1, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4185_; 
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 1, v___x_4183_);
lean_ctor_set(v___x_4166_, 0, v___x_4178_);
v___x_4185_ = v___x_4166_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4178_);
lean_ctor_set(v_reuseFailAlloc_4186_, 1, v___x_4183_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
v_a_4138_ = v___x_4185_;
goto v___jp_4137_;
}
}
}
}
v___jp_4192_:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = lean_box(0);
lean_inc(v___x_4191_);
v___x_4194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4191_, v_fst_4173_, v_snd_4174_, v_fst_4169_, v___x_4193_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
v___y_4143_ = v___x_4194_;
goto v___jp_4142_;
}
v___jp_4198_:
{
if (v___x_4197_ == 0)
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
lean_dec(v_snd_4174_);
lean_dec(v_fst_4173_);
lean_dec(v_fst_4169_);
v___x_4199_ = lean_box(v___x_4195_);
v___x_4200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4196_);
lean_ctor_set(v___x_4200_, 1, v___x_4199_);
lean_inc(v_a_4130_);
v___x_4201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4201_, 0, v_a_4130_);
lean_ctor_set(v___x_4201_, 1, v___x_4200_);
v___x_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4178_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
v_a_4138_ = v___x_4202_;
goto v___jp_4137_;
}
else
{
lean_object* v_toCold_4203_; lean_object* v_options_4204_; uint8_t v_hasTrace_4205_; 
lean_dec(v___x_4196_);
v_toCold_4203_ = lean_ctor_get(v___y_4134_, 0);
v_options_4204_ = lean_ctor_get(v_toCold_4203_, 2);
v_hasTrace_4205_ = lean_ctor_get_uint8(v_options_4204_, sizeof(void*)*1);
if (v_hasTrace_4205_ == 0)
{
goto v___jp_4192_;
}
else
{
lean_object* v_inheritedTraceOptions_4206_; lean_object* v___x_4207_; uint8_t v___x_4208_; 
v_inheritedTraceOptions_4206_ = lean_ctor_get(v_toCold_4203_, 11);
v___x_4207_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_4208_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4206_, v_options_4204_, v___x_4207_);
if (v___x_4208_ == 0)
{
goto v___jp_4192_;
}
else
{
lean_object* v_var_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v_var_4209_ = lean_ctor_get(v___x_4191_, 0);
v___x_4210_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4209_);
v___x_4211_ = l_Nat_reprFast(v_var_4209_);
v___x_4212_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4211_);
v___x_4213_ = l_Lean_MessageData_ofFormat(v___x_4212_);
v___x_4214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4210_);
lean_ctor_set(v___x_4214_, 1, v___x_4213_);
v___x_4215_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4190_, v___x_4214_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4217_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v___x_4215_, 1);
lean_inc(v___x_4191_);
v___x_4217_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4191_, v_fst_4173_, v_snd_4174_, v_fst_4169_, v_a_4216_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
v___y_4143_ = v___x_4217_;
goto v___jp_4142_;
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
lean_dec(v_snd_4174_);
lean_dec(v_fst_4173_);
lean_dec(v_fst_4169_);
lean_dec(v_a_4130_);
v_a_4218_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4220_ = v___x_4215_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4215_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4218_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
}
}
}
v___jp_4226_:
{
if (v___y_4227_ == 0)
{
lean_dec(v___x_4196_);
goto v___jp_4179_;
}
else
{
uint8_t v___x_4228_; 
v___x_4228_ = lean_nat_dec_lt(v___x_4196_, v_fst_4173_);
if (v___x_4228_ == 0)
{
lean_dec(v___x_4196_);
goto v___jp_4179_;
}
else
{
lean_del_object(v___x_4176_);
lean_del_object(v___x_4171_);
lean_del_object(v___x_4166_);
goto v___jp_4198_;
}
}
}
v___jp_4229_:
{
if (v___x_4195_ == 0)
{
uint8_t v___x_4230_; 
v___x_4230_ = lean_unbox(v_snd_4174_);
if (v___x_4230_ == 0)
{
v___y_4227_ = v___x_4162_;
goto v___jp_4226_;
}
else
{
v___y_4227_ = v___x_4195_;
goto v___jp_4226_;
}
}
else
{
uint8_t v___x_4231_; 
v___x_4231_ = lean_unbox(v_snd_4174_);
v___y_4227_ = v___x_4231_;
goto v___jp_4226_;
}
}
}
}
}
}
v___jp_4137_:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4139_ = lean_unsigned_to_nat(1u);
v___x_4140_ = lean_nat_add(v_a_4130_, v___x_4139_);
lean_dec(v_a_4130_);
v_a_4130_ = v___x_4140_;
v_b_4131_ = v_a_4138_;
goto _start;
}
v___jp_4142_:
{
if (lean_obj_tag(v___y_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4153_; 
v_a_4144_ = lean_ctor_get(v___y_4143_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___y_4143_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4146_ = v___y_4143_;
v_isShared_4147_ = v_isSharedCheck_4153_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___y_4143_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4153_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
if (lean_obj_tag(v_a_4144_) == 0)
{
lean_object* v_a_4148_; lean_object* v___x_4150_; 
lean_dec(v_a_4130_);
v_a_4148_ = lean_ctor_get(v_a_4144_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v_a_4144_, 1);
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v_a_4148_);
v___x_4150_ = v___x_4146_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4148_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
else
{
lean_object* v_a_4152_; 
lean_del_object(v___x_4146_);
v_a_4152_ = lean_ctor_get(v_a_4144_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v_a_4144_, 1);
v_a_4138_ = v_a_4152_;
goto v___jp_4137_;
}
}
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
lean_dec(v_a_4130_);
v_a_4154_ = lean_ctor_get(v___y_4143_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___y_4143_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___y_4143_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___y_4143_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___boxed(lean_object* v_upperBound_4237_, lean_object* v___y_4238_, lean_object* v_a_4239_, lean_object* v_b_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4237_, v___y_4238_, v_a_4239_, v_b_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec_ref(v___y_4238_);
lean_dec(v_upperBound_4237_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(lean_object* v_as_4247_, size_t v_i_4248_, size_t v_stop_4249_, lean_object* v_b_4250_){
_start:
{
lean_object* v___y_4252_; uint8_t v___x_4256_; 
v___x_4256_ = lean_usize_dec_eq(v_i_4248_, v_stop_4249_);
if (v___x_4256_ == 0)
{
lean_object* v___x_4257_; uint8_t v___x_4260_; 
v___x_4257_ = lean_array_uget_borrowed(v_as_4247_, v_i_4248_);
v___x_4260_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v___x_4257_);
if (v___x_4260_ == 0)
{
goto v___jp_4258_;
}
else
{
if (v___x_4256_ == 0)
{
v___y_4252_ = v_b_4250_;
goto v___jp_4251_;
}
else
{
goto v___jp_4258_;
}
}
v___jp_4258_:
{
lean_object* v___x_4259_; 
lean_inc(v___x_4257_);
v___x_4259_ = lean_array_push(v_b_4250_, v___x_4257_);
v___y_4252_ = v___x_4259_;
goto v___jp_4251_;
}
}
else
{
return v_b_4250_;
}
v___jp_4251_:
{
size_t v___x_4253_; size_t v___x_4254_; 
v___x_4253_ = ((size_t)1ULL);
v___x_4254_ = lean_usize_add(v_i_4248_, v___x_4253_);
v_i_4248_ = v___x_4254_;
v_b_4250_ = v___y_4252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___boxed(lean_object* v_as_4261_, lean_object* v_i_4262_, lean_object* v_stop_4263_, lean_object* v_b_4264_){
_start:
{
size_t v_i_boxed_4265_; size_t v_stop_boxed_4266_; lean_object* v_res_4267_; 
v_i_boxed_4265_ = lean_unbox_usize(v_i_4262_);
lean_dec(v_i_4262_);
v_stop_boxed_4266_ = lean_unbox_usize(v_stop_4263_);
lean_dec(v_stop_4263_);
v_res_4267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_as_4261_, v_i_boxed_4265_, v_stop_boxed_4266_, v_b_4264_);
lean_dec_ref(v_as_4261_);
return v_res_4267_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2(void){
_start:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4271_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__1));
v___x_4272_ = l_Lean_MessageData_ofFormat(v___x_4271_);
return v___x_4272_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4273_ = lean_box(1);
v___x_4274_ = l_Lean_MessageData_ofFormat(v___x_4273_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(lean_object* v_a_4276_, lean_object* v_a_4277_){
_start:
{
if (lean_obj_tag(v_a_4276_) == 0)
{
lean_object* v___x_4278_; 
v___x_4278_ = l_List_reverse___redArg(v_a_4277_);
return v___x_4278_;
}
else
{
lean_object* v_head_4279_; lean_object* v_snd_4280_; lean_object* v_tail_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4328_; 
v_head_4279_ = lean_ctor_get(v_a_4276_, 0);
lean_inc(v_head_4279_);
v_snd_4280_ = lean_ctor_get(v_head_4279_, 1);
lean_inc(v_snd_4280_);
v_tail_4281_ = lean_ctor_get(v_a_4276_, 1);
v_isSharedCheck_4328_ = !lean_is_exclusive(v_a_4276_);
if (v_isSharedCheck_4328_ == 0)
{
lean_object* v_unused_4329_; 
v_unused_4329_ = lean_ctor_get(v_a_4276_, 0);
lean_dec(v_unused_4329_);
v___x_4283_ = v_a_4276_;
v_isShared_4284_ = v_isSharedCheck_4328_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_tail_4281_);
lean_dec(v_a_4276_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4328_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v_fst_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4326_; 
v_fst_4285_ = lean_ctor_get(v_head_4279_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v_head_4279_);
if (v_isSharedCheck_4326_ == 0)
{
lean_object* v_unused_4327_; 
v_unused_4327_ = lean_ctor_get(v_head_4279_, 1);
lean_dec(v_unused_4327_);
v___x_4287_ = v_head_4279_;
v_isShared_4288_ = v_isSharedCheck_4326_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_fst_4285_);
lean_dec(v_head_4279_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4326_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v_fst_4289_; lean_object* v_snd_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4325_; 
v_fst_4289_ = lean_ctor_get(v_snd_4280_, 0);
v_snd_4290_ = lean_ctor_get(v_snd_4280_, 1);
v_isSharedCheck_4325_ = !lean_is_exclusive(v_snd_4280_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4292_ = v_snd_4280_;
v_isShared_4293_ = v_isSharedCheck_4325_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_snd_4290_);
lean_inc(v_fst_4289_);
lean_dec(v_snd_4280_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4325_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4299_; 
v___x_4294_ = l_Nat_reprFast(v_fst_4285_);
v___x_4295_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4294_);
v___x_4296_ = l_Lean_MessageData_ofFormat(v___x_4295_);
v___x_4297_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2);
if (v_isShared_4293_ == 0)
{
lean_ctor_set_tag(v___x_4292_, 7);
lean_ctor_set(v___x_4292_, 1, v___x_4297_);
lean_ctor_set(v___x_4292_, 0, v___x_4296_);
v___x_4299_ = v___x_4292_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4296_);
lean_ctor_set(v_reuseFailAlloc_4324_, 1, v___x_4297_);
v___x_4299_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
lean_object* v___x_4300_; lean_object* v___x_4302_; 
v___x_4300_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3);
if (v_isShared_4288_ == 0)
{
lean_ctor_set_tag(v___x_4287_, 7);
lean_ctor_set(v___x_4287_, 1, v___x_4300_);
lean_ctor_set(v___x_4287_, 0, v___x_4299_);
v___x_4302_ = v___x_4287_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v___x_4299_);
lean_ctor_set(v_reuseFailAlloc_4323_, 1, v___x_4300_);
v___x_4302_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___y_4309_; uint8_t v___x_4320_; 
v___x_4303_ = l_Nat_reprFast(v_fst_4289_);
v___x_4304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4303_);
v___x_4305_ = l_Lean_MessageData_ofFormat(v___x_4304_);
v___x_4306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
lean_ctor_set(v___x_4306_, 1, v___x_4297_);
v___x_4307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
lean_ctor_set(v___x_4307_, 1, v___x_4300_);
v___x_4320_ = lean_unbox(v_snd_4290_);
lean_dec(v_snd_4290_);
if (v___x_4320_ == 0)
{
lean_object* v___x_4321_; 
v___x_4321_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__4));
v___y_4309_ = v___x_4321_;
goto v___jp_4308_;
}
else
{
lean_object* v___x_4322_; 
v___x_4322_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4));
v___y_4309_ = v___x_4322_;
goto v___jp_4308_;
}
v___jp_4308_:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4317_; 
lean_inc_ref(v___y_4309_);
v___x_4310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4310_, 0, v___y_4309_);
v___x_4311_ = l_Lean_MessageData_ofFormat(v___x_4310_);
v___x_4312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4307_);
lean_ctor_set(v___x_4312_, 1, v___x_4311_);
v___x_4313_ = l_Lean_MessageData_paren(v___x_4312_);
v___x_4314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4302_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
v___x_4315_ = l_Lean_MessageData_paren(v___x_4314_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 1, v_a_4277_);
lean_ctor_set(v___x_4283_, 0, v___x_4315_);
v___x_4317_ = v___x_4283_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4315_);
lean_ctor_set(v_reuseFailAlloc_4319_, 1, v_a_4277_);
v___x_4317_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
v_a_4276_ = v_tail_4281_;
v_a_4277_ = v___x_4317_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(size_t v_sz_4330_, size_t v_i_4331_, lean_object* v_bs_4332_){
_start:
{
uint8_t v___x_4333_; 
v___x_4333_ = lean_usize_dec_lt(v_i_4331_, v_sz_4330_);
if (v___x_4333_ == 0)
{
return v_bs_4332_;
}
else
{
lean_object* v_v_4334_; lean_object* v_var_4335_; lean_object* v___x_4336_; lean_object* v_bs_x27_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; size_t v___x_4343_; size_t v___x_4344_; lean_object* v___x_4345_; 
v_v_4334_ = lean_array_uget(v_bs_4332_, v_i_4331_);
v_var_4335_ = lean_ctor_get(v_v_4334_, 0);
lean_inc(v_var_4335_);
v___x_4336_ = lean_unsigned_to_nat(0u);
v_bs_x27_4337_ = lean_array_uset(v_bs_4332_, v_i_4331_, v___x_4336_);
v___x_4338_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_v_4334_);
v___x_4339_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_v_4334_);
lean_dec(v_v_4334_);
v___x_4340_ = lean_box(v___x_4339_);
v___x_4341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4338_);
lean_ctor_set(v___x_4341_, 1, v___x_4340_);
v___x_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4342_, 0, v_var_4335_);
lean_ctor_set(v___x_4342_, 1, v___x_4341_);
v___x_4343_ = ((size_t)1ULL);
v___x_4344_ = lean_usize_add(v_i_4331_, v___x_4343_);
v___x_4345_ = lean_array_uset(v_bs_x27_4337_, v_i_4331_, v___x_4342_);
v_i_4331_ = v___x_4344_;
v_bs_4332_ = v___x_4345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___boxed(lean_object* v_sz_4347_, lean_object* v_i_4348_, lean_object* v_bs_4349_){
_start:
{
size_t v_sz_boxed_4350_; size_t v_i_boxed_4351_; lean_object* v_res_4352_; 
v_sz_boxed_4350_ = lean_unbox_usize(v_sz_4347_);
lean_dec(v_sz_4347_);
v_i_boxed_4351_ = lean_unbox_usize(v_i_4348_);
lean_dec(v_i_4348_);
v_res_4352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_boxed_4350_, v_i_boxed_4351_, v_bs_4349_);
return v_res_4352_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1(void){
_start:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4354_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0));
v___x_4355_ = l_Lean_stringToMessageData(v___x_4354_);
return v___x_4355_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4(void){
_start:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4359_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3));
v___x_4360_ = l_Lean_stringToMessageData(v___x_4359_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(lean_object* v_data_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_){
_start:
{
lean_object* v___x_4367_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v_bestIdx_4373_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4501_; lean_object* v___x_4525_; lean_object* v___x_4526_; uint8_t v___x_4527_; 
v___x_4367_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default));
v_bestIdx_4373_ = lean_unsigned_to_nat(0u);
v___x_4525_ = lean_array_get_size(v_data_4361_);
v___x_4526_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_4527_ = lean_nat_dec_lt(v_bestIdx_4373_, v___x_4525_);
if (v___x_4527_ == 0)
{
v___y_4501_ = v___x_4526_;
goto v___jp_4500_;
}
else
{
uint8_t v___x_4528_; 
v___x_4528_ = lean_nat_dec_le(v___x_4525_, v___x_4525_);
if (v___x_4528_ == 0)
{
if (v___x_4527_ == 0)
{
v___y_4501_ = v___x_4526_;
goto v___jp_4500_;
}
else
{
size_t v___x_4529_; size_t v___x_4530_; lean_object* v___x_4531_; 
v___x_4529_ = ((size_t)0ULL);
v___x_4530_ = lean_usize_of_nat(v___x_4525_);
v___x_4531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4361_, v___x_4529_, v___x_4530_, v___x_4526_);
v___y_4501_ = v___x_4531_;
goto v___jp_4500_;
}
}
else
{
size_t v___x_4532_; size_t v___x_4533_; lean_object* v___x_4534_; 
v___x_4532_ = ((size_t)0ULL);
v___x_4533_ = lean_usize_of_nat(v___x_4525_);
v___x_4534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4361_, v___x_4532_, v___x_4533_, v___x_4526_);
v___y_4501_ = v___x_4534_;
goto v___jp_4500_;
}
}
v___jp_4368_:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4371_ = lean_array_get(v___x_4367_, v___y_4370_, v___y_4369_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4370_);
v___x_4372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4371_);
return v___x_4372_;
}
v___jp_4374_:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4382_ = lean_array_get_borrowed(v___x_4367_, v___y_4377_, v_bestIdx_4373_);
v___x_4383_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4382_);
v___x_4384_ = lean_nat_dec_eq(v___x_4383_, v_bestIdx_4373_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; lean_object* v___x_4386_; uint8_t v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4385_ = lean_unsigned_to_nat(1u);
v___x_4386_ = lean_array_get_size(v___y_4377_);
v___x_4387_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4382_);
v___x_4388_ = lean_box(0);
v___x_4389_ = lean_box(v___x_4387_);
v___x_4390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4383_);
lean_ctor_set(v___x_4390_, 1, v___x_4389_);
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v_bestIdx_4373_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4388_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v___x_4386_, v___y_4377_, v___x_4385_, v___x_4392_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4448_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4396_ = v___x_4393_;
v_isShared_4397_ = v_isSharedCheck_4448_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4393_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4448_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v_fst_4398_; 
v_fst_4398_ = lean_ctor_get(v_a_4394_, 0);
if (lean_obj_tag(v_fst_4398_) == 0)
{
lean_object* v_snd_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4442_; 
lean_del_object(v___x_4396_);
v_snd_4399_ = lean_ctor_get(v_a_4394_, 1);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_a_4394_);
if (v_isSharedCheck_4442_ == 0)
{
lean_object* v_unused_4443_; 
v_unused_4443_ = lean_ctor_get(v_a_4394_, 0);
lean_dec(v_unused_4443_);
v___x_4401_ = v_a_4394_;
v_isShared_4402_ = v_isSharedCheck_4442_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_snd_4399_);
lean_dec(v_a_4394_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4442_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v_fst_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4440_; 
v_fst_4403_ = lean_ctor_get(v_snd_4399_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v_snd_4399_);
if (v_isSharedCheck_4440_ == 0)
{
lean_object* v_unused_4441_; 
v_unused_4441_ = lean_ctor_get(v_snd_4399_, 1);
lean_dec(v_unused_4441_);
v___x_4405_ = v_snd_4399_;
v_isShared_4406_ = v_isSharedCheck_4440_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_fst_4403_);
lean_dec(v_snd_4399_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4440_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4407_; 
lean_inc_ref(v___y_4376_);
lean_inc(v___y_4381_);
lean_inc_ref(v___y_4380_);
lean_inc(v___y_4379_);
lean_inc_ref(v___y_4378_);
v___x_4407_ = lean_apply_5(v___y_4376_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, lean_box(0));
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; uint8_t v___x_4409_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc(v_a_4408_);
lean_dec_ref_known(v___x_4407_, 1);
v___x_4409_ = lean_unbox(v_a_4408_);
lean_dec(v_a_4408_);
if (v___x_4409_ == 0)
{
lean_del_object(v___x_4405_);
lean_del_object(v___x_4401_);
lean_dec(v___y_4375_);
v___y_4369_ = v_fst_4403_;
v___y_4370_ = v___y_4377_;
goto v___jp_4368_;
}
else
{
lean_object* v___x_4410_; lean_object* v_var_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4417_; 
v___x_4410_ = lean_array_get_borrowed(v___x_4367_, v___y_4377_, v_fst_4403_);
v_var_4411_ = lean_ctor_get(v___x_4410_, 0);
v___x_4412_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4411_);
v___x_4413_ = l_Nat_reprFast(v_var_4411_);
v___x_4414_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4413_);
v___x_4415_ = l_Lean_MessageData_ofFormat(v___x_4414_);
if (v_isShared_4406_ == 0)
{
lean_ctor_set_tag(v___x_4405_, 7);
lean_ctor_set(v___x_4405_, 1, v___x_4415_);
lean_ctor_set(v___x_4405_, 0, v___x_4412_);
v___x_4417_ = v___x_4405_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4412_);
lean_ctor_set(v_reuseFailAlloc_4431_, 1, v___x_4415_);
v___x_4417_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
lean_object* v___x_4418_; lean_object* v___x_4420_; 
v___x_4418_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
if (v_isShared_4402_ == 0)
{
lean_ctor_set_tag(v___x_4401_, 7);
lean_ctor_set(v___x_4401_, 1, v___x_4418_);
lean_ctor_set(v___x_4401_, 0, v___x_4417_);
v___x_4420_ = v___x_4401_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v___x_4417_);
lean_ctor_set(v_reuseFailAlloc_4430_, 1, v___x_4418_);
v___x_4420_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
lean_object* v___x_4421_; 
v___x_4421_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4375_, v___x_4420_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_dec_ref_known(v___x_4421_, 1);
v___y_4369_ = v_fst_4403_;
v___y_4370_ = v___y_4377_;
goto v___jp_4368_;
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
lean_dec(v_fst_4403_);
lean_dec_ref(v___y_4377_);
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v___x_4421_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4421_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_a_4422_);
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
}
}
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
lean_del_object(v___x_4405_);
lean_dec(v_fst_4403_);
lean_del_object(v___x_4401_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4375_);
v_a_4432_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4407_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4407_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
}
}
else
{
lean_object* v_val_4444_; lean_object* v___x_4446_; 
lean_inc_ref(v_fst_4398_);
lean_dec(v_a_4394_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4375_);
v_val_4444_ = lean_ctor_get(v_fst_4398_, 0);
lean_inc(v_val_4444_);
lean_dec_ref_known(v_fst_4398_, 1);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 0, v_val_4444_);
v___x_4446_ = v___x_4396_;
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
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4375_);
v_a_4449_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4393_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4393_);
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
lean_object* v___x_4457_; 
lean_inc(v___x_4382_);
lean_dec(v___x_4383_);
lean_dec_ref(v___y_4377_);
lean_inc_ref(v___y_4376_);
lean_inc(v___y_4381_);
lean_inc_ref(v___y_4380_);
lean_inc(v___y_4379_);
lean_inc_ref(v___y_4378_);
v___x_4457_ = lean_apply_5(v___y_4376_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, lean_box(0));
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4491_; 
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
lean_dec(v___y_4375_);
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 0, v___x_4382_);
v___x_4464_ = v___x_4460_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4382_);
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
v_var_4466_ = lean_ctor_get(v___x_4382_, 0);
v___x_4467_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
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
v___x_4474_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4375_, v___x_4473_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
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
lean_ctor_set(v___x_4476_, 0, v___x_4382_);
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4382_);
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
lean_dec(v___x_4382_);
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
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec(v___x_4382_);
lean_dec(v___y_4375_);
v_a_4492_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4457_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4457_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
}
v___jp_4500_:
{
lean_object* v_cls_4502_; lean_object* v___f_4503_; lean_object* v___x_4504_; lean_object* v_a_4505_; uint8_t v___x_4506_; 
v_cls_4502_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___f_4503_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2));
v___x_4504_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4502_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
v_a_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_a_4505_);
lean_dec_ref(v___x_4504_);
v___x_4506_ = lean_unbox(v_a_4505_);
lean_dec(v_a_4505_);
if (v___x_4506_ == 0)
{
v___y_4375_ = v_cls_4502_;
v___y_4376_ = v___f_4503_;
v___y_4377_ = v___y_4501_;
v___y_4378_ = v_a_4362_;
v___y_4379_ = v_a_4363_;
v___y_4380_ = v_a_4364_;
v___y_4381_ = v_a_4365_;
goto v___jp_4374_;
}
else
{
lean_object* v___x_4507_; size_t v_sz_4508_; size_t v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4507_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4);
v_sz_4508_ = lean_array_size(v___y_4501_);
v___x_4509_ = ((size_t)0ULL);
lean_inc_ref(v___y_4501_);
v___x_4510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_4508_, v___x_4509_, v___y_4501_);
v___x_4511_ = lean_array_to_list(v___x_4510_);
v___x_4512_ = lean_box(0);
v___x_4513_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v___x_4511_, v___x_4512_);
v___x_4514_ = l_Lean_MessageData_ofList(v___x_4513_);
v___x_4515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4515_, 0, v___x_4507_);
lean_ctor_set(v___x_4515_, 1, v___x_4514_);
v___x_4516_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4502_, v___x_4515_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
if (lean_obj_tag(v___x_4516_) == 0)
{
lean_dec_ref_known(v___x_4516_, 1);
v___y_4375_ = v_cls_4502_;
v___y_4376_ = v___f_4503_;
v___y_4377_ = v___y_4501_;
v___y_4378_ = v_a_4362_;
v___y_4379_ = v_a_4363_;
v___y_4380_ = v_a_4364_;
v___y_4381_ = v_a_4365_;
goto v___jp_4374_;
}
else
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4524_; 
lean_dec_ref(v___y_4501_);
v_a_4517_ = lean_ctor_get(v___x_4516_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4516_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4519_ = v___x_4516_;
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v___x_4516_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4522_; 
if (v_isShared_4520_ == 0)
{
v___x_4522_ = v___x_4519_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object* v_data_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_);
lean_dec(v_a_4539_);
lean_dec_ref(v_a_4538_);
lean_dec(v_a_4537_);
lean_dec_ref(v_a_4536_);
lean_dec_ref(v_data_4535_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object* v_upperBound_4542_, lean_object* v___y_4543_, lean_object* v_inst_4544_, lean_object* v_R_4545_, lean_object* v_a_4546_, lean_object* v_b_4547_, lean_object* v_c_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v___x_4554_; 
v___x_4554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4542_, v___y_4543_, v_a_4546_, v_b_4547_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object* v_upperBound_4555_, lean_object* v___y_4556_, lean_object* v_inst_4557_, lean_object* v_R_4558_, lean_object* v_a_4559_, lean_object* v_b_4560_, lean_object* v_c_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_upperBound_4555_, v___y_4556_, v_inst_4557_, v_R_4558_, v_a_4559_, v_b_4560_, v_c_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec_ref(v___y_4556_);
lean_dec(v_upperBound_4555_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(lean_object* v_snd_4568_, lean_object* v_fst_4569_, lean_object* v_as_x27_4570_, lean_object* v_b_4571_){
_start:
{
if (lean_obj_tag(v_as_x27_4570_) == 0)
{
lean_object* v___x_4573_; 
lean_dec_ref(v_fst_4569_);
v___x_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4573_, 0, v_b_4571_);
return v___x_4573_;
}
else
{
lean_object* v_head_4574_; lean_object* v_tail_4575_; lean_object* v_fst_4576_; lean_object* v_snd_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v_head_4574_ = lean_ctor_get(v_as_x27_4570_, 0);
v_tail_4575_ = lean_ctor_get(v_as_x27_4570_, 1);
v_fst_4576_ = lean_ctor_get(v_head_4574_, 0);
v_snd_4577_ = lean_ctor_get(v_head_4574_, 1);
v___x_4578_ = lean_int_neg(v_snd_4568_);
lean_inc(v_fst_4576_);
lean_inc_ref(v_fst_4569_);
lean_inc(v_snd_4577_);
v___x_4579_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_snd_4577_, v_fst_4569_, v___x_4578_, v_fst_4576_);
v___x_4580_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_4579_);
v___x_4581_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_b_4571_, v___x_4580_);
v_as_x27_4570_ = v_tail_4575_;
v_b_4571_ = v___x_4581_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg___boxed(lean_object* v_snd_4583_, lean_object* v_fst_4584_, lean_object* v_as_x27_4585_, lean_object* v_b_4586_, lean_object* v___y_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4583_, v_fst_4584_, v_as_x27_4585_, v_b_4586_);
lean_dec(v_as_x27_4585_);
lean_dec(v_snd_4583_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(lean_object* v_upperBounds_4589_, lean_object* v_as_x27_4590_, lean_object* v_b_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
if (lean_obj_tag(v_as_x27_4590_) == 0)
{
lean_object* v___x_4597_; 
v___x_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4597_, 0, v_b_4591_);
return v___x_4597_;
}
else
{
lean_object* v_head_4598_; lean_object* v_tail_4599_; lean_object* v_fst_4600_; lean_object* v_snd_4601_; lean_object* v___x_4602_; lean_object* v_a_4603_; 
v_head_4598_ = lean_ctor_get(v_as_x27_4590_, 0);
v_tail_4599_ = lean_ctor_get(v_as_x27_4590_, 1);
v_fst_4600_ = lean_ctor_get(v_head_4598_, 0);
v_snd_4601_ = lean_ctor_get(v_head_4598_, 1);
lean_inc(v_fst_4600_);
v___x_4602_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4601_, v_fst_4600_, v_upperBounds_4589_, v_b_4591_);
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
lean_inc(v_a_4603_);
lean_dec_ref(v___x_4602_);
v_as_x27_4590_ = v_tail_4599_;
v_b_4591_ = v_a_4603_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg___boxed(lean_object* v_upperBounds_4605_, lean_object* v_as_x27_4606_, lean_object* v_b_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4605_, v_as_x27_4606_, v_b_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
lean_dec(v_as_x27_4606_);
lean_dec(v_upperBounds_4605_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(lean_object* v_as_x27_4614_, lean_object* v_b_4615_){
_start:
{
if (lean_obj_tag(v_as_x27_4614_) == 0)
{
lean_object* v___x_4617_; 
v___x_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4617_, 0, v_b_4615_);
return v___x_4617_;
}
else
{
lean_object* v_head_4618_; lean_object* v_tail_4619_; lean_object* v___x_4620_; 
v_head_4618_ = lean_ctor_get(v_as_x27_4614_, 0);
v_tail_4619_ = lean_ctor_get(v_as_x27_4614_, 1);
lean_inc(v_head_4618_);
v___x_4620_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_b_4615_, v_head_4618_);
v_as_x27_4614_ = v_tail_4619_;
v_b_4615_ = v___x_4620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg___boxed(lean_object* v_as_x27_4622_, lean_object* v_b_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4622_, v_b_4623_);
lean_dec(v_as_x27_4622_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(lean_object* v_p_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_){
_start:
{
lean_object* v_data_4632_; lean_object* v___x_4633_; 
lean_inc_ref(v_p_4626_);
v_data_4632_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(v_p_4626_);
v___x_4633_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4632_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
lean_dec_ref(v_data_4632_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v_irrelevant_4635_; lean_object* v_lowerBounds_4636_; lean_object* v_upperBounds_4637_; lean_object* v_assumptions_4638_; lean_object* v_eliminations_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4654_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
lean_inc(v_a_4634_);
lean_dec_ref_known(v___x_4633_, 1);
v_irrelevant_4635_ = lean_ctor_get(v_a_4634_, 1);
lean_inc(v_irrelevant_4635_);
v_lowerBounds_4636_ = lean_ctor_get(v_a_4634_, 2);
lean_inc(v_lowerBounds_4636_);
v_upperBounds_4637_ = lean_ctor_get(v_a_4634_, 3);
lean_inc(v_upperBounds_4637_);
lean_dec(v_a_4634_);
v_assumptions_4638_ = lean_ctor_get(v_p_4626_, 0);
v_eliminations_4639_ = lean_ctor_get(v_p_4626_, 4);
v_isSharedCheck_4654_ = !lean_is_exclusive(v_p_4626_);
if (v_isSharedCheck_4654_ == 0)
{
lean_object* v_unused_4655_; lean_object* v_unused_4656_; lean_object* v_unused_4657_; lean_object* v_unused_4658_; lean_object* v_unused_4659_; 
v_unused_4655_ = lean_ctor_get(v_p_4626_, 6);
lean_dec(v_unused_4655_);
v_unused_4656_ = lean_ctor_get(v_p_4626_, 5);
lean_dec(v_unused_4656_);
v_unused_4657_ = lean_ctor_get(v_p_4626_, 3);
lean_dec(v_unused_4657_);
v_unused_4658_ = lean_ctor_get(v_p_4626_, 2);
lean_dec(v_unused_4658_);
v_unused_4659_ = lean_ctor_get(v_p_4626_, 1);
lean_dec(v_unused_4659_);
v___x_4641_ = v_p_4626_;
v_isShared_4642_ = v_isSharedCheck_4654_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_eliminations_4639_);
lean_inc(v_assumptions_4638_);
lean_dec(v_p_4626_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4654_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4649_; 
v___x_4643_ = lean_unsigned_to_nat(0u);
v___x_4644_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v___x_4645_ = 1;
v___x_4646_ = lean_box(0);
v___x_4647_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 6, v___x_4647_);
lean_ctor_set(v___x_4641_, 5, v___x_4646_);
lean_ctor_set(v___x_4641_, 3, v___x_4644_);
lean_ctor_set(v___x_4641_, 2, v___x_4644_);
lean_ctor_set(v___x_4641_, 1, v___x_4643_);
v___x_4649_ = v___x_4641_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_assumptions_4638_);
lean_ctor_set(v_reuseFailAlloc_4653_, 1, v___x_4643_);
lean_ctor_set(v_reuseFailAlloc_4653_, 2, v___x_4644_);
lean_ctor_set(v_reuseFailAlloc_4653_, 3, v___x_4644_);
lean_ctor_set(v_reuseFailAlloc_4653_, 4, v_eliminations_4639_);
lean_ctor_set(v_reuseFailAlloc_4653_, 5, v___x_4646_);
lean_ctor_set(v_reuseFailAlloc_4653_, 6, v___x_4647_);
v___x_4649_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
lean_object* v___x_4650_; lean_object* v_a_4651_; lean_object* v___x_4652_; 
lean_ctor_set_uint8(v___x_4649_, sizeof(void*)*7, v___x_4645_);
v___x_4650_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_irrelevant_4635_, v___x_4649_);
lean_dec(v_irrelevant_4635_);
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_a_4651_);
lean_dec_ref(v___x_4650_);
v___x_4652_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4637_, v_lowerBounds_4636_, v_a_4651_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
lean_dec(v_lowerBounds_4636_);
lean_dec(v_upperBounds_4637_);
return v___x_4652_;
}
}
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
lean_dec_ref(v_p_4626_);
v_a_4660_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4633_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4633_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin___boxed(lean_object* v_p_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_);
lean_dec(v_a_4672_);
lean_dec_ref(v_a_4671_);
lean_dec(v_a_4670_);
lean_dec_ref(v_a_4669_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(lean_object* v_snd_4675_, lean_object* v_fst_4676_, lean_object* v_as_4677_, lean_object* v_as_x27_4678_, lean_object* v_b_4679_, lean_object* v_a_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v___x_4686_; 
v___x_4686_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4675_, v_fst_4676_, v_as_x27_4678_, v_b_4679_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___boxed(lean_object* v_snd_4687_, lean_object* v_fst_4688_, lean_object* v_as_4689_, lean_object* v_as_x27_4690_, lean_object* v_b_4691_, lean_object* v_a_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(v_snd_4687_, v_fst_4688_, v_as_4689_, v_as_x27_4690_, v_b_4691_, v_a_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v_as_x27_4690_);
lean_dec(v_as_4689_);
lean_dec(v_snd_4687_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(lean_object* v_as_4699_, lean_object* v_as_x27_4700_, lean_object* v_b_4701_, lean_object* v_a_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v___x_4708_; 
v___x_4708_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4700_, v_b_4701_);
return v___x_4708_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___boxed(lean_object* v_as_4709_, lean_object* v_as_x27_4710_, lean_object* v_b_4711_, lean_object* v_a_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(v_as_4709_, v_as_x27_4710_, v_b_4711_, v_a_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
lean_dec(v_as_x27_4710_);
lean_dec(v_as_4709_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(lean_object* v_upperBounds_4719_, lean_object* v_as_4720_, lean_object* v_as_x27_4721_, lean_object* v_b_4722_, lean_object* v_a_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
lean_object* v___x_4729_; 
v___x_4729_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4719_, v_as_x27_4721_, v_b_4722_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___boxed(lean_object* v_upperBounds_4730_, lean_object* v_as_4731_, lean_object* v_as_x27_4732_, lean_object* v_b_4733_, lean_object* v_a_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
lean_object* v_res_4740_; 
v_res_4740_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(v_upperBounds_4730_, v_as_4731_, v_as_x27_4732_, v_b_4733_, v_a_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v_as_x27_4732_);
lean_dec(v_as_4731_);
lean_dec(v_upperBounds_4730_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object* v_x_4741_, lean_object* v_x_4742_){
_start:
{
if (lean_obj_tag(v_x_4742_) == 0)
{
lean_inc(v_x_4741_);
return v_x_4741_;
}
else
{
lean_object* v_key_4743_; lean_object* v_value_4744_; lean_object* v_tail_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v_key_4743_ = lean_ctor_get(v_x_4742_, 0);
v_value_4744_ = lean_ctor_get(v_x_4742_, 1);
v_tail_4745_ = lean_ctor_get(v_x_4742_, 2);
v___x_4746_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4741_, v_tail_4745_);
lean_inc(v_value_4744_);
lean_inc(v_key_4743_);
v___x_4747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4747_, 0, v_key_4743_);
lean_ctor_set(v___x_4747_, 1, v_value_4744_);
v___x_4748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4747_);
lean_ctor_set(v___x_4748_, 1, v___x_4746_);
return v___x_4748_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2___boxed(lean_object* v_x_4749_, lean_object* v_x_4750_){
_start:
{
lean_object* v_res_4751_; 
v_res_4751_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4749_, v_x_4750_);
lean_dec(v_x_4750_);
lean_dec(v_x_4749_);
return v_res_4751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object* v_as_4752_, size_t v_i_4753_, size_t v_stop_4754_, lean_object* v_b_4755_){
_start:
{
uint8_t v___x_4756_; 
v___x_4756_ = lean_usize_dec_eq(v_i_4753_, v_stop_4754_);
if (v___x_4756_ == 0)
{
size_t v___x_4757_; size_t v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4757_ = ((size_t)1ULL);
v___x_4758_ = lean_usize_sub(v_i_4753_, v___x_4757_);
v___x_4759_ = lean_array_uget_borrowed(v_as_4752_, v___x_4758_);
v___x_4760_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_b_4755_, v___x_4759_);
lean_dec(v_b_4755_);
v_i_4753_ = v___x_4758_;
v_b_4755_ = v___x_4760_;
goto _start;
}
else
{
return v_b_4755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object* v_as_4762_, lean_object* v_i_4763_, lean_object* v_stop_4764_, lean_object* v_b_4765_){
_start:
{
size_t v_i_boxed_4766_; size_t v_stop_boxed_4767_; lean_object* v_res_4768_; 
v_i_boxed_4766_ = lean_unbox_usize(v_i_4763_);
lean_dec(v_i_4763_);
v_stop_boxed_4767_ = lean_unbox_usize(v_stop_4764_);
lean_dec(v_stop_4764_);
v_res_4768_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_as_4762_, v_i_boxed_4766_, v_stop_boxed_4767_, v_b_4765_);
lean_dec_ref(v_as_4762_);
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object* v_a_4769_, lean_object* v_a_4770_){
_start:
{
if (lean_obj_tag(v_a_4769_) == 0)
{
lean_object* v___x_4771_; 
v___x_4771_ = l_List_reverse___redArg(v_a_4770_);
return v___x_4771_;
}
else
{
lean_object* v_head_4772_; lean_object* v_tail_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4890_; 
v_head_4772_ = lean_ctor_get(v_a_4769_, 0);
v_tail_4773_ = lean_ctor_get(v_a_4769_, 1);
v_isSharedCheck_4890_ = !lean_is_exclusive(v_a_4769_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4775_ = v_a_4769_;
v_isShared_4776_ = v_isSharedCheck_4890_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_tail_4773_);
lean_inc(v_head_4772_);
lean_dec(v_a_4769_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4890_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___y_4778_; lean_object* v_snd_4783_; lean_object* v_constraint_4784_; lean_object* v_fst_4785_; lean_object* v_lowerBound_4786_; lean_object* v_upperBound_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___y_4792_; lean_object* v___y_4793_; 
v_snd_4783_ = lean_ctor_get(v_head_4772_, 1);
v_constraint_4784_ = lean_ctor_get(v_snd_4783_, 1);
lean_inc_ref(v_constraint_4784_);
v_fst_4785_ = lean_ctor_get(v_head_4772_, 0);
lean_inc(v_fst_4785_);
lean_dec(v_head_4772_);
v_lowerBound_4786_ = lean_ctor_get(v_constraint_4784_, 0);
lean_inc(v_lowerBound_4786_);
v_upperBound_4787_ = lean_ctor_get(v_constraint_4784_, 1);
lean_inc(v_upperBound_4787_);
lean_dec_ref(v_constraint_4784_);
v___x_4788_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_fst_4785_);
lean_dec(v_fst_4785_);
v___x_4789_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_4790_ = lean_string_append(v___x_4788_, v___x_4789_);
if (lean_obj_tag(v_lowerBound_4786_) == 0)
{
if (lean_obj_tag(v_upperBound_4787_) == 0)
{
lean_object* v___x_4798_; lean_object* v___x_4799_; 
v___x_4798_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_4799_ = lean_string_append(v___x_4790_, v___x_4798_);
v___y_4778_ = v___x_4799_;
goto v___jp_4777_;
}
else
{
lean_object* v_val_4800_; lean_object* v___x_4801_; lean_object* v___y_4803_; lean_object* v_intZero_4808_; uint8_t v_isNeg_4809_; 
v_val_4800_ = lean_ctor_get(v_upperBound_4787_, 0);
lean_inc(v_val_4800_);
lean_dec_ref_known(v_upperBound_4787_, 1);
v___x_4801_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
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
v___x_4805_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4806_ = lean_string_append(v___x_4804_, v___x_4805_);
v___x_4807_ = lean_string_append(v___x_4790_, v___x_4806_);
lean_dec_ref(v___x_4806_);
v___y_4778_ = v___x_4807_;
goto v___jp_4777_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_4787_) == 0)
{
lean_object* v_val_4819_; lean_object* v___x_4820_; lean_object* v___y_4822_; lean_object* v_intZero_4827_; uint8_t v_isNeg_4828_; 
v_val_4819_ = lean_ctor_get(v_lowerBound_4786_, 0);
lean_inc(v_val_4819_);
lean_dec_ref_known(v_lowerBound_4786_, 1);
v___x_4820_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4827_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4828_ = lean_int_dec_lt(v_val_4819_, v_intZero_4827_);
if (v_isNeg_4828_ == 0)
{
lean_object* v_a_4829_; lean_object* v___x_4830_; 
v_a_4829_ = lean_nat_abs(v_val_4819_);
lean_dec(v_val_4819_);
v___x_4830_ = l_Nat_reprFast(v_a_4829_);
v___y_4822_ = v___x_4830_;
goto v___jp_4821_;
}
else
{
lean_object* v_abs_4831_; lean_object* v_one_4832_; lean_object* v_a_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; 
v_abs_4831_ = lean_nat_abs(v_val_4819_);
lean_dec(v_val_4819_);
v_one_4832_ = lean_unsigned_to_nat(1u);
v_a_4833_ = lean_nat_sub(v_abs_4831_, v_one_4832_);
lean_dec(v_abs_4831_);
v___x_4834_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4835_ = lean_nat_add(v_a_4833_, v_one_4832_);
lean_dec(v_a_4833_);
v___x_4836_ = l_Nat_reprFast(v___x_4835_);
v___x_4837_ = lean_string_append(v___x_4834_, v___x_4836_);
lean_dec_ref(v___x_4836_);
v___y_4822_ = v___x_4837_;
goto v___jp_4821_;
}
v___jp_4821_:
{
lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4823_ = lean_string_append(v___x_4820_, v___y_4822_);
lean_dec_ref(v___y_4822_);
v___x_4824_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_4825_ = lean_string_append(v___x_4823_, v___x_4824_);
v___x_4826_ = lean_string_append(v___x_4790_, v___x_4825_);
lean_dec_ref(v___x_4825_);
v___y_4778_ = v___x_4826_;
goto v___jp_4777_;
}
}
else
{
lean_object* v_val_4838_; lean_object* v_val_4839_; uint8_t v___x_4840_; 
v_val_4838_ = lean_ctor_get(v_lowerBound_4786_, 0);
lean_inc(v_val_4838_);
lean_dec_ref_known(v_lowerBound_4786_, 1);
v_val_4839_ = lean_ctor_get(v_upperBound_4787_, 0);
lean_inc(v_val_4839_);
lean_dec_ref_known(v_upperBound_4787_, 1);
v___x_4840_ = lean_int_dec_lt(v_val_4839_, v_val_4838_);
if (v___x_4840_ == 0)
{
uint8_t v___x_4841_; 
v___x_4841_ = lean_int_dec_eq(v_val_4838_, v_val_4839_);
if (v___x_4841_ == 0)
{
lean_object* v___x_4842_; lean_object* v___y_4844_; lean_object* v_intZero_4859_; uint8_t v_isNeg_4860_; 
v___x_4842_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4859_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4860_ = lean_int_dec_lt(v_val_4838_, v_intZero_4859_);
if (v_isNeg_4860_ == 0)
{
lean_object* v_a_4861_; lean_object* v___x_4862_; 
v_a_4861_ = lean_nat_abs(v_val_4838_);
lean_dec(v_val_4838_);
v___x_4862_ = l_Nat_reprFast(v_a_4861_);
v___y_4844_ = v___x_4862_;
goto v___jp_4843_;
}
else
{
lean_object* v_abs_4863_; lean_object* v_one_4864_; lean_object* v_a_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
v_abs_4863_ = lean_nat_abs(v_val_4838_);
lean_dec(v_val_4838_);
v_one_4864_ = lean_unsigned_to_nat(1u);
v_a_4865_ = lean_nat_sub(v_abs_4863_, v_one_4864_);
lean_dec(v_abs_4863_);
v___x_4866_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4867_ = lean_nat_add(v_a_4865_, v_one_4864_);
lean_dec(v_a_4865_);
v___x_4868_ = l_Nat_reprFast(v___x_4867_);
v___x_4869_ = lean_string_append(v___x_4866_, v___x_4868_);
lean_dec_ref(v___x_4868_);
v___y_4844_ = v___x_4869_;
goto v___jp_4843_;
}
v___jp_4843_:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v_intZero_4848_; uint8_t v_isNeg_4849_; 
v___x_4845_ = lean_string_append(v___x_4842_, v___y_4844_);
lean_dec_ref(v___y_4844_);
v___x_4846_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_4847_ = lean_string_append(v___x_4845_, v___x_4846_);
v_intZero_4848_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4849_ = lean_int_dec_lt(v_val_4839_, v_intZero_4848_);
if (v_isNeg_4849_ == 0)
{
lean_object* v_a_4850_; lean_object* v___x_4851_; 
v_a_4850_ = lean_nat_abs(v_val_4839_);
lean_dec(v_val_4839_);
v___x_4851_ = l_Nat_reprFast(v_a_4850_);
v___y_4792_ = v___x_4847_;
v___y_4793_ = v___x_4851_;
goto v___jp_4791_;
}
else
{
lean_object* v_abs_4852_; lean_object* v_one_4853_; lean_object* v_a_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v_abs_4852_ = lean_nat_abs(v_val_4839_);
lean_dec(v_val_4839_);
v_one_4853_ = lean_unsigned_to_nat(1u);
v_a_4854_ = lean_nat_sub(v_abs_4852_, v_one_4853_);
lean_dec(v_abs_4852_);
v___x_4855_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4856_ = lean_nat_add(v_a_4854_, v_one_4853_);
lean_dec(v_a_4854_);
v___x_4857_ = l_Nat_reprFast(v___x_4856_);
v___x_4858_ = lean_string_append(v___x_4855_, v___x_4857_);
lean_dec_ref(v___x_4857_);
v___y_4792_ = v___x_4847_;
v___y_4793_ = v___x_4858_;
goto v___jp_4791_;
}
}
}
else
{
lean_object* v___x_4870_; lean_object* v___y_4872_; lean_object* v_intZero_4877_; uint8_t v_isNeg_4878_; 
lean_dec(v_val_4839_);
v___x_4870_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_4877_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4878_ = lean_int_dec_lt(v_val_4838_, v_intZero_4877_);
if (v_isNeg_4878_ == 0)
{
lean_object* v_a_4879_; lean_object* v___x_4880_; 
v_a_4879_ = lean_nat_abs(v_val_4838_);
lean_dec(v_val_4838_);
v___x_4880_ = l_Nat_reprFast(v_a_4879_);
v___y_4872_ = v___x_4880_;
goto v___jp_4871_;
}
else
{
lean_object* v_abs_4881_; lean_object* v_one_4882_; lean_object* v_a_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v_abs_4881_ = lean_nat_abs(v_val_4838_);
lean_dec(v_val_4838_);
v_one_4882_ = lean_unsigned_to_nat(1u);
v_a_4883_ = lean_nat_sub(v_abs_4881_, v_one_4882_);
lean_dec(v_abs_4881_);
v___x_4884_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4885_ = lean_nat_add(v_a_4883_, v_one_4882_);
lean_dec(v_a_4883_);
v___x_4886_ = l_Nat_reprFast(v___x_4885_);
v___x_4887_ = lean_string_append(v___x_4884_, v___x_4886_);
lean_dec_ref(v___x_4886_);
v___y_4872_ = v___x_4887_;
goto v___jp_4871_;
}
v___jp_4871_:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4873_ = lean_string_append(v___x_4870_, v___y_4872_);
lean_dec_ref(v___y_4872_);
v___x_4874_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_4875_ = lean_string_append(v___x_4873_, v___x_4874_);
v___x_4876_ = lean_string_append(v___x_4790_, v___x_4875_);
lean_dec_ref(v___x_4875_);
v___y_4778_ = v___x_4876_;
goto v___jp_4777_;
}
}
}
else
{
lean_object* v___x_4888_; lean_object* v___x_4889_; 
lean_dec(v_val_4839_);
lean_dec(v_val_4838_);
v___x_4888_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_4889_ = lean_string_append(v___x_4790_, v___x_4888_);
v___y_4778_ = v___x_4889_;
goto v___jp_4777_;
}
}
}
v___jp_4777_:
{
lean_object* v___x_4780_; 
if (v_isShared_4776_ == 0)
{
lean_ctor_set(v___x_4775_, 1, v_a_4770_);
lean_ctor_set(v___x_4775_, 0, v___y_4778_);
v___x_4780_ = v___x_4775_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v___y_4778_);
lean_ctor_set(v_reuseFailAlloc_4782_, 1, v_a_4770_);
v___x_4780_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
v_a_4769_ = v_tail_4773_;
v_a_4770_ = v___x_4780_;
goto _start;
}
}
v___jp_4791_:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4794_ = lean_string_append(v___y_4792_, v___y_4793_);
lean_dec_ref(v___y_4793_);
v___x_4795_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4796_ = lean_string_append(v___x_4794_, v___x_4795_);
v___x_4797_ = lean_string_append(v___x_4790_, v___x_4796_);
lean_dec_ref(v___x_4796_);
v___y_4778_ = v___x_4797_;
goto v___jp_4777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object* v_cls_4891_, lean_object* v_msg_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_){
_start:
{
lean_object* v_ref_4898_; lean_object* v___x_4899_; lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4945_; 
v_ref_4898_ = lean_ctor_get(v___y_4895_, 2);
v___x_4899_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4892_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_);
v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4902_ = v___x_4899_;
v_isShared_4903_ = v_isSharedCheck_4945_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4899_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4945_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4904_; lean_object* v_traceState_4905_; lean_object* v_env_4906_; lean_object* v_nextMacroScope_4907_; lean_object* v_ngen_4908_; lean_object* v_auxDeclNGen_4909_; lean_object* v_cache_4910_; lean_object* v_recordedDeps_4911_; lean_object* v_messages_4912_; lean_object* v_infoState_4913_; lean_object* v_snapshotTasks_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4944_; 
v___x_4904_ = lean_st_ref_take(v___y_4896_);
v_traceState_4905_ = lean_ctor_get(v___x_4904_, 4);
v_env_4906_ = lean_ctor_get(v___x_4904_, 0);
v_nextMacroScope_4907_ = lean_ctor_get(v___x_4904_, 1);
v_ngen_4908_ = lean_ctor_get(v___x_4904_, 2);
v_auxDeclNGen_4909_ = lean_ctor_get(v___x_4904_, 3);
v_cache_4910_ = lean_ctor_get(v___x_4904_, 5);
v_recordedDeps_4911_ = lean_ctor_get(v___x_4904_, 6);
v_messages_4912_ = lean_ctor_get(v___x_4904_, 7);
v_infoState_4913_ = lean_ctor_get(v___x_4904_, 8);
v_snapshotTasks_4914_ = lean_ctor_get(v___x_4904_, 9);
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4916_ = v___x_4904_;
v_isShared_4917_ = v_isSharedCheck_4944_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_snapshotTasks_4914_);
lean_inc(v_infoState_4913_);
lean_inc(v_messages_4912_);
lean_inc(v_recordedDeps_4911_);
lean_inc(v_cache_4910_);
lean_inc(v_traceState_4905_);
lean_inc(v_auxDeclNGen_4909_);
lean_inc(v_ngen_4908_);
lean_inc(v_nextMacroScope_4907_);
lean_inc(v_env_4906_);
lean_dec(v___x_4904_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4944_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
uint64_t v_tid_4918_; lean_object* v_traces_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4943_; 
v_tid_4918_ = lean_ctor_get_uint64(v_traceState_4905_, sizeof(void*)*1);
v_traces_4919_ = lean_ctor_get(v_traceState_4905_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v_traceState_4905_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4921_ = v_traceState_4905_;
v_isShared_4922_ = v_isSharedCheck_4943_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_traces_4919_);
lean_dec(v_traceState_4905_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4943_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v___x_4923_; lean_object* v___x_4924_; double v___x_4925_; uint8_t v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4934_; 
v___x_4923_ = lean_box(0);
v___x_4924_ = lean_box(0);
v___x_4925_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4926_ = 0;
v___x_4927_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4928_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4928_, 0, v_cls_4891_);
lean_ctor_set(v___x_4928_, 1, v___x_4924_);
lean_ctor_set(v___x_4928_, 2, v___x_4927_);
lean_ctor_set_float(v___x_4928_, sizeof(void*)*3, v___x_4925_);
lean_ctor_set_float(v___x_4928_, sizeof(void*)*3 + 8, v___x_4925_);
lean_ctor_set_uint8(v___x_4928_, sizeof(void*)*3 + 16, v___x_4926_);
v___x_4929_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4930_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4930_, 0, v___x_4928_);
lean_ctor_set(v___x_4930_, 1, v_a_4900_);
lean_ctor_set(v___x_4930_, 2, v___x_4929_);
lean_inc(v_ref_4898_);
v___x_4931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4931_, 0, v_ref_4898_);
lean_ctor_set(v___x_4931_, 1, v___x_4930_);
v___x_4932_ = l_Lean_PersistentArray_push___redArg(v_traces_4919_, v___x_4931_);
if (v_isShared_4922_ == 0)
{
lean_ctor_set(v___x_4921_, 0, v___x_4932_);
v___x_4934_ = v___x_4921_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v___x_4932_);
lean_ctor_set_uint64(v_reuseFailAlloc_4942_, sizeof(void*)*1, v_tid_4918_);
v___x_4934_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
lean_object* v___x_4936_; 
if (v_isShared_4917_ == 0)
{
lean_ctor_set(v___x_4916_, 4, v___x_4934_);
v___x_4936_ = v___x_4916_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v_env_4906_);
lean_ctor_set(v_reuseFailAlloc_4941_, 1, v_nextMacroScope_4907_);
lean_ctor_set(v_reuseFailAlloc_4941_, 2, v_ngen_4908_);
lean_ctor_set(v_reuseFailAlloc_4941_, 3, v_auxDeclNGen_4909_);
lean_ctor_set(v_reuseFailAlloc_4941_, 4, v___x_4934_);
lean_ctor_set(v_reuseFailAlloc_4941_, 5, v_cache_4910_);
lean_ctor_set(v_reuseFailAlloc_4941_, 6, v_recordedDeps_4911_);
lean_ctor_set(v_reuseFailAlloc_4941_, 7, v_messages_4912_);
lean_ctor_set(v_reuseFailAlloc_4941_, 8, v_infoState_4913_);
lean_ctor_set(v_reuseFailAlloc_4941_, 9, v_snapshotTasks_4914_);
v___x_4936_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
lean_object* v___x_4937_; lean_object* v___x_4939_; 
v___x_4937_ = lean_st_ref_put(v___y_4896_, v___x_4936_);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 0, v___x_4923_);
v___x_4939_ = v___x_4902_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v___x_4923_);
v___x_4939_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
return v___x_4939_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg___boxed(lean_object* v_cls_4946_, lean_object* v_msg_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_){
_start:
{
lean_object* v_res_4953_; 
v_res_4953_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4946_, v_msg_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
lean_dec(v___y_4951_);
lean_dec_ref(v___y_4950_);
lean_dec(v___y_4949_);
lean_dec_ref(v___y_4948_);
return v_res_4953_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1(void){
_start:
{
lean_object* v___x_4955_; lean_object* v___x_4956_; 
v___x_4955_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__0));
v___x_4956_ = l_Lean_stringToMessageData(v___x_4955_);
return v___x_4956_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1(void){
_start:
{
lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4958_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__0));
v___x_4959_ = l_Lean_stringToMessageData(v___x_4958_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega(lean_object* v_p_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, uint8_t v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_){
_start:
{
lean_object* v___y_4972_; lean_object* v___y_4973_; lean_object* v___y_4974_; uint8_t v___y_4975_; lean_object* v___y_4976_; lean_object* v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v_toCold_4986_; lean_object* v_options_4987_; uint8_t v_hasTrace_4988_; 
v_toCold_4986_ = lean_ctor_get(v_a_4968_, 0);
v_options_4987_ = lean_ctor_get(v_toCold_4986_, 2);
v_hasTrace_4988_ = lean_ctor_get_uint8(v_options_4987_, sizeof(void*)*1);
if (v_hasTrace_4988_ == 0)
{
v___y_4972_ = v_a_4961_;
v___y_4973_ = v_a_4962_;
v___y_4974_ = v_a_4963_;
v___y_4975_ = v_a_4964_;
v___y_4976_ = v_a_4965_;
v___y_4977_ = v_a_4966_;
v___y_4978_ = v_a_4967_;
v___y_4979_ = v_a_4968_;
v___y_4980_ = v_a_4969_;
goto v___jp_4971_;
}
else
{
lean_object* v_inheritedTraceOptions_4989_; lean_object* v_cls_4990_; lean_object* v___x_4991_; uint8_t v___x_4992_; 
v_inheritedTraceOptions_4989_ = lean_ctor_get(v_toCold_4986_, 11);
v_cls_4990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4991_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_4992_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4989_, v_options_4987_, v___x_4991_);
if (v___x_4992_ == 0)
{
v___y_4972_ = v_a_4961_;
v___y_4973_ = v_a_4962_;
v___y_4974_ = v_a_4963_;
v___y_4975_ = v_a_4964_;
v___y_4976_ = v_a_4965_;
v___y_4977_ = v_a_4966_;
v___y_4978_ = v_a_4967_;
v___y_4979_ = v_a_4968_;
v___y_4980_ = v_a_4969_;
goto v___jp_4971_;
}
else
{
lean_object* v_constraints_4993_; uint8_t v_possible_4994_; lean_object* v___x_4995_; lean_object* v___y_4997_; 
v_constraints_4993_ = lean_ctor_get(v_p_4960_, 2);
v_possible_4994_ = lean_ctor_get_uint8(v_p_4960_, sizeof(void*)*7);
v___x_4995_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1);
if (v_possible_4994_ == 0)
{
lean_object* v___x_5010_; 
v___x_5010_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
v___y_4997_ = v___x_5010_;
goto v___jp_4996_;
}
else
{
uint8_t v___x_5011_; 
v___x_5011_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_4960_);
if (v___x_5011_ == 0)
{
lean_object* v_buckets_5012_; lean_object* v___x_5013_; lean_object* v___y_5015_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; uint8_t v___x_5022_; 
v_buckets_5012_ = lean_ctor_get(v_constraints_4993_, 1);
v___x_5013_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5019_ = lean_box(0);
v___x_5020_ = lean_array_get_size(v_buckets_5012_);
v___x_5021_ = lean_unsigned_to_nat(0u);
v___x_5022_ = lean_nat_dec_lt(v___x_5021_, v___x_5020_);
if (v___x_5022_ == 0)
{
v___y_5015_ = v___x_5019_;
goto v___jp_5014_;
}
else
{
size_t v___x_5023_; size_t v___x_5024_; lean_object* v___x_5025_; 
v___x_5023_ = lean_usize_of_nat(v___x_5020_);
v___x_5024_ = ((size_t)0ULL);
v___x_5025_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5012_, v___x_5023_, v___x_5024_, v___x_5019_);
v___y_5015_ = v___x_5025_;
goto v___jp_5014_;
}
v___jp_5014_:
{
lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; 
v___x_5016_ = lean_box(0);
v___x_5017_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5015_, v___x_5016_);
v___x_5018_ = l_String_intercalate(v___x_5013_, v___x_5017_);
v___y_4997_ = v___x_5018_;
goto v___jp_4996_;
}
}
else
{
lean_object* v___x_5026_; 
v___x_5026_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_4997_ = v___x_5026_;
goto v___jp_4996_;
}
}
v___jp_4996_:
{
lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; 
v___x_4998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4998_, 0, v___y_4997_);
v___x_4999_ = l_Lean_MessageData_ofFormat(v___x_4998_);
v___x_5000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4995_);
lean_ctor_set(v___x_5000_, 1, v___x_4999_);
v___x_5001_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4990_, v___x_5000_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_);
if (lean_obj_tag(v___x_5001_) == 0)
{
lean_dec_ref_known(v___x_5001_, 1);
v___y_4972_ = v_a_4961_;
v___y_4973_ = v_a_4962_;
v___y_4974_ = v_a_4963_;
v___y_4975_ = v_a_4964_;
v___y_4976_ = v_a_4965_;
v___y_4977_ = v_a_4966_;
v___y_4978_ = v_a_4967_;
v___y_4979_ = v_a_4968_;
v___y_4980_ = v_a_4969_;
goto v___jp_4971_;
}
else
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
lean_dec_ref(v_p_4960_);
v_a_5002_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v___x_5001_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_5001_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5007_; 
if (v_isShared_5005_ == 0)
{
v___x_5007_ = v___x_5004_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_5002_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
}
}
v___jp_4971_:
{
uint8_t v_possible_4981_; 
v_possible_4981_ = lean_ctor_get_uint8(v_p_4960_, sizeof(void*)*7);
if (v_possible_4981_ == 0)
{
lean_object* v___x_4982_; 
v___x_4982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4982_, 0, v_p_4960_);
return v___x_4982_;
}
else
{
lean_object* v___x_4983_; 
v___x_4983_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_4960_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
if (lean_obj_tag(v___x_4983_) == 0)
{
lean_object* v_a_4984_; lean_object* v___x_4985_; 
v_a_4984_ = lean_ctor_get(v___x_4983_, 0);
lean_inc(v_a_4984_);
lean_dec_ref_known(v___x_4983_, 1);
v___x_4985_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_a_4984_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
return v___x_4985_;
}
else
{
return v___x_4983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination(lean_object* v_p_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, uint8_t v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_){
_start:
{
lean_object* v___y_5039_; lean_object* v___y_5040_; lean_object* v___y_5041_; uint8_t v___y_5042_; lean_object* v___y_5043_; lean_object* v___y_5044_; lean_object* v___y_5045_; lean_object* v___y_5046_; lean_object* v___y_5047_; uint8_t v_possible_5051_; 
v_possible_5051_ = lean_ctor_get_uint8(v_p_5027_, sizeof(void*)*7);
if (v_possible_5051_ == 0)
{
lean_object* v___x_5052_; 
v___x_5052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5052_, 0, v_p_5027_);
return v___x_5052_;
}
else
{
lean_object* v_constraints_5053_; uint8_t v___x_5054_; 
v_constraints_5053_ = lean_ctor_get(v_p_5027_, 2);
v___x_5054_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_5027_);
if (v___x_5054_ == 0)
{
lean_object* v_toCold_5055_; lean_object* v_options_5056_; uint8_t v_hasTrace_5057_; 
v_toCold_5055_ = lean_ctor_get(v_a_5035_, 0);
v_options_5056_ = lean_ctor_get(v_toCold_5055_, 2);
v_hasTrace_5057_ = lean_ctor_get_uint8(v_options_5056_, sizeof(void*)*1);
if (v_hasTrace_5057_ == 0)
{
v___y_5039_ = v_a_5028_;
v___y_5040_ = v_a_5029_;
v___y_5041_ = v_a_5030_;
v___y_5042_ = v_a_5031_;
v___y_5043_ = v_a_5032_;
v___y_5044_ = v_a_5033_;
v___y_5045_ = v_a_5034_;
v___y_5046_ = v_a_5035_;
v___y_5047_ = v_a_5036_;
goto v___jp_5038_;
}
else
{
lean_object* v_inheritedTraceOptions_5058_; lean_object* v_cls_5059_; lean_object* v___x_5060_; uint8_t v___x_5061_; 
v_inheritedTraceOptions_5058_ = lean_ctor_get(v_toCold_5055_, 11);
v_cls_5059_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_5060_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_5061_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5058_, v_options_5056_, v___x_5060_);
if (v___x_5061_ == 0)
{
v___y_5039_ = v_a_5028_;
v___y_5040_ = v_a_5029_;
v___y_5041_ = v_a_5030_;
v___y_5042_ = v_a_5031_;
v___y_5043_ = v_a_5032_;
v___y_5044_ = v_a_5033_;
v___y_5045_ = v_a_5034_;
v___y_5046_ = v_a_5035_;
v___y_5047_ = v_a_5036_;
goto v___jp_5038_;
}
else
{
lean_object* v___x_5062_; lean_object* v___y_5064_; 
v___x_5062_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1);
if (v___x_5054_ == 0)
{
lean_object* v_buckets_5077_; lean_object* v___x_5078_; lean_object* v___y_5080_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; uint8_t v___x_5087_; 
v_buckets_5077_ = lean_ctor_get(v_constraints_5053_, 1);
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
v___x_5068_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5059_, v___x_5067_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_);
if (lean_obj_tag(v___x_5068_) == 0)
{
lean_dec_ref_known(v___x_5068_, 1);
v___y_5039_ = v_a_5028_;
v___y_5040_ = v_a_5029_;
v___y_5041_ = v_a_5030_;
v___y_5042_ = v_a_5031_;
v___y_5043_ = v_a_5032_;
v___y_5044_ = v_a_5033_;
v___y_5045_ = v_a_5034_;
v___y_5046_ = v_a_5035_;
v___y_5047_ = v_a_5036_;
goto v___jp_5038_;
}
else
{
lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5076_; 
lean_dec_ref(v_p_5027_);
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
lean_ctor_set(v___x_5092_, 0, v_p_5027_);
return v___x_5092_;
}
}
v___jp_5038_:
{
lean_object* v___x_5048_; 
v___x_5048_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_5027_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_);
if (lean_obj_tag(v___x_5048_) == 0)
{
lean_object* v_a_5049_; lean_object* v___x_5050_; 
v_a_5049_ = lean_ctor_get(v___x_5048_, 0);
lean_inc(v_a_5049_);
lean_dec_ref_known(v___x_5048_, 1);
v___x_5050_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_a_5049_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_);
return v___x_5050_;
}
else
{
return v___x_5048_;
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
uint8_t v___y_16400__boxed_5144_; lean_object* v_res_5145_; 
v___y_16400__boxed_5144_ = lean_unbox(v___y_5137_);
v_res_5145_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(v_cls_5132_, v_msg_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_16400__boxed_5144_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_);
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
