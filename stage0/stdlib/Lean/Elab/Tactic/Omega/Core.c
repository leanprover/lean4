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
lean_object* v_s_787_; lean_object* v_c_788_; lean_object* v_j_789_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; uint8_t v___x_908_; 
v_s_787_ = lean_ctor_get(v_x_680_, 0);
lean_inc_ref(v_s_787_);
v_c_788_ = lean_ctor_get(v_x_680_, 1);
lean_inc(v_c_788_);
v_j_789_ = lean_ctor_get(v_x_680_, 2);
lean_inc_ref(v_j_789_);
lean_dec_ref_known(v_x_680_, 3);
v___x_908_ = l_Lean_Omega_instBEqConstraint_beq(v_s_678_, v_s_787_);
if (v___x_908_ == 0)
{
goto v___jp_846_;
}
else
{
uint8_t v___x_909_; 
v___x_909_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_x_679_, v_c_788_);
if (v___x_909_ == 0)
{
goto v___jp_846_;
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
lean_inc_ref(v___y_801_);
v___x_803_ = lean_string_append(v___y_801_, v___y_802_);
lean_dec_ref(v___y_802_);
v___x_804_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_805_ = lean_string_append(v___x_803_, v___x_804_);
v___y_791_ = v___y_800_;
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
v___x_817_ = lean_string_append(v___y_815_, v___y_816_);
lean_dec_ref(v___y_816_);
v___x_818_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_819_ = lean_string_append(v___x_817_, v___x_818_);
v___y_791_ = v___y_814_;
v___y_792_ = v___x_819_;
goto v___jp_790_;
}
v___jp_820_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v_intZero_828_; uint8_t v_isNeg_829_; 
lean_inc_ref(v___y_823_);
v___x_825_ = lean_string_append(v___y_823_, v___y_824_);
lean_dec_ref(v___y_824_);
v___x_826_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_827_ = lean_string_append(v___x_825_, v___x_826_);
v_intZero_828_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_829_ = lean_int_dec_lt(v___y_821_, v_intZero_828_);
if (v_isNeg_829_ == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; 
v_a_830_ = lean_nat_abs(v___y_821_);
lean_dec(v___y_821_);
v___x_831_ = l_Nat_reprFast(v_a_830_);
v___y_814_ = v___y_822_;
v___y_815_ = v___x_827_;
v___y_816_ = v___x_831_;
goto v___jp_813_;
}
else
{
lean_object* v_abs_832_; lean_object* v_one_833_; lean_object* v_a_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_abs_832_ = lean_nat_abs(v___y_821_);
lean_dec(v___y_821_);
v_one_833_ = lean_unsigned_to_nat(1u);
v_a_834_ = lean_nat_sub(v_abs_832_, v_one_833_);
lean_dec(v_abs_832_);
v___x_835_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_836_ = lean_nat_add(v_a_834_, v_one_833_);
lean_dec(v_a_834_);
v___x_837_ = l_Nat_reprFast(v___x_836_);
v___x_838_ = lean_string_append(v___x_835_, v___x_837_);
lean_dec_ref(v___x_837_);
v___y_814_ = v___y_822_;
v___y_815_ = v___x_827_;
v___y_816_ = v___x_838_;
goto v___jp_813_;
}
}
v___jp_839_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_inc_ref(v___y_841_);
v___x_843_ = lean_string_append(v___y_841_, v___y_842_);
lean_dec_ref(v___y_842_);
v___x_844_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_845_ = lean_string_append(v___x_843_, v___x_844_);
v___y_791_ = v___y_840_;
v___y_792_ = v___x_845_;
goto v___jp_790_;
}
v___jp_846_:
{
lean_object* v_lowerBound_847_; lean_object* v_upperBound_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_lowerBound_847_ = lean_ctor_get(v_s_678_, 0);
lean_inc(v_lowerBound_847_);
v_upperBound_848_ = lean_ctor_get(v_s_678_, 1);
lean_inc(v_upperBound_848_);
lean_dec_ref(v_s_678_);
v___x_849_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_679_);
lean_dec(v_x_679_);
v___x_850_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_851_ = lean_string_append(v___x_849_, v___x_850_);
if (lean_obj_tag(v_lowerBound_847_) == 0)
{
if (lean_obj_tag(v_upperBound_848_) == 0)
{
lean_object* v___x_852_; 
v___x_852_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_791_ = v___x_851_;
v___y_792_ = v___x_852_;
goto v___jp_790_;
}
else
{
lean_object* v_val_853_; lean_object* v___x_854_; lean_object* v_intZero_855_; uint8_t v_isNeg_856_; 
v_val_853_ = lean_ctor_get(v_upperBound_848_, 0);
lean_inc(v_val_853_);
lean_dec_ref_known(v_upperBound_848_, 1);
v___x_854_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_855_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_856_ = lean_int_dec_lt(v_val_853_, v_intZero_855_);
if (v_isNeg_856_ == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; 
v_a_857_ = lean_nat_abs(v_val_853_);
lean_dec(v_val_853_);
v___x_858_ = l_Nat_reprFast(v_a_857_);
v___y_800_ = v___x_851_;
v___y_801_ = v___x_854_;
v___y_802_ = v___x_858_;
goto v___jp_799_;
}
else
{
lean_object* v_abs_859_; lean_object* v_one_860_; lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_abs_859_ = lean_nat_abs(v_val_853_);
lean_dec(v_val_853_);
v_one_860_ = lean_unsigned_to_nat(1u);
v_a_861_ = lean_nat_sub(v_abs_859_, v_one_860_);
lean_dec(v_abs_859_);
v___x_862_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_863_ = lean_nat_add(v_a_861_, v_one_860_);
lean_dec(v_a_861_);
v___x_864_ = l_Nat_reprFast(v___x_863_);
v___x_865_ = lean_string_append(v___x_862_, v___x_864_);
lean_dec_ref(v___x_864_);
v___y_800_ = v___x_851_;
v___y_801_ = v___x_854_;
v___y_802_ = v___x_865_;
goto v___jp_799_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_848_) == 0)
{
lean_object* v_val_866_; lean_object* v___x_867_; lean_object* v_intZero_868_; uint8_t v_isNeg_869_; 
v_val_866_ = lean_ctor_get(v_lowerBound_847_, 0);
lean_inc(v_val_866_);
lean_dec_ref_known(v_lowerBound_847_, 1);
v___x_867_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_868_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_869_ = lean_int_dec_lt(v_val_866_, v_intZero_868_);
if (v_isNeg_869_ == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; 
v_a_870_ = lean_nat_abs(v_val_866_);
lean_dec(v_val_866_);
v___x_871_ = l_Nat_reprFast(v_a_870_);
v___y_807_ = v___x_851_;
v___y_808_ = v___x_867_;
v___y_809_ = v___x_871_;
goto v___jp_806_;
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
v___y_807_ = v___x_851_;
v___y_808_ = v___x_867_;
v___y_809_ = v___x_878_;
goto v___jp_806_;
}
}
else
{
lean_object* v_val_879_; lean_object* v_val_880_; uint8_t v___x_881_; 
v_val_879_ = lean_ctor_get(v_lowerBound_847_, 0);
lean_inc(v_val_879_);
lean_dec_ref_known(v_lowerBound_847_, 1);
v_val_880_ = lean_ctor_get(v_upperBound_848_, 0);
lean_inc(v_val_880_);
lean_dec_ref_known(v_upperBound_848_, 1);
v___x_881_ = lean_int_dec_lt(v_val_880_, v_val_879_);
if (v___x_881_ == 0)
{
uint8_t v___x_882_; 
v___x_882_ = lean_int_dec_eq(v_val_879_, v_val_880_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v_intZero_884_; uint8_t v_isNeg_885_; 
v___x_883_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_884_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_885_ = lean_int_dec_lt(v_val_879_, v_intZero_884_);
if (v_isNeg_885_ == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_886_ = lean_nat_abs(v_val_879_);
lean_dec(v_val_879_);
v___x_887_ = l_Nat_reprFast(v_a_886_);
v___y_821_ = v_val_880_;
v___y_822_ = v___x_851_;
v___y_823_ = v___x_883_;
v___y_824_ = v___x_887_;
goto v___jp_820_;
}
else
{
lean_object* v_abs_888_; lean_object* v_one_889_; lean_object* v_a_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_abs_888_ = lean_nat_abs(v_val_879_);
lean_dec(v_val_879_);
v_one_889_ = lean_unsigned_to_nat(1u);
v_a_890_ = lean_nat_sub(v_abs_888_, v_one_889_);
lean_dec(v_abs_888_);
v___x_891_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_892_ = lean_nat_add(v_a_890_, v_one_889_);
lean_dec(v_a_890_);
v___x_893_ = l_Nat_reprFast(v___x_892_);
v___x_894_ = lean_string_append(v___x_891_, v___x_893_);
lean_dec_ref(v___x_893_);
v___y_821_ = v_val_880_;
v___y_822_ = v___x_851_;
v___y_823_ = v___x_883_;
v___y_824_ = v___x_894_;
goto v___jp_820_;
}
}
else
{
lean_object* v___x_895_; lean_object* v_intZero_896_; uint8_t v_isNeg_897_; 
lean_dec(v_val_880_);
v___x_895_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_896_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_897_ = lean_int_dec_lt(v_val_879_, v_intZero_896_);
if (v_isNeg_897_ == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_898_ = lean_nat_abs(v_val_879_);
lean_dec(v_val_879_);
v___x_899_ = l_Nat_reprFast(v_a_898_);
v___y_840_ = v___x_851_;
v___y_841_ = v___x_895_;
v___y_842_ = v___x_899_;
goto v___jp_839_;
}
else
{
lean_object* v_abs_900_; lean_object* v_one_901_; lean_object* v_a_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_abs_900_ = lean_nat_abs(v_val_879_);
lean_dec(v_val_879_);
v_one_901_ = lean_unsigned_to_nat(1u);
v_a_902_ = lean_nat_sub(v_abs_900_, v_one_901_);
lean_dec(v_abs_900_);
v___x_903_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_904_ = lean_nat_add(v_a_902_, v_one_901_);
lean_dec(v_a_902_);
v___x_905_ = l_Nat_reprFast(v___x_904_);
v___x_906_ = lean_string_append(v___x_903_, v___x_905_);
lean_dec_ref(v___x_905_);
v___y_840_ = v___x_851_;
v___y_841_ = v___x_895_;
v___y_842_ = v___x_906_;
goto v___jp_839_;
}
}
}
else
{
lean_object* v___x_907_; 
lean_dec(v_val_880_);
lean_dec(v_val_879_);
v___x_907_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_791_ = v___x_851_;
v___y_792_ = v___x_907_;
goto v___jp_790_;
}
}
}
}
}
case 2:
{
lean_object* v_s_911_; lean_object* v_t_912_; lean_object* v_j_913_; lean_object* v_k_914_; lean_object* v_lowerBound_915_; lean_object* v_upperBound_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___y_921_; lean_object* v___y_934_; lean_object* v___y_935_; 
v_s_911_ = lean_ctor_get(v_x_680_, 0);
lean_inc_ref(v_s_911_);
v_t_912_ = lean_ctor_get(v_x_680_, 1);
lean_inc_ref(v_t_912_);
v_j_913_ = lean_ctor_get(v_x_680_, 3);
lean_inc_ref(v_j_913_);
v_k_914_ = lean_ctor_get(v_x_680_, 4);
lean_inc_ref(v_k_914_);
lean_dec_ref_known(v_x_680_, 5);
v_lowerBound_915_ = lean_ctor_get(v_s_678_, 0);
lean_inc(v_lowerBound_915_);
v_upperBound_916_ = lean_ctor_get(v_s_678_, 1);
lean_inc(v_upperBound_916_);
lean_dec_ref(v_s_678_);
v___x_917_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_679_);
v___x_918_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_919_ = lean_string_append(v___x_917_, v___x_918_);
if (lean_obj_tag(v_lowerBound_915_) == 0)
{
if (lean_obj_tag(v_upperBound_916_) == 0)
{
lean_object* v___x_939_; 
v___x_939_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_921_ = v___x_939_;
goto v___jp_920_;
}
else
{
lean_object* v_val_940_; lean_object* v___x_941_; lean_object* v___y_943_; lean_object* v_intZero_947_; uint8_t v_isNeg_948_; 
v_val_940_ = lean_ctor_get(v_upperBound_916_, 0);
lean_inc(v_val_940_);
lean_dec_ref_known(v_upperBound_916_, 1);
v___x_941_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_947_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_948_ = lean_int_dec_lt(v_val_940_, v_intZero_947_);
if (v_isNeg_948_ == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; 
v_a_949_ = lean_nat_abs(v_val_940_);
lean_dec(v_val_940_);
v___x_950_ = l_Nat_reprFast(v_a_949_);
v___y_943_ = v___x_950_;
goto v___jp_942_;
}
else
{
lean_object* v_abs_951_; lean_object* v_one_952_; lean_object* v_a_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_abs_951_ = lean_nat_abs(v_val_940_);
lean_dec(v_val_940_);
v_one_952_ = lean_unsigned_to_nat(1u);
v_a_953_ = lean_nat_sub(v_abs_951_, v_one_952_);
lean_dec(v_abs_951_);
v___x_954_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_955_ = lean_nat_add(v_a_953_, v_one_952_);
lean_dec(v_a_953_);
v___x_956_ = l_Nat_reprFast(v___x_955_);
v___x_957_ = lean_string_append(v___x_954_, v___x_956_);
lean_dec_ref(v___x_956_);
v___y_943_ = v___x_957_;
goto v___jp_942_;
}
v___jp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_string_append(v___x_941_, v___y_943_);
lean_dec_ref(v___y_943_);
v___x_945_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_946_ = lean_string_append(v___x_944_, v___x_945_);
v___y_921_ = v___x_946_;
goto v___jp_920_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_916_) == 0)
{
lean_object* v_val_958_; lean_object* v___x_959_; lean_object* v___y_961_; lean_object* v_intZero_965_; uint8_t v_isNeg_966_; 
v_val_958_ = lean_ctor_get(v_lowerBound_915_, 0);
lean_inc(v_val_958_);
lean_dec_ref_known(v_lowerBound_915_, 1);
v___x_959_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_965_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_966_ = lean_int_dec_lt(v_val_958_, v_intZero_965_);
if (v_isNeg_966_ == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; 
v_a_967_ = lean_nat_abs(v_val_958_);
lean_dec(v_val_958_);
v___x_968_ = l_Nat_reprFast(v_a_967_);
v___y_961_ = v___x_968_;
goto v___jp_960_;
}
else
{
lean_object* v_abs_969_; lean_object* v_one_970_; lean_object* v_a_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_abs_969_ = lean_nat_abs(v_val_958_);
lean_dec(v_val_958_);
v_one_970_ = lean_unsigned_to_nat(1u);
v_a_971_ = lean_nat_sub(v_abs_969_, v_one_970_);
lean_dec(v_abs_969_);
v___x_972_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_973_ = lean_nat_add(v_a_971_, v_one_970_);
lean_dec(v_a_971_);
v___x_974_ = l_Nat_reprFast(v___x_973_);
v___x_975_ = lean_string_append(v___x_972_, v___x_974_);
lean_dec_ref(v___x_974_);
v___y_961_ = v___x_975_;
goto v___jp_960_;
}
v___jp_960_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_string_append(v___x_959_, v___y_961_);
lean_dec_ref(v___y_961_);
v___x_963_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_964_ = lean_string_append(v___x_962_, v___x_963_);
v___y_921_ = v___x_964_;
goto v___jp_920_;
}
}
else
{
lean_object* v_val_976_; lean_object* v_val_977_; uint8_t v___x_978_; 
v_val_976_ = lean_ctor_get(v_lowerBound_915_, 0);
lean_inc(v_val_976_);
lean_dec_ref_known(v_lowerBound_915_, 1);
v_val_977_ = lean_ctor_get(v_upperBound_916_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_upperBound_916_, 1);
v___x_978_ = lean_int_dec_lt(v_val_977_, v_val_976_);
if (v___x_978_ == 0)
{
uint8_t v___x_979_; 
v___x_979_ = lean_int_dec_eq(v_val_976_, v_val_977_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___y_982_; lean_object* v_intZero_997_; uint8_t v_isNeg_998_; 
v___x_980_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_997_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_998_ = lean_int_dec_lt(v_val_976_, v_intZero_997_);
if (v_isNeg_998_ == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_nat_abs(v_val_976_);
lean_dec(v_val_976_);
v___x_1000_ = l_Nat_reprFast(v_a_999_);
v___y_982_ = v___x_1000_;
goto v___jp_981_;
}
else
{
lean_object* v_abs_1001_; lean_object* v_one_1002_; lean_object* v_a_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_abs_1001_ = lean_nat_abs(v_val_976_);
lean_dec(v_val_976_);
v_one_1002_ = lean_unsigned_to_nat(1u);
v_a_1003_ = lean_nat_sub(v_abs_1001_, v_one_1002_);
lean_dec(v_abs_1001_);
v___x_1004_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1005_ = lean_nat_add(v_a_1003_, v_one_1002_);
lean_dec(v_a_1003_);
v___x_1006_ = l_Nat_reprFast(v___x_1005_);
v___x_1007_ = lean_string_append(v___x_1004_, v___x_1006_);
lean_dec_ref(v___x_1006_);
v___y_982_ = v___x_1007_;
goto v___jp_981_;
}
v___jp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_intZero_986_; uint8_t v_isNeg_987_; 
v___x_983_ = lean_string_append(v___x_980_, v___y_982_);
lean_dec_ref(v___y_982_);
v___x_984_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
v_intZero_986_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_987_ = lean_int_dec_lt(v_val_977_, v_intZero_986_);
if (v_isNeg_987_ == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; 
v_a_988_ = lean_nat_abs(v_val_977_);
lean_dec(v_val_977_);
v___x_989_ = l_Nat_reprFast(v_a_988_);
v___y_934_ = v___x_985_;
v___y_935_ = v___x_989_;
goto v___jp_933_;
}
else
{
lean_object* v_abs_990_; lean_object* v_one_991_; lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_abs_990_ = lean_nat_abs(v_val_977_);
lean_dec(v_val_977_);
v_one_991_ = lean_unsigned_to_nat(1u);
v_a_992_ = lean_nat_sub(v_abs_990_, v_one_991_);
lean_dec(v_abs_990_);
v___x_993_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_994_ = lean_nat_add(v_a_992_, v_one_991_);
lean_dec(v_a_992_);
v___x_995_ = l_Nat_reprFast(v___x_994_);
v___x_996_ = lean_string_append(v___x_993_, v___x_995_);
lean_dec_ref(v___x_995_);
v___y_934_ = v___x_985_;
v___y_935_ = v___x_996_;
goto v___jp_933_;
}
}
}
else
{
lean_object* v___x_1008_; lean_object* v___y_1010_; lean_object* v_intZero_1014_; uint8_t v_isNeg_1015_; 
lean_dec(v_val_977_);
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1014_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1015_ = lean_int_dec_lt(v_val_976_, v_intZero_1014_);
if (v_isNeg_1015_ == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; 
v_a_1016_ = lean_nat_abs(v_val_976_);
lean_dec(v_val_976_);
v___x_1017_ = l_Nat_reprFast(v_a_1016_);
v___y_1010_ = v___x_1017_;
goto v___jp_1009_;
}
else
{
lean_object* v_abs_1018_; lean_object* v_one_1019_; lean_object* v_a_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_abs_1018_ = lean_nat_abs(v_val_976_);
lean_dec(v_val_976_);
v_one_1019_ = lean_unsigned_to_nat(1u);
v_a_1020_ = lean_nat_sub(v_abs_1018_, v_one_1019_);
lean_dec(v_abs_1018_);
v___x_1021_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1022_ = lean_nat_add(v_a_1020_, v_one_1019_);
lean_dec(v_a_1020_);
v___x_1023_ = l_Nat_reprFast(v___x_1022_);
v___x_1024_ = lean_string_append(v___x_1021_, v___x_1023_);
lean_dec_ref(v___x_1023_);
v___y_1010_ = v___x_1024_;
goto v___jp_1009_;
}
v___jp_1009_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = lean_string_append(v___x_1008_, v___y_1010_);
lean_dec_ref(v___y_1010_);
v___x_1012_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1013_ = lean_string_append(v___x_1011_, v___x_1012_);
v___y_921_ = v___x_1013_;
goto v___jp_920_;
}
}
}
else
{
lean_object* v___x_1025_; 
lean_dec(v_val_977_);
lean_dec(v_val_976_);
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_921_ = v___x_1025_;
goto v___jp_920_;
}
}
}
v___jp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_922_ = lean_string_append(v___x_919_, v___y_921_);
lean_dec_ref(v___y_921_);
v___x_923_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__10));
v___x_924_ = lean_string_append(v___x_922_, v___x_923_);
lean_inc(v_x_679_);
v___x_925_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_911_, v_x_679_, v_j_913_);
v___x_926_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_925_);
v___x_927_ = lean_string_append(v___x_924_, v___x_926_);
lean_dec_ref(v___x_926_);
v___x_928_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_929_ = lean_string_append(v___x_927_, v___x_928_);
v___x_930_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_912_, v_x_679_, v_k_914_);
v___x_931_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_930_);
v___x_932_ = lean_string_append(v___x_929_, v___x_931_);
lean_dec_ref(v___x_931_);
return v___x_932_;
}
v___jp_933_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = lean_string_append(v___y_934_, v___y_935_);
lean_dec_ref(v___y_935_);
v___x_937_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_938_ = lean_string_append(v___x_936_, v___x_937_);
v___y_921_ = v___x_938_;
goto v___jp_920_;
}
}
case 3:
{
lean_object* v_s_1026_; lean_object* v_t_1027_; lean_object* v_x_1028_; lean_object* v_y_1029_; lean_object* v_a_1030_; lean_object* v_j_1031_; lean_object* v_b_1032_; lean_object* v_k_1033_; lean_object* v_lowerBound_1034_; lean_object* v_upperBound_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___y_1040_; lean_object* v___y_1061_; lean_object* v___y_1062_; 
v_s_1026_ = lean_ctor_get(v_x_680_, 0);
lean_inc_ref(v_s_1026_);
v_t_1027_ = lean_ctor_get(v_x_680_, 1);
lean_inc_ref(v_t_1027_);
v_x_1028_ = lean_ctor_get(v_x_680_, 2);
lean_inc(v_x_1028_);
v_y_1029_ = lean_ctor_get(v_x_680_, 3);
lean_inc(v_y_1029_);
v_a_1030_ = lean_ctor_get(v_x_680_, 4);
lean_inc(v_a_1030_);
v_j_1031_ = lean_ctor_get(v_x_680_, 5);
lean_inc_ref(v_j_1031_);
v_b_1032_ = lean_ctor_get(v_x_680_, 6);
lean_inc(v_b_1032_);
v_k_1033_ = lean_ctor_get(v_x_680_, 7);
lean_inc_ref(v_k_1033_);
lean_dec_ref_known(v_x_680_, 8);
v_lowerBound_1034_ = lean_ctor_get(v_s_678_, 0);
lean_inc(v_lowerBound_1034_);
v_upperBound_1035_ = lean_ctor_get(v_s_678_, 1);
lean_inc(v_upperBound_1035_);
lean_dec_ref(v_s_678_);
v___x_1036_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_679_);
lean_dec(v_x_679_);
v___x_1037_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1038_ = lean_string_append(v___x_1036_, v___x_1037_);
if (lean_obj_tag(v_lowerBound_1034_) == 0)
{
if (lean_obj_tag(v_upperBound_1035_) == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1040_ = v___x_1066_;
goto v___jp_1039_;
}
else
{
lean_object* v_val_1067_; lean_object* v___x_1068_; lean_object* v___y_1070_; lean_object* v_intZero_1074_; uint8_t v_isNeg_1075_; 
v_val_1067_ = lean_ctor_get(v_upperBound_1035_, 0);
lean_inc(v_val_1067_);
lean_dec_ref_known(v_upperBound_1035_, 1);
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1074_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1075_ = lean_int_dec_lt(v_val_1067_, v_intZero_1074_);
if (v_isNeg_1075_ == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; 
v_a_1076_ = lean_nat_abs(v_val_1067_);
lean_dec(v_val_1067_);
v___x_1077_ = l_Nat_reprFast(v_a_1076_);
v___y_1070_ = v___x_1077_;
goto v___jp_1069_;
}
else
{
lean_object* v_abs_1078_; lean_object* v_one_1079_; lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_abs_1078_ = lean_nat_abs(v_val_1067_);
lean_dec(v_val_1067_);
v_one_1079_ = lean_unsigned_to_nat(1u);
v_a_1080_ = lean_nat_sub(v_abs_1078_, v_one_1079_);
lean_dec(v_abs_1078_);
v___x_1081_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1082_ = lean_nat_add(v_a_1080_, v_one_1079_);
lean_dec(v_a_1080_);
v___x_1083_ = l_Nat_reprFast(v___x_1082_);
v___x_1084_ = lean_string_append(v___x_1081_, v___x_1083_);
lean_dec_ref(v___x_1083_);
v___y_1070_ = v___x_1084_;
goto v___jp_1069_;
}
v___jp_1069_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_string_append(v___x_1068_, v___y_1070_);
lean_dec_ref(v___y_1070_);
v___x_1072_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1073_ = lean_string_append(v___x_1071_, v___x_1072_);
v___y_1040_ = v___x_1073_;
goto v___jp_1039_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1035_) == 0)
{
lean_object* v_val_1085_; lean_object* v___x_1086_; lean_object* v___y_1088_; lean_object* v_intZero_1092_; uint8_t v_isNeg_1093_; 
v_val_1085_ = lean_ctor_get(v_lowerBound_1034_, 0);
lean_inc(v_val_1085_);
lean_dec_ref_known(v_lowerBound_1034_, 1);
v___x_1086_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1092_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1093_ = lean_int_dec_lt(v_val_1085_, v_intZero_1092_);
if (v_isNeg_1093_ == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; 
v_a_1094_ = lean_nat_abs(v_val_1085_);
lean_dec(v_val_1085_);
v___x_1095_ = l_Nat_reprFast(v_a_1094_);
v___y_1088_ = v___x_1095_;
goto v___jp_1087_;
}
else
{
lean_object* v_abs_1096_; lean_object* v_one_1097_; lean_object* v_a_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_abs_1096_ = lean_nat_abs(v_val_1085_);
lean_dec(v_val_1085_);
v_one_1097_ = lean_unsigned_to_nat(1u);
v_a_1098_ = lean_nat_sub(v_abs_1096_, v_one_1097_);
lean_dec(v_abs_1096_);
v___x_1099_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1100_ = lean_nat_add(v_a_1098_, v_one_1097_);
lean_dec(v_a_1098_);
v___x_1101_ = l_Nat_reprFast(v___x_1100_);
v___x_1102_ = lean_string_append(v___x_1099_, v___x_1101_);
lean_dec_ref(v___x_1101_);
v___y_1088_ = v___x_1102_;
goto v___jp_1087_;
}
v___jp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_string_append(v___x_1086_, v___y_1088_);
lean_dec_ref(v___y_1088_);
v___x_1090_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1091_ = lean_string_append(v___x_1089_, v___x_1090_);
v___y_1040_ = v___x_1091_;
goto v___jp_1039_;
}
}
else
{
lean_object* v_val_1103_; lean_object* v_val_1104_; uint8_t v___x_1105_; 
v_val_1103_ = lean_ctor_get(v_lowerBound_1034_, 0);
lean_inc(v_val_1103_);
lean_dec_ref_known(v_lowerBound_1034_, 1);
v_val_1104_ = lean_ctor_get(v_upperBound_1035_, 0);
lean_inc(v_val_1104_);
lean_dec_ref_known(v_upperBound_1035_, 1);
v___x_1105_ = lean_int_dec_lt(v_val_1104_, v_val_1103_);
if (v___x_1105_ == 0)
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_int_dec_eq(v_val_1103_, v_val_1104_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___y_1109_; lean_object* v_intZero_1124_; uint8_t v_isNeg_1125_; 
v___x_1107_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1124_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1125_ = lean_int_dec_lt(v_val_1103_, v_intZero_1124_);
if (v_isNeg_1125_ == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1127_; 
v_a_1126_ = lean_nat_abs(v_val_1103_);
lean_dec(v_val_1103_);
v___x_1127_ = l_Nat_reprFast(v_a_1126_);
v___y_1109_ = v___x_1127_;
goto v___jp_1108_;
}
else
{
lean_object* v_abs_1128_; lean_object* v_one_1129_; lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_abs_1128_ = lean_nat_abs(v_val_1103_);
lean_dec(v_val_1103_);
v_one_1129_ = lean_unsigned_to_nat(1u);
v_a_1130_ = lean_nat_sub(v_abs_1128_, v_one_1129_);
lean_dec(v_abs_1128_);
v___x_1131_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1132_ = lean_nat_add(v_a_1130_, v_one_1129_);
lean_dec(v_a_1130_);
v___x_1133_ = l_Nat_reprFast(v___x_1132_);
v___x_1134_ = lean_string_append(v___x_1131_, v___x_1133_);
lean_dec_ref(v___x_1133_);
v___y_1109_ = v___x_1134_;
goto v___jp_1108_;
}
v___jp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v_intZero_1113_; uint8_t v_isNeg_1114_; 
v___x_1110_ = lean_string_append(v___x_1107_, v___y_1109_);
lean_dec_ref(v___y_1109_);
v___x_1111_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1112_ = lean_string_append(v___x_1110_, v___x_1111_);
v_intZero_1113_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1114_ = lean_int_dec_lt(v_val_1104_, v_intZero_1113_);
if (v_isNeg_1114_ == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; 
v_a_1115_ = lean_nat_abs(v_val_1104_);
lean_dec(v_val_1104_);
v___x_1116_ = l_Nat_reprFast(v_a_1115_);
v___y_1061_ = v___x_1112_;
v___y_1062_ = v___x_1116_;
goto v___jp_1060_;
}
else
{
lean_object* v_abs_1117_; lean_object* v_one_1118_; lean_object* v_a_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_abs_1117_ = lean_nat_abs(v_val_1104_);
lean_dec(v_val_1104_);
v_one_1118_ = lean_unsigned_to_nat(1u);
v_a_1119_ = lean_nat_sub(v_abs_1117_, v_one_1118_);
lean_dec(v_abs_1117_);
v___x_1120_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1121_ = lean_nat_add(v_a_1119_, v_one_1118_);
lean_dec(v_a_1119_);
v___x_1122_ = l_Nat_reprFast(v___x_1121_);
v___x_1123_ = lean_string_append(v___x_1120_, v___x_1122_);
lean_dec_ref(v___x_1122_);
v___y_1061_ = v___x_1112_;
v___y_1062_ = v___x_1123_;
goto v___jp_1060_;
}
}
}
else
{
lean_object* v___x_1135_; lean_object* v___y_1137_; lean_object* v_intZero_1141_; uint8_t v_isNeg_1142_; 
lean_dec(v_val_1104_);
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1141_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1142_ = lean_int_dec_lt(v_val_1103_, v_intZero_1141_);
if (v_isNeg_1142_ == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; 
v_a_1143_ = lean_nat_abs(v_val_1103_);
lean_dec(v_val_1103_);
v___x_1144_ = l_Nat_reprFast(v_a_1143_);
v___y_1137_ = v___x_1144_;
goto v___jp_1136_;
}
else
{
lean_object* v_abs_1145_; lean_object* v_one_1146_; lean_object* v_a_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_abs_1145_ = lean_nat_abs(v_val_1103_);
lean_dec(v_val_1103_);
v_one_1146_ = lean_unsigned_to_nat(1u);
v_a_1147_ = lean_nat_sub(v_abs_1145_, v_one_1146_);
lean_dec(v_abs_1145_);
v___x_1148_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1149_ = lean_nat_add(v_a_1147_, v_one_1146_);
lean_dec(v_a_1147_);
v___x_1150_ = l_Nat_reprFast(v___x_1149_);
v___x_1151_ = lean_string_append(v___x_1148_, v___x_1150_);
lean_dec_ref(v___x_1150_);
v___y_1137_ = v___x_1151_;
goto v___jp_1136_;
}
v___jp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = lean_string_append(v___x_1135_, v___y_1137_);
lean_dec_ref(v___y_1137_);
v___x_1139_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1140_ = lean_string_append(v___x_1138_, v___x_1139_);
v___y_1040_ = v___x_1140_;
goto v___jp_1039_;
}
}
}
else
{
lean_object* v___x_1152_; 
lean_dec(v_val_1104_);
lean_dec(v_val_1103_);
v___x_1152_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1040_ = v___x_1152_;
goto v___jp_1039_;
}
}
}
v___jp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1041_ = lean_string_append(v___x_1038_, v___y_1040_);
lean_dec_ref(v___y_1040_);
v___x_1042_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__11));
v___x_1043_ = lean_string_append(v___x_1041_, v___x_1042_);
v___x_1044_ = l_Int_repr(v_a_1030_);
lean_dec(v_a_1030_);
v___x_1045_ = lean_string_append(v___x_1043_, v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__12));
v___x_1047_ = lean_string_append(v___x_1045_, v___x_1046_);
v___x_1048_ = l_Int_repr(v_b_1032_);
lean_dec(v_b_1032_);
v___x_1049_ = lean_string_append(v___x_1047_, v___x_1048_);
lean_dec_ref(v___x_1048_);
v___x_1050_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__13));
v___x_1051_ = lean_string_append(v___x_1049_, v___x_1050_);
v___x_1052_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_s_1026_, v_x_1028_, v_j_1031_);
v___x_1053_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1052_);
v___x_1054_ = lean_string_append(v___x_1051_, v___x_1053_);
lean_dec_ref(v___x_1053_);
v___x_1055_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_1056_ = lean_string_append(v___x_1054_, v___x_1055_);
v___x_1057_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_t_1027_, v_y_1029_, v_k_1033_);
v___x_1058_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1057_);
v___x_1059_ = lean_string_append(v___x_1056_, v___x_1058_);
lean_dec_ref(v___x_1058_);
return v___x_1059_;
}
v___jp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = lean_string_append(v___y_1061_, v___y_1062_);
lean_dec_ref(v___y_1062_);
v___x_1064_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1065_ = lean_string_append(v___x_1063_, v___x_1064_);
v___y_1040_ = v___x_1065_;
goto v___jp_1039_;
}
}
default: 
{
lean_object* v_m_1153_; lean_object* v_r_1154_; lean_object* v_i_1155_; lean_object* v_x_1156_; lean_object* v_j_1157_; lean_object* v_lowerBound_1158_; lean_object* v_upperBound_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___y_1164_; lean_object* v___y_1181_; lean_object* v___y_1182_; 
v_m_1153_ = lean_ctor_get(v_x_680_, 0);
lean_inc(v_m_1153_);
v_r_1154_ = lean_ctor_get(v_x_680_, 1);
lean_inc(v_r_1154_);
v_i_1155_ = lean_ctor_get(v_x_680_, 2);
lean_inc(v_i_1155_);
v_x_1156_ = lean_ctor_get(v_x_680_, 3);
lean_inc(v_x_1156_);
v_j_1157_ = lean_ctor_get(v_x_680_, 4);
lean_inc_ref(v_j_1157_);
lean_dec_ref_known(v_x_680_, 5);
v_lowerBound_1158_ = lean_ctor_get(v_s_678_, 0);
lean_inc(v_lowerBound_1158_);
v_upperBound_1159_ = lean_ctor_get(v_s_678_, 1);
lean_inc(v_upperBound_1159_);
lean_dec_ref(v_s_678_);
v___x_1160_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_x_679_);
lean_dec(v_x_679_);
v___x_1161_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_1162_ = lean_string_append(v___x_1160_, v___x_1161_);
if (lean_obj_tag(v_lowerBound_1158_) == 0)
{
if (lean_obj_tag(v_upperBound_1159_) == 0)
{
lean_object* v___x_1186_; 
v___x_1186_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___y_1164_ = v___x_1186_;
goto v___jp_1163_;
}
else
{
lean_object* v_val_1187_; lean_object* v___x_1188_; lean_object* v___y_1190_; lean_object* v_intZero_1194_; uint8_t v_isNeg_1195_; 
v_val_1187_ = lean_ctor_get(v_upperBound_1159_, 0);
lean_inc(v_val_1187_);
lean_dec_ref_known(v_upperBound_1159_, 1);
v___x_1188_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_1194_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1195_ = lean_int_dec_lt(v_val_1187_, v_intZero_1194_);
if (v_isNeg_1195_ == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1197_; 
v_a_1196_ = lean_nat_abs(v_val_1187_);
lean_dec(v_val_1187_);
v___x_1197_ = l_Nat_reprFast(v_a_1196_);
v___y_1190_ = v___x_1197_;
goto v___jp_1189_;
}
else
{
lean_object* v_abs_1198_; lean_object* v_one_1199_; lean_object* v_a_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_abs_1198_ = lean_nat_abs(v_val_1187_);
lean_dec(v_val_1187_);
v_one_1199_ = lean_unsigned_to_nat(1u);
v_a_1200_ = lean_nat_sub(v_abs_1198_, v_one_1199_);
lean_dec(v_abs_1198_);
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1202_ = lean_nat_add(v_a_1200_, v_one_1199_);
lean_dec(v_a_1200_);
v___x_1203_ = l_Nat_reprFast(v___x_1202_);
v___x_1204_ = lean_string_append(v___x_1201_, v___x_1203_);
lean_dec_ref(v___x_1203_);
v___y_1190_ = v___x_1204_;
goto v___jp_1189_;
}
v___jp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_string_append(v___x_1188_, v___y_1190_);
lean_dec_ref(v___y_1190_);
v___x_1192_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1193_ = lean_string_append(v___x_1191_, v___x_1192_);
v___y_1164_ = v___x_1193_;
goto v___jp_1163_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_1159_) == 0)
{
lean_object* v_val_1205_; lean_object* v___x_1206_; lean_object* v___y_1208_; lean_object* v_intZero_1212_; uint8_t v_isNeg_1213_; 
v_val_1205_ = lean_ctor_get(v_lowerBound_1158_, 0);
lean_inc(v_val_1205_);
lean_dec_ref_known(v_lowerBound_1158_, 1);
v___x_1206_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1212_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1213_ = lean_int_dec_lt(v_val_1205_, v_intZero_1212_);
if (v_isNeg_1213_ == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1215_; 
v_a_1214_ = lean_nat_abs(v_val_1205_);
lean_dec(v_val_1205_);
v___x_1215_ = l_Nat_reprFast(v_a_1214_);
v___y_1208_ = v___x_1215_;
goto v___jp_1207_;
}
else
{
lean_object* v_abs_1216_; lean_object* v_one_1217_; lean_object* v_a_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_abs_1216_ = lean_nat_abs(v_val_1205_);
lean_dec(v_val_1205_);
v_one_1217_ = lean_unsigned_to_nat(1u);
v_a_1218_ = lean_nat_sub(v_abs_1216_, v_one_1217_);
lean_dec(v_abs_1216_);
v___x_1219_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1220_ = lean_nat_add(v_a_1218_, v_one_1217_);
lean_dec(v_a_1218_);
v___x_1221_ = l_Nat_reprFast(v___x_1220_);
v___x_1222_ = lean_string_append(v___x_1219_, v___x_1221_);
lean_dec_ref(v___x_1221_);
v___y_1208_ = v___x_1222_;
goto v___jp_1207_;
}
v___jp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_string_append(v___x_1206_, v___y_1208_);
lean_dec_ref(v___y_1208_);
v___x_1210_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_1211_ = lean_string_append(v___x_1209_, v___x_1210_);
v___y_1164_ = v___x_1211_;
goto v___jp_1163_;
}
}
else
{
lean_object* v_val_1223_; lean_object* v_val_1224_; uint8_t v___x_1225_; 
v_val_1223_ = lean_ctor_get(v_lowerBound_1158_, 0);
lean_inc(v_val_1223_);
lean_dec_ref_known(v_lowerBound_1158_, 1);
v_val_1224_ = lean_ctor_get(v_upperBound_1159_, 0);
lean_inc(v_val_1224_);
lean_dec_ref_known(v_upperBound_1159_, 1);
v___x_1225_ = lean_int_dec_lt(v_val_1224_, v_val_1223_);
if (v___x_1225_ == 0)
{
uint8_t v___x_1226_; 
v___x_1226_ = lean_int_dec_eq(v_val_1223_, v_val_1224_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___y_1229_; lean_object* v_intZero_1244_; uint8_t v_isNeg_1245_; 
v___x_1227_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_1244_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1245_ = lean_int_dec_lt(v_val_1223_, v_intZero_1244_);
if (v_isNeg_1245_ == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1247_; 
v_a_1246_ = lean_nat_abs(v_val_1223_);
lean_dec(v_val_1223_);
v___x_1247_ = l_Nat_reprFast(v_a_1246_);
v___y_1229_ = v___x_1247_;
goto v___jp_1228_;
}
else
{
lean_object* v_abs_1248_; lean_object* v_one_1249_; lean_object* v_a_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_abs_1248_ = lean_nat_abs(v_val_1223_);
lean_dec(v_val_1223_);
v_one_1249_ = lean_unsigned_to_nat(1u);
v_a_1250_ = lean_nat_sub(v_abs_1248_, v_one_1249_);
lean_dec(v_abs_1248_);
v___x_1251_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1252_ = lean_nat_add(v_a_1250_, v_one_1249_);
lean_dec(v_a_1250_);
v___x_1253_ = l_Nat_reprFast(v___x_1252_);
v___x_1254_ = lean_string_append(v___x_1251_, v___x_1253_);
lean_dec_ref(v___x_1253_);
v___y_1229_ = v___x_1254_;
goto v___jp_1228_;
}
v___jp_1228_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v_intZero_1233_; uint8_t v_isNeg_1234_; 
v___x_1230_ = lean_string_append(v___x_1227_, v___y_1229_);
lean_dec_ref(v___y_1229_);
v___x_1231_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_1232_ = lean_string_append(v___x_1230_, v___x_1231_);
v_intZero_1233_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1234_ = lean_int_dec_lt(v_val_1224_, v_intZero_1233_);
if (v_isNeg_1234_ == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1236_; 
v_a_1235_ = lean_nat_abs(v_val_1224_);
lean_dec(v_val_1224_);
v___x_1236_ = l_Nat_reprFast(v_a_1235_);
v___y_1181_ = v___x_1232_;
v___y_1182_ = v___x_1236_;
goto v___jp_1180_;
}
else
{
lean_object* v_abs_1237_; lean_object* v_one_1238_; lean_object* v_a_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_abs_1237_ = lean_nat_abs(v_val_1224_);
lean_dec(v_val_1224_);
v_one_1238_ = lean_unsigned_to_nat(1u);
v_a_1239_ = lean_nat_sub(v_abs_1237_, v_one_1238_);
lean_dec(v_abs_1237_);
v___x_1240_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1241_ = lean_nat_add(v_a_1239_, v_one_1238_);
lean_dec(v_a_1239_);
v___x_1242_ = l_Nat_reprFast(v___x_1241_);
v___x_1243_ = lean_string_append(v___x_1240_, v___x_1242_);
lean_dec_ref(v___x_1242_);
v___y_1181_ = v___x_1232_;
v___y_1182_ = v___x_1243_;
goto v___jp_1180_;
}
}
}
else
{
lean_object* v___x_1255_; lean_object* v___y_1257_; lean_object* v_intZero_1261_; uint8_t v_isNeg_1262_; 
lean_dec(v_val_1224_);
v___x_1255_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_1261_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_1262_ = lean_int_dec_lt(v_val_1223_, v_intZero_1261_);
if (v_isNeg_1262_ == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1264_; 
v_a_1263_ = lean_nat_abs(v_val_1223_);
lean_dec(v_val_1223_);
v___x_1264_ = l_Nat_reprFast(v_a_1263_);
v___y_1257_ = v___x_1264_;
goto v___jp_1256_;
}
else
{
lean_object* v_abs_1265_; lean_object* v_one_1266_; lean_object* v_a_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_abs_1265_ = lean_nat_abs(v_val_1223_);
lean_dec(v_val_1223_);
v_one_1266_ = lean_unsigned_to_nat(1u);
v_a_1267_ = lean_nat_sub(v_abs_1265_, v_one_1266_);
lean_dec(v_abs_1265_);
v___x_1268_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_1269_ = lean_nat_add(v_a_1267_, v_one_1266_);
lean_dec(v_a_1267_);
v___x_1270_ = l_Nat_reprFast(v___x_1269_);
v___x_1271_ = lean_string_append(v___x_1268_, v___x_1270_);
lean_dec_ref(v___x_1270_);
v___y_1257_ = v___x_1271_;
goto v___jp_1256_;
}
v___jp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_string_append(v___x_1255_, v___y_1257_);
lean_dec_ref(v___y_1257_);
v___x_1259_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_1260_ = lean_string_append(v___x_1258_, v___x_1259_);
v___y_1164_ = v___x_1260_;
goto v___jp_1163_;
}
}
}
else
{
lean_object* v___x_1272_; 
lean_dec(v_val_1224_);
lean_dec(v_val_1223_);
v___x_1272_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___y_1164_ = v___x_1272_;
goto v___jp_1163_;
}
}
}
v___jp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1165_ = lean_string_append(v___x_1162_, v___y_1164_);
lean_dec_ref(v___y_1164_);
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__14));
v___x_1167_ = lean_string_append(v___x_1165_, v___x_1166_);
v___x_1168_ = l_Nat_reprFast(v_m_1153_);
v___x_1169_ = lean_string_append(v___x_1167_, v___x_1168_);
lean_dec_ref(v___x_1168_);
v___x_1170_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__15));
v___x_1171_ = lean_string_append(v___x_1169_, v___x_1170_);
v___x_1172_ = l_Nat_reprFast(v_i_1155_);
v___x_1173_ = lean_string_append(v___x_1171_, v___x_1172_);
lean_dec_ref(v___x_1172_);
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__16));
v___x_1175_ = lean_string_append(v___x_1173_, v___x_1174_);
v___x_1176_ = l_Lean_Omega_Constraint_exact(v_r_1154_);
v___x_1177_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v___x_1176_, v_x_1156_, v_j_1157_);
v___x_1178_ = l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet(v___x_1177_);
v___x_1179_ = lean_string_append(v___x_1175_, v___x_1178_);
lean_dec_ref(v___x_1178_);
return v___x_1179_;
}
v___jp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = lean_string_append(v___y_1181_, v___y_1182_);
lean_dec_ref(v___y_1182_);
v___x_1184_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_1185_ = lean_string_append(v___x_1183_, v___x_1184_);
v___y_1164_ = v___x_1185_;
goto v___jp_1163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_instToString(lean_object* v_s_1273_, lean_object* v_x_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Justification_toString), 3, 2);
lean_closure_set(v___x_1275_, 0, v_s_1273_);
lean_closure_set(v___x_1275_, 1, v_x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(lean_object* v_nilFn_1276_, lean_object* v_consFn_1277_, lean_object* v_x_1278_){
_start:
{
if (lean_obj_tag(v_x_1278_) == 0)
{
lean_dec_ref(v_consFn_1277_);
lean_inc_ref(v_nilFn_1276_);
return v_nilFn_1276_;
}
else
{
lean_object* v_head_1279_; lean_object* v_tail_1280_; lean_object* v___y_1282_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_head_1279_ = lean_ctor_get(v_x_1278_, 0);
v_tail_1280_ = lean_ctor_get(v_x_1278_, 1);
v___x_1285_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1286_ = lean_int_dec_le(v___x_1285_, v_head_1279_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1287_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1288_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1289_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1290_ = lean_int_neg(v_head_1279_);
v___x_1291_ = l_Int_toNat(v___x_1290_);
lean_dec(v___x_1290_);
v___x_1292_ = l_Lean_instToExprInt_mkNat(v___x_1291_);
v___x_1293_ = l_Lean_mkApp3(v___x_1287_, v___x_1288_, v___x_1289_, v___x_1292_);
v___y_1282_ = v___x_1293_;
goto v___jp_1281_;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = l_Int_toNat(v_head_1279_);
v___x_1295_ = l_Lean_instToExprInt_mkNat(v___x_1294_);
v___y_1282_ = v___x_1295_;
goto v___jp_1281_;
}
v___jp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
lean_inc_ref(v_consFn_1277_);
v___x_1283_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1276_, v_consFn_1277_, v_tail_1280_);
v___x_1284_ = l_Lean_mkAppB(v_consFn_1277_, v___y_1282_, v___x_1283_);
return v___x_1284_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0___boxed(lean_object* v_nilFn_1296_, lean_object* v_consFn_1297_, lean_object* v_x_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nilFn_1296_, v_consFn_1297_, v_x_1298_);
lean_dec(v_x_1298_);
lean_dec_ref(v_nilFn_1296_);
return v_res_1299_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = lean_box(0);
v___x_1306_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__1));
v___x_1307_ = l_Lean_Expr_const___override(v___x_1306_, v___x_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof(lean_object* v_s_1308_, lean_object* v_x_1309_, lean_object* v_v_1310_, lean_object* v_prf_1311_){
_start:
{
lean_object* v___x_1312_; lean_object* v___y_1314_; lean_object* v_lowerBound_1319_; lean_object* v_upperBound_1320_; lean_object* v___x_1321_; lean_object* v_type_1322_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1330_; 
v___x_1312_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_tidyProof___closed__2);
v_lowerBound_1319_ = lean_ctor_get(v_s_1308_, 0);
v_upperBound_1320_ = lean_ctor_get(v_s_1308_, 1);
v___x_1321_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1322_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1319_) == 0)
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1330_ = v___x_1346_;
goto v___jp_1329_;
}
else
{
lean_object* v_val_1347_; lean_object* v___x_1348_; lean_object* v___y_1350_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_val_1347_ = lean_ctor_get(v_lowerBound_1319_, 0);
v___x_1348_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1352_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1353_ = lean_int_dec_le(v___x_1352_, v_val_1347_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1354_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1355_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1356_ = lean_int_neg(v_val_1347_);
v___x_1357_ = l_Int_toNat(v___x_1356_);
lean_dec(v___x_1356_);
v___x_1358_ = l_Lean_instToExprInt_mkNat(v___x_1357_);
v___x_1359_ = l_Lean_mkApp3(v___x_1354_, v_type_1322_, v___x_1355_, v___x_1358_);
v___y_1350_ = v___x_1359_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = l_Int_toNat(v_val_1347_);
v___x_1361_ = l_Lean_instToExprInt_mkNat(v___x_1360_);
v___y_1350_ = v___x_1361_;
goto v___jp_1349_;
}
v___jp_1349_:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_mkAppB(v___x_1348_, v_type_1322_, v___y_1350_);
v___y_1330_ = v___x_1351_;
goto v___jp_1329_;
}
}
v___jp_1313_:
{
lean_object* v_nil_1315_; lean_object* v_cons_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_nil_1315_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1316_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1317_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1315_, v_cons_1316_, v_x_1309_);
v___x_1318_ = l_Lean_mkApp4(v___x_1312_, v___y_1314_, v___x_1317_, v_v_1310_, v_prf_1311_);
return v___x_1318_;
}
v___jp_1323_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_inc_ref(v___y_1324_);
v___x_1327_ = l_Lean_mkAppB(v___y_1324_, v_type_1322_, v___y_1326_);
v___x_1328_ = l_Lean_Expr_app___override(v___y_1325_, v___x_1327_);
v___y_1314_ = v___x_1328_;
goto v___jp_1313_;
}
v___jp_1329_:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_Expr_app___override(v___x_1321_, v___y_1330_);
if (lean_obj_tag(v_upperBound_1320_) == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1333_ = l_Lean_Expr_app___override(v___x_1331_, v___x_1332_);
v___y_1314_ = v___x_1333_;
goto v___jp_1313_;
}
else
{
lean_object* v_val_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v_val_1334_ = lean_ctor_get(v_upperBound_1320_, 0);
v___x_1335_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1336_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1337_ = lean_int_dec_le(v___x_1336_, v_val_1334_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1338_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1339_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1340_ = lean_int_neg(v_val_1334_);
v___x_1341_ = l_Int_toNat(v___x_1340_);
lean_dec(v___x_1340_);
v___x_1342_ = l_Lean_instToExprInt_mkNat(v___x_1341_);
v___x_1343_ = l_Lean_mkApp3(v___x_1338_, v_type_1322_, v___x_1339_, v___x_1342_);
v___y_1324_ = v___x_1335_;
v___y_1325_ = v___x_1331_;
v___y_1326_ = v___x_1343_;
goto v___jp_1323_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = l_Int_toNat(v_val_1334_);
v___x_1345_ = l_Lean_instToExprInt_mkNat(v___x_1344_);
v___y_1324_ = v___x_1335_;
v___y_1325_ = v___x_1331_;
v___y_1326_ = v___x_1345_;
goto v___jp_1323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_tidyProof___boxed(lean_object* v_s_1362_, lean_object* v_x_1363_, lean_object* v_v_1364_, lean_object* v_prf_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1362_, v_x_1363_, v_v_1364_, v_prf_1365_);
lean_dec(v_x_1363_);
lean_dec_ref(v_s_1362_);
return v_res_1366_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_box(0);
v___x_1374_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__1));
v___x_1375_ = l_Lean_Expr_const___override(v___x_1374_, v___x_1373_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof(lean_object* v_s_1376_, lean_object* v_t_1377_, lean_object* v_x_1378_, lean_object* v_v_1379_, lean_object* v_ps_1380_, lean_object* v_pt_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1433_; lean_object* v_lowerBound_1451_; lean_object* v_upperBound_1452_; lean_object* v___x_1453_; lean_object* v_type_1454_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1462_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_combineProof___closed__2);
v_lowerBound_1451_ = lean_ctor_get(v_s_1376_, 0);
v_upperBound_1452_ = lean_ctor_get(v_s_1376_, 1);
v___x_1453_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1454_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1451_) == 0)
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1462_ = v___x_1478_;
goto v___jp_1461_;
}
else
{
lean_object* v_val_1479_; lean_object* v___x_1480_; lean_object* v___y_1482_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v_val_1479_ = lean_ctor_get(v_lowerBound_1451_, 0);
v___x_1480_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1484_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1485_ = lean_int_dec_le(v___x_1484_, v_val_1479_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1486_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1487_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1488_ = lean_int_neg(v_val_1479_);
v___x_1489_ = l_Int_toNat(v___x_1488_);
lean_dec(v___x_1488_);
v___x_1490_ = l_Lean_instToExprInt_mkNat(v___x_1489_);
v___x_1491_ = l_Lean_mkApp3(v___x_1486_, v_type_1454_, v___x_1487_, v___x_1490_);
v___y_1482_ = v___x_1491_;
goto v___jp_1481_;
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = l_Int_toNat(v_val_1479_);
v___x_1493_ = l_Lean_instToExprInt_mkNat(v___x_1492_);
v___y_1482_ = v___x_1493_;
goto v___jp_1481_;
}
v___jp_1481_:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_mkAppB(v___x_1480_, v_type_1454_, v___y_1482_);
v___y_1462_ = v___x_1483_;
goto v___jp_1461_;
}
}
v___jp_1384_:
{
lean_object* v_nil_1387_; lean_object* v_cons_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_nil_1387_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1388_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1389_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1387_, v_cons_1388_, v_x_1378_);
v___x_1390_ = l_Lean_mkApp6(v___x_1383_, v___y_1385_, v___y_1386_, v___x_1389_, v_v_1379_, v_ps_1380_, v_pt_1381_);
return v___x_1390_;
}
v___jp_1391_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_inc_ref(v___y_1394_);
v___x_1397_ = l_Lean_mkAppB(v___y_1394_, v___y_1393_, v___y_1396_);
v___x_1398_ = l_Lean_Expr_app___override(v___y_1392_, v___x_1397_);
v___y_1385_ = v___y_1395_;
v___y_1386_ = v___x_1398_;
goto v___jp_1384_;
}
v___jp_1399_:
{
lean_object* v_upperBound_1405_; lean_object* v___x_1406_; 
v_upperBound_1405_ = lean_ctor_get(v_t_1377_, 1);
lean_inc_ref(v___y_1401_);
v___x_1406_ = l_Lean_Expr_app___override(v___y_1401_, v___y_1404_);
if (lean_obj_tag(v_upperBound_1405_) == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1407_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1408_ = l_Lean_Expr_app___override(v___x_1407_, v___y_1402_);
v___x_1409_ = l_Lean_Expr_app___override(v___x_1406_, v___x_1408_);
v___y_1385_ = v___y_1403_;
v___y_1386_ = v___x_1409_;
goto v___jp_1384_;
}
else
{
lean_object* v_val_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v_val_1410_ = lean_ctor_get(v_upperBound_1405_, 0);
v___x_1411_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1412_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1413_ = lean_int_dec_le(v___x_1412_, v_val_1410_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1414_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1415_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1400_);
v___x_1416_ = l_Lean_Name_mkStr2(v___y_1400_, v___x_1415_);
v___x_1417_ = l_Lean_Expr_const___override(v___x_1416_, v___x_1382_);
v___x_1418_ = lean_int_neg(v_val_1410_);
v___x_1419_ = l_Int_toNat(v___x_1418_);
lean_dec(v___x_1418_);
v___x_1420_ = l_Lean_instToExprInt_mkNat(v___x_1419_);
lean_inc_ref(v___y_1402_);
v___x_1421_ = l_Lean_mkApp3(v___x_1414_, v___y_1402_, v___x_1417_, v___x_1420_);
v___y_1392_ = v___x_1406_;
v___y_1393_ = v___y_1402_;
v___y_1394_ = v___x_1411_;
v___y_1395_ = v___y_1403_;
v___y_1396_ = v___x_1421_;
goto v___jp_1391_;
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = l_Int_toNat(v_val_1410_);
v___x_1423_ = l_Lean_instToExprInt_mkNat(v___x_1422_);
v___y_1392_ = v___x_1406_;
v___y_1393_ = v___y_1402_;
v___y_1394_ = v___x_1411_;
v___y_1395_ = v___y_1403_;
v___y_1396_ = v___x_1423_;
goto v___jp_1391_;
}
}
}
v___jp_1424_:
{
lean_object* v___x_1431_; 
lean_inc_ref(v___y_1428_);
lean_inc_ref(v___y_1426_);
v___x_1431_ = l_Lean_mkAppB(v___y_1426_, v___y_1428_, v___y_1430_);
v___y_1400_ = v___y_1425_;
v___y_1401_ = v___y_1427_;
v___y_1402_ = v___y_1428_;
v___y_1403_ = v___y_1429_;
v___y_1404_ = v___x_1431_;
goto v___jp_1399_;
}
v___jp_1432_:
{
lean_object* v_lowerBound_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_type_1437_; 
v_lowerBound_1434_ = lean_ctor_get(v_t_1377_, 0);
v___x_1435_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1436_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1437_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1434_) == 0)
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1400_ = v___x_1436_;
v___y_1401_ = v___x_1435_;
v___y_1402_ = v_type_1437_;
v___y_1403_ = v___y_1433_;
v___y_1404_ = v___x_1438_;
goto v___jp_1399_;
}
else
{
lean_object* v_val_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_val_1439_ = lean_ctor_get(v_lowerBound_1434_, 0);
v___x_1440_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1441_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1442_ = lean_int_dec_le(v___x_1441_, v_val_1439_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1443_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1444_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1445_ = lean_int_neg(v_val_1439_);
v___x_1446_ = l_Int_toNat(v___x_1445_);
lean_dec(v___x_1445_);
v___x_1447_ = l_Lean_instToExprInt_mkNat(v___x_1446_);
v___x_1448_ = l_Lean_mkApp3(v___x_1443_, v_type_1437_, v___x_1444_, v___x_1447_);
v___y_1425_ = v___x_1436_;
v___y_1426_ = v___x_1440_;
v___y_1427_ = v___x_1435_;
v___y_1428_ = v_type_1437_;
v___y_1429_ = v___y_1433_;
v___y_1430_ = v___x_1448_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = l_Int_toNat(v_val_1439_);
v___x_1450_ = l_Lean_instToExprInt_mkNat(v___x_1449_);
v___y_1425_ = v___x_1436_;
v___y_1426_ = v___x_1440_;
v___y_1427_ = v___x_1435_;
v___y_1428_ = v_type_1437_;
v___y_1429_ = v___y_1433_;
v___y_1430_ = v___x_1450_;
goto v___jp_1424_;
}
}
}
v___jp_1455_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_inc_ref(v___y_1456_);
v___x_1459_ = l_Lean_mkAppB(v___y_1456_, v_type_1454_, v___y_1458_);
v___x_1460_ = l_Lean_Expr_app___override(v___y_1457_, v___x_1459_);
v___y_1433_ = v___x_1460_;
goto v___jp_1432_;
}
v___jp_1461_:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_Expr_app___override(v___x_1453_, v___y_1462_);
if (lean_obj_tag(v_upperBound_1452_) == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1465_ = l_Lean_Expr_app___override(v___x_1463_, v___x_1464_);
v___y_1433_ = v___x_1465_;
goto v___jp_1432_;
}
else
{
lean_object* v_val_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_val_1466_ = lean_ctor_get(v_upperBound_1452_, 0);
v___x_1467_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1468_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1469_ = lean_int_dec_le(v___x_1468_, v_val_1466_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1470_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1471_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1472_ = lean_int_neg(v_val_1466_);
v___x_1473_ = l_Int_toNat(v___x_1472_);
lean_dec(v___x_1472_);
v___x_1474_ = l_Lean_instToExprInt_mkNat(v___x_1473_);
v___x_1475_ = l_Lean_mkApp3(v___x_1470_, v_type_1454_, v___x_1471_, v___x_1474_);
v___y_1456_ = v___x_1467_;
v___y_1457_ = v___x_1463_;
v___y_1458_ = v___x_1475_;
goto v___jp_1455_;
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = l_Int_toNat(v_val_1466_);
v___x_1477_ = l_Lean_instToExprInt_mkNat(v___x_1476_);
v___y_1456_ = v___x_1467_;
v___y_1457_ = v___x_1463_;
v___y_1458_ = v___x_1477_;
goto v___jp_1455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_combineProof___boxed(lean_object* v_s_1494_, lean_object* v_t_1495_, lean_object* v_x_1496_, lean_object* v_v_1497_, lean_object* v_ps_1498_, lean_object* v_pt_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1494_, v_t_1495_, v_x_1496_, v_v_1497_, v_ps_1498_, v_pt_1499_);
lean_dec(v_x_1496_);
lean_dec_ref(v_t_1495_);
lean_dec_ref(v_s_1494_);
return v_res_1500_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_box(0);
v___x_1507_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__1));
v___x_1508_ = l_Lean_Expr_const___override(v___x_1507_, v___x_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof(lean_object* v_s_1509_, lean_object* v_t_1510_, lean_object* v_a_1511_, lean_object* v_x_1512_, lean_object* v_b_1513_, lean_object* v_y_1514_, lean_object* v_v_1515_, lean_object* v_px_1516_, lean_object* v_py_1517_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1604_; lean_object* v_lowerBound_1622_; lean_object* v_upperBound_1623_; lean_object* v___x_1624_; lean_object* v_type_1625_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1633_; 
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2, &l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Justification_comboProof___closed__2);
v_lowerBound_1622_ = lean_ctor_get(v_s_1509_, 0);
v_upperBound_1623_ = lean_ctor_get(v_s_1509_, 1);
v___x_1624_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v_type_1625_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1622_) == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1633_ = v___x_1649_;
goto v___jp_1632_;
}
else
{
lean_object* v_val_1650_; lean_object* v___x_1651_; lean_object* v___y_1653_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v_val_1650_ = lean_ctor_get(v_lowerBound_1622_, 0);
v___x_1651_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1655_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1656_ = lean_int_dec_le(v___x_1655_, v_val_1650_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1657_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1658_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1659_ = lean_int_neg(v_val_1650_);
v___x_1660_ = l_Int_toNat(v___x_1659_);
lean_dec(v___x_1659_);
v___x_1661_ = l_Lean_instToExprInt_mkNat(v___x_1660_);
v___x_1662_ = l_Lean_mkApp3(v___x_1657_, v_type_1625_, v___x_1658_, v___x_1661_);
v___y_1653_ = v___x_1662_;
goto v___jp_1652_;
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = l_Int_toNat(v_val_1650_);
v___x_1664_ = l_Lean_instToExprInt_mkNat(v___x_1663_);
v___y_1653_ = v___x_1664_;
goto v___jp_1652_;
}
v___jp_1652_:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_mkAppB(v___x_1651_, v_type_1625_, v___y_1653_);
v___y_1633_ = v___x_1654_;
goto v___jp_1632_;
}
}
v___jp_1520_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v___y_1524_, v___y_1521_, v_y_1514_);
v___x_1529_ = l_Lean_mkApp9(v___x_1519_, v___y_1526_, v___y_1525_, v___y_1523_, v___y_1522_, v___y_1527_, v___x_1528_, v_v_1515_, v_px_1516_, v_py_1517_);
return v___x_1529_;
}
v___jp_1530_:
{
lean_object* v_type_1534_; lean_object* v_nil_1535_; lean_object* v_cons_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v_type_1534_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_nil_1535_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1536_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_1537_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1535_, v_cons_1536_, v_x_1512_);
v___x_1538_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1539_ = lean_int_dec_le(v___x_1538_, v_b_1513_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1540_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1541_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1542_ = lean_int_neg(v_b_1513_);
v___x_1543_ = l_Int_toNat(v___x_1542_);
lean_dec(v___x_1542_);
v___x_1544_ = l_Lean_instToExprInt_mkNat(v___x_1543_);
v___x_1545_ = l_Lean_mkApp3(v___x_1540_, v_type_1534_, v___x_1541_, v___x_1544_);
v___y_1521_ = v_cons_1536_;
v___y_1522_ = v___x_1537_;
v___y_1523_ = v___y_1533_;
v___y_1524_ = v_nil_1535_;
v___y_1525_ = v___y_1531_;
v___y_1526_ = v___y_1532_;
v___y_1527_ = v___x_1545_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = l_Int_toNat(v_b_1513_);
v___x_1547_ = l_Lean_instToExprInt_mkNat(v___x_1546_);
v___y_1521_ = v_cons_1536_;
v___y_1522_ = v___x_1537_;
v___y_1523_ = v___y_1533_;
v___y_1524_ = v_nil_1535_;
v___y_1525_ = v___y_1531_;
v___y_1526_ = v___y_1532_;
v___y_1527_ = v___x_1547_;
goto v___jp_1520_;
}
}
v___jp_1548_:
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1552_ = lean_int_dec_le(v___x_1551_, v_a_1511_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1553_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1554_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1555_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1556_ = lean_int_neg(v_a_1511_);
v___x_1557_ = l_Int_toNat(v___x_1556_);
lean_dec(v___x_1556_);
v___x_1558_ = l_Lean_instToExprInt_mkNat(v___x_1557_);
v___x_1559_ = l_Lean_mkApp3(v___x_1553_, v___x_1554_, v___x_1555_, v___x_1558_);
v___y_1531_ = v___y_1550_;
v___y_1532_ = v___y_1549_;
v___y_1533_ = v___x_1559_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = l_Int_toNat(v_a_1511_);
v___x_1561_ = l_Lean_instToExprInt_mkNat(v___x_1560_);
v___y_1531_ = v___y_1550_;
v___y_1532_ = v___y_1549_;
v___y_1533_ = v___x_1561_;
goto v___jp_1530_;
}
}
v___jp_1562_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_inc_ref(v___y_1564_);
v___x_1568_ = l_Lean_mkAppB(v___y_1564_, v___y_1563_, v___y_1567_);
v___x_1569_ = l_Lean_Expr_app___override(v___y_1565_, v___x_1568_);
v___y_1549_ = v___y_1566_;
v___y_1550_ = v___x_1569_;
goto v___jp_1548_;
}
v___jp_1570_:
{
lean_object* v_upperBound_1576_; lean_object* v___x_1577_; 
v_upperBound_1576_ = lean_ctor_get(v_t_1510_, 1);
lean_inc_ref(v___y_1573_);
v___x_1577_ = l_Lean_Expr_app___override(v___y_1573_, v___y_1575_);
if (lean_obj_tag(v_upperBound_1576_) == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1578_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__6);
v___x_1579_ = l_Lean_Expr_app___override(v___x_1578_, v___y_1571_);
v___x_1580_ = l_Lean_Expr_app___override(v___x_1577_, v___x_1579_);
v___y_1549_ = v___y_1574_;
v___y_1550_ = v___x_1580_;
goto v___jp_1548_;
}
else
{
lean_object* v_val_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v_val_1581_ = lean_ctor_get(v_upperBound_1576_, 0);
v___x_1582_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1583_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1584_ = lean_int_dec_le(v___x_1583_, v_val_1581_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1585_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1586_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__24));
lean_inc_ref(v___y_1572_);
v___x_1587_ = l_Lean_Name_mkStr2(v___y_1572_, v___x_1586_);
v___x_1588_ = l_Lean_Expr_const___override(v___x_1587_, v___x_1518_);
v___x_1589_ = lean_int_neg(v_val_1581_);
v___x_1590_ = l_Int_toNat(v___x_1589_);
lean_dec(v___x_1589_);
v___x_1591_ = l_Lean_instToExprInt_mkNat(v___x_1590_);
lean_inc_ref(v___y_1571_);
v___x_1592_ = l_Lean_mkApp3(v___x_1585_, v___y_1571_, v___x_1588_, v___x_1591_);
v___y_1563_ = v___y_1571_;
v___y_1564_ = v___x_1582_;
v___y_1565_ = v___x_1577_;
v___y_1566_ = v___y_1574_;
v___y_1567_ = v___x_1592_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = l_Int_toNat(v_val_1581_);
v___x_1594_ = l_Lean_instToExprInt_mkNat(v___x_1593_);
v___y_1563_ = v___y_1571_;
v___y_1564_ = v___x_1582_;
v___y_1565_ = v___x_1577_;
v___y_1566_ = v___y_1574_;
v___y_1567_ = v___x_1594_;
goto v___jp_1562_;
}
}
}
v___jp_1595_:
{
lean_object* v___x_1602_; 
lean_inc_ref(v___y_1596_);
lean_inc_ref(v___y_1599_);
v___x_1602_ = l_Lean_mkAppB(v___y_1599_, v___y_1596_, v___y_1601_);
v___y_1571_ = v___y_1596_;
v___y_1572_ = v___y_1598_;
v___y_1573_ = v___y_1597_;
v___y_1574_ = v___y_1600_;
v___y_1575_ = v___x_1602_;
goto v___jp_1570_;
}
v___jp_1603_:
{
lean_object* v_lowerBound_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v_type_1608_; 
v_lowerBound_1605_ = lean_ctor_get(v_t_1510_, 0);
v___x_1606_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
v___x_1607_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__4));
v_type_1608_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
if (lean_obj_tag(v_lowerBound_1605_) == 0)
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_1571_ = v_type_1608_;
v___y_1572_ = v___x_1607_;
v___y_1573_ = v___x_1606_;
v___y_1574_ = v___y_1604_;
v___y_1575_ = v___x_1609_;
goto v___jp_1570_;
}
else
{
lean_object* v_val_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v_val_1610_ = lean_ctor_get(v_lowerBound_1605_, 0);
v___x_1611_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1612_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1613_ = lean_int_dec_le(v___x_1612_, v_val_1610_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1614_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1615_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1616_ = lean_int_neg(v_val_1610_);
v___x_1617_ = l_Int_toNat(v___x_1616_);
lean_dec(v___x_1616_);
v___x_1618_ = l_Lean_instToExprInt_mkNat(v___x_1617_);
v___x_1619_ = l_Lean_mkApp3(v___x_1614_, v_type_1608_, v___x_1615_, v___x_1618_);
v___y_1596_ = v_type_1608_;
v___y_1597_ = v___x_1606_;
v___y_1598_ = v___x_1607_;
v___y_1599_ = v___x_1611_;
v___y_1600_ = v___y_1604_;
v___y_1601_ = v___x_1619_;
goto v___jp_1595_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = l_Int_toNat(v_val_1610_);
v___x_1621_ = l_Lean_instToExprInt_mkNat(v___x_1620_);
v___y_1596_ = v_type_1608_;
v___y_1597_ = v___x_1606_;
v___y_1598_ = v___x_1607_;
v___y_1599_ = v___x_1611_;
v___y_1600_ = v___y_1604_;
v___y_1601_ = v___x_1621_;
goto v___jp_1595_;
}
}
}
v___jp_1626_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_inc_ref(v___y_1628_);
v___x_1630_ = l_Lean_mkAppB(v___y_1628_, v_type_1625_, v___y_1629_);
v___x_1631_ = l_Lean_Expr_app___override(v___y_1627_, v___x_1630_);
v___y_1604_ = v___x_1631_;
goto v___jp_1603_;
}
v___jp_1632_:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Expr_app___override(v___x_1624_, v___y_1633_);
if (lean_obj_tag(v_upperBound_1623_) == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_1636_ = l_Lean_Expr_app___override(v___x_1634_, v___x_1635_);
v___y_1604_ = v___x_1636_;
goto v___jp_1603_;
}
else
{
lean_object* v_val_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v_val_1637_ = lean_ctor_get(v_upperBound_1623_, 0);
v___x_1638_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_1639_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1640_ = lean_int_dec_le(v___x_1639_, v_val_1637_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1641_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1642_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1643_ = lean_int_neg(v_val_1637_);
v___x_1644_ = l_Int_toNat(v___x_1643_);
lean_dec(v___x_1643_);
v___x_1645_ = l_Lean_instToExprInt_mkNat(v___x_1644_);
v___x_1646_ = l_Lean_mkApp3(v___x_1641_, v_type_1625_, v___x_1642_, v___x_1645_);
v___y_1627_ = v___x_1634_;
v___y_1628_ = v___x_1638_;
v___y_1629_ = v___x_1646_;
goto v___jp_1626_;
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = l_Int_toNat(v_val_1637_);
v___x_1648_ = l_Lean_instToExprInt_mkNat(v___x_1647_);
v___y_1627_ = v___x_1634_;
v___y_1628_ = v___x_1638_;
v___y_1629_ = v___x_1648_;
goto v___jp_1626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_comboProof___boxed(lean_object* v_s_1665_, lean_object* v_t_1666_, lean_object* v_a_1667_, lean_object* v_x_1668_, lean_object* v_b_1669_, lean_object* v_y_1670_, lean_object* v_v_1671_, lean_object* v_px_1672_, lean_object* v_py_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1665_, v_t_1666_, v_a_1667_, v_x_1668_, v_b_1669_, v_y_1670_, v_v_1671_, v_px_1672_, v_py_1673_);
lean_dec(v_y_1670_);
lean_dec(v_b_1669_);
lean_dec(v_x_1668_);
lean_dec(v_a_1667_);
lean_dec_ref(v_t_1666_);
lean_dec_ref(v_s_1665_);
return v_res_1674_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__10));
v___x_1681_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2));
v___x_1682_ = l_Lean_Expr_const___override(v___x_1681_, v___x_1680_);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_box(0);
v___x_1687_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__5));
v___x_1688_ = l_Lean_Expr_const___override(v___x_1687_, v___x_1686_);
return v___x_1688_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = lean_box(0);
v___x_1693_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__8));
v___x_1694_ = l_Lean_Expr_const___override(v___x_1693_, v___x_1692_);
return v___x_1694_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_box(0);
v___x_1703_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__12));
v___x_1704_ = l_Lean_Expr_const___override(v___x_1703_, v___x_1702_);
return v___x_1704_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = lean_box(0);
v___x_1712_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15));
v___x_1713_ = l_Lean_Expr_const___override(v___x_1712_, v___x_1711_);
return v___x_1713_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_box(0);
v___x_1720_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__18));
v___x_1721_ = l_Lean_Expr_const___override(v___x_1720_, v___x_1719_);
return v___x_1721_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = lean_box(0);
v___x_1728_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__21));
v___x_1729_ = l_Lean_Expr_const___override(v___x_1728_, v___x_1727_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof(lean_object* v_m_1730_, lean_object* v_r_1731_, lean_object* v_i_1732_, lean_object* v_x_1733_, lean_object* v_v_1734_, lean_object* v_w_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_m_1741_; lean_object* v___y_1743_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v_m_1741_ = l_Lean_mkNatLit(v_m_1730_);
v___x_1771_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1772_ = lean_int_dec_le(v___x_1771_, v_r_1731_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1773_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1774_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1775_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1776_ = lean_int_neg(v_r_1731_);
v___x_1777_ = l_Int_toNat(v___x_1776_);
lean_dec(v___x_1776_);
v___x_1778_ = l_Lean_instToExprInt_mkNat(v___x_1777_);
v___x_1779_ = l_Lean_mkApp3(v___x_1773_, v___x_1774_, v___x_1775_, v___x_1778_);
v___y_1743_ = v___x_1779_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = l_Int_toNat(v_r_1731_);
v___x_1781_ = l_Lean_instToExprInt_mkNat(v___x_1780_);
v___y_1743_ = v___x_1781_;
goto v___jp_1742_;
}
v___jp_1742_:
{
lean_object* v_i_1744_; lean_object* v_nil_1745_; lean_object* v_cons_1746_; lean_object* v_x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_i_1744_ = l_Lean_mkNatLit(v_i_1732_);
v_nil_1745_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1746_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v_x_1747_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1745_, v_cons_1746_, v_x_1733_);
v___x_1748_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__3);
v___x_1749_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6);
v___x_1750_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9);
v___x_1751_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13);
lean_inc_ref(v_x_1747_);
v___x_1752_ = l_Lean_Expr_app___override(v___x_1751_, v_x_1747_);
lean_inc_ref(v_i_1744_);
v___x_1753_ = l_Lean_mkApp4(v___x_1748_, v___x_1749_, v___x_1750_, v___x_1752_, v_i_1744_);
v___x_1754_ = l_Lean_Meta_mkDecideProof(v___x_1753_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16);
lean_inc_ref(v_i_1744_);
lean_inc_ref_n(v_v_1734_, 2);
v___x_1757_ = l_Lean_mkAppB(v___x_1756_, v_v_1734_, v_i_1744_);
v___x_1758_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc_ref(v_x_1747_);
lean_inc_ref(v_m_1741_);
v___x_1759_ = l_Lean_mkApp3(v___x_1758_, v_m_1741_, v_x_1747_, v_v_1734_);
v___x_1760_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v___x_1757_, v___x_1759_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1770_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1770_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1770_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1765_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__22);
v___x_1766_ = l_Lean_mkApp8(v___x_1765_, v_m_1741_, v___y_1743_, v_i_1744_, v_x_1747_, v_v_1734_, v_a_1755_, v_a_1761_, v_w_1735_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1766_);
v___x_1768_ = v___x_1763_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
else
{
lean_dec(v_a_1755_);
lean_dec_ref(v_x_1747_);
lean_dec_ref(v_i_1744_);
lean_dec_ref(v___y_1743_);
lean_dec_ref(v_m_1741_);
lean_dec_ref(v_w_1735_);
lean_dec_ref(v_v_1734_);
return v___x_1760_;
}
}
else
{
lean_dec_ref(v_x_1747_);
lean_dec_ref(v_i_1744_);
lean_dec_ref(v___y_1743_);
lean_dec_ref(v_m_1741_);
lean_dec_ref(v_w_1735_);
lean_dec_ref(v_v_1734_);
return v___x_1754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof___boxed(lean_object* v_m_1782_, lean_object* v_r_1783_, lean_object* v_i_1784_, lean_object* v_x_1785_, lean_object* v_v_1786_, lean_object* v_w_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1782_, v_r_1783_, v_i_1784_, v_x_1785_, v_v_1786_, v_w_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_x_1785_);
lean_dec(v_r_1783_);
return v_res_1793_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0(void){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_instMonadEIO___redArg();
return v___x_1794_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__0);
v___x_1796_ = l_StateRefT_x27_instMonad___redArg(v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(lean_object* v_c_1801_, lean_object* v_v_1802_, lean_object* v_assumptions_1803_, lean_object* v_x_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, uint8_t v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v___x_1815_; lean_object* v_toApplicative_1816_; lean_object* v_toFunctor_1817_; lean_object* v_toSeq_1818_; lean_object* v_toSeqLeft_1819_; lean_object* v_toSeqRight_1820_; lean_object* v___f_1821_; lean_object* v___f_1822_; lean_object* v___f_1823_; lean_object* v___f_1824_; lean_object* v___x_1825_; lean_object* v___f_1826_; lean_object* v___f_1827_; lean_object* v___f_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v_toApplicative_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1927_; 
v___x_1815_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1, &l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__1);
v_toApplicative_1816_ = lean_ctor_get(v___x_1815_, 0);
v_toFunctor_1817_ = lean_ctor_get(v_toApplicative_1816_, 0);
v_toSeq_1818_ = lean_ctor_get(v_toApplicative_1816_, 2);
v_toSeqLeft_1819_ = lean_ctor_get(v_toApplicative_1816_, 3);
v_toSeqRight_1820_ = lean_ctor_get(v_toApplicative_1816_, 4);
v___f_1821_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__2));
v___f_1822_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1817_, 2);
v___f_1823_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1823_, 0, v_toFunctor_1817_);
v___f_1824_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1824_, 0, v_toFunctor_1817_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___f_1823_);
lean_ctor_set(v___x_1825_, 1, v___f_1824_);
lean_inc(v_toSeqRight_1820_);
v___f_1826_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1826_, 0, v_toSeqRight_1820_);
lean_inc(v_toSeqLeft_1819_);
v___f_1827_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1827_, 0, v_toSeqLeft_1819_);
lean_inc(v_toSeq_1818_);
v___f_1828_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1828_, 0, v_toSeq_1818_);
v___x_1829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1825_);
lean_ctor_set(v___x_1829_, 1, v___f_1821_);
lean_ctor_set(v___x_1829_, 2, v___f_1828_);
lean_ctor_set(v___x_1829_, 3, v___f_1827_);
lean_ctor_set(v___x_1829_, 4, v___f_1826_);
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v___f_1822_);
v___x_1831_ = l_StateRefT_x27_instMonad___redArg(v___x_1830_);
v_toApplicative_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v___x_1831_, 1);
lean_dec(v_unused_1928_);
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1927_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_toApplicative_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1927_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v_toFunctor_1836_; lean_object* v_toSeq_1837_; lean_object* v_toSeqLeft_1838_; lean_object* v_toSeqRight_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1925_; 
v_toFunctor_1836_ = lean_ctor_get(v_toApplicative_1832_, 0);
v_toSeq_1837_ = lean_ctor_get(v_toApplicative_1832_, 2);
v_toSeqLeft_1838_ = lean_ctor_get(v_toApplicative_1832_, 3);
v_toSeqRight_1839_ = lean_ctor_get(v_toApplicative_1832_, 4);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_toApplicative_1832_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; 
v_unused_1926_ = lean_ctor_get(v_toApplicative_1832_, 1);
lean_dec(v_unused_1926_);
v___x_1841_ = v_toApplicative_1832_;
v_isShared_1842_ = v_isSharedCheck_1925_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_toSeqRight_1839_);
lean_inc(v_toSeqLeft_1838_);
lean_inc(v_toSeq_1837_);
lean_inc(v_toFunctor_1836_);
lean_dec(v_toApplicative_1832_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1925_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___f_1843_; lean_object* v___f_1844_; lean_object* v___f_1845_; lean_object* v___f_1846_; lean_object* v___x_1847_; lean_object* v___f_1848_; lean_object* v___f_1849_; lean_object* v___f_1850_; lean_object* v___x_1852_; 
v___f_1843_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__4));
v___f_1844_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___closed__5));
lean_inc_ref(v_toFunctor_1836_);
v___f_1845_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1845_, 0, v_toFunctor_1836_);
v___f_1846_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1846_, 0, v_toFunctor_1836_);
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___f_1845_);
lean_ctor_set(v___x_1847_, 1, v___f_1846_);
v___f_1848_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1848_, 0, v_toSeqRight_1839_);
v___f_1849_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1849_, 0, v_toSeqLeft_1838_);
v___f_1850_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1850_, 0, v_toSeq_1837_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 4, v___f_1848_);
lean_ctor_set(v___x_1841_, 3, v___f_1849_);
lean_ctor_set(v___x_1841_, 2, v___f_1850_);
lean_ctor_set(v___x_1841_, 1, v___f_1843_);
lean_ctor_set(v___x_1841_, 0, v___x_1847_);
v___x_1852_ = v___x_1841_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___f_1843_);
lean_ctor_set(v_reuseFailAlloc_1924_, 2, v___f_1850_);
lean_ctor_set(v_reuseFailAlloc_1924_, 3, v___f_1849_);
lean_ctor_set(v_reuseFailAlloc_1924_, 4, v___f_1848_);
v___x_1852_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1854_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v___f_1844_);
lean_ctor_set(v___x_1834_, 0, v___x_1852_);
v___x_1854_ = v___x_1834_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v___f_1844_);
v___x_1854_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1855_ = l_StateRefT_x27_instMonad___redArg(v___x_1854_);
v___x_1856_ = l_ReaderT_instMonad___redArg(v___x_1855_);
v___x_1857_ = l_ReaderT_instMonad___redArg(v___x_1856_);
v___x_1858_ = l_StateRefT_x27_instMonad___redArg(v___x_1857_);
v___x_1859_ = l_StateRefT_x27_instMonad___redArg(v___x_1858_);
switch(lean_obj_tag(v_x_1804_))
{
case 0:
{
lean_object* v_i_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_3464__overap_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_dec_ref(v_v_1802_);
v_i_1860_ = lean_ctor_get(v_x_1804_, 2);
lean_inc(v_i_1860_);
lean_dec_ref_known(v_x_1804_, 3);
v___x_1861_ = l_Lean_instInhabitedExpr;
v___x_1862_ = l_instInhabitedOfMonad___redArg(v___x_1859_, v___x_1861_);
v___x_3464__overap_1863_ = lean_array_get(v___x_1862_, v_assumptions_1803_, v_i_1860_);
lean_dec(v_i_1860_);
lean_dec(v___x_1862_);
v___x_1864_ = lean_box(v_a_1808_);
lean_inc(v_a_1813_);
lean_inc_ref(v_a_1812_);
lean_inc(v_a_1811_);
lean_inc_ref(v_a_1810_);
lean_inc(v_a_1809_);
lean_inc_ref(v_a_1807_);
lean_inc(v_a_1806_);
lean_inc(v_a_1805_);
v___x_1865_ = lean_apply_10(v___x_3464__overap_1863_, v_a_1805_, v_a_1806_, v_a_1807_, v___x_1864_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, lean_box(0));
return v___x_1865_;
}
case 1:
{
lean_object* v_s_1866_; lean_object* v_c_1867_; lean_object* v_j_1868_; lean_object* v___x_1869_; 
lean_dec_ref(v___x_1859_);
v_s_1866_ = lean_ctor_get(v_x_1804_, 0);
lean_inc_ref(v_s_1866_);
v_c_1867_ = lean_ctor_get(v_x_1804_, 1);
lean_inc(v_c_1867_);
v_j_1868_ = lean_ctor_get(v_x_1804_, 2);
lean_inc_ref(v_j_1868_);
lean_dec_ref_known(v_x_1804_, 3);
lean_inc_ref(v_v_1802_);
v___x_1869_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1867_, v_v_1802_, v_assumptions_1803_, v_j_1868_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1878_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1874_ = l_Lean_Elab_Tactic_Omega_Justification_tidyProof(v_s_1866_, v_c_1867_, v_v_1802_, v_a_1870_);
lean_dec(v_c_1867_);
lean_dec_ref(v_s_1866_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1874_);
v___x_1876_ = v___x_1872_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
else
{
lean_dec(v_c_1867_);
lean_dec_ref(v_s_1866_);
lean_dec_ref(v_v_1802_);
return v___x_1869_;
}
}
case 2:
{
lean_object* v_s_1879_; lean_object* v_t_1880_; lean_object* v_j_1881_; lean_object* v_k_1882_; lean_object* v___x_1883_; 
lean_dec_ref(v___x_1859_);
v_s_1879_ = lean_ctor_get(v_x_1804_, 0);
lean_inc_ref(v_s_1879_);
v_t_1880_ = lean_ctor_get(v_x_1804_, 1);
lean_inc_ref(v_t_1880_);
v_j_1881_ = lean_ctor_get(v_x_1804_, 3);
lean_inc_ref(v_j_1881_);
v_k_1882_ = lean_ctor_get(v_x_1804_, 4);
lean_inc_ref(v_k_1882_);
lean_dec_ref_known(v_x_1804_, 5);
lean_inc_ref(v_v_1802_);
v___x_1883_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1801_, v_v_1802_, v_assumptions_1803_, v_j_1881_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1885_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
lean_inc_ref(v_v_1802_);
v___x_1885_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1801_, v_v_1802_, v_assumptions_1803_, v_k_1882_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1894_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = l_Lean_Elab_Tactic_Omega_Justification_combineProof(v_s_1879_, v_t_1880_, v_c_1801_, v_v_1802_, v_a_1884_, v_a_1886_);
lean_dec_ref(v_t_1880_);
lean_dec_ref(v_s_1879_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1890_);
v___x_1892_ = v___x_1888_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
else
{
lean_dec(v_a_1884_);
lean_dec_ref(v_t_1880_);
lean_dec_ref(v_s_1879_);
lean_dec_ref(v_v_1802_);
return v___x_1885_;
}
}
else
{
lean_dec_ref(v_k_1882_);
lean_dec_ref(v_t_1880_);
lean_dec_ref(v_s_1879_);
lean_dec_ref(v_v_1802_);
return v___x_1883_;
}
}
case 3:
{
lean_object* v_s_1895_; lean_object* v_t_1896_; lean_object* v_x_1897_; lean_object* v_y_1898_; lean_object* v_a_1899_; lean_object* v_j_1900_; lean_object* v_b_1901_; lean_object* v_k_1902_; lean_object* v___x_1903_; 
lean_dec_ref(v___x_1859_);
v_s_1895_ = lean_ctor_get(v_x_1804_, 0);
lean_inc_ref(v_s_1895_);
v_t_1896_ = lean_ctor_get(v_x_1804_, 1);
lean_inc_ref(v_t_1896_);
v_x_1897_ = lean_ctor_get(v_x_1804_, 2);
lean_inc(v_x_1897_);
v_y_1898_ = lean_ctor_get(v_x_1804_, 3);
lean_inc(v_y_1898_);
v_a_1899_ = lean_ctor_get(v_x_1804_, 4);
lean_inc(v_a_1899_);
v_j_1900_ = lean_ctor_get(v_x_1804_, 5);
lean_inc_ref(v_j_1900_);
v_b_1901_ = lean_ctor_get(v_x_1804_, 6);
lean_inc(v_b_1901_);
v_k_1902_ = lean_ctor_get(v_x_1804_, 7);
lean_inc_ref(v_k_1902_);
lean_dec_ref_known(v_x_1804_, 8);
lean_inc_ref(v_v_1802_);
v___x_1903_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1897_, v_v_1802_, v_assumptions_1803_, v_j_1900_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1905_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1903_, 1);
lean_inc_ref(v_v_1802_);
v___x_1905_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_y_1898_, v_v_1802_, v_assumptions_1803_, v_k_1902_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1914_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1914_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1914_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1910_ = l_Lean_Elab_Tactic_Omega_Justification_comboProof(v_s_1895_, v_t_1896_, v_a_1899_, v_x_1897_, v_b_1901_, v_y_1898_, v_v_1802_, v_a_1904_, v_a_1906_);
lean_dec(v_y_1898_);
lean_dec(v_b_1901_);
lean_dec(v_x_1897_);
lean_dec(v_a_1899_);
lean_dec_ref(v_t_1896_);
lean_dec_ref(v_s_1895_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1910_);
v___x_1912_ = v___x_1908_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
else
{
lean_dec(v_a_1904_);
lean_dec(v_b_1901_);
lean_dec(v_a_1899_);
lean_dec(v_y_1898_);
lean_dec(v_x_1897_);
lean_dec_ref(v_t_1896_);
lean_dec_ref(v_s_1895_);
lean_dec_ref(v_v_1802_);
return v___x_1905_;
}
}
else
{
lean_dec_ref(v_k_1902_);
lean_dec(v_b_1901_);
lean_dec(v_a_1899_);
lean_dec(v_y_1898_);
lean_dec(v_x_1897_);
lean_dec_ref(v_t_1896_);
lean_dec_ref(v_s_1895_);
lean_dec_ref(v_v_1802_);
return v___x_1903_;
}
}
default: 
{
lean_object* v_m_1915_; lean_object* v_r_1916_; lean_object* v_i_1917_; lean_object* v_x_1918_; lean_object* v_j_1919_; lean_object* v___x_1920_; 
lean_dec_ref(v___x_1859_);
v_m_1915_ = lean_ctor_get(v_x_1804_, 0);
lean_inc(v_m_1915_);
v_r_1916_ = lean_ctor_get(v_x_1804_, 1);
lean_inc(v_r_1916_);
v_i_1917_ = lean_ctor_get(v_x_1804_, 2);
lean_inc(v_i_1917_);
v_x_1918_ = lean_ctor_get(v_x_1804_, 3);
lean_inc(v_x_1918_);
v_j_1919_ = lean_ctor_get(v_x_1804_, 4);
lean_inc_ref(v_j_1919_);
lean_dec_ref_known(v_x_1804_, 5);
lean_inc_ref(v_v_1802_);
v___x_1920_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1918_, v_v_1802_, v_assumptions_1803_, v_j_1919_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1922_ = l_Lean_Elab_Tactic_Omega_Justification_bmodProof(v_m_1915_, v_r_1916_, v_i_1917_, v_x_1918_, v_v_1802_, v_a_1921_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
lean_dec(v_x_1918_);
lean_dec(v_r_1916_);
return v___x_1922_;
}
else
{
lean_dec(v_x_1918_);
lean_dec(v_i_1917_);
lean_dec(v_r_1916_);
lean_dec(v_m_1915_);
lean_dec_ref(v_v_1802_);
return v___x_1920_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___redArg___boxed(lean_object* v_c_1929_, lean_object* v_v_1930_, lean_object* v_assumptions_1931_, lean_object* v_x_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
uint8_t v_a_boxed_1943_; lean_object* v_res_1944_; 
v_a_boxed_1943_ = lean_unbox(v_a_1936_);
v_res_1944_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1929_, v_v_1930_, v_assumptions_1931_, v_x_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_boxed_1943_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec(v_a_1933_);
lean_dec_ref(v_assumptions_1931_);
lean_dec(v_c_1929_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof(lean_object* v_s_1945_, lean_object* v_c_1946_, lean_object* v_v_1947_, lean_object* v_assumptions_1948_, lean_object* v_x_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, uint8_t v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1946_, v_v_1947_, v_assumptions_1948_, v_x_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_proof___boxed(lean_object* v_s_1961_, lean_object* v_c_1962_, lean_object* v_v_1963_, lean_object* v_assumptions_1964_, lean_object* v_x_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
uint8_t v_a_boxed_1976_; lean_object* v_res_1977_; 
v_a_boxed_1976_ = lean_unbox(v_a_1969_);
v_res_1977_ = l_Lean_Elab_Tactic_Omega_Justification_proof(v_s_1961_, v_c_1962_, v_v_1963_, v_assumptions_1964_, v_x_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_boxed_1976_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec(v_a_1966_);
lean_dec_ref(v_assumptions_1964_);
lean_dec(v_c_1962_);
lean_dec_ref(v_s_1961_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_instToString___lam__0(lean_object* v_f_1978_){
_start:
{
lean_object* v_coeffs_1979_; lean_object* v_constraint_1980_; lean_object* v_justification_1981_; lean_object* v___x_1982_; 
v_coeffs_1979_ = lean_ctor_get(v_f_1978_, 0);
lean_inc(v_coeffs_1979_);
v_constraint_1980_ = lean_ctor_get(v_f_1978_, 1);
lean_inc_ref(v_constraint_1980_);
v_justification_1981_ = lean_ctor_get(v_f_1978_, 2);
lean_inc_ref(v_justification_1981_);
lean_dec_ref(v_f_1978_);
v___x_1982_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_1980_, v_coeffs_1979_, v_justification_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_tidy(lean_object* v_f_1985_){
_start:
{
lean_object* v_coeffs_1986_; lean_object* v_constraint_1987_; lean_object* v_justification_1988_; lean_object* v___x_1989_; 
v_coeffs_1986_ = lean_ctor_get(v_f_1985_, 0);
v_constraint_1987_ = lean_ctor_get(v_f_1985_, 1);
v_justification_1988_ = lean_ctor_get(v_f_1985_, 2);
lean_inc_ref(v_justification_1988_);
lean_inc(v_coeffs_1986_);
lean_inc_ref(v_constraint_1987_);
v___x_1989_ = l_Lean_Elab_Tactic_Omega_Justification_tidy_x3f(v_constraint_1987_, v_coeffs_1986_, v_justification_1988_);
if (lean_obj_tag(v___x_1989_) == 0)
{
return v_f_1985_;
}
else
{
lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2001_; 
v_isSharedCheck_2001_ = !lean_is_exclusive(v_f_1985_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; lean_object* v_unused_2003_; lean_object* v_unused_2004_; 
v_unused_2002_ = lean_ctor_get(v_f_1985_, 2);
lean_dec(v_unused_2002_);
v_unused_2003_ = lean_ctor_get(v_f_1985_, 1);
lean_dec(v_unused_2003_);
v_unused_2004_ = lean_ctor_get(v_f_1985_, 0);
lean_dec(v_unused_2004_);
v___x_1991_ = v_f_1985_;
v_isShared_1992_ = v_isSharedCheck_2001_;
goto v_resetjp_1990_;
}
else
{
lean_dec(v_f_1985_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2001_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_val_1993_; lean_object* v_snd_1994_; lean_object* v_fst_1995_; lean_object* v_fst_1996_; lean_object* v_snd_1997_; lean_object* v___x_1999_; 
v_val_1993_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_val_1993_);
lean_dec_ref_known(v___x_1989_, 1);
v_snd_1994_ = lean_ctor_get(v_val_1993_, 1);
lean_inc(v_snd_1994_);
v_fst_1995_ = lean_ctor_get(v_val_1993_, 0);
lean_inc(v_fst_1995_);
lean_dec(v_val_1993_);
v_fst_1996_ = lean_ctor_get(v_snd_1994_, 0);
lean_inc(v_fst_1996_);
v_snd_1997_ = lean_ctor_get(v_snd_1994_, 1);
lean_inc(v_snd_1997_);
lean_dec(v_snd_1994_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 2, v_snd_1997_);
lean_ctor_set(v___x_1991_, 1, v_fst_1995_);
lean_ctor_set(v___x_1991_, 0, v_fst_1996_);
v___x_1999_ = v___x_1991_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_fst_1996_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_fst_1995_);
lean_ctor_set(v_reuseFailAlloc_2000_, 2, v_snd_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Fact_combo(lean_object* v_a_2005_, lean_object* v_f_2006_, lean_object* v_b_2007_, lean_object* v_g_2008_){
_start:
{
lean_object* v_coeffs_2009_; lean_object* v_constraint_2010_; lean_object* v_justification_2011_; lean_object* v_coeffs_2012_; lean_object* v_constraint_2013_; lean_object* v_justification_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2024_; 
v_coeffs_2009_ = lean_ctor_get(v_f_2006_, 0);
lean_inc(v_coeffs_2009_);
v_constraint_2010_ = lean_ctor_get(v_f_2006_, 1);
lean_inc_ref(v_constraint_2010_);
v_justification_2011_ = lean_ctor_get(v_f_2006_, 2);
lean_inc_ref(v_justification_2011_);
lean_dec_ref(v_f_2006_);
v_coeffs_2012_ = lean_ctor_get(v_g_2008_, 0);
v_constraint_2013_ = lean_ctor_get(v_g_2008_, 1);
v_justification_2014_ = lean_ctor_get(v_g_2008_, 2);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_g_2008_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2016_ = v_g_2008_;
v_isShared_2017_ = v_isSharedCheck_2024_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_justification_2014_);
lean_inc(v_constraint_2013_);
lean_inc(v_coeffs_2012_);
lean_dec(v_g_2008_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2024_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
lean_inc(v_coeffs_2012_);
lean_inc(v_coeffs_2009_);
v___x_2018_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_2005_, v_b_2007_, v_coeffs_2009_, v_coeffs_2012_);
lean_inc_ref(v_constraint_2013_);
lean_inc(v_b_2007_);
lean_inc_ref(v_constraint_2010_);
lean_inc(v_a_2005_);
v___x_2019_ = l_Lean_Omega_Constraint_combo(v_a_2005_, v_constraint_2010_, v_b_2007_, v_constraint_2013_);
v___x_2020_ = lean_alloc_ctor(3, 8, 0);
lean_ctor_set(v___x_2020_, 0, v_constraint_2010_);
lean_ctor_set(v___x_2020_, 1, v_constraint_2013_);
lean_ctor_set(v___x_2020_, 2, v_coeffs_2009_);
lean_ctor_set(v___x_2020_, 3, v_coeffs_2012_);
lean_ctor_set(v___x_2020_, 4, v_a_2005_);
lean_ctor_set(v___x_2020_, 5, v_justification_2011_);
lean_ctor_set(v___x_2020_, 6, v_b_2007_);
lean_ctor_set(v___x_2020_, 7, v_justification_2014_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 2, v___x_2020_);
lean_ctor_set(v___x_2016_, 1, v___x_2019_);
lean_ctor_set(v___x_2016_, 0, v___x_2018_);
v___x_2022_ = v___x_2016_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__10));
v___x_2051_ = l_Lean_mkAtom(v___x_2050_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__11);
v___x_2053_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2054_ = lean_array_push(v___x_2053_, v___x_2052_);
return v___x_2054_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2055_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__12);
v___x_2056_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__9));
v___x_2057_ = lean_box(2);
v___x_2058_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v___x_2056_);
lean_ctor_set(v___x_2058_, 2, v___x_2055_);
return v___x_2058_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__13);
v___x_2060_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2061_ = lean_array_push(v___x_2060_, v___x_2059_);
return v___x_2061_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2062_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__14);
v___x_2063_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__7));
v___x_2064_ = lean_box(2);
v___x_2065_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
lean_ctor_set(v___x_2065_, 1, v___x_2063_);
lean_ctor_set(v___x_2065_, 2, v___x_2062_);
return v___x_2065_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__15);
v___x_2067_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2068_ = lean_array_push(v___x_2067_, v___x_2066_);
return v___x_2068_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2069_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__16);
v___x_2070_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__5));
v___x_2071_ = lean_box(2);
v___x_2072_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v___x_2070_);
lean_ctor_set(v___x_2072_, 2, v___x_2069_);
return v___x_2072_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__17);
v___x_2074_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__3));
v___x_2075_ = lean_array_push(v___x_2074_, v___x_2073_);
return v___x_2075_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2076_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__18);
v___x_2077_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__2));
v___x_2078_ = lean_box(2);
v___x_2079_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v___x_2077_);
lean_ctor_set(v___x_2079_, 2, v___x_2076_);
return v___x_2079_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam(void){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse_x3f__spec___autoParam___closed__19);
return v___x_2080_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_isEmpty(lean_object* v_p_2081_){
_start:
{
lean_object* v_constraints_2082_; lean_object* v_size_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v_constraints_2082_ = lean_ctor_get(v_p_2081_, 2);
v_size_2083_ = lean_ctor_get(v_constraints_2082_, 0);
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = lean_nat_dec_eq(v_size_2083_, v___x_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_isEmpty___boxed(lean_object* v_p_2086_){
_start:
{
uint8_t v_res_2087_; lean_object* v_r_2088_; 
v_res_2087_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2086_);
lean_dec_ref(v_p_2086_);
v_r_2088_ = lean_box(v_res_2087_);
return v_r_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object* v_a_2089_, lean_object* v_b_2090_, lean_object* v_d_2091_){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v_a_2089_);
lean_ctor_set(v___x_2092_, 1, v_b_2090_);
v___x_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v_d_2091_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object* v___x_2094_, lean_object* v_x_2095_){
_start:
{
lean_object* v_snd_2096_; lean_object* v_constraint_2097_; lean_object* v_fst_2098_; lean_object* v_lowerBound_2099_; lean_object* v_upperBound_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___y_2105_; lean_object* v___y_2106_; 
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
v___x_2101_ = l_List_toString___redArg(v___x_2094_, v_fst_2098_);
v___x_2102_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_2103_ = lean_string_append(v___x_2101_, v___x_2102_);
if (lean_obj_tag(v_lowerBound_2099_) == 0)
{
if (lean_obj_tag(v_upperBound_2100_) == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_2112_ = lean_string_append(v___x_2103_, v___x_2111_);
return v___x_2112_;
}
else
{
lean_object* v_val_2113_; lean_object* v___x_2114_; lean_object* v___y_2116_; lean_object* v_intZero_2121_; uint8_t v_isNeg_2122_; 
v_val_2113_ = lean_ctor_get(v_upperBound_2100_, 0);
lean_inc(v_val_2113_);
lean_dec_ref_known(v_upperBound_2100_, 1);
v___x_2114_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_2121_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2122_ = lean_int_dec_lt(v_val_2113_, v_intZero_2121_);
if (v_isNeg_2122_ == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; 
v_a_2123_ = lean_nat_abs(v_val_2113_);
lean_dec(v_val_2113_);
v___x_2124_ = l_Nat_reprFast(v_a_2123_);
v___y_2116_ = v___x_2124_;
goto v___jp_2115_;
}
else
{
lean_object* v_abs_2125_; lean_object* v_one_2126_; lean_object* v_a_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_abs_2125_ = lean_nat_abs(v_val_2113_);
lean_dec(v_val_2113_);
v_one_2126_ = lean_unsigned_to_nat(1u);
v_a_2127_ = lean_nat_sub(v_abs_2125_, v_one_2126_);
lean_dec(v_abs_2125_);
v___x_2128_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2129_ = lean_nat_add(v_a_2127_, v_one_2126_);
lean_dec(v_a_2127_);
v___x_2130_ = l_Nat_reprFast(v___x_2129_);
v___x_2131_ = lean_string_append(v___x_2128_, v___x_2130_);
lean_dec_ref(v___x_2130_);
v___y_2116_ = v___x_2131_;
goto v___jp_2115_;
}
v___jp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2117_ = lean_string_append(v___x_2114_, v___y_2116_);
lean_dec_ref(v___y_2116_);
v___x_2118_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2119_ = lean_string_append(v___x_2117_, v___x_2118_);
v___x_2120_ = lean_string_append(v___x_2103_, v___x_2119_);
lean_dec_ref(v___x_2119_);
return v___x_2120_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_2100_) == 0)
{
lean_object* v_val_2132_; lean_object* v___x_2133_; lean_object* v___y_2135_; lean_object* v_intZero_2140_; uint8_t v_isNeg_2141_; 
v_val_2132_ = lean_ctor_get(v_lowerBound_2099_, 0);
lean_inc(v_val_2132_);
lean_dec_ref_known(v_lowerBound_2099_, 1);
v___x_2133_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2140_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2141_ = lean_int_dec_lt(v_val_2132_, v_intZero_2140_);
if (v_isNeg_2141_ == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; 
v_a_2142_ = lean_nat_abs(v_val_2132_);
lean_dec(v_val_2132_);
v___x_2143_ = l_Nat_reprFast(v_a_2142_);
v___y_2135_ = v___x_2143_;
goto v___jp_2134_;
}
else
{
lean_object* v_abs_2144_; lean_object* v_one_2145_; lean_object* v_a_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_abs_2144_ = lean_nat_abs(v_val_2132_);
lean_dec(v_val_2132_);
v_one_2145_ = lean_unsigned_to_nat(1u);
v_a_2146_ = lean_nat_sub(v_abs_2144_, v_one_2145_);
lean_dec(v_abs_2144_);
v___x_2147_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2148_ = lean_nat_add(v_a_2146_, v_one_2145_);
lean_dec(v_a_2146_);
v___x_2149_ = l_Nat_reprFast(v___x_2148_);
v___x_2150_ = lean_string_append(v___x_2147_, v___x_2149_);
lean_dec_ref(v___x_2149_);
v___y_2135_ = v___x_2150_;
goto v___jp_2134_;
}
v___jp_2134_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2136_ = lean_string_append(v___x_2133_, v___y_2135_);
lean_dec_ref(v___y_2135_);
v___x_2137_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_2138_ = lean_string_append(v___x_2136_, v___x_2137_);
v___x_2139_ = lean_string_append(v___x_2103_, v___x_2138_);
lean_dec_ref(v___x_2138_);
return v___x_2139_;
}
}
else
{
lean_object* v_val_2151_; lean_object* v_val_2152_; uint8_t v___x_2153_; 
v_val_2151_ = lean_ctor_get(v_lowerBound_2099_, 0);
lean_inc(v_val_2151_);
lean_dec_ref_known(v_lowerBound_2099_, 1);
v_val_2152_ = lean_ctor_get(v_upperBound_2100_, 0);
lean_inc(v_val_2152_);
lean_dec_ref_known(v_upperBound_2100_, 1);
v___x_2153_ = lean_int_dec_lt(v_val_2152_, v_val_2151_);
if (v___x_2153_ == 0)
{
uint8_t v___x_2154_; 
v___x_2154_ = lean_int_dec_eq(v_val_2151_, v_val_2152_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; lean_object* v___y_2157_; lean_object* v_intZero_2172_; uint8_t v_isNeg_2173_; 
v___x_2155_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2172_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2173_ = lean_int_dec_lt(v_val_2151_, v_intZero_2172_);
if (v_isNeg_2173_ == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; 
v_a_2174_ = lean_nat_abs(v_val_2151_);
lean_dec(v_val_2151_);
v___x_2175_ = l_Nat_reprFast(v_a_2174_);
v___y_2157_ = v___x_2175_;
goto v___jp_2156_;
}
else
{
lean_object* v_abs_2176_; lean_object* v_one_2177_; lean_object* v_a_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v_abs_2176_ = lean_nat_abs(v_val_2151_);
lean_dec(v_val_2151_);
v_one_2177_ = lean_unsigned_to_nat(1u);
v_a_2178_ = lean_nat_sub(v_abs_2176_, v_one_2177_);
lean_dec(v_abs_2176_);
v___x_2179_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2180_ = lean_nat_add(v_a_2178_, v_one_2177_);
lean_dec(v_a_2178_);
v___x_2181_ = l_Nat_reprFast(v___x_2180_);
v___x_2182_ = lean_string_append(v___x_2179_, v___x_2181_);
lean_dec_ref(v___x_2181_);
v___y_2157_ = v___x_2182_;
goto v___jp_2156_;
}
v___jp_2156_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v_intZero_2161_; uint8_t v_isNeg_2162_; 
v___x_2158_ = lean_string_append(v___x_2155_, v___y_2157_);
lean_dec_ref(v___y_2157_);
v___x_2159_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_2160_ = lean_string_append(v___x_2158_, v___x_2159_);
v_intZero_2161_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2162_ = lean_int_dec_lt(v_val_2152_, v_intZero_2161_);
if (v_isNeg_2162_ == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2164_; 
v_a_2163_ = lean_nat_abs(v_val_2152_);
lean_dec(v_val_2152_);
v___x_2164_ = l_Nat_reprFast(v_a_2163_);
v___y_2105_ = v___x_2160_;
v___y_2106_ = v___x_2164_;
goto v___jp_2104_;
}
else
{
lean_object* v_abs_2165_; lean_object* v_one_2166_; lean_object* v_a_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v_abs_2165_ = lean_nat_abs(v_val_2152_);
lean_dec(v_val_2152_);
v_one_2166_ = lean_unsigned_to_nat(1u);
v_a_2167_ = lean_nat_sub(v_abs_2165_, v_one_2166_);
lean_dec(v_abs_2165_);
v___x_2168_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2169_ = lean_nat_add(v_a_2167_, v_one_2166_);
lean_dec(v_a_2167_);
v___x_2170_ = l_Nat_reprFast(v___x_2169_);
v___x_2171_ = lean_string_append(v___x_2168_, v___x_2170_);
lean_dec_ref(v___x_2170_);
v___y_2105_ = v___x_2160_;
v___y_2106_ = v___x_2171_;
goto v___jp_2104_;
}
}
}
else
{
lean_object* v___x_2183_; lean_object* v___y_2185_; lean_object* v_intZero_2190_; uint8_t v_isNeg_2191_; 
lean_dec(v_val_2152_);
v___x_2183_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_2190_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2191_ = lean_int_dec_lt(v_val_2151_, v_intZero_2190_);
if (v_isNeg_2191_ == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2193_; 
v_a_2192_ = lean_nat_abs(v_val_2151_);
lean_dec(v_val_2151_);
v___x_2193_ = l_Nat_reprFast(v_a_2192_);
v___y_2185_ = v___x_2193_;
goto v___jp_2184_;
}
else
{
lean_object* v_abs_2194_; lean_object* v_one_2195_; lean_object* v_a_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v_abs_2194_ = lean_nat_abs(v_val_2151_);
lean_dec(v_val_2151_);
v_one_2195_ = lean_unsigned_to_nat(1u);
v_a_2196_ = lean_nat_sub(v_abs_2194_, v_one_2195_);
lean_dec(v_abs_2194_);
v___x_2197_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2198_ = lean_nat_add(v_a_2196_, v_one_2195_);
lean_dec(v_a_2196_);
v___x_2199_ = l_Nat_reprFast(v___x_2198_);
v___x_2200_ = lean_string_append(v___x_2197_, v___x_2199_);
lean_dec_ref(v___x_2199_);
v___y_2185_ = v___x_2200_;
goto v___jp_2184_;
}
v___jp_2184_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2186_ = lean_string_append(v___x_2183_, v___y_2185_);
lean_dec_ref(v___y_2185_);
v___x_2187_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_2188_ = lean_string_append(v___x_2186_, v___x_2187_);
v___x_2189_ = lean_string_append(v___x_2103_, v___x_2188_);
lean_dec_ref(v___x_2188_);
return v___x_2189_;
}
}
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec(v_val_2152_);
lean_dec(v_val_2151_);
v___x_2201_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_2202_ = lean_string_append(v___x_2103_, v___x_2201_);
return v___x_2202_;
}
}
}
v___jp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2107_ = lean_string_append(v___y_2105_, v___y_2106_);
lean_dec_ref(v___y_2106_);
v___x_2108_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2109_ = lean_string_append(v___x_2107_, v___x_2108_);
v___x_2110_ = lean_string_append(v___x_2103_, v___x_2109_);
lean_dec_ref(v___x_2109_);
return v___x_2110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2(lean_object* v___x_2203_, lean_object* v___f_2204_, lean_object* v_l_2205_, lean_object* v_acc_2206_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2203_, v___f_2204_, v_acc_2206_, v_l_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3(lean_object* v___f_2229_, lean_object* v___f_2230_, lean_object* v_p_2231_){
_start:
{
uint8_t v_possible_2232_; 
v_possible_2232_ = lean_ctor_get_uint8(v_p_2231_, sizeof(void*)*7);
if (v_possible_2232_ == 0)
{
lean_object* v___x_2233_; 
lean_dec_ref(v_p_2231_);
lean_dec_ref(v___f_2230_);
lean_dec_ref(v___f_2229_);
v___x_2233_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
return v___x_2233_;
}
else
{
lean_object* v_constraints_2234_; uint8_t v___x_2235_; 
v_constraints_2234_ = lean_ctor_get(v_p_2231_, 2);
lean_inc_ref(v_constraints_2234_);
v___x_2235_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2231_);
lean_dec_ref(v_p_2231_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; lean_object* v_buckets_2237_; lean_object* v___x_2238_; lean_object* v___y_2240_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; 
v___x_2236_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10));
v_buckets_2237_ = lean_ctor_get(v_constraints_2234_, 1);
lean_inc_ref(v_buckets_2237_);
lean_dec_ref(v_constraints_2234_);
v___x_2238_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_array_get_size(v_buckets_2237_);
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = lean_nat_dec_lt(v___x_2246_, v___x_2245_);
if (v___x_2247_ == 0)
{
lean_dec_ref(v_buckets_2237_);
lean_dec_ref(v___f_2230_);
v___y_2240_ = v___x_2244_;
goto v___jp_2239_;
}
else
{
lean_object* v___f_2248_; size_t v___x_2249_; size_t v___x_2250_; lean_object* v___x_2251_; 
v___f_2248_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2), 4, 2);
lean_closure_set(v___f_2248_, 0, v___x_2236_);
lean_closure_set(v___f_2248_, 1, v___f_2230_);
v___x_2249_ = lean_usize_of_nat(v___x_2245_);
v___x_2250_ = ((size_t)0ULL);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2236_, v___f_2248_, v_buckets_2237_, v___x_2249_, v___x_2250_, v___x_2244_);
v___y_2240_ = v___x_2251_;
goto v___jp_2239_;
}
v___jp_2239_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = lean_box(0);
v___x_2242_ = l_List_mapTR_loop___redArg(v___f_2229_, v___y_2240_, v___x_2241_);
v___x_2243_ = l_String_intercalate(v___x_2238_, v___x_2242_);
return v___x_2243_;
}
}
else
{
lean_object* v___x_2252_; 
lean_dec_ref(v_constraints_2234_);
lean_dec_ref(v___f_2230_);
lean_dec_ref(v___f_2229_);
v___x_2252_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
return v___x_2252_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = lean_box(0);
v___x_2268_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1));
v___x_2269_ = l_Lean_Expr_const___override(v___x_2268_, v___x_2267_);
return v___x_2269_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = lean_box(0);
v___x_2276_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5));
v___x_2277_ = l_Lean_Expr_const___override(v___x_2276_, v___x_2275_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = lean_box(0);
v___x_2285_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8));
v___x_2286_ = l_Lean_Expr_const___override(v___x_2285_, v___x_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse(lean_object* v_s_2287_, lean_object* v_x_2288_, lean_object* v_j_2289_, lean_object* v_assumptions_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, uint8_t v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2292_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc_n(v_a_2302_, 2);
lean_dec_ref_known(v___x_2301_, 1);
v___x_2303_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_2288_, v_a_2302_, v_assumptions_2290_, v_j_2289_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; lean_object* v_lowerBound_2306_; lean_object* v_upperBound_2307_; lean_object* v_nil_2308_; lean_object* v_cons_2309_; lean_object* v___x_2310_; lean_object* v___y_2312_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___x_2335_; lean_object* v___y_2337_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_lowerBound_2306_ = lean_ctor_get(v_s_2287_, 0);
v_upperBound_2307_ = lean_ctor_get(v_s_2287_, 1);
v_nil_2308_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2309_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2310_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2308_, v_cons_2309_, v_x_2288_);
v___x_2335_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
if (lean_obj_tag(v_lowerBound_2306_) == 0)
{
lean_object* v___x_2353_; 
v___x_2353_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_2337_ = v___x_2353_;
goto v___jp_2336_;
}
else
{
lean_object* v_val_2354_; lean_object* v___x_2355_; lean_object* v___y_2357_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v_val_2354_ = lean_ctor_get(v_lowerBound_2306_, 0);
v___x_2355_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2359_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2360_ = lean_int_dec_le(v___x_2359_, v_val_2354_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2361_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2362_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2363_ = lean_int_neg(v_val_2354_);
v___x_2364_ = l_Int_toNat(v___x_2363_);
lean_dec(v___x_2363_);
v___x_2365_ = l_Lean_instToExprInt_mkNat(v___x_2364_);
v___x_2366_ = l_Lean_mkApp3(v___x_2361_, v___x_2305_, v___x_2362_, v___x_2365_);
v___y_2357_ = v___x_2366_;
goto v___jp_2356_;
}
else
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = l_Int_toNat(v_val_2354_);
v___x_2368_ = l_Lean_instToExprInt_mkNat(v___x_2367_);
v___y_2357_ = v___x_2368_;
goto v___jp_2356_;
}
v___jp_2356_:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_mkAppB(v___x_2355_, v___x_2305_, v___y_2357_);
v___y_2337_ = v___x_2358_;
goto v___jp_2336_;
}
}
v___jp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2313_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2);
lean_inc_ref(v___y_2312_);
v___x_2314_ = l_Lean_Expr_app___override(v___x_2313_, v___y_2312_);
v___x_2315_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6);
v___x_2316_ = l_Lean_Meta_mkEq(v___x_2314_, v___x_2315_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = l_Lean_Meta_mkDecideProof(v_a_2317_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2328_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2328_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2328_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2323_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9);
v___x_2324_ = l_Lean_mkApp5(v___x_2323_, v___y_2312_, v_a_2319_, v___x_2310_, v_a_2302_, v_a_2304_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2324_);
v___x_2326_ = v___x_2321_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
else
{
lean_dec_ref(v___y_2312_);
lean_dec_ref(v___x_2310_);
lean_dec(v_a_2304_);
lean_dec(v_a_2302_);
return v___x_2318_;
}
}
else
{
lean_dec_ref(v___y_2312_);
lean_dec_ref(v___x_2310_);
lean_dec(v_a_2304_);
lean_dec(v_a_2302_);
return v___x_2316_;
}
}
v___jp_2329_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_inc_ref(v___y_2330_);
v___x_2333_ = l_Lean_mkAppB(v___y_2330_, v___x_2305_, v___y_2332_);
v___x_2334_ = l_Lean_Expr_app___override(v___y_2331_, v___x_2333_);
v___y_2312_ = v___x_2334_;
goto v___jp_2311_;
}
v___jp_2336_:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_Expr_app___override(v___x_2335_, v___y_2337_);
if (lean_obj_tag(v_upperBound_2307_) == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_2340_ = l_Lean_Expr_app___override(v___x_2338_, v___x_2339_);
v___y_2312_ = v___x_2340_;
goto v___jp_2311_;
}
else
{
lean_object* v_val_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v_val_2341_ = lean_ctor_get(v_upperBound_2307_, 0);
v___x_2342_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2343_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2344_ = lean_int_dec_le(v___x_2343_, v_val_2341_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2345_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2346_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2347_ = lean_int_neg(v_val_2341_);
v___x_2348_ = l_Int_toNat(v___x_2347_);
lean_dec(v___x_2347_);
v___x_2349_ = l_Lean_instToExprInt_mkNat(v___x_2348_);
v___x_2350_ = l_Lean_mkApp3(v___x_2345_, v___x_2305_, v___x_2346_, v___x_2349_);
v___y_2330_ = v___x_2342_;
v___y_2331_ = v___x_2338_;
v___y_2332_ = v___x_2350_;
goto v___jp_2329_;
}
else
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = l_Int_toNat(v_val_2341_);
v___x_2352_ = l_Lean_instToExprInt_mkNat(v___x_2351_);
v___y_2330_ = v___x_2342_;
v___y_2331_ = v___x_2338_;
v___y_2332_ = v___x_2352_;
goto v___jp_2329_;
}
}
}
}
else
{
lean_dec(v_a_2302_);
return v___x_2303_;
}
}
else
{
lean_dec_ref(v_j_2289_);
return v___x_2301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed(lean_object* v_s_2369_, lean_object* v_x_2370_, lean_object* v_j_2371_, lean_object* v_assumptions_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
uint8_t v_a_boxed_2383_; lean_object* v_res_2384_; 
v_a_boxed_2383_ = lean_unbox(v_a_2376_);
v_res_2384_ = l_Lean_Elab_Tactic_Omega_Problem_proveFalse(v_s_2369_, v_x_2370_, v_j_2371_, v_assumptions_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_boxed_2383_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_assumptions_2372_);
lean_dec(v_x_2370_);
lean_dec_ref(v_s_2369_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0(lean_object* v_constraint_2385_, lean_object* v_coeffs_2386_, lean_object* v_justification_2387_, lean_object* v_x_2388_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_2385_, v_coeffs_2386_, v_justification_2387_);
return v___x_2389_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(lean_object* v_a_2390_, lean_object* v_x_2391_){
_start:
{
if (lean_obj_tag(v_x_2391_) == 0)
{
uint8_t v___x_2392_; 
v___x_2392_ = 0;
return v___x_2392_;
}
else
{
lean_object* v_key_2393_; lean_object* v_tail_2394_; uint8_t v___x_2395_; 
v_key_2393_ = lean_ctor_get(v_x_2391_, 0);
v_tail_2394_ = lean_ctor_get(v_x_2391_, 2);
v___x_2395_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2393_, v_a_2390_);
if (v___x_2395_ == 0)
{
v_x_2391_ = v_tail_2394_;
goto _start;
}
else
{
return v___x_2395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg___boxed(lean_object* v_a_2397_, lean_object* v_x_2398_){
_start:
{
uint8_t v_res_2399_; lean_object* v_r_2400_; 
v_res_2399_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2397_, v_x_2398_);
lean_dec(v_x_2398_);
lean_dec(v_a_2397_);
v_r_2400_ = lean_box(v_res_2399_);
return v_r_2400_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(uint64_t v_x_2401_, lean_object* v_x_2402_){
_start:
{
if (lean_obj_tag(v_x_2402_) == 0)
{
return v_x_2401_;
}
else
{
lean_object* v_head_2403_; lean_object* v_tail_2404_; lean_object* v_intZero_2405_; uint8_t v_isNeg_2406_; 
v_head_2403_ = lean_ctor_get(v_x_2402_, 0);
v_tail_2404_ = lean_ctor_get(v_x_2402_, 1);
v_intZero_2405_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2406_ = lean_int_dec_lt(v_head_2403_, v_intZero_2405_);
if (v_isNeg_2406_ == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; uint64_t v___x_2410_; uint64_t v___x_2411_; 
v_a_2407_ = lean_nat_abs(v_head_2403_);
v___x_2408_ = lean_unsigned_to_nat(2u);
v___x_2409_ = lean_nat_mul(v___x_2408_, v_a_2407_);
lean_dec(v_a_2407_);
v___x_2410_ = lean_uint64_of_nat(v___x_2409_);
lean_dec(v___x_2409_);
v___x_2411_ = lean_uint64_mix_hash(v_x_2401_, v___x_2410_);
v_x_2401_ = v___x_2411_;
v_x_2402_ = v_tail_2404_;
goto _start;
}
else
{
lean_object* v_abs_2413_; lean_object* v_one_2414_; lean_object* v_a_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; uint64_t v___x_2419_; uint64_t v___x_2420_; 
v_abs_2413_ = lean_nat_abs(v_head_2403_);
v_one_2414_ = lean_unsigned_to_nat(1u);
v_a_2415_ = lean_nat_sub(v_abs_2413_, v_one_2414_);
lean_dec(v_abs_2413_);
v___x_2416_ = lean_unsigned_to_nat(2u);
v___x_2417_ = lean_nat_mul(v___x_2416_, v_a_2415_);
lean_dec(v_a_2415_);
v___x_2418_ = lean_nat_add(v___x_2417_, v_one_2414_);
lean_dec(v___x_2417_);
v___x_2419_ = lean_uint64_of_nat(v___x_2418_);
lean_dec(v___x_2418_);
v___x_2420_ = lean_uint64_mix_hash(v_x_2401_, v___x_2419_);
v_x_2401_ = v___x_2420_;
v_x_2402_ = v_tail_2404_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0___boxed(lean_object* v_x_2422_, lean_object* v_x_2423_){
_start:
{
uint64_t v_x_806__boxed_2424_; uint64_t v_res_2425_; lean_object* v_r_2426_; 
v_x_806__boxed_2424_ = lean_unbox_uint64(v_x_2422_);
lean_dec_ref(v_x_2422_);
v_res_2425_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v_x_806__boxed_2424_, v_x_2423_);
lean_dec(v_x_2423_);
v_r_2426_ = lean_box_uint64(v_res_2425_);
return v_r_2426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_2427_, lean_object* v_x_2428_){
_start:
{
if (lean_obj_tag(v_x_2428_) == 0)
{
return v_x_2427_;
}
else
{
lean_object* v_key_2429_; lean_object* v_value_2430_; lean_object* v_tail_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2455_; 
v_key_2429_ = lean_ctor_get(v_x_2428_, 0);
v_value_2430_ = lean_ctor_get(v_x_2428_, 1);
v_tail_2431_ = lean_ctor_get(v_x_2428_, 2);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_x_2428_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2433_ = v_x_2428_;
v_isShared_2434_ = v_isSharedCheck_2455_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_tail_2431_);
lean_inc(v_value_2430_);
lean_inc(v_key_2429_);
lean_dec(v_x_2428_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2455_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; uint64_t v___x_2436_; uint64_t v___x_2437_; uint64_t v___x_2438_; uint64_t v___x_2439_; uint64_t v_fold_2440_; uint64_t v___x_2441_; uint64_t v___x_2442_; uint64_t v___x_2443_; size_t v___x_2444_; size_t v___x_2445_; size_t v___x_2446_; size_t v___x_2447_; size_t v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2435_ = lean_array_get_size(v_x_2427_);
v___x_2436_ = 7ULL;
v___x_2437_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2436_, v_key_2429_);
v___x_2438_ = 32ULL;
v___x_2439_ = lean_uint64_shift_right(v___x_2437_, v___x_2438_);
v_fold_2440_ = lean_uint64_xor(v___x_2437_, v___x_2439_);
v___x_2441_ = 16ULL;
v___x_2442_ = lean_uint64_shift_right(v_fold_2440_, v___x_2441_);
v___x_2443_ = lean_uint64_xor(v_fold_2440_, v___x_2442_);
v___x_2444_ = lean_uint64_to_usize(v___x_2443_);
v___x_2445_ = lean_usize_of_nat(v___x_2435_);
v___x_2446_ = ((size_t)1ULL);
v___x_2447_ = lean_usize_sub(v___x_2445_, v___x_2446_);
v___x_2448_ = lean_usize_land(v___x_2444_, v___x_2447_);
v___x_2449_ = lean_array_uget_borrowed(v_x_2427_, v___x_2448_);
lean_inc(v___x_2449_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 2, v___x_2449_);
v___x_2451_ = v___x_2433_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_key_2429_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_value_2430_);
lean_ctor_set(v_reuseFailAlloc_2454_, 2, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_array_uset(v_x_2427_, v___x_2448_, v___x_2451_);
v_x_2427_ = v___x_2452_;
v_x_2428_ = v_tail_2431_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(lean_object* v_i_2456_, lean_object* v_source_2457_, lean_object* v_target_2458_){
_start:
{
lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2459_ = lean_array_get_size(v_source_2457_);
v___x_2460_ = lean_nat_dec_lt(v_i_2456_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_dec_ref(v_source_2457_);
lean_dec(v_i_2456_);
return v_target_2458_;
}
else
{
lean_object* v_es_2461_; lean_object* v___x_2462_; lean_object* v_source_2463_; lean_object* v_target_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_es_2461_ = lean_array_fget(v_source_2457_, v_i_2456_);
v___x_2462_ = lean_box(0);
v_source_2463_ = lean_array_fset(v_source_2457_, v_i_2456_, v___x_2462_);
v_target_2464_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_target_2458_, v_es_2461_);
v___x_2465_ = lean_unsigned_to_nat(1u);
v___x_2466_ = lean_nat_add(v_i_2456_, v___x_2465_);
lean_dec(v_i_2456_);
v_i_2456_ = v___x_2466_;
v_source_2457_ = v_source_2463_;
v_target_2458_ = v_target_2464_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(lean_object* v_data_2468_){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v_nbuckets_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2469_ = lean_array_get_size(v_data_2468_);
v___x_2470_ = lean_unsigned_to_nat(2u);
v_nbuckets_2471_ = lean_nat_mul(v___x_2469_, v___x_2470_);
v___x_2472_ = lean_unsigned_to_nat(0u);
v___x_2473_ = lean_box(0);
v___x_2474_ = lean_mk_array(v_nbuckets_2471_, v___x_2473_);
v___x_2475_ = lean_array_propagate_mark(v_data_2468_, v___x_2474_);
v___x_2476_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v___x_2472_, v_data_2468_, v___x_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(lean_object* v_m_2477_, lean_object* v_a_2478_, lean_object* v_b_2479_){
_start:
{
lean_object* v_size_2480_; lean_object* v_buckets_2481_; lean_object* v___x_2482_; uint64_t v___x_2483_; uint64_t v___x_2484_; uint64_t v___x_2485_; uint64_t v___x_2486_; uint64_t v_fold_2487_; uint64_t v___x_2488_; uint64_t v___x_2489_; uint64_t v___x_2490_; size_t v___x_2491_; size_t v___x_2492_; size_t v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; lean_object* v_bkt_2496_; uint8_t v___x_2497_; 
v_size_2480_ = lean_ctor_get(v_m_2477_, 0);
v_buckets_2481_ = lean_ctor_get(v_m_2477_, 1);
v___x_2482_ = lean_array_get_size(v_buckets_2481_);
v___x_2483_ = 7ULL;
v___x_2484_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2483_, v_a_2478_);
v___x_2485_ = 32ULL;
v___x_2486_ = lean_uint64_shift_right(v___x_2484_, v___x_2485_);
v_fold_2487_ = lean_uint64_xor(v___x_2484_, v___x_2486_);
v___x_2488_ = 16ULL;
v___x_2489_ = lean_uint64_shift_right(v_fold_2487_, v___x_2488_);
v___x_2490_ = lean_uint64_xor(v_fold_2487_, v___x_2489_);
v___x_2491_ = lean_uint64_to_usize(v___x_2490_);
v___x_2492_ = lean_usize_of_nat(v___x_2482_);
v___x_2493_ = ((size_t)1ULL);
v___x_2494_ = lean_usize_sub(v___x_2492_, v___x_2493_);
v___x_2495_ = lean_usize_land(v___x_2491_, v___x_2494_);
v_bkt_2496_ = lean_array_uget_borrowed(v_buckets_2481_, v___x_2495_);
v___x_2497_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2478_, v_bkt_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2518_; 
lean_inc_ref(v_buckets_2481_);
lean_inc(v_size_2480_);
v_isSharedCheck_2518_ = !lean_is_exclusive(v_m_2477_);
if (v_isSharedCheck_2518_ == 0)
{
lean_object* v_unused_2519_; lean_object* v_unused_2520_; 
v_unused_2519_ = lean_ctor_get(v_m_2477_, 1);
lean_dec(v_unused_2519_);
v_unused_2520_ = lean_ctor_get(v_m_2477_, 0);
lean_dec(v_unused_2520_);
v___x_2499_ = v_m_2477_;
v_isShared_2500_ = v_isSharedCheck_2518_;
goto v_resetjp_2498_;
}
else
{
lean_dec(v_m_2477_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2518_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2501_; lean_object* v_size_x27_2502_; lean_object* v___x_2503_; lean_object* v_buckets_x27_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v___x_2501_ = lean_unsigned_to_nat(1u);
v_size_x27_2502_ = lean_nat_add(v_size_2480_, v___x_2501_);
lean_dec(v_size_2480_);
lean_inc(v_bkt_2496_);
v___x_2503_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2503_, 0, v_a_2478_);
lean_ctor_set(v___x_2503_, 1, v_b_2479_);
lean_ctor_set(v___x_2503_, 2, v_bkt_2496_);
v_buckets_x27_2504_ = lean_array_uset(v_buckets_2481_, v___x_2495_, v___x_2503_);
v___x_2505_ = lean_unsigned_to_nat(4u);
v___x_2506_ = lean_nat_mul(v_size_x27_2502_, v___x_2505_);
v___x_2507_ = lean_unsigned_to_nat(3u);
v___x_2508_ = lean_nat_div(v___x_2506_, v___x_2507_);
lean_dec(v___x_2506_);
v___x_2509_ = lean_array_get_size(v_buckets_x27_2504_);
v___x_2510_ = lean_nat_dec_le(v___x_2508_, v___x_2509_);
lean_dec(v___x_2508_);
if (v___x_2510_ == 0)
{
lean_object* v_val_2511_; lean_object* v___x_2513_; 
v_val_2511_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2504_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 1, v_val_2511_);
lean_ctor_set(v___x_2499_, 0, v_size_x27_2502_);
v___x_2513_ = v___x_2499_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_size_x27_2502_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_val_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
else
{
lean_object* v___x_2516_; 
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 1, v_buckets_x27_2504_);
lean_ctor_set(v___x_2499_, 0, v_size_x27_2502_);
v___x_2516_ = v___x_2499_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_size_x27_2502_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_buckets_x27_2504_);
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
else
{
lean_dec(v_b_2479_);
lean_dec(v_a_2478_);
return v_m_2477_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(lean_object* v_a_2521_, lean_object* v_b_2522_, lean_object* v_x_2523_){
_start:
{
if (lean_obj_tag(v_x_2523_) == 0)
{
lean_dec(v_b_2522_);
lean_dec(v_a_2521_);
return v_x_2523_;
}
else
{
lean_object* v_key_2524_; lean_object* v_value_2525_; lean_object* v_tail_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2538_; 
v_key_2524_ = lean_ctor_get(v_x_2523_, 0);
v_value_2525_ = lean_ctor_get(v_x_2523_, 1);
v_tail_2526_ = lean_ctor_get(v_x_2523_, 2);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_x_2523_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2528_ = v_x_2523_;
v_isShared_2529_ = v_isSharedCheck_2538_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_tail_2526_);
lean_inc(v_value_2525_);
lean_inc(v_key_2524_);
lean_dec(v_x_2523_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2538_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
uint8_t v___x_2530_; 
v___x_2530_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2524_, v_a_2521_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2531_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2521_, v_b_2522_, v_tail_2526_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 2, v___x_2531_);
v___x_2533_ = v___x_2528_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_key_2524_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_value_2525_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
else
{
lean_object* v___x_2536_; 
lean_dec(v_value_2525_);
lean_dec(v_key_2524_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v_b_2522_);
lean_ctor_set(v___x_2528_, 0, v_a_2521_);
v___x_2536_ = v___x_2528_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2521_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_b_2522_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_tail_2526_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(lean_object* v_m_2539_, lean_object* v_a_2540_, lean_object* v_b_2541_){
_start:
{
lean_object* v_size_2542_; lean_object* v_buckets_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2587_; 
v_size_2542_ = lean_ctor_get(v_m_2539_, 0);
v_buckets_2543_ = lean_ctor_get(v_m_2539_, 1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_m_2539_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2545_ = v_m_2539_;
v_isShared_2546_ = v_isSharedCheck_2587_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_buckets_2543_);
lean_inc(v_size_2542_);
lean_dec(v_m_2539_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2587_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; uint64_t v___x_2548_; uint64_t v___x_2549_; uint64_t v___x_2550_; uint64_t v___x_2551_; uint64_t v_fold_2552_; uint64_t v___x_2553_; uint64_t v___x_2554_; uint64_t v___x_2555_; size_t v___x_2556_; size_t v___x_2557_; size_t v___x_2558_; size_t v___x_2559_; size_t v___x_2560_; lean_object* v_bkt_2561_; uint8_t v___x_2562_; 
v___x_2547_ = lean_array_get_size(v_buckets_2543_);
v___x_2548_ = 7ULL;
v___x_2549_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2548_, v_a_2540_);
v___x_2550_ = 32ULL;
v___x_2551_ = lean_uint64_shift_right(v___x_2549_, v___x_2550_);
v_fold_2552_ = lean_uint64_xor(v___x_2549_, v___x_2551_);
v___x_2553_ = 16ULL;
v___x_2554_ = lean_uint64_shift_right(v_fold_2552_, v___x_2553_);
v___x_2555_ = lean_uint64_xor(v_fold_2552_, v___x_2554_);
v___x_2556_ = lean_uint64_to_usize(v___x_2555_);
v___x_2557_ = lean_usize_of_nat(v___x_2547_);
v___x_2558_ = ((size_t)1ULL);
v___x_2559_ = lean_usize_sub(v___x_2557_, v___x_2558_);
v___x_2560_ = lean_usize_land(v___x_2556_, v___x_2559_);
v_bkt_2561_ = lean_array_uget_borrowed(v_buckets_2543_, v___x_2560_);
v___x_2562_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2540_, v_bkt_2561_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; lean_object* v_size_x27_2564_; lean_object* v___x_2565_; lean_object* v_buckets_x27_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2563_ = lean_unsigned_to_nat(1u);
v_size_x27_2564_ = lean_nat_add(v_size_2542_, v___x_2563_);
lean_dec(v_size_2542_);
lean_inc(v_bkt_2561_);
v___x_2565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2565_, 0, v_a_2540_);
lean_ctor_set(v___x_2565_, 1, v_b_2541_);
lean_ctor_set(v___x_2565_, 2, v_bkt_2561_);
v_buckets_x27_2566_ = lean_array_uset(v_buckets_2543_, v___x_2560_, v___x_2565_);
v___x_2567_ = lean_unsigned_to_nat(4u);
v___x_2568_ = lean_nat_mul(v_size_x27_2564_, v___x_2567_);
v___x_2569_ = lean_unsigned_to_nat(3u);
v___x_2570_ = lean_nat_div(v___x_2568_, v___x_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_array_get_size(v_buckets_x27_2566_);
v___x_2572_ = lean_nat_dec_le(v___x_2570_, v___x_2571_);
lean_dec(v___x_2570_);
if (v___x_2572_ == 0)
{
lean_object* v_val_2573_; lean_object* v___x_2575_; 
v_val_2573_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2566_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 1, v_val_2573_);
lean_ctor_set(v___x_2545_, 0, v_size_x27_2564_);
v___x_2575_ = v___x_2545_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_size_x27_2564_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_val_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
else
{
lean_object* v___x_2578_; 
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 1, v_buckets_x27_2566_);
lean_ctor_set(v___x_2545_, 0, v_size_x27_2564_);
v___x_2578_ = v___x_2545_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_size_x27_2564_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_buckets_x27_2566_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
else
{
lean_object* v___x_2580_; lean_object* v_buckets_x27_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2585_; 
lean_inc(v_bkt_2561_);
v___x_2580_ = lean_box(0);
v_buckets_x27_2581_ = lean_array_uset(v_buckets_2543_, v___x_2560_, v___x_2580_);
v___x_2582_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2540_, v_b_2541_, v_bkt_2561_);
v___x_2583_ = lean_array_uset(v_buckets_x27_2581_, v___x_2560_, v___x_2582_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 1, v___x_2583_);
v___x_2585_ = v___x_2545_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_size_2542_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(lean_object* v_p_2588_, lean_object* v_x_2589_){
_start:
{
lean_object* v_coeffs_2590_; lean_object* v_constraint_2591_; lean_object* v_justification_2592_; uint8_t v___x_2593_; 
v_coeffs_2590_ = lean_ctor_get(v_x_2589_, 0);
lean_inc(v_coeffs_2590_);
v_constraint_2591_ = lean_ctor_get(v_x_2589_, 1);
lean_inc_ref(v_constraint_2591_);
v_justification_2592_ = lean_ctor_get(v_x_2589_, 2);
v___x_2593_ = l_Lean_Omega_Constraint_isImpossible(v_constraint_2591_);
if (v___x_2593_ == 0)
{
lean_object* v_assumptions_2594_; lean_object* v_numVars_2595_; lean_object* v_constraints_2596_; lean_object* v_equalities_2597_; lean_object* v_eliminations_2598_; uint8_t v_possible_2599_; lean_object* v_proveFalse_x3f_2600_; lean_object* v_explanation_x3f_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2619_; 
v_assumptions_2594_ = lean_ctor_get(v_p_2588_, 0);
v_numVars_2595_ = lean_ctor_get(v_p_2588_, 1);
v_constraints_2596_ = lean_ctor_get(v_p_2588_, 2);
v_equalities_2597_ = lean_ctor_get(v_p_2588_, 3);
v_eliminations_2598_ = lean_ctor_get(v_p_2588_, 4);
v_possible_2599_ = lean_ctor_get_uint8(v_p_2588_, sizeof(void*)*7);
v_proveFalse_x3f_2600_ = lean_ctor_get(v_p_2588_, 5);
v_explanation_x3f_2601_ = lean_ctor_get(v_p_2588_, 6);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_p_2588_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2603_ = v_p_2588_;
v_isShared_2604_ = v_isSharedCheck_2619_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_explanation_x3f_2601_);
lean_inc(v_proveFalse_x3f_2600_);
lean_inc(v_eliminations_2598_);
lean_inc(v_equalities_2597_);
lean_inc(v_constraints_2596_);
lean_inc(v_numVars_2595_);
lean_inc(v_assumptions_2594_);
lean_dec(v_p_2588_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2619_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___y_2606_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = l_List_lengthTR___redArg(v_coeffs_2590_);
v___x_2618_ = lean_nat_dec_le(v_numVars_2595_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_dec(v___x_2617_);
v___y_2606_ = v_numVars_2595_;
goto v___jp_2605_;
}
else
{
lean_dec(v_numVars_2595_);
v___y_2606_ = v___x_2617_;
goto v___jp_2605_;
}
v___jp_2605_:
{
lean_object* v___x_2607_; uint8_t v___x_2608_; 
lean_inc(v_coeffs_2590_);
v___x_2607_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_constraints_2596_, v_coeffs_2590_, v_x_2589_);
v___x_2608_ = l_Lean_Omega_Constraint_isExact(v_constraint_2591_);
lean_dec_ref(v_constraint_2591_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2610_; 
lean_dec(v_coeffs_2590_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 2, v___x_2607_);
lean_ctor_set(v___x_2603_, 1, v___y_2606_);
v___x_2610_ = v___x_2603_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_assumptions_2594_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v___y_2606_);
lean_ctor_set(v_reuseFailAlloc_2611_, 2, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2611_, 3, v_equalities_2597_);
lean_ctor_set(v_reuseFailAlloc_2611_, 4, v_eliminations_2598_);
lean_ctor_set(v_reuseFailAlloc_2611_, 5, v_proveFalse_x3f_2600_);
lean_ctor_set(v_reuseFailAlloc_2611_, 6, v_explanation_x3f_2601_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*7, v_possible_2599_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
else
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2612_ = lean_box(0);
v___x_2613_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_equalities_2597_, v_coeffs_2590_, v___x_2612_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 3, v___x_2613_);
lean_ctor_set(v___x_2603_, 2, v___x_2607_);
lean_ctor_set(v___x_2603_, 1, v___y_2606_);
v___x_2615_ = v___x_2603_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_assumptions_2594_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v___y_2606_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2616_, 3, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2616_, 4, v_eliminations_2598_);
lean_ctor_set(v_reuseFailAlloc_2616_, 5, v_proveFalse_x3f_2600_);
lean_ctor_set(v_reuseFailAlloc_2616_, 6, v_explanation_x3f_2601_);
lean_ctor_set_uint8(v_reuseFailAlloc_2616_, sizeof(void*)*7, v_possible_2599_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
else
{
lean_object* v_assumptions_2620_; lean_object* v_numVars_2621_; lean_object* v_constraints_2622_; lean_object* v_equalities_2623_; lean_object* v_eliminations_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2636_; 
lean_inc_ref(v_justification_2592_);
lean_dec_ref(v_x_2589_);
v_assumptions_2620_ = lean_ctor_get(v_p_2588_, 0);
v_numVars_2621_ = lean_ctor_get(v_p_2588_, 1);
v_constraints_2622_ = lean_ctor_get(v_p_2588_, 2);
v_equalities_2623_ = lean_ctor_get(v_p_2588_, 3);
v_eliminations_2624_ = lean_ctor_get(v_p_2588_, 4);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_p_2588_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; lean_object* v_unused_2638_; 
v_unused_2637_ = lean_ctor_get(v_p_2588_, 6);
lean_dec(v_unused_2637_);
v_unused_2638_ = lean_ctor_get(v_p_2588_, 5);
lean_dec(v_unused_2638_);
v___x_2626_ = v_p_2588_;
v_isShared_2627_ = v_isSharedCheck_2636_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_eliminations_2624_);
lean_inc(v_equalities_2623_);
lean_inc(v_constraints_2622_);
lean_inc(v_numVars_2621_);
lean_inc(v_assumptions_2620_);
lean_dec(v_p_2588_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2636_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___f_2628_; uint8_t v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
lean_inc_ref(v_justification_2592_);
lean_inc(v_coeffs_2590_);
lean_inc_ref(v_constraint_2591_);
v___f_2628_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0), 4, 3);
lean_closure_set(v___f_2628_, 0, v_constraint_2591_);
lean_closure_set(v___f_2628_, 1, v_coeffs_2590_);
lean_closure_set(v___f_2628_, 2, v_justification_2592_);
v___x_2629_ = 0;
lean_inc_ref(v_assumptions_2620_);
v___x_2630_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed), 14, 4);
lean_closure_set(v___x_2630_, 0, v_constraint_2591_);
lean_closure_set(v___x_2630_, 1, v_coeffs_2590_);
lean_closure_set(v___x_2630_, 2, v_justification_2592_);
lean_closure_set(v___x_2630_, 3, v_assumptions_2620_);
v___x_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
v___x_2632_ = lean_mk_thunk(v___f_2628_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 6, v___x_2632_);
lean_ctor_set(v___x_2626_, 5, v___x_2631_);
v___x_2634_ = v___x_2626_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_assumptions_2620_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_numVars_2621_);
lean_ctor_set(v_reuseFailAlloc_2635_, 2, v_constraints_2622_);
lean_ctor_set(v_reuseFailAlloc_2635_, 3, v_equalities_2623_);
lean_ctor_set(v_reuseFailAlloc_2635_, 4, v_eliminations_2624_);
lean_ctor_set(v_reuseFailAlloc_2635_, 5, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2635_, 6, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_ctor_set_uint8(v___x_2634_, sizeof(void*)*7, v___x_2629_);
return v___x_2634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0(lean_object* v_00_u03b2_2639_, lean_object* v_m_2640_, lean_object* v_a_2641_, lean_object* v_b_2642_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_m_2640_, v_a_2641_, v_b_2642_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1(lean_object* v_00_u03b2_2644_, lean_object* v_m_2645_, lean_object* v_a_2646_, lean_object* v_b_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_m_2645_, v_a_2646_, v_b_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_object* v_00_u03b2_2649_, lean_object* v_a_2650_, lean_object* v_x_2651_){
_start:
{
uint8_t v___x_2652_; 
v___x_2652_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2650_, v_x_2651_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2653_, lean_object* v_a_2654_, lean_object* v_x_2655_){
_start:
{
uint8_t v_res_2656_; lean_object* v_r_2657_; 
v_res_2656_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(v_00_u03b2_2653_, v_a_2654_, v_x_2655_);
lean_dec(v_x_2655_);
lean_dec(v_a_2654_);
v_r_2657_ = lean_box(v_res_2656_);
return v_r_2657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2(lean_object* v_00_u03b2_2658_, lean_object* v_data_2659_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_data_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3(lean_object* v_00_u03b2_2661_, lean_object* v_a_2662_, lean_object* v_b_2663_, lean_object* v_x_2664_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2662_, v_b_2663_, v_x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2666_, lean_object* v_i_2667_, lean_object* v_source_2668_, lean_object* v_target_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v_i_2667_, v_source_2668_, v_target_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2671_, lean_object* v_x_2672_, lean_object* v_x_2673_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_x_2672_, v_x_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(lean_object* v_a_2675_, lean_object* v_x_2676_){
_start:
{
if (lean_obj_tag(v_x_2676_) == 0)
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_box(0);
return v___x_2677_;
}
else
{
lean_object* v_key_2678_; lean_object* v_value_2679_; lean_object* v_tail_2680_; uint8_t v___x_2681_; 
v_key_2678_ = lean_ctor_get(v_x_2676_, 0);
v_value_2679_ = lean_ctor_get(v_x_2676_, 1);
v_tail_2680_ = lean_ctor_get(v_x_2676_, 2);
v___x_2681_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2678_, v_a_2675_);
if (v___x_2681_ == 0)
{
v_x_2676_ = v_tail_2680_;
goto _start;
}
else
{
lean_object* v___x_2683_; 
lean_inc(v_value_2679_);
v___x_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2683_, 0, v_value_2679_);
return v___x_2683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg___boxed(lean_object* v_a_2684_, lean_object* v_x_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2684_, v_x_2685_);
lean_dec(v_x_2685_);
lean_dec(v_a_2684_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(lean_object* v_m_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v_buckets_2689_; lean_object* v___x_2690_; uint64_t v___x_2691_; uint64_t v___x_2692_; uint64_t v___x_2693_; uint64_t v___x_2694_; uint64_t v_fold_2695_; uint64_t v___x_2696_; uint64_t v___x_2697_; uint64_t v___x_2698_; size_t v___x_2699_; size_t v___x_2700_; size_t v___x_2701_; size_t v___x_2702_; size_t v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_buckets_2689_ = lean_ctor_get(v_m_2687_, 1);
v___x_2690_ = lean_array_get_size(v_buckets_2689_);
v___x_2691_ = 7ULL;
v___x_2692_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2691_, v_a_2688_);
v___x_2693_ = 32ULL;
v___x_2694_ = lean_uint64_shift_right(v___x_2692_, v___x_2693_);
v_fold_2695_ = lean_uint64_xor(v___x_2692_, v___x_2694_);
v___x_2696_ = 16ULL;
v___x_2697_ = lean_uint64_shift_right(v_fold_2695_, v___x_2696_);
v___x_2698_ = lean_uint64_xor(v_fold_2695_, v___x_2697_);
v___x_2699_ = lean_uint64_to_usize(v___x_2698_);
v___x_2700_ = lean_usize_of_nat(v___x_2690_);
v___x_2701_ = ((size_t)1ULL);
v___x_2702_ = lean_usize_sub(v___x_2700_, v___x_2701_);
v___x_2703_ = lean_usize_land(v___x_2699_, v___x_2702_);
v___x_2704_ = lean_array_uget_borrowed(v_buckets_2689_, v___x_2703_);
v___x_2705_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2688_, v___x_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg___boxed(lean_object* v_m_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2706_, v_a_2707_);
lean_dec(v_a_2707_);
lean_dec_ref(v_m_2706_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addConstraint(lean_object* v_p_2709_, lean_object* v_x_2710_){
_start:
{
uint8_t v_possible_2711_; 
v_possible_2711_ = lean_ctor_get_uint8(v_p_2709_, sizeof(void*)*7);
if (v_possible_2711_ == 0)
{
lean_dec_ref(v_x_2710_);
return v_p_2709_;
}
else
{
lean_object* v_coeffs_2712_; lean_object* v_constraint_2713_; lean_object* v_justification_2714_; lean_object* v_constraints_2715_; lean_object* v___x_2716_; 
v_coeffs_2712_ = lean_ctor_get(v_x_2710_, 0);
v_constraint_2713_ = lean_ctor_get(v_x_2710_, 1);
v_justification_2714_ = lean_ctor_get(v_x_2710_, 2);
v_constraints_2715_ = lean_ctor_get(v_p_2709_, 2);
v___x_2716_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2715_, v_coeffs_2712_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_lowerBound_2717_; 
v_lowerBound_2717_ = lean_ctor_get(v_constraint_2713_, 0);
if (lean_obj_tag(v_lowerBound_2717_) == 0)
{
lean_object* v_upperBound_2718_; 
v_upperBound_2718_ = lean_ctor_get(v_constraint_2713_, 1);
if (lean_obj_tag(v_upperBound_2718_) == 0)
{
lean_dec_ref(v_x_2710_);
return v_p_2709_;
}
else
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2709_, v_x_2710_);
return v___x_2719_;
}
}
else
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2709_, v_x_2710_);
return v___x_2720_;
}
}
else
{
lean_object* v_val_2721_; lean_object* v_coeffs_2722_; lean_object* v_constraint_2723_; lean_object* v_justification_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2739_; 
v_val_2721_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_val_2721_);
lean_dec_ref_known(v___x_2716_, 1);
v_coeffs_2722_ = lean_ctor_get(v_val_2721_, 0);
v_constraint_2723_ = lean_ctor_get(v_val_2721_, 1);
v_justification_2724_ = lean_ctor_get(v_val_2721_, 2);
v_isSharedCheck_2739_ = !lean_is_exclusive(v_val_2721_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2726_ = v_val_2721_;
v_isShared_2727_ = v_isSharedCheck_2739_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_justification_2724_);
lean_inc(v_constraint_2723_);
lean_inc(v_coeffs_2722_);
lean_dec(v_val_2721_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2739_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2728_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc(v_coeffs_2712_);
v___x_2729_ = l_instDecidableEqList___redArg(v___x_2728_, v_coeffs_2712_, v_coeffs_2722_);
if (v___x_2729_ == 0)
{
lean_del_object(v___x_2726_);
lean_dec_ref(v_justification_2724_);
lean_dec_ref(v_constraint_2723_);
lean_dec_ref(v_x_2710_);
return v_p_2709_;
}
else
{
lean_object* v_r_2730_; uint8_t v___x_2731_; 
lean_inc_ref_n(v_constraint_2723_, 2);
lean_inc_ref(v_constraint_2713_);
v_r_2730_ = l_Lean_Omega_Constraint_combine(v_constraint_2713_, v_constraint_2723_);
lean_inc_ref(v_r_2730_);
v___x_2731_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2730_, v_constraint_2723_);
if (v___x_2731_ == 0)
{
uint8_t v___x_2732_; 
lean_inc_ref(v_constraint_2713_);
lean_inc_ref(v_r_2730_);
v___x_2732_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2730_, v_constraint_2713_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; lean_object* v___x_2735_; 
lean_inc_ref(v_justification_2714_);
lean_inc_ref(v_constraint_2713_);
lean_inc_n(v_coeffs_2712_, 2);
lean_dec_ref(v_x_2710_);
v___x_2733_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_2733_, 0, v_constraint_2713_);
lean_ctor_set(v___x_2733_, 1, v_constraint_2723_);
lean_ctor_set(v___x_2733_, 2, v_coeffs_2712_);
lean_ctor_set(v___x_2733_, 3, v_justification_2714_);
lean_ctor_set(v___x_2733_, 4, v_justification_2724_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 2, v___x_2733_);
lean_ctor_set(v___x_2726_, 1, v_r_2730_);
lean_ctor_set(v___x_2726_, 0, v_coeffs_2712_);
v___x_2735_ = v___x_2726_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_coeffs_2712_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_r_2730_);
lean_ctor_set(v_reuseFailAlloc_2737_, 2, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2709_, v___x_2735_);
return v___x_2736_;
}
}
else
{
lean_object* v___x_2738_; 
lean_dec_ref(v_r_2730_);
lean_del_object(v___x_2726_);
lean_dec_ref(v_justification_2724_);
lean_dec_ref(v_constraint_2723_);
v___x_2738_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2709_, v_x_2710_);
return v___x_2738_;
}
}
else
{
lean_dec_ref(v_r_2730_);
lean_del_object(v___x_2726_);
lean_dec_ref(v_justification_2724_);
lean_dec_ref(v_constraint_2723_);
lean_dec_ref(v_x_2710_);
return v_p_2709_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(lean_object* v_00_u03b2_2740_, lean_object* v_m_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2741_, v_a_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___boxed(lean_object* v_00_u03b2_2744_, lean_object* v_m_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(v_00_u03b2_2744_, v_m_2745_, v_a_2746_);
lean_dec(v_a_2746_);
lean_dec_ref(v_m_2745_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(lean_object* v_00_u03b2_2748_, lean_object* v_a_2749_, lean_object* v_x_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2749_, v_x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2752_, lean_object* v_a_2753_, lean_object* v_x_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(v_00_u03b2_2752_, v_a_2753_, v_x_2754_);
lean_dec(v_x_2754_);
lean_dec(v_a_2753_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(lean_object* v_x_2756_, lean_object* v_x_2757_){
_start:
{
if (lean_obj_tag(v_x_2757_) == 0)
{
return v_x_2756_;
}
else
{
if (lean_obj_tag(v_x_2756_) == 0)
{
lean_object* v_key_2758_; lean_object* v_tail_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v_key_2758_ = lean_ctor_get(v_x_2757_, 0);
lean_inc_n(v_key_2758_, 2);
v_tail_2759_ = lean_ctor_get(v_x_2757_, 2);
lean_inc(v_tail_2759_);
lean_dec_ref_known(v_x_2757_, 3);
v___x_2760_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2758_);
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v_key_2758_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
v_x_2756_ = v___x_2762_;
v_x_2757_ = v_tail_2759_;
goto _start;
}
else
{
lean_object* v_val_2764_; lean_object* v_key_2765_; lean_object* v_tail_2766_; lean_object* v_fst_2767_; lean_object* v_snd_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2789_; 
v_val_2764_ = lean_ctor_get(v_x_2756_, 0);
lean_inc(v_val_2764_);
v_key_2765_ = lean_ctor_get(v_x_2757_, 0);
lean_inc(v_key_2765_);
v_tail_2766_ = lean_ctor_get(v_x_2757_, 2);
lean_inc(v_tail_2766_);
lean_dec_ref_known(v_x_2757_, 3);
v_fst_2767_ = lean_ctor_get(v_val_2764_, 0);
v_snd_2768_ = lean_ctor_get(v_val_2764_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_val_2764_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2770_ = v_val_2764_;
v_isShared_2771_ = v_isSharedCheck_2789_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_snd_2768_);
lean_inc(v_fst_2767_);
lean_dec(v_val_2764_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2789_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2772_ = lean_unsigned_to_nat(2u);
v___x_2773_ = lean_nat_dec_le(v___x_2772_, v_snd_2768_);
if (v___x_2773_ == 0)
{
lean_del_object(v___x_2770_);
lean_dec(v_snd_2768_);
lean_dec(v_fst_2767_);
lean_dec(v_key_2765_);
v_x_2757_ = v_tail_2766_;
goto _start;
}
else
{
lean_object* v_m_x27_2775_; uint8_t v___x_2782_; 
lean_inc(v_key_2765_);
v_m_x27_2775_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2765_);
v___x_2782_ = lean_nat_dec_lt(v_m_x27_2775_, v_snd_2768_);
if (v___x_2782_ == 0)
{
uint8_t v___x_2783_; 
v___x_2783_ = lean_nat_dec_eq(v_m_x27_2775_, v_snd_2768_);
lean_dec(v_snd_2768_);
if (v___x_2783_ == 0)
{
lean_dec(v_m_x27_2775_);
lean_del_object(v___x_2770_);
lean_dec(v_fst_2767_);
lean_dec(v_key_2765_);
v_x_2757_ = v_tail_2766_;
goto _start;
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
lean_inc(v_key_2765_);
v___x_2785_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_key_2765_);
v___x_2786_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_fst_2767_);
v___x_2787_ = lean_nat_dec_lt(v___x_2785_, v___x_2786_);
lean_dec(v___x_2786_);
lean_dec(v___x_2785_);
if (v___x_2787_ == 0)
{
lean_dec(v_m_x27_2775_);
lean_del_object(v___x_2770_);
lean_dec(v_key_2765_);
v_x_2757_ = v_tail_2766_;
goto _start;
}
else
{
lean_dec_ref_known(v_x_2756_, 1);
goto v___jp_2776_;
}
}
}
else
{
lean_dec(v_snd_2768_);
lean_dec(v_fst_2767_);
lean_dec_ref_known(v_x_2756_, 1);
goto v___jp_2776_;
}
v___jp_2776_:
{
lean_object* v___x_2778_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 1, v_m_x27_2775_);
lean_ctor_set(v___x_2770_, 0, v_key_2765_);
v___x_2778_ = v___x_2770_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_key_2765_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_m_x27_2775_);
v___x_2778_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
v_x_2756_ = v___x_2779_;
v_x_2757_ = v_tail_2766_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(lean_object* v_as_2790_, size_t v_i_2791_, size_t v_stop_2792_, lean_object* v_b_2793_){
_start:
{
uint8_t v___x_2794_; 
v___x_2794_ = lean_usize_dec_eq(v_i_2791_, v_stop_2792_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; lean_object* v___x_2796_; size_t v___x_2797_; size_t v___x_2798_; 
v___x_2795_ = lean_array_uget_borrowed(v_as_2790_, v_i_2791_);
lean_inc(v___x_2795_);
v___x_2796_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(v_b_2793_, v___x_2795_);
v___x_2797_ = ((size_t)1ULL);
v___x_2798_ = lean_usize_add(v_i_2791_, v___x_2797_);
v_i_2791_ = v___x_2798_;
v_b_2793_ = v___x_2796_;
goto _start;
}
else
{
return v_b_2793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1___boxed(lean_object* v_as_2800_, lean_object* v_i_2801_, lean_object* v_stop_2802_, lean_object* v_b_2803_){
_start:
{
size_t v_i_boxed_2804_; size_t v_stop_boxed_2805_; lean_object* v_res_2806_; 
v_i_boxed_2804_ = lean_unbox_usize(v_i_2801_);
lean_dec(v_i_2801_);
v_stop_boxed_2805_ = lean_unbox_usize(v_stop_2802_);
lean_dec(v_stop_2802_);
v_res_2806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_as_2800_, v_i_boxed_2804_, v_stop_boxed_2805_, v_b_2803_);
lean_dec_ref(v_as_2800_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality(lean_object* v_p_2807_){
_start:
{
lean_object* v_equalities_2808_; lean_object* v_buckets_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v_equalities_2808_ = lean_ctor_get(v_p_2807_, 3);
v_buckets_2809_ = lean_ctor_get(v_equalities_2808_, 1);
v___x_2810_ = lean_box(0);
v___x_2811_ = lean_unsigned_to_nat(0u);
v___x_2812_ = lean_array_get_size(v_buckets_2809_);
v___x_2813_ = lean_nat_dec_lt(v___x_2811_, v___x_2812_);
if (v___x_2813_ == 0)
{
return v___x_2810_;
}
else
{
size_t v___x_2814_; size_t v___x_2815_; lean_object* v___x_2816_; 
v___x_2814_ = ((size_t)0ULL);
v___x_2815_ = lean_usize_of_nat(v___x_2812_);
v___x_2816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2809_, v___x_2814_, v___x_2815_, v___x_2810_);
return v___x_2816_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(lean_object* v___y_2868_, lean_object* v_sign_2869_, lean_object* v_val_2870_, lean_object* v_x_2871_, lean_object* v_x_2872_){
_start:
{
if (lean_obj_tag(v_x_2872_) == 0)
{
lean_dec_ref(v_val_2870_);
lean_dec(v___y_2868_);
return v_x_2871_;
}
else
{
lean_object* v_key_2873_; lean_object* v_value_2874_; lean_object* v_tail_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; 
v_key_2873_ = lean_ctor_get(v_x_2872_, 0);
lean_inc(v_key_2873_);
v_value_2874_ = lean_ctor_get(v_x_2872_, 1);
lean_inc(v_value_2874_);
v_tail_2875_ = lean_ctor_get(v_x_2872_, 2);
lean_inc(v_tail_2875_);
lean_dec_ref_known(v_x_2872_, 3);
lean_inc(v___y_2868_);
v___x_2876_ = l_Lean_Omega_IntList_get(v_key_2873_, v___y_2868_);
lean_dec(v_key_2873_);
v___x_2877_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2878_ = lean_int_dec_eq(v___x_2876_, v___x_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v_k_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2879_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2880_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2881_ = lean_int_mul(v___x_2880_, v_sign_2869_);
v_k_2882_ = lean_int_mul(v___x_2881_, v___x_2876_);
lean_dec(v___x_2876_);
lean_dec(v___x_2881_);
lean_inc_ref(v_val_2870_);
v___x_2883_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_k_2882_, v_val_2870_, v___x_2879_, v_value_2874_);
v___x_2884_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_2883_);
v___x_2885_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2871_, v___x_2884_);
v_x_2871_ = v___x_2885_;
v_x_2872_ = v_tail_2875_;
goto _start;
}
else
{
lean_object* v___x_2887_; 
lean_dec(v___x_2876_);
v___x_2887_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_x_2871_, v_value_2874_);
v_x_2871_ = v___x_2887_;
v_x_2872_ = v_tail_2875_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0___boxed(lean_object* v___y_2889_, lean_object* v_sign_2890_, lean_object* v_val_2891_, lean_object* v_x_2892_, lean_object* v_x_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2889_, v_sign_2890_, v_val_2891_, v_x_2892_, v_x_2893_);
lean_dec(v_sign_2890_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object* v___y_2895_, lean_object* v_sign_2896_, lean_object* v_val_2897_, lean_object* v_as_2898_, size_t v_i_2899_, size_t v_stop_2900_, lean_object* v_b_2901_){
_start:
{
uint8_t v___x_2902_; 
v___x_2902_ = lean_usize_dec_eq(v_i_2899_, v_stop_2900_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; lean_object* v___x_2904_; size_t v___x_2905_; size_t v___x_2906_; 
v___x_2903_ = lean_array_uget_borrowed(v_as_2898_, v_i_2899_);
lean_inc(v___x_2903_);
lean_inc_ref(v_val_2897_);
lean_inc(v___y_2895_);
v___x_2904_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__0(v___y_2895_, v_sign_2896_, v_val_2897_, v_b_2901_, v___x_2903_);
v___x_2905_ = ((size_t)1ULL);
v___x_2906_ = lean_usize_add(v_i_2899_, v___x_2905_);
v_i_2899_ = v___x_2906_;
v_b_2901_ = v___x_2904_;
goto _start;
}
else
{
lean_dec_ref(v_val_2897_);
lean_dec(v___y_2895_);
return v_b_2901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1___boxed(lean_object* v___y_2908_, lean_object* v_sign_2909_, lean_object* v_val_2910_, lean_object* v_as_2911_, lean_object* v_i_2912_, lean_object* v_stop_2913_, lean_object* v_b_2914_){
_start:
{
size_t v_i_boxed_2915_; size_t v_stop_boxed_2916_; lean_object* v_res_2917_; 
v_i_boxed_2915_ = lean_unbox_usize(v_i_2912_);
lean_dec(v_i_2912_);
v_stop_boxed_2916_ = lean_unbox_usize(v_stop_2913_);
lean_dec(v_stop_2913_);
v_res_2917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2908_, v_sign_2909_, v_val_2910_, v_as_2911_, v_i_boxed_2915_, v_stop_boxed_2916_, v_b_2914_);
lean_dec_ref(v_as_2911_);
lean_dec(v_sign_2909_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(lean_object* v_a_2918_, lean_object* v_a_2919_){
_start:
{
if (lean_obj_tag(v_a_2918_) == 0)
{
lean_object* v___x_2920_; 
lean_dec(v_a_2919_);
v___x_2920_ = lean_box(0);
return v___x_2920_;
}
else
{
lean_object* v_head_2921_; lean_object* v_tail_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v_head_2921_ = lean_ctor_get(v_a_2918_, 0);
v_tail_2922_ = lean_ctor_get(v_a_2918_, 1);
v___x_2923_ = lean_nat_abs(v_head_2921_);
v___x_2924_ = lean_unsigned_to_nat(1u);
v___x_2925_ = lean_nat_dec_eq(v___x_2923_, v___x_2924_);
lean_dec(v___x_2923_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_nat_add(v_a_2919_, v___x_2924_);
lean_dec(v_a_2919_);
v_a_2918_ = v_tail_2922_;
v_a_2919_ = v___x_2926_;
goto _start;
}
else
{
lean_object* v___x_2928_; 
v___x_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2928_, 0, v_a_2919_);
return v___x_2928_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2___boxed(lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(v_a_2929_, v_a_2930_);
lean_dec(v_a_2929_);
return v_res_2931_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1(void){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2933_ = lean_box(0);
v___x_2934_ = lean_unsigned_to_nat(16u);
v___x_2935_ = lean_mk_array(v___x_2934_, v___x_2933_);
return v___x_2935_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1);
v___x_2937_ = lean_unsigned_to_nat(0u);
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___x_2936_);
return v___x_2938_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3(void){
_start:
{
lean_object* v___f_2939_; lean_object* v___x_2940_; 
v___f_2939_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0));
v___x_2940_ = lean_mk_thunk(v___f_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(lean_object* v_p_2941_, lean_object* v_c_2942_){
_start:
{
lean_object* v___y_2944_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_unsigned_to_nat(0u);
v___x_2988_ = l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(v_c_2942_, v___x_2987_);
if (lean_obj_tag(v___x_2988_) == 0)
{
v___y_2944_ = v___x_2987_;
goto v___jp_2943_;
}
else
{
lean_object* v_val_2989_; 
v_val_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_val_2989_);
lean_dec_ref_known(v___x_2988_, 1);
v___y_2944_ = v_val_2989_;
goto v___jp_2943_;
}
v___jp_2943_:
{
lean_object* v_assumptions_2945_; lean_object* v_constraints_2946_; lean_object* v_eliminations_2947_; lean_object* v___x_2948_; 
v_assumptions_2945_ = lean_ctor_get(v_p_2941_, 0);
v_constraints_2946_ = lean_ctor_get(v_p_2941_, 2);
lean_inc_ref(v_constraints_2946_);
v_eliminations_2947_ = lean_ctor_get(v_p_2941_, 4);
v___x_2948_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2946_, v_c_2942_);
if (lean_obj_tag(v___x_2948_) == 1)
{
lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2979_; 
lean_inc(v_eliminations_2947_);
lean_inc_ref(v_assumptions_2945_);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_p_2941_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; lean_object* v_unused_2981_; lean_object* v_unused_2982_; lean_object* v_unused_2983_; lean_object* v_unused_2984_; lean_object* v_unused_2985_; lean_object* v_unused_2986_; 
v_unused_2980_ = lean_ctor_get(v_p_2941_, 6);
lean_dec(v_unused_2980_);
v_unused_2981_ = lean_ctor_get(v_p_2941_, 5);
lean_dec(v_unused_2981_);
v_unused_2982_ = lean_ctor_get(v_p_2941_, 4);
lean_dec(v_unused_2982_);
v_unused_2983_ = lean_ctor_get(v_p_2941_, 3);
lean_dec(v_unused_2983_);
v_unused_2984_ = lean_ctor_get(v_p_2941_, 2);
lean_dec(v_unused_2984_);
v_unused_2985_ = lean_ctor_get(v_p_2941_, 1);
lean_dec(v_unused_2985_);
v_unused_2986_ = lean_ctor_get(v_p_2941_, 0);
lean_dec(v_unused_2986_);
v___x_2950_ = v_p_2941_;
v_isShared_2951_ = v_isSharedCheck_2979_;
goto v_resetjp_2949_;
}
else
{
lean_dec(v_p_2941_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2979_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v_val_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v_buckets_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2977_; 
v_val_2952_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_val_2952_);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2953_ = lean_unsigned_to_nat(0u);
v___x_2954_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v_buckets_2955_ = lean_ctor_get(v_constraints_2946_, 1);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_constraints_2946_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; 
v_unused_2978_ = lean_ctor_get(v_constraints_2946_, 0);
lean_dec(v_unused_2978_);
v___x_2957_ = v_constraints_2946_;
v_isShared_2958_ = v_isSharedCheck_2977_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_buckets_2955_);
lean_dec(v_constraints_2946_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2977_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; lean_object* v_sign_2960_; lean_object* v___x_2962_; 
lean_inc_n(v___y_2944_, 2);
v___x_2959_ = l_Lean_Omega_IntList_get(v_c_2942_, v___y_2944_);
v_sign_2960_ = l_Int_sign(v___x_2959_);
lean_dec(v___x_2959_);
lean_inc(v_sign_2960_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 1, v_sign_2960_);
lean_ctor_set(v___x_2957_, 0, v___y_2944_);
v___x_2962_ = v___x_2957_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___y_2944_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_sign_2960_);
v___x_2962_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; uint8_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v_init_2969_; 
lean_inc(v_val_2952_);
v___x_2963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2963_, 0, v_val_2952_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
lean_ctor_set(v___x_2964_, 1, v_eliminations_2947_);
v___x_2965_ = 1;
v___x_2966_ = lean_box(0);
v___x_2967_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 6, v___x_2967_);
lean_ctor_set(v___x_2950_, 5, v___x_2966_);
lean_ctor_set(v___x_2950_, 4, v___x_2964_);
lean_ctor_set(v___x_2950_, 3, v___x_2954_);
lean_ctor_set(v___x_2950_, 2, v___x_2954_);
lean_ctor_set(v___x_2950_, 1, v___x_2953_);
v_init_2969_ = v___x_2950_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_assumptions_2945_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v___x_2953_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2975_, 3, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2975_, 4, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2975_, 5, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2975_, 6, v___x_2967_);
v_init_2969_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2970_; uint8_t v___x_2971_; 
lean_ctor_set_uint8(v_init_2969_, sizeof(void*)*7, v___x_2965_);
v___x_2970_ = lean_array_get_size(v_buckets_2955_);
v___x_2971_ = lean_nat_dec_lt(v___x_2953_, v___x_2970_);
if (v___x_2971_ == 0)
{
lean_dec(v_sign_2960_);
lean_dec_ref(v_buckets_2955_);
lean_dec(v_val_2952_);
lean_dec(v___y_2944_);
return v_init_2969_;
}
else
{
size_t v___x_2972_; size_t v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = ((size_t)0ULL);
v___x_2973_ = lean_usize_of_nat(v___x_2970_);
v___x_2974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2944_, v_sign_2960_, v_val_2952_, v_buckets_2955_, v___x_2972_, v___x_2973_, v_init_2969_);
lean_dec_ref(v_buckets_2955_);
lean_dec(v_sign_2960_);
return v___x_2974_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2948_);
lean_dec_ref(v_constraints_2946_);
lean_dec(v___y_2944_);
return v_p_2941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___boxed(lean_object* v_p_2990_, lean_object* v_c_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_2990_, v_c_2991_);
lean_dec(v_c_2991_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(lean_object* v_msgData_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v___x_2999_; lean_object* v_env_3000_; uint8_t v___x_3001_; lean_object* v_env_3002_; lean_object* v___x_3003_; lean_object* v_toCold_3004_; lean_object* v_mctx_3005_; lean_object* v_lctx_3006_; lean_object* v_options_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_2999_ = lean_st_ref_get(v___y_2997_);
v_env_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_ref(v_env_3000_);
lean_dec(v___x_2999_);
v___x_3001_ = 0;
v_env_3002_ = l_Lean_Environment_setRecordingDeps(v_env_3000_, v___x_3001_);
v___x_3003_ = lean_st_ref_get(v___y_2995_);
v_toCold_3004_ = lean_ctor_get(v___y_2996_, 0);
v_mctx_3005_ = lean_ctor_get(v___x_3003_, 0);
lean_inc_ref(v_mctx_3005_);
lean_dec(v___x_3003_);
v_lctx_3006_ = lean_ctor_get(v___y_2994_, 2);
v_options_3007_ = lean_ctor_get(v_toCold_3004_, 2);
lean_inc_ref(v_options_3007_);
lean_inc_ref(v_lctx_3006_);
v___x_3008_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3008_, 0, v_env_3002_);
lean_ctor_set(v___x_3008_, 1, v_mctx_3005_);
lean_ctor_set(v___x_3008_, 2, v_lctx_3006_);
lean_ctor_set(v___x_3008_, 3, v_options_3007_);
v___x_3009_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
lean_ctor_set(v___x_3009_, 1, v_msgData_2993_);
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0___boxed(lean_object* v_msgData_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msgData_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(lean_object* v_msg_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_ref_3024_; lean_object* v___x_3025_; lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3034_; 
v_ref_3024_ = lean_ctor_get(v___y_3021_, 2);
v___x_3025_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3028_ = v___x_3025_;
v_isShared_3029_ = v_isSharedCheck_3034_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3025_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3034_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; lean_object* v___x_3032_; 
lean_inc(v_ref_3024_);
v___x_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3030_, 0, v_ref_3024_);
lean_ctor_set(v___x_3030_, 1, v_a_3026_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set_tag(v___x_3028_, 1);
lean_ctor_set(v___x_3028_, 0, v___x_3030_);
v___x_3032_ = v___x_3028_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg___boxed(lean_object* v_msg_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
return v_res_3041_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0));
v___x_3044_ = l_Lean_stringToMessageData(v___x_3043_);
return v___x_3044_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2));
v___x_3047_ = l_Lean_stringToMessageData(v___x_3046_);
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4));
v___x_3050_ = l_Lean_stringToMessageData(v___x_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(lean_object* v_p_3051_, lean_object* v_c_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, uint8_t v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v_constraints_3063_; lean_object* v___x_3064_; 
v_constraints_3063_ = lean_ctor_get(v_p_3051_, 2);
v___x_3064_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_3063_, v_c_3052_);
if (lean_obj_tag(v___x_3064_) == 1)
{
lean_object* v_val_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3164_; 
v_val_3065_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3067_ = v___x_3064_;
v_isShared_3068_ = v_isSharedCheck_3164_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_val_3065_);
lean_dec(v___x_3064_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3164_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v_constraint_3069_; lean_object* v_lowerBound_3070_; 
v_constraint_3069_ = lean_ctor_get(v_val_3065_, 1);
v_lowerBound_3070_ = lean_ctor_get(v_constraint_3069_, 0);
lean_inc(v_lowerBound_3070_);
if (lean_obj_tag(v_lowerBound_3070_) == 1)
{
lean_object* v_upperBound_3071_; 
lean_del_object(v___x_3067_);
v_upperBound_3071_ = lean_ctor_get(v_constraint_3069_, 1);
lean_inc(v_upperBound_3071_);
if (lean_obj_tag(v_upperBound_3071_) == 1)
{
lean_object* v_coeffs_3072_; lean_object* v_justification_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3151_; 
v_coeffs_3072_ = lean_ctor_get(v_val_3065_, 0);
v_justification_3073_ = lean_ctor_get(v_val_3065_, 2);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_val_3065_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; 
v_unused_3152_ = lean_ctor_get(v_val_3065_, 1);
lean_dec(v_unused_3152_);
v___x_3075_ = v_val_3065_;
v_isShared_3076_ = v_isSharedCheck_3151_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_justification_3073_);
lean_inc(v_coeffs_3072_);
lean_dec(v_val_3065_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3151_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v_val_3077_; lean_object* v_val_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v_m_3081_; lean_object* v___x_3082_; 
v_val_3077_ = lean_ctor_get(v_lowerBound_3070_, 0);
lean_inc(v_val_3077_);
lean_dec_ref_known(v_lowerBound_3070_, 1);
v_val_3078_ = lean_ctor_get(v_upperBound_3071_, 0);
lean_inc(v_val_3078_);
lean_dec_ref_known(v_upperBound_3071_, 1);
lean_inc(v_c_3052_);
v___x_3079_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_c_3052_);
v___x_3080_ = lean_unsigned_to_nat(1u);
v_m_3081_ = lean_nat_add(v___x_3079_, v___x_3080_);
lean_dec(v___x_3079_);
v___x_3082_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3054_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v_nil_3086_; lean_object* v_cons_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___x_3082_, 1);
v___x_3084_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__19);
lean_inc(v_m_3081_);
v___x_3085_ = l_Lean_mkNatLit(v_m_3081_);
v_nil_3086_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3087_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3088_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3086_, v_cons_3087_, v_c_3052_);
lean_dec(v_c_3052_);
v___x_3089_ = l_Lean_mkApp3(v___x_3084_, v___x_3085_, v___x_3088_, v_a_3083_);
v___x_3090_ = l_Lean_Elab_Tactic_Omega_lookup(v___x_3089_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3134_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3093_ = v___x_3090_;
v_isShared_3094_ = v_isSharedCheck_3134_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3134_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v_fst_3095_; lean_object* v_snd_3096_; uint8_t v___x_3109_; 
v_fst_3095_ = lean_ctor_get(v_a_3091_, 0);
lean_inc(v_fst_3095_);
v_snd_3096_ = lean_ctor_get(v_a_3091_, 1);
lean_inc(v_snd_3096_);
lean_dec(v_a_3091_);
v___x_3109_ = lean_int_dec_eq(v_val_3078_, v_val_3077_);
lean_dec(v_val_3078_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
lean_dec(v_snd_3096_);
lean_dec(v_fst_3095_);
lean_del_object(v___x_3093_);
lean_dec(v_m_3081_);
lean_dec(v_val_3077_);
lean_del_object(v___x_3075_);
lean_dec_ref(v_justification_3073_);
lean_dec(v_coeffs_3072_);
lean_dec_ref(v_p_3051_);
v___x_3110_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1);
v___x_3111_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3110_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3111_;
}
else
{
if (lean_obj_tag(v_snd_3096_) == 0)
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec(v_fst_3095_);
lean_del_object(v___x_3093_);
lean_dec(v_m_3081_);
lean_dec(v_val_3077_);
lean_del_object(v___x_3075_);
lean_dec_ref(v_justification_3073_);
lean_dec(v_coeffs_3072_);
lean_dec_ref(v_p_3051_);
v___x_3112_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3);
v___x_3113_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3112_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3113_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3113_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
else
{
lean_object* v_val_3122_; uint8_t v___x_3123_; 
v_val_3122_ = lean_ctor_get(v_snd_3096_, 0);
lean_inc(v_val_3122_);
lean_dec_ref_known(v_snd_3096_, 1);
v___x_3123_ = l_List_isEmpty___redArg(v_val_3122_);
lean_dec(v_val_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_fst_3095_);
lean_del_object(v___x_3093_);
lean_dec(v_m_3081_);
lean_dec(v_val_3077_);
lean_del_object(v___x_3075_);
lean_dec_ref(v_justification_3073_);
lean_dec(v_coeffs_3072_);
lean_dec_ref(v_p_3051_);
v___x_3124_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5);
v___x_3125_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v___x_3124_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
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
goto v___jp_3097_;
}
}
}
v___jp_3097_:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3103_; 
lean_inc(v_coeffs_3072_);
lean_inc_n(v_m_3081_, 2);
v___x_3098_ = l_Lean_Omega_bmod__coeffs(v_m_3081_, v_fst_3095_, v_coeffs_3072_);
v___x_3099_ = l_Int_bmod(v_val_3077_, v_m_3081_);
v___x_3100_ = l_Lean_Omega_Constraint_exact(v___x_3099_);
v___x_3101_ = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(v___x_3101_, 0, v_m_3081_);
lean_ctor_set(v___x_3101_, 1, v_val_3077_);
lean_ctor_set(v___x_3101_, 2, v_fst_3095_);
lean_ctor_set(v___x_3101_, 3, v_coeffs_3072_);
lean_ctor_set(v___x_3101_, 4, v_justification_3073_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 2, v___x_3101_);
lean_ctor_set(v___x_3075_, 1, v___x_3100_);
lean_ctor_set(v___x_3075_, 0, v___x_3098_);
v___x_3103_ = v___x_3075_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3108_, 2, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
v___x_3104_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_3051_, v___x_3103_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3104_);
v___x_3106_ = v___x_3093_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec(v_m_3081_);
lean_dec(v_val_3078_);
lean_dec(v_val_3077_);
lean_del_object(v___x_3075_);
lean_dec_ref(v_justification_3073_);
lean_dec(v_coeffs_3072_);
lean_dec_ref(v_p_3051_);
v_a_3135_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3090_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3090_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec(v_m_3081_);
lean_dec(v_val_3078_);
lean_dec(v_val_3077_);
lean_del_object(v___x_3075_);
lean_dec_ref(v_justification_3073_);
lean_dec(v_coeffs_3072_);
lean_dec(v_c_3052_);
lean_dec_ref(v_p_3051_);
v_a_3143_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3082_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3082_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
}
else
{
lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_upperBound_3071_);
lean_dec(v_val_3065_);
lean_dec(v_c_3052_);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_lowerBound_3070_);
if (v_isSharedCheck_3159_ == 0)
{
lean_object* v_unused_3160_; 
v_unused_3160_ = lean_ctor_get(v_lowerBound_3070_, 0);
lean_dec(v_unused_3160_);
v___x_3154_ = v_lowerBound_3070_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_dec(v_lowerBound_3070_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
lean_ctor_set_tag(v___x_3154_, 0);
lean_ctor_set(v___x_3154_, 0, v_p_3051_);
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_p_3051_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
else
{
lean_object* v___x_3162_; 
lean_dec(v_lowerBound_3070_);
lean_dec(v_val_3065_);
lean_dec(v_c_3052_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set_tag(v___x_3067_, 0);
lean_ctor_set(v___x_3067_, 0, v_p_3051_);
v___x_3162_ = v___x_3067_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_p_3051_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
else
{
lean_object* v___x_3165_; 
lean_dec(v___x_3064_);
lean_dec(v_c_3052_);
v___x_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3165_, 0, v_p_3051_);
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___boxed(lean_object* v_p_3166_, lean_object* v_c_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
uint8_t v_a_boxed_3178_; lean_object* v_res_3179_; 
v_a_boxed_3178_ = lean_unbox(v_a_3171_);
v_res_3179_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3166_, v_c_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_boxed_3178_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_);
lean_dec(v_a_3176_);
lean_dec_ref(v_a_3175_);
lean_dec(v_a_3174_);
lean_dec_ref(v_a_3173_);
lean_dec(v_a_3172_);
lean_dec_ref(v_a_3170_);
lean_dec(v_a_3169_);
lean_dec(v_a_3168_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_object* v_00_u03b1_3180_, lean_object* v_msg_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, uint8_t v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3181_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___boxed(lean_object* v_00_u03b1_3193_, lean_object* v_msg_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
uint8_t v___y_8992__boxed_3205_; lean_object* v_res_3206_; 
v___y_8992__boxed_3205_ = lean_unbox(v___y_3198_);
v_res_3206_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(v_00_u03b1_3193_, v_msg_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_8992__boxed_3205_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec(v___y_3195_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality(lean_object* v_p_3207_, lean_object* v_c_3208_, lean_object* v_m_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, uint8_t v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_){
_start:
{
lean_object* v___x_3220_; uint8_t v___x_3221_; 
v___x_3220_ = lean_unsigned_to_nat(1u);
v___x_3221_ = lean_nat_dec_eq(v_m_3209_, v___x_3220_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3207_, v_c_3208_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_);
return v___x_3222_;
}
else
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_3207_, v_c_3208_);
lean_dec(v_c_3208_);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
return v___x_3224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality___boxed(lean_object* v_p_3225_, lean_object* v_c_3226_, lean_object* v_m_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_){
_start:
{
uint8_t v_a_boxed_3238_; lean_object* v_res_3239_; 
v_a_boxed_3238_ = lean_unbox(v_a_3231_);
v_res_3239_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3225_, v_c_3226_, v_m_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_boxed_3238_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
lean_dec(v_a_3236_);
lean_dec_ref(v_a_3235_);
lean_dec(v_a_3234_);
lean_dec_ref(v_a_3233_);
lean_dec(v_a_3232_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec(v_a_3228_);
lean_dec(v_m_3227_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(lean_object* v_p_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, uint8_t v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_){
_start:
{
uint8_t v_possible_3251_; 
v_possible_3251_ = lean_ctor_get_uint8(v_p_3240_, sizeof(void*)*7);
if (v_possible_3251_ == 0)
{
lean_object* v___x_3252_; 
v___x_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3252_, 0, v_p_3240_);
return v___x_3252_;
}
else
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_3240_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3254_, 0, v_p_3240_);
return v___x_3254_;
}
else
{
lean_object* v_val_3255_; lean_object* v_fst_3256_; lean_object* v_snd_3257_; lean_object* v___x_3258_; 
v_val_3255_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_val_3255_);
lean_dec_ref_known(v___x_3253_, 1);
v_fst_3256_ = lean_ctor_get(v_val_3255_, 0);
lean_inc(v_fst_3256_);
v_snd_3257_ = lean_ctor_get(v_val_3255_, 1);
lean_inc(v_snd_3257_);
lean_dec(v_val_3255_);
v___x_3258_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3240_, v_fst_3256_, v_snd_3257_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_);
lean_dec(v_snd_3257_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref_known(v___x_3258_, 1);
v_p_3240_ = v_a_3259_;
goto _start;
}
else
{
return v___x_3258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities___boxed(lean_object* v_p_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
uint8_t v_a_boxed_3272_; lean_object* v_res_3273_; 
v_a_boxed_3272_ = lean_unbox(v_a_3265_);
v_res_3273_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_boxed_3272_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
lean_dec(v_a_3270_);
lean_dec_ref(v_a_3269_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3264_);
lean_dec(v_a_3263_);
lean_dec(v_a_3262_);
return v_res_3273_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = lean_box(0);
v___x_3281_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1));
v___x_3282_ = l_Lean_Expr_const___override(v___x_3281_, v___x_3280_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object* v_c_3283_, lean_object* v_x_3284_, lean_object* v_p_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, uint8_t v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3287_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
v___x_3298_ = lean_box(v_a_3289_);
lean_inc(v_a_3294_);
lean_inc_ref(v_a_3293_);
lean_inc(v_a_3292_);
lean_inc_ref(v_a_3291_);
lean_inc(v_a_3290_);
lean_inc_ref(v_a_3288_);
lean_inc(v_a_3287_);
lean_inc(v_a_3286_);
v___x_3299_ = lean_apply_10(v_p_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v___x_3298_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, lean_box(0));
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3325_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3302_ = v___x_3299_;
v_isShared_3303_ = v_isSharedCheck_3325_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3299_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3325_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; lean_object* v___y_3306_; lean_object* v___x_3314_; uint8_t v___x_3315_; 
v___x_3304_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2);
v___x_3314_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3315_ = lean_int_dec_le(v___x_3314_, v_c_3283_);
if (v___x_3315_ == 0)
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3316_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3317_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3318_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3319_ = lean_int_neg(v_c_3283_);
v___x_3320_ = l_Int_toNat(v___x_3319_);
lean_dec(v___x_3319_);
v___x_3321_ = l_Lean_instToExprInt_mkNat(v___x_3320_);
v___x_3322_ = l_Lean_mkApp3(v___x_3316_, v___x_3317_, v___x_3318_, v___x_3321_);
v___y_3306_ = v___x_3322_;
goto v___jp_3305_;
}
else
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = l_Int_toNat(v_c_3283_);
v___x_3324_ = l_Lean_instToExprInt_mkNat(v___x_3323_);
v___y_3306_ = v___x_3324_;
goto v___jp_3305_;
}
v___jp_3305_:
{
lean_object* v_nil_3307_; lean_object* v_cons_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3312_; 
v_nil_3307_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3308_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3309_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3307_, v_cons_3308_, v_x_3284_);
v___x_3310_ = l_Lean_mkApp4(v___x_3304_, v___y_3306_, v___x_3309_, v_a_3297_, v_a_3300_);
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 0, v___x_3310_);
v___x_3312_ = v___x_3302_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
else
{
lean_dec(v_a_3297_);
return v___x_3299_;
}
}
else
{
lean_dec_ref(v_p_3285_);
return v___x_3296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object* v_c_3326_, lean_object* v_x_3327_, lean_object* v_p_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_){
_start:
{
uint8_t v_a_boxed_3339_; lean_object* v_res_3340_; 
v_a_boxed_3339_ = lean_unbox(v_a_3332_);
v_res_3340_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(v_c_3326_, v_x_3327_, v_p_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_boxed_3339_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
lean_dec(v_a_3337_);
lean_dec_ref(v_a_3336_);
lean_dec(v_a_3335_);
lean_dec_ref(v_a_3334_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3331_);
lean_dec(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec(v_x_3327_);
lean_dec(v_c_3326_);
return v_res_3340_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2(void){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3347_ = lean_box(0);
v___x_3348_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1));
v___x_3349_ = l_Lean_Expr_const___override(v___x_3348_, v___x_3347_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(lean_object* v_c_3350_, lean_object* v_x_3351_, lean_object* v_p_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, uint8_t v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3354_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3363_, 1);
v___x_3365_ = lean_box(v_a_3356_);
lean_inc(v_a_3361_);
lean_inc_ref(v_a_3360_);
lean_inc(v_a_3359_);
lean_inc_ref(v_a_3358_);
lean_inc(v_a_3357_);
lean_inc_ref(v_a_3355_);
lean_inc(v_a_3354_);
lean_inc(v_a_3353_);
v___x_3366_ = lean_apply_10(v_p_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v___x_3365_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, lean_box(0));
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3392_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3392_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3392_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3371_; lean_object* v___y_3373_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3371_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2);
v___x_3381_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3382_ = lean_int_dec_le(v___x_3381_, v_c_3350_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3383_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3384_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3385_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3386_ = lean_int_neg(v_c_3350_);
v___x_3387_ = l_Int_toNat(v___x_3386_);
lean_dec(v___x_3386_);
v___x_3388_ = l_Lean_instToExprInt_mkNat(v___x_3387_);
v___x_3389_ = l_Lean_mkApp3(v___x_3383_, v___x_3384_, v___x_3385_, v___x_3388_);
v___y_3373_ = v___x_3389_;
goto v___jp_3372_;
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = l_Int_toNat(v_c_3350_);
v___x_3391_ = l_Lean_instToExprInt_mkNat(v___x_3390_);
v___y_3373_ = v___x_3391_;
goto v___jp_3372_;
}
v___jp_3372_:
{
lean_object* v_nil_3374_; lean_object* v_cons_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3379_; 
v_nil_3374_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3375_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3376_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3374_, v_cons_3375_, v_x_3351_);
v___x_3377_ = l_Lean_mkApp4(v___x_3371_, v___y_3373_, v___x_3376_, v_a_3364_, v_a_3367_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3377_);
v___x_3379_ = v___x_3369_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_dec(v_a_3364_);
return v___x_3366_;
}
}
else
{
lean_dec_ref(v_p_3352_);
return v___x_3363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed(lean_object* v_c_3393_, lean_object* v_x_3394_, lean_object* v_p_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
uint8_t v_a_boxed_3406_; lean_object* v_res_3407_; 
v_a_boxed_3406_ = lean_unbox(v_a_3399_);
v_res_3407_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(v_c_3393_, v_x_3394_, v_p_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_boxed_3406_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3398_);
lean_dec(v_a_3397_);
lean_dec(v_a_3396_);
lean_dec(v_x_3394_);
lean_dec(v_c_3393_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(lean_object* v_prf_x3f_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, uint8_t v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
if (lean_obj_tag(v_prf_x3f_3408_) == 0)
{
lean_object* v___x_3419_; uint8_t v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3419_ = lean_box(0);
v___x_3420_ = 0;
v___x_3421_ = lean_box(0);
v___x_3422_ = l_Lean_Meta_mkFreshExprMVar(v___x_3419_, v___x_3420_, v___x_3421_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; uint8_t v___x_3424_; lean_object* v___x_3425_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_a_3423_);
lean_dec_ref_known(v___x_3422_, 1);
v___x_3424_ = 0;
v___x_3425_ = l_Lean_Meta_mkSorry(v_a_3423_, v___x_3424_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
return v___x_3425_;
}
else
{
return v___x_3422_;
}
}
else
{
lean_object* v_val_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v_val_3426_ = lean_ctor_get(v_prf_x3f_3408_, 0);
lean_inc(v_val_3426_);
lean_dec_ref_known(v_prf_x3f_3408_, 1);
v___x_3427_ = lean_box(v___y_3412_);
lean_inc(v___y_3417_);
lean_inc_ref(v___y_3416_);
lean_inc(v___y_3415_);
lean_inc_ref(v___y_3414_);
lean_inc(v___y_3413_);
lean_inc_ref(v___y_3411_);
lean_inc(v___y_3410_);
lean_inc(v___y_3409_);
v___x_3428_ = lean_apply_10(v_val_3426_, v___y_3409_, v___y_3410_, v___y_3411_, v___x_3427_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, lean_box(0));
return v___x_3428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed(lean_object* v_prf_x3f_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
uint8_t v___y_833__boxed_3440_; lean_object* v_res_3441_; 
v___y_833__boxed_3440_ = lean_unbox(v___y_3433_);
v_res_3441_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(v_prf_x3f_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_833__boxed_3440_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec(v___y_3430_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality(lean_object* v_p_3442_, lean_object* v_const_3443_, lean_object* v_coeffs_3444_, lean_object* v_prf_x3f_3445_){
_start:
{
lean_object* v_assumptions_3446_; lean_object* v_numVars_3447_; lean_object* v_constraints_3448_; lean_object* v_equalities_3449_; lean_object* v_eliminations_3450_; uint8_t v_possible_3451_; lean_object* v_proveFalse_x3f_3452_; lean_object* v_explanation_x3f_3453_; lean_object* v_prf_3454_; lean_object* v_i_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v_p_x27_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v_f_3464_; lean_object* v_f_3465_; lean_object* v_f_3466_; lean_object* v___x_3467_; 
v_assumptions_3446_ = lean_ctor_get(v_p_3442_, 0);
v_numVars_3447_ = lean_ctor_get(v_p_3442_, 1);
v_constraints_3448_ = lean_ctor_get(v_p_3442_, 2);
v_equalities_3449_ = lean_ctor_get(v_p_3442_, 3);
v_eliminations_3450_ = lean_ctor_get(v_p_3442_, 4);
v_possible_3451_ = lean_ctor_get_uint8(v_p_3442_, sizeof(void*)*7);
v_proveFalse_x3f_3452_ = lean_ctor_get(v_p_3442_, 5);
v_explanation_x3f_3453_ = lean_ctor_get(v_p_3442_, 6);
v_prf_3454_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3454_, 0, v_prf_x3f_3445_);
v_i_3455_ = lean_array_get_size(v_assumptions_3446_);
lean_inc_n(v_coeffs_3444_, 2);
lean_inc(v_const_3443_);
v___x_3456_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed), 13, 3);
lean_closure_set(v___x_3456_, 0, v_const_3443_);
lean_closure_set(v___x_3456_, 1, v_coeffs_3444_);
lean_closure_set(v___x_3456_, 2, v_prf_3454_);
lean_inc_ref(v_assumptions_3446_);
v___x_3457_ = lean_array_push(v_assumptions_3446_, v___x_3456_);
lean_inc_ref(v_explanation_x3f_3453_);
lean_inc(v_proveFalse_x3f_3452_);
lean_inc(v_eliminations_3450_);
lean_inc_ref(v_equalities_3449_);
lean_inc_ref(v_constraints_3448_);
lean_inc(v_numVars_3447_);
v_p_x27_3458_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3458_, 0, v___x_3457_);
lean_ctor_set(v_p_x27_3458_, 1, v_numVars_3447_);
lean_ctor_set(v_p_x27_3458_, 2, v_constraints_3448_);
lean_ctor_set(v_p_x27_3458_, 3, v_equalities_3449_);
lean_ctor_set(v_p_x27_3458_, 4, v_eliminations_3450_);
lean_ctor_set(v_p_x27_3458_, 5, v_proveFalse_x3f_3452_);
lean_ctor_set(v_p_x27_3458_, 6, v_explanation_x3f_3453_);
lean_ctor_set_uint8(v_p_x27_3458_, sizeof(void*)*7, v_possible_3451_);
v___x_3459_ = lean_int_neg(v_const_3443_);
lean_dec(v_const_3443_);
v___x_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
v___x_3461_ = lean_box(0);
v___x_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
lean_inc_ref(v___x_3462_);
v___x_3463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
lean_ctor_set(v___x_3463_, 1, v_coeffs_3444_);
lean_ctor_set(v___x_3463_, 2, v_i_3455_);
v_f_3464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3464_, 0, v_coeffs_3444_);
lean_ctor_set(v_f_3464_, 1, v___x_3462_);
lean_ctor_set(v_f_3464_, 2, v___x_3463_);
v_f_3465_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3442_, v_f_3464_);
v_f_3466_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3465_);
v___x_3467_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3458_, v_f_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality(lean_object* v_p_3468_, lean_object* v_const_3469_, lean_object* v_coeffs_3470_, lean_object* v_prf_x3f_3471_){
_start:
{
lean_object* v_assumptions_3472_; lean_object* v_numVars_3473_; lean_object* v_constraints_3474_; lean_object* v_equalities_3475_; lean_object* v_eliminations_3476_; uint8_t v_possible_3477_; lean_object* v_proveFalse_x3f_3478_; lean_object* v_explanation_x3f_3479_; lean_object* v_prf_3480_; lean_object* v_i_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v_p_x27_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v_f_3489_; lean_object* v_f_3490_; lean_object* v_f_3491_; lean_object* v___x_3492_; 
v_assumptions_3472_ = lean_ctor_get(v_p_3468_, 0);
v_numVars_3473_ = lean_ctor_get(v_p_3468_, 1);
v_constraints_3474_ = lean_ctor_get(v_p_3468_, 2);
v_equalities_3475_ = lean_ctor_get(v_p_3468_, 3);
v_eliminations_3476_ = lean_ctor_get(v_p_3468_, 4);
v_possible_3477_ = lean_ctor_get_uint8(v_p_3468_, sizeof(void*)*7);
v_proveFalse_x3f_3478_ = lean_ctor_get(v_p_3468_, 5);
v_explanation_x3f_3479_ = lean_ctor_get(v_p_3468_, 6);
v_prf_3480_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3480_, 0, v_prf_x3f_3471_);
v_i_3481_ = lean_array_get_size(v_assumptions_3472_);
lean_inc_n(v_coeffs_3470_, 2);
lean_inc(v_const_3469_);
v___x_3482_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed), 13, 3);
lean_closure_set(v___x_3482_, 0, v_const_3469_);
lean_closure_set(v___x_3482_, 1, v_coeffs_3470_);
lean_closure_set(v___x_3482_, 2, v_prf_3480_);
lean_inc_ref(v_assumptions_3472_);
v___x_3483_ = lean_array_push(v_assumptions_3472_, v___x_3482_);
lean_inc_ref(v_explanation_x3f_3479_);
lean_inc(v_proveFalse_x3f_3478_);
lean_inc(v_eliminations_3476_);
lean_inc_ref(v_equalities_3475_);
lean_inc_ref(v_constraints_3474_);
lean_inc(v_numVars_3473_);
v_p_x27_3484_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3484_, 0, v___x_3483_);
lean_ctor_set(v_p_x27_3484_, 1, v_numVars_3473_);
lean_ctor_set(v_p_x27_3484_, 2, v_constraints_3474_);
lean_ctor_set(v_p_x27_3484_, 3, v_equalities_3475_);
lean_ctor_set(v_p_x27_3484_, 4, v_eliminations_3476_);
lean_ctor_set(v_p_x27_3484_, 5, v_proveFalse_x3f_3478_);
lean_ctor_set(v_p_x27_3484_, 6, v_explanation_x3f_3479_);
lean_ctor_set_uint8(v_p_x27_3484_, sizeof(void*)*7, v_possible_3477_);
v___x_3485_ = lean_int_neg(v_const_3469_);
lean_dec(v_const_3469_);
v___x_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_inc_ref(v___x_3486_);
v___x_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
lean_inc_ref(v___x_3487_);
v___x_3488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v_coeffs_3470_);
lean_ctor_set(v___x_3488_, 2, v_i_3481_);
v_f_3489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3489_, 0, v_coeffs_3470_);
lean_ctor_set(v_f_3489_, 1, v___x_3487_);
lean_ctor_set(v_f_3489_, 2, v___x_3488_);
v_f_3490_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3468_, v_f_3489_);
v_f_3491_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3490_);
v___x_3492_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3484_, v_f_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(lean_object* v_x_3493_, lean_object* v_x_3494_){
_start:
{
if (lean_obj_tag(v_x_3494_) == 0)
{
return v_x_3493_;
}
else
{
lean_object* v_head_3495_; lean_object* v_snd_3496_; lean_object* v_tail_3497_; lean_object* v_fst_3498_; lean_object* v_fst_3499_; lean_object* v_snd_3500_; lean_object* v___x_3501_; 
v_head_3495_ = lean_ctor_get(v_x_3494_, 0);
lean_inc(v_head_3495_);
v_snd_3496_ = lean_ctor_get(v_head_3495_, 1);
lean_inc(v_snd_3496_);
v_tail_3497_ = lean_ctor_get(v_x_3494_, 1);
lean_inc(v_tail_3497_);
lean_dec_ref_known(v_x_3494_, 2);
v_fst_3498_ = lean_ctor_get(v_head_3495_, 0);
lean_inc(v_fst_3498_);
lean_dec(v_head_3495_);
v_fst_3499_ = lean_ctor_get(v_snd_3496_, 0);
lean_inc(v_fst_3499_);
v_snd_3500_ = lean_ctor_get(v_snd_3496_, 1);
lean_inc(v_snd_3500_);
lean_dec(v_snd_3496_);
v___x_3501_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality(v_x_3493_, v_fst_3498_, v_fst_3499_, v_snd_3500_);
v_x_3493_ = v___x_3501_;
v_x_3494_ = v_tail_3497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequalities(lean_object* v_p_3503_, lean_object* v_ineqs_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(v_p_3503_, v_ineqs_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(lean_object* v_x_3506_, lean_object* v_x_3507_){
_start:
{
if (lean_obj_tag(v_x_3507_) == 0)
{
return v_x_3506_;
}
else
{
lean_object* v_head_3508_; lean_object* v_snd_3509_; lean_object* v_tail_3510_; lean_object* v_fst_3511_; lean_object* v_fst_3512_; lean_object* v_snd_3513_; lean_object* v___x_3514_; 
v_head_3508_ = lean_ctor_get(v_x_3507_, 0);
lean_inc(v_head_3508_);
v_snd_3509_ = lean_ctor_get(v_head_3508_, 1);
lean_inc(v_snd_3509_);
v_tail_3510_ = lean_ctor_get(v_x_3507_, 1);
lean_inc(v_tail_3510_);
lean_dec_ref_known(v_x_3507_, 2);
v_fst_3511_ = lean_ctor_get(v_head_3508_, 0);
lean_inc(v_fst_3511_);
lean_dec(v_head_3508_);
v_fst_3512_ = lean_ctor_get(v_snd_3509_, 0);
lean_inc(v_fst_3512_);
v_snd_3513_ = lean_ctor_get(v_snd_3509_, 1);
lean_inc(v_snd_3513_);
lean_dec(v_snd_3509_);
v___x_3514_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality(v_x_3506_, v_fst_3511_, v_fst_3512_, v_snd_3513_);
v_x_3506_ = v___x_3514_;
v_x_3507_ = v_tail_3510_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEqualities(lean_object* v_p_3516_, lean_object* v_eqs_3517_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(v_p_3516_, v_eqs_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0(lean_object* v___x_3525_, lean_object* v_x_3526_){
_start:
{
lean_object* v_constraint_3527_; lean_object* v_coeffs_3528_; lean_object* v_lowerBound_3529_; lean_object* v_upperBound_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___y_3535_; lean_object* v___y_3536_; 
v_constraint_3527_ = lean_ctor_get(v_x_3526_, 1);
lean_inc_ref(v_constraint_3527_);
v_coeffs_3528_ = lean_ctor_get(v_x_3526_, 0);
lean_inc(v_coeffs_3528_);
lean_dec_ref(v_x_3526_);
v_lowerBound_3529_ = lean_ctor_get(v_constraint_3527_, 0);
lean_inc(v_lowerBound_3529_);
v_upperBound_3530_ = lean_ctor_get(v_constraint_3527_, 1);
lean_inc(v_upperBound_3530_);
lean_dec_ref(v_constraint_3527_);
v___x_3531_ = l_List_toString___redArg(v___x_3525_, v_coeffs_3528_);
v___x_3532_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3533_ = lean_string_append(v___x_3531_, v___x_3532_);
if (lean_obj_tag(v_lowerBound_3529_) == 0)
{
if (lean_obj_tag(v_upperBound_3530_) == 0)
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3542_ = lean_string_append(v___x_3533_, v___x_3541_);
return v___x_3542_;
}
else
{
lean_object* v_val_3543_; lean_object* v___x_3544_; lean_object* v___y_3546_; lean_object* v_intZero_3551_; uint8_t v_isNeg_3552_; 
v_val_3543_ = lean_ctor_get(v_upperBound_3530_, 0);
lean_inc(v_val_3543_);
lean_dec_ref_known(v_upperBound_3530_, 1);
v___x_3544_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3551_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3552_ = lean_int_dec_lt(v_val_3543_, v_intZero_3551_);
if (v_isNeg_3552_ == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3554_; 
v_a_3553_ = lean_nat_abs(v_val_3543_);
lean_dec(v_val_3543_);
v___x_3554_ = l_Nat_reprFast(v_a_3553_);
v___y_3546_ = v___x_3554_;
goto v___jp_3545_;
}
else
{
lean_object* v_abs_3555_; lean_object* v_one_3556_; lean_object* v_a_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v_abs_3555_ = lean_nat_abs(v_val_3543_);
lean_dec(v_val_3543_);
v_one_3556_ = lean_unsigned_to_nat(1u);
v_a_3557_ = lean_nat_sub(v_abs_3555_, v_one_3556_);
lean_dec(v_abs_3555_);
v___x_3558_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3559_ = lean_nat_add(v_a_3557_, v_one_3556_);
lean_dec(v_a_3557_);
v___x_3560_ = l_Nat_reprFast(v___x_3559_);
v___x_3561_ = lean_string_append(v___x_3558_, v___x_3560_);
lean_dec_ref(v___x_3560_);
v___y_3546_ = v___x_3561_;
goto v___jp_3545_;
}
v___jp_3545_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3547_ = lean_string_append(v___x_3544_, v___y_3546_);
lean_dec_ref(v___y_3546_);
v___x_3548_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3549_ = lean_string_append(v___x_3547_, v___x_3548_);
v___x_3550_ = lean_string_append(v___x_3533_, v___x_3549_);
lean_dec_ref(v___x_3549_);
return v___x_3550_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3530_) == 0)
{
lean_object* v_val_3562_; lean_object* v___x_3563_; lean_object* v___y_3565_; lean_object* v_intZero_3570_; uint8_t v_isNeg_3571_; 
v_val_3562_ = lean_ctor_get(v_lowerBound_3529_, 0);
lean_inc(v_val_3562_);
lean_dec_ref_known(v_lowerBound_3529_, 1);
v___x_3563_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3570_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3571_ = lean_int_dec_lt(v_val_3562_, v_intZero_3570_);
if (v_isNeg_3571_ == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3573_; 
v_a_3572_ = lean_nat_abs(v_val_3562_);
lean_dec(v_val_3562_);
v___x_3573_ = l_Nat_reprFast(v_a_3572_);
v___y_3565_ = v___x_3573_;
goto v___jp_3564_;
}
else
{
lean_object* v_abs_3574_; lean_object* v_one_3575_; lean_object* v_a_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v_abs_3574_ = lean_nat_abs(v_val_3562_);
lean_dec(v_val_3562_);
v_one_3575_ = lean_unsigned_to_nat(1u);
v_a_3576_ = lean_nat_sub(v_abs_3574_, v_one_3575_);
lean_dec(v_abs_3574_);
v___x_3577_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3578_ = lean_nat_add(v_a_3576_, v_one_3575_);
lean_dec(v_a_3576_);
v___x_3579_ = l_Nat_reprFast(v___x_3578_);
v___x_3580_ = lean_string_append(v___x_3577_, v___x_3579_);
lean_dec_ref(v___x_3579_);
v___y_3565_ = v___x_3580_;
goto v___jp_3564_;
}
v___jp_3564_:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3566_ = lean_string_append(v___x_3563_, v___y_3565_);
lean_dec_ref(v___y_3565_);
v___x_3567_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3568_ = lean_string_append(v___x_3566_, v___x_3567_);
v___x_3569_ = lean_string_append(v___x_3533_, v___x_3568_);
lean_dec_ref(v___x_3568_);
return v___x_3569_;
}
}
else
{
lean_object* v_val_3581_; lean_object* v_val_3582_; uint8_t v___x_3583_; 
v_val_3581_ = lean_ctor_get(v_lowerBound_3529_, 0);
lean_inc(v_val_3581_);
lean_dec_ref_known(v_lowerBound_3529_, 1);
v_val_3582_ = lean_ctor_get(v_upperBound_3530_, 0);
lean_inc(v_val_3582_);
lean_dec_ref_known(v_upperBound_3530_, 1);
v___x_3583_ = lean_int_dec_lt(v_val_3582_, v_val_3581_);
if (v___x_3583_ == 0)
{
uint8_t v___x_3584_; 
v___x_3584_ = lean_int_dec_eq(v_val_3581_, v_val_3582_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3585_; lean_object* v___y_3587_; lean_object* v_intZero_3602_; uint8_t v_isNeg_3603_; 
v___x_3585_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3602_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3603_ = lean_int_dec_lt(v_val_3581_, v_intZero_3602_);
if (v_isNeg_3603_ == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3605_; 
v_a_3604_ = lean_nat_abs(v_val_3581_);
lean_dec(v_val_3581_);
v___x_3605_ = l_Nat_reprFast(v_a_3604_);
v___y_3587_ = v___x_3605_;
goto v___jp_3586_;
}
else
{
lean_object* v_abs_3606_; lean_object* v_one_3607_; lean_object* v_a_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v_abs_3606_ = lean_nat_abs(v_val_3581_);
lean_dec(v_val_3581_);
v_one_3607_ = lean_unsigned_to_nat(1u);
v_a_3608_ = lean_nat_sub(v_abs_3606_, v_one_3607_);
lean_dec(v_abs_3606_);
v___x_3609_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3610_ = lean_nat_add(v_a_3608_, v_one_3607_);
lean_dec(v_a_3608_);
v___x_3611_ = l_Nat_reprFast(v___x_3610_);
v___x_3612_ = lean_string_append(v___x_3609_, v___x_3611_);
lean_dec_ref(v___x_3611_);
v___y_3587_ = v___x_3612_;
goto v___jp_3586_;
}
v___jp_3586_:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v_intZero_3591_; uint8_t v_isNeg_3592_; 
v___x_3588_ = lean_string_append(v___x_3585_, v___y_3587_);
lean_dec_ref(v___y_3587_);
v___x_3589_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3590_ = lean_string_append(v___x_3588_, v___x_3589_);
v_intZero_3591_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3592_ = lean_int_dec_lt(v_val_3582_, v_intZero_3591_);
if (v_isNeg_3592_ == 0)
{
lean_object* v_a_3593_; lean_object* v___x_3594_; 
v_a_3593_ = lean_nat_abs(v_val_3582_);
lean_dec(v_val_3582_);
v___x_3594_ = l_Nat_reprFast(v_a_3593_);
v___y_3535_ = v___x_3590_;
v___y_3536_ = v___x_3594_;
goto v___jp_3534_;
}
else
{
lean_object* v_abs_3595_; lean_object* v_one_3596_; lean_object* v_a_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v_abs_3595_ = lean_nat_abs(v_val_3582_);
lean_dec(v_val_3582_);
v_one_3596_ = lean_unsigned_to_nat(1u);
v_a_3597_ = lean_nat_sub(v_abs_3595_, v_one_3596_);
lean_dec(v_abs_3595_);
v___x_3598_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3599_ = lean_nat_add(v_a_3597_, v_one_3596_);
lean_dec(v_a_3597_);
v___x_3600_ = l_Nat_reprFast(v___x_3599_);
v___x_3601_ = lean_string_append(v___x_3598_, v___x_3600_);
lean_dec_ref(v___x_3600_);
v___y_3535_ = v___x_3590_;
v___y_3536_ = v___x_3601_;
goto v___jp_3534_;
}
}
}
else
{
lean_object* v___x_3613_; lean_object* v___y_3615_; lean_object* v_intZero_3620_; uint8_t v_isNeg_3621_; 
lean_dec(v_val_3582_);
v___x_3613_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3620_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3621_ = lean_int_dec_lt(v_val_3581_, v_intZero_3620_);
if (v_isNeg_3621_ == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3623_; 
v_a_3622_ = lean_nat_abs(v_val_3581_);
lean_dec(v_val_3581_);
v___x_3623_ = l_Nat_reprFast(v_a_3622_);
v___y_3615_ = v___x_3623_;
goto v___jp_3614_;
}
else
{
lean_object* v_abs_3624_; lean_object* v_one_3625_; lean_object* v_a_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v_abs_3624_ = lean_nat_abs(v_val_3581_);
lean_dec(v_val_3581_);
v_one_3625_ = lean_unsigned_to_nat(1u);
v_a_3626_ = lean_nat_sub(v_abs_3624_, v_one_3625_);
lean_dec(v_abs_3624_);
v___x_3627_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3628_ = lean_nat_add(v_a_3626_, v_one_3625_);
lean_dec(v_a_3626_);
v___x_3629_ = l_Nat_reprFast(v___x_3628_);
v___x_3630_ = lean_string_append(v___x_3627_, v___x_3629_);
lean_dec_ref(v___x_3629_);
v___y_3615_ = v___x_3630_;
goto v___jp_3614_;
}
v___jp_3614_:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3616_ = lean_string_append(v___x_3613_, v___y_3615_);
lean_dec_ref(v___y_3615_);
v___x_3617_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3618_ = lean_string_append(v___x_3616_, v___x_3617_);
v___x_3619_ = lean_string_append(v___x_3533_, v___x_3618_);
lean_dec_ref(v___x_3618_);
return v___x_3619_;
}
}
}
else
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
lean_dec(v_val_3582_);
lean_dec(v_val_3581_);
v___x_3631_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3632_ = lean_string_append(v___x_3533_, v___x_3631_);
return v___x_3632_;
}
}
}
v___jp_3534_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3537_ = lean_string_append(v___y_3535_, v___y_3536_);
lean_dec_ref(v___y_3536_);
v___x_3538_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3539_ = lean_string_append(v___x_3537_, v___x_3538_);
v___x_3540_ = lean_string_append(v___x_3533_, v___x_3539_);
lean_dec_ref(v___x_3539_);
return v___x_3540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1(lean_object* v___x_3633_, lean_object* v_x_3634_){
_start:
{
lean_object* v_fst_3635_; lean_object* v_constraint_3636_; lean_object* v_coeffs_3637_; lean_object* v_lowerBound_3638_; lean_object* v_upperBound_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___y_3644_; lean_object* v___y_3645_; 
v_fst_3635_ = lean_ctor_get(v_x_3634_, 0);
lean_inc(v_fst_3635_);
lean_dec_ref(v_x_3634_);
v_constraint_3636_ = lean_ctor_get(v_fst_3635_, 1);
lean_inc_ref(v_constraint_3636_);
v_coeffs_3637_ = lean_ctor_get(v_fst_3635_, 0);
lean_inc(v_coeffs_3637_);
lean_dec(v_fst_3635_);
v_lowerBound_3638_ = lean_ctor_get(v_constraint_3636_, 0);
lean_inc(v_lowerBound_3638_);
v_upperBound_3639_ = lean_ctor_get(v_constraint_3636_, 1);
lean_inc(v_upperBound_3639_);
lean_dec_ref(v_constraint_3636_);
v___x_3640_ = l_List_toString___redArg(v___x_3633_, v_coeffs_3637_);
v___x_3641_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3642_ = lean_string_append(v___x_3640_, v___x_3641_);
if (lean_obj_tag(v_lowerBound_3638_) == 0)
{
if (lean_obj_tag(v_upperBound_3639_) == 0)
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3651_ = lean_string_append(v___x_3642_, v___x_3650_);
return v___x_3651_;
}
else
{
lean_object* v_val_3652_; lean_object* v___x_3653_; lean_object* v___y_3655_; lean_object* v_intZero_3660_; uint8_t v_isNeg_3661_; 
v_val_3652_ = lean_ctor_get(v_upperBound_3639_, 0);
lean_inc(v_val_3652_);
lean_dec_ref_known(v_upperBound_3639_, 1);
v___x_3653_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3660_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3661_ = lean_int_dec_lt(v_val_3652_, v_intZero_3660_);
if (v_isNeg_3661_ == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3663_; 
v_a_3662_ = lean_nat_abs(v_val_3652_);
lean_dec(v_val_3652_);
v___x_3663_ = l_Nat_reprFast(v_a_3662_);
v___y_3655_ = v___x_3663_;
goto v___jp_3654_;
}
else
{
lean_object* v_abs_3664_; lean_object* v_one_3665_; lean_object* v_a_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v_abs_3664_ = lean_nat_abs(v_val_3652_);
lean_dec(v_val_3652_);
v_one_3665_ = lean_unsigned_to_nat(1u);
v_a_3666_ = lean_nat_sub(v_abs_3664_, v_one_3665_);
lean_dec(v_abs_3664_);
v___x_3667_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3668_ = lean_nat_add(v_a_3666_, v_one_3665_);
lean_dec(v_a_3666_);
v___x_3669_ = l_Nat_reprFast(v___x_3668_);
v___x_3670_ = lean_string_append(v___x_3667_, v___x_3669_);
lean_dec_ref(v___x_3669_);
v___y_3655_ = v___x_3670_;
goto v___jp_3654_;
}
v___jp_3654_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3656_ = lean_string_append(v___x_3653_, v___y_3655_);
lean_dec_ref(v___y_3655_);
v___x_3657_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3658_ = lean_string_append(v___x_3656_, v___x_3657_);
v___x_3659_ = lean_string_append(v___x_3642_, v___x_3658_);
lean_dec_ref(v___x_3658_);
return v___x_3659_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3639_) == 0)
{
lean_object* v_val_3671_; lean_object* v___x_3672_; lean_object* v___y_3674_; lean_object* v_intZero_3679_; uint8_t v_isNeg_3680_; 
v_val_3671_ = lean_ctor_get(v_lowerBound_3638_, 0);
lean_inc(v_val_3671_);
lean_dec_ref_known(v_lowerBound_3638_, 1);
v___x_3672_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3679_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3680_ = lean_int_dec_lt(v_val_3671_, v_intZero_3679_);
if (v_isNeg_3680_ == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3682_; 
v_a_3681_ = lean_nat_abs(v_val_3671_);
lean_dec(v_val_3671_);
v___x_3682_ = l_Nat_reprFast(v_a_3681_);
v___y_3674_ = v___x_3682_;
goto v___jp_3673_;
}
else
{
lean_object* v_abs_3683_; lean_object* v_one_3684_; lean_object* v_a_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v_abs_3683_ = lean_nat_abs(v_val_3671_);
lean_dec(v_val_3671_);
v_one_3684_ = lean_unsigned_to_nat(1u);
v_a_3685_ = lean_nat_sub(v_abs_3683_, v_one_3684_);
lean_dec(v_abs_3683_);
v___x_3686_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3687_ = lean_nat_add(v_a_3685_, v_one_3684_);
lean_dec(v_a_3685_);
v___x_3688_ = l_Nat_reprFast(v___x_3687_);
v___x_3689_ = lean_string_append(v___x_3686_, v___x_3688_);
lean_dec_ref(v___x_3688_);
v___y_3674_ = v___x_3689_;
goto v___jp_3673_;
}
v___jp_3673_:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3675_ = lean_string_append(v___x_3672_, v___y_3674_);
lean_dec_ref(v___y_3674_);
v___x_3676_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3677_ = lean_string_append(v___x_3675_, v___x_3676_);
v___x_3678_ = lean_string_append(v___x_3642_, v___x_3677_);
lean_dec_ref(v___x_3677_);
return v___x_3678_;
}
}
else
{
lean_object* v_val_3690_; lean_object* v_val_3691_; uint8_t v___x_3692_; 
v_val_3690_ = lean_ctor_get(v_lowerBound_3638_, 0);
lean_inc(v_val_3690_);
lean_dec_ref_known(v_lowerBound_3638_, 1);
v_val_3691_ = lean_ctor_get(v_upperBound_3639_, 0);
lean_inc(v_val_3691_);
lean_dec_ref_known(v_upperBound_3639_, 1);
v___x_3692_ = lean_int_dec_lt(v_val_3691_, v_val_3690_);
if (v___x_3692_ == 0)
{
uint8_t v___x_3693_; 
v___x_3693_ = lean_int_dec_eq(v_val_3690_, v_val_3691_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3694_; lean_object* v___y_3696_; lean_object* v_intZero_3711_; uint8_t v_isNeg_3712_; 
v___x_3694_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3711_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3712_ = lean_int_dec_lt(v_val_3690_, v_intZero_3711_);
if (v_isNeg_3712_ == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3714_; 
v_a_3713_ = lean_nat_abs(v_val_3690_);
lean_dec(v_val_3690_);
v___x_3714_ = l_Nat_reprFast(v_a_3713_);
v___y_3696_ = v___x_3714_;
goto v___jp_3695_;
}
else
{
lean_object* v_abs_3715_; lean_object* v_one_3716_; lean_object* v_a_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v_abs_3715_ = lean_nat_abs(v_val_3690_);
lean_dec(v_val_3690_);
v_one_3716_ = lean_unsigned_to_nat(1u);
v_a_3717_ = lean_nat_sub(v_abs_3715_, v_one_3716_);
lean_dec(v_abs_3715_);
v___x_3718_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3719_ = lean_nat_add(v_a_3717_, v_one_3716_);
lean_dec(v_a_3717_);
v___x_3720_ = l_Nat_reprFast(v___x_3719_);
v___x_3721_ = lean_string_append(v___x_3718_, v___x_3720_);
lean_dec_ref(v___x_3720_);
v___y_3696_ = v___x_3721_;
goto v___jp_3695_;
}
v___jp_3695_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v_intZero_3700_; uint8_t v_isNeg_3701_; 
v___x_3697_ = lean_string_append(v___x_3694_, v___y_3696_);
lean_dec_ref(v___y_3696_);
v___x_3698_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3699_ = lean_string_append(v___x_3697_, v___x_3698_);
v_intZero_3700_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3701_ = lean_int_dec_lt(v_val_3691_, v_intZero_3700_);
if (v_isNeg_3701_ == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3703_; 
v_a_3702_ = lean_nat_abs(v_val_3691_);
lean_dec(v_val_3691_);
v___x_3703_ = l_Nat_reprFast(v_a_3702_);
v___y_3644_ = v___x_3699_;
v___y_3645_ = v___x_3703_;
goto v___jp_3643_;
}
else
{
lean_object* v_abs_3704_; lean_object* v_one_3705_; lean_object* v_a_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v_abs_3704_ = lean_nat_abs(v_val_3691_);
lean_dec(v_val_3691_);
v_one_3705_ = lean_unsigned_to_nat(1u);
v_a_3706_ = lean_nat_sub(v_abs_3704_, v_one_3705_);
lean_dec(v_abs_3704_);
v___x_3707_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3708_ = lean_nat_add(v_a_3706_, v_one_3705_);
lean_dec(v_a_3706_);
v___x_3709_ = l_Nat_reprFast(v___x_3708_);
v___x_3710_ = lean_string_append(v___x_3707_, v___x_3709_);
lean_dec_ref(v___x_3709_);
v___y_3644_ = v___x_3699_;
v___y_3645_ = v___x_3710_;
goto v___jp_3643_;
}
}
}
else
{
lean_object* v___x_3722_; lean_object* v___y_3724_; lean_object* v_intZero_3729_; uint8_t v_isNeg_3730_; 
lean_dec(v_val_3691_);
v___x_3722_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3729_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3730_ = lean_int_dec_lt(v_val_3690_, v_intZero_3729_);
if (v_isNeg_3730_ == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3732_; 
v_a_3731_ = lean_nat_abs(v_val_3690_);
lean_dec(v_val_3690_);
v___x_3732_ = l_Nat_reprFast(v_a_3731_);
v___y_3724_ = v___x_3732_;
goto v___jp_3723_;
}
else
{
lean_object* v_abs_3733_; lean_object* v_one_3734_; lean_object* v_a_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v_abs_3733_ = lean_nat_abs(v_val_3690_);
lean_dec(v_val_3690_);
v_one_3734_ = lean_unsigned_to_nat(1u);
v_a_3735_ = lean_nat_sub(v_abs_3733_, v_one_3734_);
lean_dec(v_abs_3733_);
v___x_3736_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3737_ = lean_nat_add(v_a_3735_, v_one_3734_);
lean_dec(v_a_3735_);
v___x_3738_ = l_Nat_reprFast(v___x_3737_);
v___x_3739_ = lean_string_append(v___x_3736_, v___x_3738_);
lean_dec_ref(v___x_3738_);
v___y_3724_ = v___x_3739_;
goto v___jp_3723_;
}
v___jp_3723_:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3725_ = lean_string_append(v___x_3722_, v___y_3724_);
lean_dec_ref(v___y_3724_);
v___x_3726_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3727_ = lean_string_append(v___x_3725_, v___x_3726_);
v___x_3728_ = lean_string_append(v___x_3642_, v___x_3727_);
lean_dec_ref(v___x_3727_);
return v___x_3728_;
}
}
}
else
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_dec(v_val_3691_);
lean_dec(v_val_3690_);
v___x_3740_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3741_ = lean_string_append(v___x_3642_, v___x_3740_);
return v___x_3741_;
}
}
}
v___jp_3643_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3646_ = lean_string_append(v___y_3644_, v___y_3645_);
lean_dec_ref(v___y_3645_);
v___x_3647_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3648_ = lean_string_append(v___x_3646_, v___x_3647_);
v___x_3649_ = lean_string_append(v___x_3642_, v___x_3648_);
lean_dec_ref(v___x_3648_);
return v___x_3649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2(lean_object* v___f_3746_, lean_object* v___f_3747_, lean_object* v___f_3748_, lean_object* v_d_3749_){
_start:
{
lean_object* v_var_3750_; lean_object* v_irrelevant_3751_; lean_object* v_lowerBounds_3752_; lean_object* v_upperBounds_3753_; lean_object* v___x_3754_; lean_object* v_irrelevant_3755_; lean_object* v_lowerBounds_3756_; lean_object* v_upperBounds_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v_var_3750_ = lean_ctor_get(v_d_3749_, 0);
lean_inc(v_var_3750_);
v_irrelevant_3751_ = lean_ctor_get(v_d_3749_, 1);
lean_inc(v_irrelevant_3751_);
v_lowerBounds_3752_ = lean_ctor_get(v_d_3749_, 2);
lean_inc(v_lowerBounds_3752_);
v_upperBounds_3753_ = lean_ctor_get(v_d_3749_, 3);
lean_inc(v_upperBounds_3753_);
lean_dec_ref(v_d_3749_);
v___x_3754_ = lean_box(0);
v_irrelevant_3755_ = l_List_mapTR_loop___redArg(v___f_3746_, v_irrelevant_3751_, v___x_3754_);
lean_inc_ref(v___f_3747_);
v_lowerBounds_3756_ = l_List_mapTR_loop___redArg(v___f_3747_, v_lowerBounds_3752_, v___x_3754_);
v_upperBounds_3757_ = l_List_mapTR_loop___redArg(v___f_3747_, v_upperBounds_3753_, v___x_3754_);
v___x_3758_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0));
v___x_3759_ = l_Nat_reprFast(v_var_3750_);
v___x_3760_ = lean_string_append(v___x_3758_, v___x_3759_);
lean_dec_ref(v___x_3759_);
v___x_3761_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_3762_ = lean_string_append(v___x_3760_, v___x_3761_);
v___x_3763_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1));
lean_inc_ref_n(v___f_3748_, 2);
v___x_3764_ = l_List_toString___redArg(v___f_3748_, v_irrelevant_3755_);
v___x_3765_ = lean_string_append(v___x_3763_, v___x_3764_);
lean_dec_ref(v___x_3764_);
v___x_3766_ = lean_string_append(v___x_3765_, v___x_3761_);
v___x_3767_ = lean_string_append(v___x_3762_, v___x_3766_);
lean_dec_ref(v___x_3766_);
v___x_3768_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2));
v___x_3769_ = l_List_toString___redArg(v___f_3748_, v_lowerBounds_3756_);
v___x_3770_ = lean_string_append(v___x_3768_, v___x_3769_);
lean_dec_ref(v___x_3769_);
v___x_3771_ = lean_string_append(v___x_3770_, v___x_3761_);
v___x_3772_ = lean_string_append(v___x_3767_, v___x_3771_);
lean_dec_ref(v___x_3771_);
v___x_3773_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3));
v___x_3774_ = l_List_toString___redArg(v___f_3748_, v_upperBounds_3757_);
v___x_3775_ = lean_string_append(v___x_3773_, v___x_3774_);
lean_dec_ref(v___x_3774_);
v___x_3776_ = lean_string_append(v___x_3772_, v___x_3775_);
lean_dec_ref(v___x_3775_);
return v___x_3776_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(lean_object* v_d_3787_){
_start:
{
lean_object* v_lowerBounds_3788_; lean_object* v_upperBounds_3789_; uint8_t v___x_3790_; 
v_lowerBounds_3788_ = lean_ctor_get(v_d_3787_, 2);
v_upperBounds_3789_ = lean_ctor_get(v_d_3787_, 3);
v___x_3790_ = l_List_isEmpty___redArg(v_lowerBounds_3788_);
if (v___x_3790_ == 0)
{
return v___x_3790_;
}
else
{
uint8_t v___x_3791_; 
v___x_3791_ = l_List_isEmpty___redArg(v_upperBounds_3789_);
return v___x_3791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty___boxed(lean_object* v_d_3792_){
_start:
{
uint8_t v_res_3793_; lean_object* v_r_3794_; 
v_res_3793_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v_d_3792_);
lean_dec_ref(v_d_3792_);
v_r_3794_ = lean_box(v_res_3793_);
return v_r_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(lean_object* v_d_3795_){
_start:
{
lean_object* v_lowerBounds_3796_; lean_object* v_upperBounds_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v_lowerBounds_3796_ = lean_ctor_get(v_d_3795_, 2);
v_upperBounds_3797_ = lean_ctor_get(v_d_3795_, 3);
v___x_3798_ = l_List_lengthTR___redArg(v_lowerBounds_3796_);
v___x_3799_ = l_List_lengthTR___redArg(v_upperBounds_3797_);
v___x_3800_ = lean_nat_mul(v___x_3798_, v___x_3799_);
lean_dec(v___x_3799_);
lean_dec(v___x_3798_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size___boxed(lean_object* v_d_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_d_3801_);
lean_dec_ref(v_d_3801_);
return v_res_3802_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(lean_object* v_d_3803_){
_start:
{
uint8_t v_lowerExact_3804_; 
v_lowerExact_3804_ = lean_ctor_get_uint8(v_d_3803_, sizeof(void*)*4);
if (v_lowerExact_3804_ == 0)
{
uint8_t v_upperExact_3805_; 
v_upperExact_3805_ = lean_ctor_get_uint8(v_d_3803_, sizeof(void*)*4 + 1);
return v_upperExact_3805_;
}
else
{
return v_lowerExact_3804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact___boxed(lean_object* v_d_3806_){
_start:
{
uint8_t v_res_3807_; lean_object* v_r_3808_; 
v_res_3807_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_d_3806_);
lean_dec_ref(v_d_3806_);
v_r_3808_ = lean_box(v_res_3807_);
return v_r_3808_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(lean_object* v_x_3809_, lean_object* v_x_3810_){
_start:
{
if (lean_obj_tag(v_x_3810_) == 0)
{
return v_x_3809_;
}
else
{
lean_object* v_head_3811_; lean_object* v_tail_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_head_3811_ = lean_ctor_get(v_x_3810_, 0);
v_tail_3812_ = lean_ctor_get(v_x_3810_, 1);
v___x_3813_ = lean_box(0);
v___x_3814_ = 1;
lean_inc(v_head_3811_);
v___x_3815_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3815_, 0, v_head_3811_);
lean_ctor_set(v___x_3815_, 1, v___x_3813_);
lean_ctor_set(v___x_3815_, 2, v___x_3813_);
lean_ctor_set(v___x_3815_, 3, v___x_3813_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*4, v___x_3814_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*4 + 1, v___x_3814_);
v___x_3816_ = lean_array_push(v_x_3809_, v___x_3815_);
v_x_3809_ = v___x_3816_;
v_x_3810_ = v_tail_3812_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2___boxed(lean_object* v_x_3818_, lean_object* v_x_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v_x_3818_, v_x_3819_);
lean_dec(v_x_3819_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object* v_upperBound_3821_, lean_object* v_b_3822_, lean_object* v___x_3823_, uint8_t v___x_3824_, lean_object* v_____r_3825_, lean_object* v_d_x27_3826_){
_start:
{
if (lean_obj_tag(v_upperBound_3821_) == 0)
{
lean_dec(v___x_3823_);
lean_dec_ref(v_b_3822_);
return v_d_x27_3826_;
}
else
{
lean_object* v_var_3827_; lean_object* v_irrelevant_3828_; lean_object* v_lowerBounds_3829_; lean_object* v_upperBounds_3830_; uint8_t v_lowerExact_3831_; uint8_t v_upperExact_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3847_; 
v_var_3827_ = lean_ctor_get(v_d_x27_3826_, 0);
v_irrelevant_3828_ = lean_ctor_get(v_d_x27_3826_, 1);
v_lowerBounds_3829_ = lean_ctor_get(v_d_x27_3826_, 2);
v_upperBounds_3830_ = lean_ctor_get(v_d_x27_3826_, 3);
v_lowerExact_3831_ = lean_ctor_get_uint8(v_d_x27_3826_, sizeof(void*)*4);
v_upperExact_3832_ = lean_ctor_get_uint8(v_d_x27_3826_, sizeof(void*)*4 + 1);
v_isSharedCheck_3847_ = !lean_is_exclusive(v_d_x27_3826_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3834_ = v_d_x27_3826_;
v_isShared_3835_ = v_isSharedCheck_3847_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_upperBounds_3830_);
lean_inc(v_lowerBounds_3829_);
lean_inc(v_irrelevant_3828_);
lean_inc(v_var_3827_);
lean_dec(v_d_x27_3826_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3847_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
lean_inc(v___x_3823_);
v___x_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3836_, 0, v_b_3822_);
lean_ctor_set(v___x_3836_, 1, v___x_3823_);
v___x_3837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3836_);
lean_ctor_set(v___x_3837_, 1, v_upperBounds_3830_);
if (v_upperExact_3832_ == 0)
{
lean_object* v___x_3839_; 
lean_dec(v___x_3823_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 3, v___x_3837_);
v___x_3839_ = v___x_3834_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_var_3827_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v_irrelevant_3828_);
lean_ctor_set(v_reuseFailAlloc_3840_, 2, v_lowerBounds_3829_);
lean_ctor_set(v_reuseFailAlloc_3840_, 3, v___x_3837_);
lean_ctor_set_uint8(v_reuseFailAlloc_3840_, sizeof(void*)*4, v_lowerExact_3831_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_ctor_set_uint8(v___x_3839_, sizeof(void*)*4 + 1, v___x_3824_);
return v___x_3839_;
}
}
else
{
lean_object* v___x_3841_; lean_object* v___x_3842_; uint8_t v___x_3843_; lean_object* v___x_3845_; 
v___x_3841_ = lean_nat_abs(v___x_3823_);
lean_dec(v___x_3823_);
v___x_3842_ = lean_unsigned_to_nat(1u);
v___x_3843_ = lean_nat_dec_eq(v___x_3841_, v___x_3842_);
lean_dec(v___x_3841_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 3, v___x_3837_);
v___x_3845_ = v___x_3834_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_var_3827_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v_irrelevant_3828_);
lean_ctor_set(v_reuseFailAlloc_3846_, 2, v_lowerBounds_3829_);
lean_ctor_set(v_reuseFailAlloc_3846_, 3, v___x_3837_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, sizeof(void*)*4, v_lowerExact_3831_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_ctor_set_uint8(v___x_3845_, sizeof(void*)*4 + 1, v___x_3843_);
return v___x_3845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0___boxed(lean_object* v_upperBound_3848_, lean_object* v_b_3849_, lean_object* v___x_3850_, lean_object* v___x_3851_, lean_object* v_____r_3852_, lean_object* v_d_x27_3853_){
_start:
{
uint8_t v___x_1956__boxed_3854_; lean_object* v_res_3855_; 
v___x_1956__boxed_3854_ = lean_unbox(v___x_3851_);
v_res_3855_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v_upperBound_3848_, v_b_3849_, v___x_3850_, v___x_1956__boxed_3854_, v_____r_3852_, v_d_x27_3853_);
lean_dec(v_upperBound_3848_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(lean_object* v_upperBound_3856_, lean_object* v_coeffs_3857_, lean_object* v_constraint_3858_, lean_object* v_b_3859_, lean_object* v_a_3860_, lean_object* v_b_3861_){
_start:
{
lean_object* v_a_3863_; uint8_t v___x_3867_; 
v___x_3867_ = lean_nat_dec_lt(v_a_3860_, v_upperBound_3856_);
if (v___x_3867_ == 0)
{
lean_dec(v_a_3860_);
lean_dec_ref(v_b_3859_);
lean_dec_ref(v_constraint_3858_);
return v_b_3861_;
}
else
{
lean_object* v___x_3868_; uint8_t v___x_3869_; 
v___x_3868_ = lean_array_get_size(v_b_3861_);
v___x_3869_ = lean_nat_dec_lt(v_a_3860_, v___x_3868_);
if (v___x_3869_ == 0)
{
v_a_3863_ = v_b_3861_;
goto v___jp_3862_;
}
else
{
lean_object* v___x_3870_; lean_object* v_v_3871_; lean_object* v___x_3872_; lean_object* v_xs_x27_3873_; lean_object* v___y_3875_; lean_object* v___x_3877_; uint8_t v___x_3878_; 
lean_inc(v_a_3860_);
v___x_3870_ = l_Lean_Omega_IntList_get(v_coeffs_3857_, v_a_3860_);
v_v_3871_ = lean_array_fget(v_b_3861_, v_a_3860_);
v___x_3872_ = lean_box(0);
v_xs_x27_3873_ = lean_array_fset(v_b_3861_, v_a_3860_, v___x_3872_);
v___x_3877_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3878_ = lean_int_dec_eq(v___x_3870_, v___x_3877_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3879_; lean_object* v_lowerBound_3880_; 
lean_inc_ref(v_constraint_3858_);
lean_inc(v___x_3870_);
v___x_3879_ = l_Lean_Omega_Constraint_scale(v___x_3870_, v_constraint_3858_);
v_lowerBound_3880_ = lean_ctor_get(v___x_3879_, 0);
if (lean_obj_tag(v_lowerBound_3880_) == 0)
{
lean_object* v_upperBound_3881_; lean_object* v___x_3882_; 
v_upperBound_3881_ = lean_ctor_get(v___x_3879_, 1);
lean_inc(v_upperBound_3881_);
lean_dec_ref(v___x_3879_);
lean_inc_ref(v_b_3859_);
v___x_3882_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v_upperBound_3881_, v_b_3859_, v___x_3870_, v___x_3878_, v___x_3872_, v_v_3871_);
lean_dec(v_upperBound_3881_);
v___y_3875_ = v___x_3882_;
goto v___jp_3874_;
}
else
{
lean_object* v_upperBound_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3910_; 
v_upperBound_3883_ = lean_ctor_get(v___x_3879_, 1);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3910_ == 0)
{
lean_object* v_unused_3911_; 
v_unused_3911_ = lean_ctor_get(v___x_3879_, 0);
lean_dec(v_unused_3911_);
v___x_3885_ = v___x_3879_;
v_isShared_3886_ = v_isSharedCheck_3910_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_upperBound_3883_);
lean_dec(v___x_3879_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3910_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v_var_3887_; lean_object* v_irrelevant_3888_; lean_object* v_lowerBounds_3889_; lean_object* v_upperBounds_3890_; uint8_t v_lowerExact_3891_; uint8_t v_upperExact_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3909_; 
v_var_3887_ = lean_ctor_get(v_v_3871_, 0);
v_irrelevant_3888_ = lean_ctor_get(v_v_3871_, 1);
v_lowerBounds_3889_ = lean_ctor_get(v_v_3871_, 2);
v_upperBounds_3890_ = lean_ctor_get(v_v_3871_, 3);
v_lowerExact_3891_ = lean_ctor_get_uint8(v_v_3871_, sizeof(void*)*4);
v_upperExact_3892_ = lean_ctor_get_uint8(v_v_3871_, sizeof(void*)*4 + 1);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_v_3871_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3894_ = v_v_3871_;
v_isShared_3895_ = v_isSharedCheck_3909_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_upperBounds_3890_);
lean_inc(v_lowerBounds_3889_);
lean_inc(v_irrelevant_3888_);
lean_inc(v_var_3887_);
lean_dec(v_v_3871_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3909_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
lean_inc(v___x_3870_);
lean_inc_ref(v_b_3859_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 1, v___x_3870_);
lean_ctor_set(v___x_3885_, 0, v_b_3859_);
v___x_3897_ = v___x_3885_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_b_3859_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v___x_3870_);
v___x_3897_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
lean_object* v___x_3898_; uint8_t v___y_3900_; 
v___x_3898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
lean_ctor_set(v___x_3898_, 1, v_lowerBounds_3889_);
if (v_lowerExact_3891_ == 0)
{
v___y_3900_ = v___x_3878_;
goto v___jp_3899_;
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; 
v___x_3905_ = lean_nat_abs(v___x_3870_);
v___x_3906_ = lean_unsigned_to_nat(1u);
v___x_3907_ = lean_nat_dec_eq(v___x_3905_, v___x_3906_);
lean_dec(v___x_3905_);
v___y_3900_ = v___x_3907_;
goto v___jp_3899_;
}
v___jp_3899_:
{
lean_object* v___x_3902_; 
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 2, v___x_3898_);
v___x_3902_ = v___x_3894_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_var_3887_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_irrelevant_3888_);
lean_ctor_set(v_reuseFailAlloc_3904_, 2, v___x_3898_);
lean_ctor_set(v_reuseFailAlloc_3904_, 3, v_upperBounds_3890_);
lean_ctor_set_uint8(v_reuseFailAlloc_3904_, sizeof(void*)*4 + 1, v_upperExact_3892_);
v___x_3902_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3903_; 
lean_ctor_set_uint8(v___x_3902_, sizeof(void*)*4, v___y_3900_);
lean_inc_ref(v_b_3859_);
v___x_3903_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v_upperBound_3883_, v_b_3859_, v___x_3870_, v___x_3878_, v___x_3872_, v___x_3902_);
lean_dec(v_upperBound_3883_);
v___y_3875_ = v___x_3903_;
goto v___jp_3874_;
}
}
}
}
}
}
}
else
{
lean_object* v_var_3912_; lean_object* v_irrelevant_3913_; lean_object* v_lowerBounds_3914_; lean_object* v_upperBounds_3915_; uint8_t v_lowerExact_3916_; uint8_t v_upperExact_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3925_; 
lean_dec(v___x_3870_);
v_var_3912_ = lean_ctor_get(v_v_3871_, 0);
v_irrelevant_3913_ = lean_ctor_get(v_v_3871_, 1);
v_lowerBounds_3914_ = lean_ctor_get(v_v_3871_, 2);
v_upperBounds_3915_ = lean_ctor_get(v_v_3871_, 3);
v_lowerExact_3916_ = lean_ctor_get_uint8(v_v_3871_, sizeof(void*)*4);
v_upperExact_3917_ = lean_ctor_get_uint8(v_v_3871_, sizeof(void*)*4 + 1);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_v_3871_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3919_ = v_v_3871_;
v_isShared_3920_ = v_isSharedCheck_3925_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_upperBounds_3915_);
lean_inc(v_lowerBounds_3914_);
lean_inc(v_irrelevant_3913_);
lean_inc(v_var_3912_);
lean_dec(v_v_3871_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3925_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3921_; lean_object* v___x_3923_; 
lean_inc_ref(v_b_3859_);
v___x_3921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3921_, 0, v_b_3859_);
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
v___y_3875_ = v___x_3923_;
goto v___jp_3874_;
}
}
}
v___jp_3874_:
{
lean_object* v___x_3876_; 
v___x_3876_ = lean_array_fset(v_xs_x27_3873_, v_a_3860_, v___y_3875_);
v_a_3863_ = v___x_3876_;
goto v___jp_3862_;
}
}
}
v___jp_3862_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = lean_unsigned_to_nat(1u);
v___x_3865_ = lean_nat_add(v_a_3860_, v___x_3864_);
lean_dec(v_a_3860_);
v_a_3860_ = v___x_3865_;
v_b_3861_ = v_a_3863_;
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
lean_object* v_snd_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4234_; 
v_snd_4164_ = lean_ctor_get(v_b_4131_, 1);
v_isSharedCheck_4234_ = !lean_is_exclusive(v_b_4131_);
if (v_isSharedCheck_4234_ == 0)
{
lean_object* v_unused_4235_; 
v_unused_4235_ = lean_ctor_get(v_b_4131_, 0);
lean_dec(v_unused_4235_);
v___x_4166_ = v_b_4131_;
v_isShared_4167_ = v_isSharedCheck_4234_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_snd_4164_);
lean_dec(v_b_4131_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4234_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v_snd_4168_; lean_object* v_fst_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4233_; 
v_snd_4168_ = lean_ctor_get(v_snd_4164_, 1);
v_fst_4169_ = lean_ctor_get(v_snd_4164_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v_snd_4164_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4171_ = v_snd_4164_;
v_isShared_4172_ = v_isSharedCheck_4233_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_snd_4168_);
lean_inc(v_fst_4169_);
lean_dec(v_snd_4164_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4233_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v_fst_4173_; lean_object* v_snd_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4232_; 
v_fst_4173_ = lean_ctor_get(v_snd_4168_, 0);
v_snd_4174_ = lean_ctor_get(v_snd_4168_, 1);
v_isSharedCheck_4232_ = !lean_is_exclusive(v_snd_4168_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4176_ = v_snd_4168_;
v_isShared_4177_ = v_isSharedCheck_4232_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_snd_4174_);
lean_inc(v_fst_4173_);
lean_dec(v_snd_4168_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4232_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4178_; lean_object* v_bestIdx_4189_; lean_object* v_cls_4190_; lean_object* v___x_4191_; uint8_t v___x_4195_; lean_object* v___x_4196_; uint8_t v___x_4197_; 
v___x_4178_ = lean_box(0);
v_bestIdx_4189_ = lean_unsigned_to_nat(0u);
v_cls_4190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4191_ = lean_array_fget_borrowed(v___y_4129_, v_a_4130_);
v___x_4195_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4191_);
v___x_4196_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4191_);
v___x_4197_ = lean_nat_dec_eq(v___x_4196_, v_bestIdx_4189_);
if (v___x_4197_ == 0)
{
uint8_t v___x_4231_; 
v___x_4231_ = lean_unbox(v_snd_4174_);
if (v___x_4231_ == 0)
{
if (v___x_4195_ == 0)
{
goto v___jp_4228_;
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
goto v___jp_4228_;
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
uint8_t v___x_4227_; 
v___x_4227_ = lean_nat_dec_lt(v___x_4196_, v_fst_4173_);
if (v___x_4227_ == 0)
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
v___jp_4228_:
{
if (v___x_4195_ == 0)
{
uint8_t v___x_4229_; 
v___x_4229_ = lean_unbox(v_snd_4174_);
if (v___x_4229_ == 0)
{
goto v___jp_4226_;
}
else
{
lean_dec(v___x_4196_);
goto v___jp_4179_;
}
}
else
{
uint8_t v___x_4230_; 
v___x_4230_ = lean_unbox(v_snd_4174_);
if (v___x_4230_ == 0)
{
lean_dec(v___x_4196_);
goto v___jp_4179_;
}
else
{
goto v___jp_4226_;
}
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___boxed(lean_object* v_upperBound_4236_, lean_object* v___y_4237_, lean_object* v_a_4238_, lean_object* v_b_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4236_, v___y_4237_, v_a_4238_, v_b_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec_ref(v___y_4237_);
lean_dec(v_upperBound_4236_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(lean_object* v_as_4246_, size_t v_i_4247_, size_t v_stop_4248_, lean_object* v_b_4249_){
_start:
{
lean_object* v___y_4251_; uint8_t v___x_4255_; 
v___x_4255_ = lean_usize_dec_eq(v_i_4247_, v_stop_4248_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4256_; uint8_t v___x_4257_; 
v___x_4256_ = lean_array_uget_borrowed(v_as_4246_, v_i_4247_);
v___x_4257_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v___x_4256_);
if (v___x_4257_ == 0)
{
lean_object* v___x_4258_; 
lean_inc(v___x_4256_);
v___x_4258_ = lean_array_push(v_b_4249_, v___x_4256_);
v___y_4251_ = v___x_4258_;
goto v___jp_4250_;
}
else
{
v___y_4251_ = v_b_4249_;
goto v___jp_4250_;
}
}
else
{
return v_b_4249_;
}
v___jp_4250_:
{
size_t v___x_4252_; size_t v___x_4253_; 
v___x_4252_ = ((size_t)1ULL);
v___x_4253_ = lean_usize_add(v_i_4247_, v___x_4252_);
v_i_4247_ = v___x_4253_;
v_b_4249_ = v___y_4251_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___boxed(lean_object* v_as_4259_, lean_object* v_i_4260_, lean_object* v_stop_4261_, lean_object* v_b_4262_){
_start:
{
size_t v_i_boxed_4263_; size_t v_stop_boxed_4264_; lean_object* v_res_4265_; 
v_i_boxed_4263_ = lean_unbox_usize(v_i_4260_);
lean_dec(v_i_4260_);
v_stop_boxed_4264_ = lean_unbox_usize(v_stop_4261_);
lean_dec(v_stop_4261_);
v_res_4265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_as_4259_, v_i_boxed_4263_, v_stop_boxed_4264_, v_b_4262_);
lean_dec_ref(v_as_4259_);
return v_res_4265_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2(void){
_start:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4269_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__1));
v___x_4270_ = l_Lean_MessageData_ofFormat(v___x_4269_);
return v___x_4270_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4271_ = lean_box(1);
v___x_4272_ = l_Lean_MessageData_ofFormat(v___x_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(lean_object* v_a_4274_, lean_object* v_a_4275_){
_start:
{
if (lean_obj_tag(v_a_4274_) == 0)
{
lean_object* v___x_4276_; 
v___x_4276_ = l_List_reverse___redArg(v_a_4275_);
return v___x_4276_;
}
else
{
lean_object* v_head_4277_; lean_object* v_snd_4278_; lean_object* v_tail_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4326_; 
v_head_4277_ = lean_ctor_get(v_a_4274_, 0);
lean_inc(v_head_4277_);
v_snd_4278_ = lean_ctor_get(v_head_4277_, 1);
lean_inc(v_snd_4278_);
v_tail_4279_ = lean_ctor_get(v_a_4274_, 1);
v_isSharedCheck_4326_ = !lean_is_exclusive(v_a_4274_);
if (v_isSharedCheck_4326_ == 0)
{
lean_object* v_unused_4327_; 
v_unused_4327_ = lean_ctor_get(v_a_4274_, 0);
lean_dec(v_unused_4327_);
v___x_4281_ = v_a_4274_;
v_isShared_4282_ = v_isSharedCheck_4326_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_tail_4279_);
lean_dec(v_a_4274_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4326_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v_fst_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4324_; 
v_fst_4283_ = lean_ctor_get(v_head_4277_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v_head_4277_);
if (v_isSharedCheck_4324_ == 0)
{
lean_object* v_unused_4325_; 
v_unused_4325_ = lean_ctor_get(v_head_4277_, 1);
lean_dec(v_unused_4325_);
v___x_4285_ = v_head_4277_;
v_isShared_4286_ = v_isSharedCheck_4324_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_fst_4283_);
lean_dec(v_head_4277_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4324_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v_fst_4287_; lean_object* v_snd_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4323_; 
v_fst_4287_ = lean_ctor_get(v_snd_4278_, 0);
v_snd_4288_ = lean_ctor_get(v_snd_4278_, 1);
v_isSharedCheck_4323_ = !lean_is_exclusive(v_snd_4278_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4290_ = v_snd_4278_;
v_isShared_4291_ = v_isSharedCheck_4323_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_snd_4288_);
lean_inc(v_fst_4287_);
lean_dec(v_snd_4278_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4323_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4297_; 
v___x_4292_ = l_Nat_reprFast(v_fst_4283_);
v___x_4293_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4292_);
v___x_4294_ = l_Lean_MessageData_ofFormat(v___x_4293_);
v___x_4295_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2);
if (v_isShared_4291_ == 0)
{
lean_ctor_set_tag(v___x_4290_, 7);
lean_ctor_set(v___x_4290_, 1, v___x_4295_);
lean_ctor_set(v___x_4290_, 0, v___x_4294_);
v___x_4297_ = v___x_4290_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4294_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v___x_4295_);
v___x_4297_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
lean_object* v___x_4298_; lean_object* v___x_4300_; 
v___x_4298_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3);
if (v_isShared_4286_ == 0)
{
lean_ctor_set_tag(v___x_4285_, 7);
lean_ctor_set(v___x_4285_, 1, v___x_4298_);
lean_ctor_set(v___x_4285_, 0, v___x_4297_);
v___x_4300_ = v___x_4285_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4297_);
lean_ctor_set(v_reuseFailAlloc_4321_, 1, v___x_4298_);
v___x_4300_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___y_4307_; uint8_t v___x_4318_; 
v___x_4301_ = l_Nat_reprFast(v_fst_4287_);
v___x_4302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4301_);
v___x_4303_ = l_Lean_MessageData_ofFormat(v___x_4302_);
v___x_4304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4303_);
lean_ctor_set(v___x_4304_, 1, v___x_4295_);
v___x_4305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4304_);
lean_ctor_set(v___x_4305_, 1, v___x_4298_);
v___x_4318_ = lean_unbox(v_snd_4288_);
lean_dec(v_snd_4288_);
if (v___x_4318_ == 0)
{
lean_object* v___x_4319_; 
v___x_4319_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__4));
v___y_4307_ = v___x_4319_;
goto v___jp_4306_;
}
else
{
lean_object* v___x_4320_; 
v___x_4320_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4));
v___y_4307_ = v___x_4320_;
goto v___jp_4306_;
}
v___jp_4306_:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4315_; 
lean_inc_ref(v___y_4307_);
v___x_4308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4308_, 0, v___y_4307_);
v___x_4309_ = l_Lean_MessageData_ofFormat(v___x_4308_);
v___x_4310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4305_);
lean_ctor_set(v___x_4310_, 1, v___x_4309_);
v___x_4311_ = l_Lean_MessageData_paren(v___x_4310_);
v___x_4312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4300_);
lean_ctor_set(v___x_4312_, 1, v___x_4311_);
v___x_4313_ = l_Lean_MessageData_paren(v___x_4312_);
if (v_isShared_4282_ == 0)
{
lean_ctor_set(v___x_4281_, 1, v_a_4275_);
lean_ctor_set(v___x_4281_, 0, v___x_4313_);
v___x_4315_ = v___x_4281_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v___x_4313_);
lean_ctor_set(v_reuseFailAlloc_4317_, 1, v_a_4275_);
v___x_4315_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
v_a_4274_ = v_tail_4279_;
v_a_4275_ = v___x_4315_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(size_t v_sz_4328_, size_t v_i_4329_, lean_object* v_bs_4330_){
_start:
{
uint8_t v___x_4331_; 
v___x_4331_ = lean_usize_dec_lt(v_i_4329_, v_sz_4328_);
if (v___x_4331_ == 0)
{
return v_bs_4330_;
}
else
{
lean_object* v_v_4332_; lean_object* v_var_4333_; lean_object* v___x_4334_; lean_object* v_bs_x27_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; size_t v___x_4341_; size_t v___x_4342_; lean_object* v___x_4343_; 
v_v_4332_ = lean_array_uget(v_bs_4330_, v_i_4329_);
v_var_4333_ = lean_ctor_get(v_v_4332_, 0);
lean_inc(v_var_4333_);
v___x_4334_ = lean_unsigned_to_nat(0u);
v_bs_x27_4335_ = lean_array_uset(v_bs_4330_, v_i_4329_, v___x_4334_);
v___x_4336_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_v_4332_);
v___x_4337_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_v_4332_);
lean_dec(v_v_4332_);
v___x_4338_ = lean_box(v___x_4337_);
v___x_4339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4336_);
lean_ctor_set(v___x_4339_, 1, v___x_4338_);
v___x_4340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4340_, 0, v_var_4333_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_4341_ = ((size_t)1ULL);
v___x_4342_ = lean_usize_add(v_i_4329_, v___x_4341_);
v___x_4343_ = lean_array_uset(v_bs_x27_4335_, v_i_4329_, v___x_4340_);
v_i_4329_ = v___x_4342_;
v_bs_4330_ = v___x_4343_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___boxed(lean_object* v_sz_4345_, lean_object* v_i_4346_, lean_object* v_bs_4347_){
_start:
{
size_t v_sz_boxed_4348_; size_t v_i_boxed_4349_; lean_object* v_res_4350_; 
v_sz_boxed_4348_ = lean_unbox_usize(v_sz_4345_);
lean_dec(v_sz_4345_);
v_i_boxed_4349_ = lean_unbox_usize(v_i_4346_);
lean_dec(v_i_4346_);
v_res_4350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_boxed_4348_, v_i_boxed_4349_, v_bs_4347_);
return v_res_4350_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1(void){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4352_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0));
v___x_4353_ = l_Lean_stringToMessageData(v___x_4352_);
return v___x_4353_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4(void){
_start:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4357_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3));
v___x_4358_ = l_Lean_stringToMessageData(v___x_4357_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(lean_object* v_data_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_){
_start:
{
lean_object* v___x_4365_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v_bestIdx_4371_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4499_; lean_object* v___x_4523_; lean_object* v___x_4524_; uint8_t v___x_4525_; 
v___x_4365_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default));
v_bestIdx_4371_ = lean_unsigned_to_nat(0u);
v___x_4523_ = lean_array_get_size(v_data_4359_);
v___x_4524_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_4525_ = lean_nat_dec_lt(v_bestIdx_4371_, v___x_4523_);
if (v___x_4525_ == 0)
{
v___y_4499_ = v___x_4524_;
goto v___jp_4498_;
}
else
{
size_t v___x_4526_; size_t v___x_4527_; lean_object* v___x_4528_; 
v___x_4526_ = ((size_t)0ULL);
v___x_4527_ = lean_usize_of_nat(v___x_4523_);
v___x_4528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4359_, v___x_4526_, v___x_4527_, v___x_4524_);
v___y_4499_ = v___x_4528_;
goto v___jp_4498_;
}
v___jp_4366_:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4369_ = lean_array_get(v___x_4365_, v___y_4367_, v___y_4368_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
v___x_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4369_);
return v___x_4370_;
}
v___jp_4372_:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; uint8_t v___x_4382_; 
v___x_4380_ = lean_array_get_borrowed(v___x_4365_, v___y_4373_, v_bestIdx_4371_);
v___x_4381_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4380_);
v___x_4382_ = lean_nat_dec_eq(v___x_4381_, v_bestIdx_4371_);
if (v___x_4382_ == 0)
{
lean_object* v___x_4383_; lean_object* v___x_4384_; uint8_t v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4383_ = lean_unsigned_to_nat(1u);
v___x_4384_ = lean_array_get_size(v___y_4373_);
v___x_4385_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4380_);
v___x_4386_ = lean_box(0);
v___x_4387_ = lean_box(v___x_4385_);
v___x_4388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4381_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
v___x_4389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4389_, 0, v_bestIdx_4371_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
v___x_4390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4386_);
lean_ctor_set(v___x_4390_, 1, v___x_4389_);
v___x_4391_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v___x_4384_, v___y_4373_, v___x_4383_, v___x_4390_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4446_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4394_ = v___x_4391_;
v_isShared_4395_ = v_isSharedCheck_4446_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4391_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4446_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v_fst_4396_; 
v_fst_4396_ = lean_ctor_get(v_a_4392_, 0);
if (lean_obj_tag(v_fst_4396_) == 0)
{
lean_object* v_snd_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4440_; 
lean_del_object(v___x_4394_);
v_snd_4397_ = lean_ctor_get(v_a_4392_, 1);
v_isSharedCheck_4440_ = !lean_is_exclusive(v_a_4392_);
if (v_isSharedCheck_4440_ == 0)
{
lean_object* v_unused_4441_; 
v_unused_4441_ = lean_ctor_get(v_a_4392_, 0);
lean_dec(v_unused_4441_);
v___x_4399_ = v_a_4392_;
v_isShared_4400_ = v_isSharedCheck_4440_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_snd_4397_);
lean_dec(v_a_4392_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4440_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v_fst_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4438_; 
v_fst_4401_ = lean_ctor_get(v_snd_4397_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v_snd_4397_);
if (v_isSharedCheck_4438_ == 0)
{
lean_object* v_unused_4439_; 
v_unused_4439_ = lean_ctor_get(v_snd_4397_, 1);
lean_dec(v_unused_4439_);
v___x_4403_ = v_snd_4397_;
v_isShared_4404_ = v_isSharedCheck_4438_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_fst_4401_);
lean_dec(v_snd_4397_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4438_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4405_; 
lean_inc_ref(v___y_4374_);
lean_inc(v___y_4379_);
lean_inc_ref(v___y_4378_);
lean_inc(v___y_4377_);
lean_inc_ref(v___y_4376_);
v___x_4405_ = lean_apply_5(v___y_4374_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, lean_box(0));
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; uint8_t v___x_4407_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref_known(v___x_4405_, 1);
v___x_4407_ = lean_unbox(v_a_4406_);
lean_dec(v_a_4406_);
if (v___x_4407_ == 0)
{
lean_del_object(v___x_4403_);
lean_del_object(v___x_4399_);
lean_dec(v___y_4375_);
v___y_4367_ = v___y_4373_;
v___y_4368_ = v_fst_4401_;
goto v___jp_4366_;
}
else
{
lean_object* v___x_4408_; lean_object* v_var_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4415_; 
v___x_4408_ = lean_array_get_borrowed(v___x_4365_, v___y_4373_, v_fst_4401_);
v_var_4409_ = lean_ctor_get(v___x_4408_, 0);
v___x_4410_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4409_);
v___x_4411_ = l_Nat_reprFast(v_var_4409_);
v___x_4412_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
v___x_4413_ = l_Lean_MessageData_ofFormat(v___x_4412_);
if (v_isShared_4404_ == 0)
{
lean_ctor_set_tag(v___x_4403_, 7);
lean_ctor_set(v___x_4403_, 1, v___x_4413_);
lean_ctor_set(v___x_4403_, 0, v___x_4410_);
v___x_4415_ = v___x_4403_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4410_);
lean_ctor_set(v_reuseFailAlloc_4429_, 1, v___x_4413_);
v___x_4415_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_object* v___x_4416_; lean_object* v___x_4418_; 
v___x_4416_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
if (v_isShared_4400_ == 0)
{
lean_ctor_set_tag(v___x_4399_, 7);
lean_ctor_set(v___x_4399_, 1, v___x_4416_);
lean_ctor_set(v___x_4399_, 0, v___x_4415_);
v___x_4418_ = v___x_4399_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v___x_4415_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v___x_4416_);
v___x_4418_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v___x_4419_; 
v___x_4419_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4375_, v___x_4418_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_dec_ref_known(v___x_4419_, 1);
v___y_4367_ = v___y_4373_;
v___y_4368_ = v_fst_4401_;
goto v___jp_4366_;
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
lean_dec(v_fst_4401_);
lean_dec_ref(v___y_4373_);
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4419_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4419_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_del_object(v___x_4403_);
lean_dec(v_fst_4401_);
lean_del_object(v___x_4399_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4373_);
v_a_4430_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4405_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4405_);
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
}
}
else
{
lean_object* v_val_4442_; lean_object* v___x_4444_; 
lean_inc_ref(v_fst_4396_);
lean_dec(v_a_4392_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4373_);
v_val_4442_ = lean_ctor_get(v_fst_4396_, 0);
lean_inc(v_val_4442_);
lean_dec_ref_known(v_fst_4396_, 1);
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 0, v_val_4442_);
v___x_4444_ = v___x_4394_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_val_4442_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4373_);
v_a_4447_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4391_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4391_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
else
{
lean_object* v___x_4455_; 
lean_inc(v___x_4380_);
lean_dec(v___x_4381_);
lean_dec_ref(v___y_4373_);
lean_inc_ref(v___y_4374_);
lean_inc(v___y_4379_);
lean_inc_ref(v___y_4378_);
lean_inc(v___y_4377_);
lean_inc_ref(v___y_4376_);
v___x_4455_ = lean_apply_5(v___y_4374_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, lean_box(0));
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4489_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4458_ = v___x_4455_;
v_isShared_4459_ = v_isSharedCheck_4489_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4455_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4489_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
uint8_t v___x_4460_; 
v___x_4460_ = lean_unbox(v_a_4456_);
lean_dec(v_a_4456_);
if (v___x_4460_ == 0)
{
lean_object* v___x_4462_; 
lean_dec(v___y_4375_);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 0, v___x_4380_);
v___x_4462_ = v___x_4458_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v___x_4380_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
else
{
lean_object* v_var_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
lean_del_object(v___x_4458_);
v_var_4464_ = lean_ctor_get(v___x_4380_, 0);
v___x_4465_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4464_);
v___x_4466_ = l_Nat_reprFast(v_var_4464_);
v___x_4467_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4466_);
v___x_4468_ = l_Lean_MessageData_ofFormat(v___x_4467_);
v___x_4469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4465_);
lean_ctor_set(v___x_4469_, 1, v___x_4468_);
v___x_4470_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
v___x_4471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4469_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
v___x_4472_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4375_, v___x_4471_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4479_; 
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4479_ == 0)
{
lean_object* v_unused_4480_; 
v_unused_4480_ = lean_ctor_get(v___x_4472_, 0);
lean_dec(v_unused_4480_);
v___x_4474_ = v___x_4472_;
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
else
{
lean_dec(v___x_4472_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4477_; 
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 0, v___x_4380_);
v___x_4477_ = v___x_4474_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v___x_4380_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
lean_dec(v___x_4380_);
v_a_4481_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4472_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4472_);
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
}
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
lean_dec(v___x_4380_);
lean_dec(v___y_4375_);
v_a_4490_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4455_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4455_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
v___jp_4498_:
{
lean_object* v_cls_4500_; lean_object* v___f_4501_; lean_object* v___x_4502_; lean_object* v_a_4503_; uint8_t v___x_4504_; 
v_cls_4500_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___f_4501_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2));
v___x_4502_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4500_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_);
v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
lean_inc(v_a_4503_);
lean_dec_ref(v___x_4502_);
v___x_4504_ = lean_unbox(v_a_4503_);
lean_dec(v_a_4503_);
if (v___x_4504_ == 0)
{
v___y_4373_ = v___y_4499_;
v___y_4374_ = v___f_4501_;
v___y_4375_ = v_cls_4500_;
v___y_4376_ = v_a_4360_;
v___y_4377_ = v_a_4361_;
v___y_4378_ = v_a_4362_;
v___y_4379_ = v_a_4363_;
goto v___jp_4372_;
}
else
{
lean_object* v___x_4505_; size_t v_sz_4506_; size_t v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4505_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4);
v_sz_4506_ = lean_array_size(v___y_4499_);
v___x_4507_ = ((size_t)0ULL);
lean_inc_ref(v___y_4499_);
v___x_4508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_4506_, v___x_4507_, v___y_4499_);
v___x_4509_ = lean_array_to_list(v___x_4508_);
v___x_4510_ = lean_box(0);
v___x_4511_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v___x_4509_, v___x_4510_);
v___x_4512_ = l_Lean_MessageData_ofList(v___x_4511_);
v___x_4513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4505_);
lean_ctor_set(v___x_4513_, 1, v___x_4512_);
v___x_4514_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4500_, v___x_4513_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_dec_ref_known(v___x_4514_, 1);
v___y_4373_ = v___y_4499_;
v___y_4374_ = v___f_4501_;
v___y_4375_ = v_cls_4500_;
v___y_4376_ = v_a_4360_;
v___y_4377_ = v_a_4361_;
v___y_4378_ = v_a_4362_;
v___y_4379_ = v_a_4363_;
goto v___jp_4372_;
}
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
lean_dec_ref(v___y_4499_);
v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4514_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4514_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object* v_data_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
lean_dec(v_a_4533_);
lean_dec_ref(v_a_4532_);
lean_dec(v_a_4531_);
lean_dec_ref(v_a_4530_);
lean_dec_ref(v_data_4529_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object* v_upperBound_4536_, lean_object* v___y_4537_, lean_object* v_inst_4538_, lean_object* v_R_4539_, lean_object* v_a_4540_, lean_object* v_b_4541_, lean_object* v_c_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v___x_4548_; 
v___x_4548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4536_, v___y_4537_, v_a_4540_, v_b_4541_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object* v_upperBound_4549_, lean_object* v___y_4550_, lean_object* v_inst_4551_, lean_object* v_R_4552_, lean_object* v_a_4553_, lean_object* v_b_4554_, lean_object* v_c_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_upperBound_4549_, v___y_4550_, v_inst_4551_, v_R_4552_, v_a_4553_, v_b_4554_, v_c_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec_ref(v___y_4550_);
lean_dec(v_upperBound_4549_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(lean_object* v_snd_4562_, lean_object* v_fst_4563_, lean_object* v_as_x27_4564_, lean_object* v_b_4565_){
_start:
{
if (lean_obj_tag(v_as_x27_4564_) == 0)
{
lean_object* v___x_4567_; 
lean_dec_ref(v_fst_4563_);
v___x_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4567_, 0, v_b_4565_);
return v___x_4567_;
}
else
{
lean_object* v_head_4568_; lean_object* v_tail_4569_; lean_object* v_fst_4570_; lean_object* v_snd_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v_head_4568_ = lean_ctor_get(v_as_x27_4564_, 0);
v_tail_4569_ = lean_ctor_get(v_as_x27_4564_, 1);
v_fst_4570_ = lean_ctor_get(v_head_4568_, 0);
v_snd_4571_ = lean_ctor_get(v_head_4568_, 1);
v___x_4572_ = lean_int_neg(v_snd_4562_);
lean_inc(v_fst_4570_);
lean_inc_ref(v_fst_4563_);
lean_inc(v_snd_4571_);
v___x_4573_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_snd_4571_, v_fst_4563_, v___x_4572_, v_fst_4570_);
v___x_4574_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_4573_);
v___x_4575_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_b_4565_, v___x_4574_);
v_as_x27_4564_ = v_tail_4569_;
v_b_4565_ = v___x_4575_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg___boxed(lean_object* v_snd_4577_, lean_object* v_fst_4578_, lean_object* v_as_x27_4579_, lean_object* v_b_4580_, lean_object* v___y_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4577_, v_fst_4578_, v_as_x27_4579_, v_b_4580_);
lean_dec(v_as_x27_4579_);
lean_dec(v_snd_4577_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(lean_object* v_upperBounds_4583_, lean_object* v_as_x27_4584_, lean_object* v_b_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
if (lean_obj_tag(v_as_x27_4584_) == 0)
{
lean_object* v___x_4591_; 
v___x_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4591_, 0, v_b_4585_);
return v___x_4591_;
}
else
{
lean_object* v_head_4592_; lean_object* v_tail_4593_; lean_object* v_fst_4594_; lean_object* v_snd_4595_; lean_object* v___x_4596_; lean_object* v_a_4597_; 
v_head_4592_ = lean_ctor_get(v_as_x27_4584_, 0);
v_tail_4593_ = lean_ctor_get(v_as_x27_4584_, 1);
v_fst_4594_ = lean_ctor_get(v_head_4592_, 0);
v_snd_4595_ = lean_ctor_get(v_head_4592_, 1);
lean_inc(v_fst_4594_);
v___x_4596_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4595_, v_fst_4594_, v_upperBounds_4583_, v_b_4585_);
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4597_);
lean_dec_ref(v___x_4596_);
v_as_x27_4584_ = v_tail_4593_;
v_b_4585_ = v_a_4597_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg___boxed(lean_object* v_upperBounds_4599_, lean_object* v_as_x27_4600_, lean_object* v_b_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4599_, v_as_x27_4600_, v_b_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v_as_x27_4600_);
lean_dec(v_upperBounds_4599_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(lean_object* v_as_x27_4608_, lean_object* v_b_4609_){
_start:
{
if (lean_obj_tag(v_as_x27_4608_) == 0)
{
lean_object* v___x_4611_; 
v___x_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4611_, 0, v_b_4609_);
return v___x_4611_;
}
else
{
lean_object* v_head_4612_; lean_object* v_tail_4613_; lean_object* v___x_4614_; 
v_head_4612_ = lean_ctor_get(v_as_x27_4608_, 0);
v_tail_4613_ = lean_ctor_get(v_as_x27_4608_, 1);
lean_inc(v_head_4612_);
v___x_4614_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_b_4609_, v_head_4612_);
v_as_x27_4608_ = v_tail_4613_;
v_b_4609_ = v___x_4614_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg___boxed(lean_object* v_as_x27_4616_, lean_object* v_b_4617_, lean_object* v___y_4618_){
_start:
{
lean_object* v_res_4619_; 
v_res_4619_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4616_, v_b_4617_);
lean_dec(v_as_x27_4616_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(lean_object* v_p_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_){
_start:
{
lean_object* v_data_4626_; lean_object* v___x_4627_; 
lean_inc_ref(v_p_4620_);
v_data_4626_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(v_p_4620_);
v___x_4627_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4626_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_);
lean_dec_ref(v_data_4626_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v_a_4628_; lean_object* v_irrelevant_4629_; lean_object* v_lowerBounds_4630_; lean_object* v_upperBounds_4631_; lean_object* v_assumptions_4632_; lean_object* v_eliminations_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4648_; 
v_a_4628_ = lean_ctor_get(v___x_4627_, 0);
lean_inc(v_a_4628_);
lean_dec_ref_known(v___x_4627_, 1);
v_irrelevant_4629_ = lean_ctor_get(v_a_4628_, 1);
lean_inc(v_irrelevant_4629_);
v_lowerBounds_4630_ = lean_ctor_get(v_a_4628_, 2);
lean_inc(v_lowerBounds_4630_);
v_upperBounds_4631_ = lean_ctor_get(v_a_4628_, 3);
lean_inc(v_upperBounds_4631_);
lean_dec(v_a_4628_);
v_assumptions_4632_ = lean_ctor_get(v_p_4620_, 0);
v_eliminations_4633_ = lean_ctor_get(v_p_4620_, 4);
v_isSharedCheck_4648_ = !lean_is_exclusive(v_p_4620_);
if (v_isSharedCheck_4648_ == 0)
{
lean_object* v_unused_4649_; lean_object* v_unused_4650_; lean_object* v_unused_4651_; lean_object* v_unused_4652_; lean_object* v_unused_4653_; 
v_unused_4649_ = lean_ctor_get(v_p_4620_, 6);
lean_dec(v_unused_4649_);
v_unused_4650_ = lean_ctor_get(v_p_4620_, 5);
lean_dec(v_unused_4650_);
v_unused_4651_ = lean_ctor_get(v_p_4620_, 3);
lean_dec(v_unused_4651_);
v_unused_4652_ = lean_ctor_get(v_p_4620_, 2);
lean_dec(v_unused_4652_);
v_unused_4653_ = lean_ctor_get(v_p_4620_, 1);
lean_dec(v_unused_4653_);
v___x_4635_ = v_p_4620_;
v_isShared_4636_ = v_isSharedCheck_4648_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_eliminations_4633_);
lean_inc(v_assumptions_4632_);
lean_dec(v_p_4620_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4648_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; uint8_t v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4643_; 
v___x_4637_ = lean_unsigned_to_nat(0u);
v___x_4638_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v___x_4639_ = 1;
v___x_4640_ = lean_box(0);
v___x_4641_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_4636_ == 0)
{
lean_ctor_set(v___x_4635_, 6, v___x_4641_);
lean_ctor_set(v___x_4635_, 5, v___x_4640_);
lean_ctor_set(v___x_4635_, 3, v___x_4638_);
lean_ctor_set(v___x_4635_, 2, v___x_4638_);
lean_ctor_set(v___x_4635_, 1, v___x_4637_);
v___x_4643_ = v___x_4635_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_assumptions_4632_);
lean_ctor_set(v_reuseFailAlloc_4647_, 1, v___x_4637_);
lean_ctor_set(v_reuseFailAlloc_4647_, 2, v___x_4638_);
lean_ctor_set(v_reuseFailAlloc_4647_, 3, v___x_4638_);
lean_ctor_set(v_reuseFailAlloc_4647_, 4, v_eliminations_4633_);
lean_ctor_set(v_reuseFailAlloc_4647_, 5, v___x_4640_);
lean_ctor_set(v_reuseFailAlloc_4647_, 6, v___x_4641_);
v___x_4643_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
lean_object* v___x_4644_; lean_object* v_a_4645_; lean_object* v___x_4646_; 
lean_ctor_set_uint8(v___x_4643_, sizeof(void*)*7, v___x_4639_);
v___x_4644_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_irrelevant_4629_, v___x_4643_);
lean_dec(v_irrelevant_4629_);
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
lean_dec_ref(v___x_4644_);
v___x_4646_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4631_, v_lowerBounds_4630_, v_a_4645_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_);
lean_dec(v_lowerBounds_4630_);
lean_dec(v_upperBounds_4631_);
return v___x_4646_;
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
lean_dec_ref(v_p_4620_);
v_a_4654_ = lean_ctor_get(v___x_4627_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4627_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4627_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin___boxed(lean_object* v_p_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
lean_object* v_res_4668_; 
v_res_4668_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
lean_dec(v_a_4666_);
lean_dec_ref(v_a_4665_);
lean_dec(v_a_4664_);
lean_dec_ref(v_a_4663_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(lean_object* v_snd_4669_, lean_object* v_fst_4670_, lean_object* v_as_4671_, lean_object* v_as_x27_4672_, lean_object* v_b_4673_, lean_object* v_a_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v___x_4680_; 
v___x_4680_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4669_, v_fst_4670_, v_as_x27_4672_, v_b_4673_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___boxed(lean_object* v_snd_4681_, lean_object* v_fst_4682_, lean_object* v_as_4683_, lean_object* v_as_x27_4684_, lean_object* v_b_4685_, lean_object* v_a_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(v_snd_4681_, v_fst_4682_, v_as_4683_, v_as_x27_4684_, v_b_4685_, v_a_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_);
lean_dec(v___y_4690_);
lean_dec_ref(v___y_4689_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
lean_dec(v_as_x27_4684_);
lean_dec(v_as_4683_);
lean_dec(v_snd_4681_);
return v_res_4692_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(lean_object* v_as_4693_, lean_object* v_as_x27_4694_, lean_object* v_b_4695_, lean_object* v_a_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v___x_4702_; 
v___x_4702_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4694_, v_b_4695_);
return v___x_4702_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___boxed(lean_object* v_as_4703_, lean_object* v_as_x27_4704_, lean_object* v_b_4705_, lean_object* v_a_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(v_as_4703_, v_as_x27_4704_, v_b_4705_, v_a_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
lean_dec(v_as_x27_4704_);
lean_dec(v_as_4703_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(lean_object* v_upperBounds_4713_, lean_object* v_as_4714_, lean_object* v_as_x27_4715_, lean_object* v_b_4716_, lean_object* v_a_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
lean_object* v___x_4723_; 
v___x_4723_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4713_, v_as_x27_4715_, v_b_4716_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___boxed(lean_object* v_upperBounds_4724_, lean_object* v_as_4725_, lean_object* v_as_x27_4726_, lean_object* v_b_4727_, lean_object* v_a_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(v_upperBounds_4724_, v_as_4725_, v_as_x27_4726_, v_b_4727_, v_a_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
lean_dec(v___y_4730_);
lean_dec_ref(v___y_4729_);
lean_dec(v_as_x27_4726_);
lean_dec(v_as_4725_);
lean_dec(v_upperBounds_4724_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object* v_x_4735_, lean_object* v_x_4736_){
_start:
{
if (lean_obj_tag(v_x_4736_) == 0)
{
lean_inc(v_x_4735_);
return v_x_4735_;
}
else
{
lean_object* v_key_4737_; lean_object* v_value_4738_; lean_object* v_tail_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v_key_4737_ = lean_ctor_get(v_x_4736_, 0);
v_value_4738_ = lean_ctor_get(v_x_4736_, 1);
v_tail_4739_ = lean_ctor_get(v_x_4736_, 2);
v___x_4740_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4735_, v_tail_4739_);
lean_inc(v_value_4738_);
lean_inc(v_key_4737_);
v___x_4741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4741_, 0, v_key_4737_);
lean_ctor_set(v___x_4741_, 1, v_value_4738_);
v___x_4742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4741_);
lean_ctor_set(v___x_4742_, 1, v___x_4740_);
return v___x_4742_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2___boxed(lean_object* v_x_4743_, lean_object* v_x_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4743_, v_x_4744_);
lean_dec(v_x_4744_);
lean_dec(v_x_4743_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object* v_as_4746_, size_t v_i_4747_, size_t v_stop_4748_, lean_object* v_b_4749_){
_start:
{
uint8_t v___x_4750_; 
v___x_4750_ = lean_usize_dec_eq(v_i_4747_, v_stop_4748_);
if (v___x_4750_ == 0)
{
size_t v___x_4751_; size_t v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4751_ = ((size_t)1ULL);
v___x_4752_ = lean_usize_sub(v_i_4747_, v___x_4751_);
v___x_4753_ = lean_array_uget_borrowed(v_as_4746_, v___x_4752_);
v___x_4754_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_b_4749_, v___x_4753_);
lean_dec(v_b_4749_);
v_i_4747_ = v___x_4752_;
v_b_4749_ = v___x_4754_;
goto _start;
}
else
{
return v_b_4749_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object* v_as_4756_, lean_object* v_i_4757_, lean_object* v_stop_4758_, lean_object* v_b_4759_){
_start:
{
size_t v_i_boxed_4760_; size_t v_stop_boxed_4761_; lean_object* v_res_4762_; 
v_i_boxed_4760_ = lean_unbox_usize(v_i_4757_);
lean_dec(v_i_4757_);
v_stop_boxed_4761_ = lean_unbox_usize(v_stop_4758_);
lean_dec(v_stop_4758_);
v_res_4762_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_as_4756_, v_i_boxed_4760_, v_stop_boxed_4761_, v_b_4759_);
lean_dec_ref(v_as_4756_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object* v_a_4763_, lean_object* v_a_4764_){
_start:
{
if (lean_obj_tag(v_a_4763_) == 0)
{
lean_object* v___x_4765_; 
v___x_4765_ = l_List_reverse___redArg(v_a_4764_);
return v___x_4765_;
}
else
{
lean_object* v_head_4766_; lean_object* v_tail_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4884_; 
v_head_4766_ = lean_ctor_get(v_a_4763_, 0);
v_tail_4767_ = lean_ctor_get(v_a_4763_, 1);
v_isSharedCheck_4884_ = !lean_is_exclusive(v_a_4763_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4769_ = v_a_4763_;
v_isShared_4770_ = v_isSharedCheck_4884_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_tail_4767_);
lean_inc(v_head_4766_);
lean_dec(v_a_4763_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4884_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___y_4772_; lean_object* v_snd_4777_; lean_object* v_constraint_4778_; lean_object* v_fst_4779_; lean_object* v_lowerBound_4780_; lean_object* v_upperBound_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___y_4786_; lean_object* v___y_4787_; 
v_snd_4777_ = lean_ctor_get(v_head_4766_, 1);
v_constraint_4778_ = lean_ctor_get(v_snd_4777_, 1);
lean_inc_ref(v_constraint_4778_);
v_fst_4779_ = lean_ctor_get(v_head_4766_, 0);
lean_inc(v_fst_4779_);
lean_dec(v_head_4766_);
v_lowerBound_4780_ = lean_ctor_get(v_constraint_4778_, 0);
lean_inc(v_lowerBound_4780_);
v_upperBound_4781_ = lean_ctor_get(v_constraint_4778_, 1);
lean_inc(v_upperBound_4781_);
lean_dec_ref(v_constraint_4778_);
v___x_4782_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_fst_4779_);
lean_dec(v_fst_4779_);
v___x_4783_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_4784_ = lean_string_append(v___x_4782_, v___x_4783_);
if (lean_obj_tag(v_lowerBound_4780_) == 0)
{
if (lean_obj_tag(v_upperBound_4781_) == 0)
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4792_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_4793_ = lean_string_append(v___x_4784_, v___x_4792_);
v___y_4772_ = v___x_4793_;
goto v___jp_4771_;
}
else
{
lean_object* v_val_4794_; lean_object* v___x_4795_; lean_object* v___y_4797_; lean_object* v_intZero_4802_; uint8_t v_isNeg_4803_; 
v_val_4794_ = lean_ctor_get(v_upperBound_4781_, 0);
lean_inc(v_val_4794_);
lean_dec_ref_known(v_upperBound_4781_, 1);
v___x_4795_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_4802_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4803_ = lean_int_dec_lt(v_val_4794_, v_intZero_4802_);
if (v_isNeg_4803_ == 0)
{
lean_object* v_a_4804_; lean_object* v___x_4805_; 
v_a_4804_ = lean_nat_abs(v_val_4794_);
lean_dec(v_val_4794_);
v___x_4805_ = l_Nat_reprFast(v_a_4804_);
v___y_4797_ = v___x_4805_;
goto v___jp_4796_;
}
else
{
lean_object* v_abs_4806_; lean_object* v_one_4807_; lean_object* v_a_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; 
v_abs_4806_ = lean_nat_abs(v_val_4794_);
lean_dec(v_val_4794_);
v_one_4807_ = lean_unsigned_to_nat(1u);
v_a_4808_ = lean_nat_sub(v_abs_4806_, v_one_4807_);
lean_dec(v_abs_4806_);
v___x_4809_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4810_ = lean_nat_add(v_a_4808_, v_one_4807_);
lean_dec(v_a_4808_);
v___x_4811_ = l_Nat_reprFast(v___x_4810_);
v___x_4812_ = lean_string_append(v___x_4809_, v___x_4811_);
lean_dec_ref(v___x_4811_);
v___y_4797_ = v___x_4812_;
goto v___jp_4796_;
}
v___jp_4796_:
{
lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4798_ = lean_string_append(v___x_4795_, v___y_4797_);
lean_dec_ref(v___y_4797_);
v___x_4799_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4800_ = lean_string_append(v___x_4798_, v___x_4799_);
v___x_4801_ = lean_string_append(v___x_4784_, v___x_4800_);
lean_dec_ref(v___x_4800_);
v___y_4772_ = v___x_4801_;
goto v___jp_4771_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_4781_) == 0)
{
lean_object* v_val_4813_; lean_object* v___x_4814_; lean_object* v___y_4816_; lean_object* v_intZero_4821_; uint8_t v_isNeg_4822_; 
v_val_4813_ = lean_ctor_get(v_lowerBound_4780_, 0);
lean_inc(v_val_4813_);
lean_dec_ref_known(v_lowerBound_4780_, 1);
v___x_4814_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4821_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4822_ = lean_int_dec_lt(v_val_4813_, v_intZero_4821_);
if (v_isNeg_4822_ == 0)
{
lean_object* v_a_4823_; lean_object* v___x_4824_; 
v_a_4823_ = lean_nat_abs(v_val_4813_);
lean_dec(v_val_4813_);
v___x_4824_ = l_Nat_reprFast(v_a_4823_);
v___y_4816_ = v___x_4824_;
goto v___jp_4815_;
}
else
{
lean_object* v_abs_4825_; lean_object* v_one_4826_; lean_object* v_a_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
v_abs_4825_ = lean_nat_abs(v_val_4813_);
lean_dec(v_val_4813_);
v_one_4826_ = lean_unsigned_to_nat(1u);
v_a_4827_ = lean_nat_sub(v_abs_4825_, v_one_4826_);
lean_dec(v_abs_4825_);
v___x_4828_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4829_ = lean_nat_add(v_a_4827_, v_one_4826_);
lean_dec(v_a_4827_);
v___x_4830_ = l_Nat_reprFast(v___x_4829_);
v___x_4831_ = lean_string_append(v___x_4828_, v___x_4830_);
lean_dec_ref(v___x_4830_);
v___y_4816_ = v___x_4831_;
goto v___jp_4815_;
}
v___jp_4815_:
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
v___x_4817_ = lean_string_append(v___x_4814_, v___y_4816_);
lean_dec_ref(v___y_4816_);
v___x_4818_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_4819_ = lean_string_append(v___x_4817_, v___x_4818_);
v___x_4820_ = lean_string_append(v___x_4784_, v___x_4819_);
lean_dec_ref(v___x_4819_);
v___y_4772_ = v___x_4820_;
goto v___jp_4771_;
}
}
else
{
lean_object* v_val_4832_; lean_object* v_val_4833_; uint8_t v___x_4834_; 
v_val_4832_ = lean_ctor_get(v_lowerBound_4780_, 0);
lean_inc(v_val_4832_);
lean_dec_ref_known(v_lowerBound_4780_, 1);
v_val_4833_ = lean_ctor_get(v_upperBound_4781_, 0);
lean_inc(v_val_4833_);
lean_dec_ref_known(v_upperBound_4781_, 1);
v___x_4834_ = lean_int_dec_lt(v_val_4833_, v_val_4832_);
if (v___x_4834_ == 0)
{
uint8_t v___x_4835_; 
v___x_4835_ = lean_int_dec_eq(v_val_4832_, v_val_4833_);
if (v___x_4835_ == 0)
{
lean_object* v___x_4836_; lean_object* v___y_4838_; lean_object* v_intZero_4853_; uint8_t v_isNeg_4854_; 
v___x_4836_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4853_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4854_ = lean_int_dec_lt(v_val_4832_, v_intZero_4853_);
if (v_isNeg_4854_ == 0)
{
lean_object* v_a_4855_; lean_object* v___x_4856_; 
v_a_4855_ = lean_nat_abs(v_val_4832_);
lean_dec(v_val_4832_);
v___x_4856_ = l_Nat_reprFast(v_a_4855_);
v___y_4838_ = v___x_4856_;
goto v___jp_4837_;
}
else
{
lean_object* v_abs_4857_; lean_object* v_one_4858_; lean_object* v_a_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
v_abs_4857_ = lean_nat_abs(v_val_4832_);
lean_dec(v_val_4832_);
v_one_4858_ = lean_unsigned_to_nat(1u);
v_a_4859_ = lean_nat_sub(v_abs_4857_, v_one_4858_);
lean_dec(v_abs_4857_);
v___x_4860_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4861_ = lean_nat_add(v_a_4859_, v_one_4858_);
lean_dec(v_a_4859_);
v___x_4862_ = l_Nat_reprFast(v___x_4861_);
v___x_4863_ = lean_string_append(v___x_4860_, v___x_4862_);
lean_dec_ref(v___x_4862_);
v___y_4838_ = v___x_4863_;
goto v___jp_4837_;
}
v___jp_4837_:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v_intZero_4842_; uint8_t v_isNeg_4843_; 
v___x_4839_ = lean_string_append(v___x_4836_, v___y_4838_);
lean_dec_ref(v___y_4838_);
v___x_4840_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_4841_ = lean_string_append(v___x_4839_, v___x_4840_);
v_intZero_4842_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4843_ = lean_int_dec_lt(v_val_4833_, v_intZero_4842_);
if (v_isNeg_4843_ == 0)
{
lean_object* v_a_4844_; lean_object* v___x_4845_; 
v_a_4844_ = lean_nat_abs(v_val_4833_);
lean_dec(v_val_4833_);
v___x_4845_ = l_Nat_reprFast(v_a_4844_);
v___y_4786_ = v___x_4841_;
v___y_4787_ = v___x_4845_;
goto v___jp_4785_;
}
else
{
lean_object* v_abs_4846_; lean_object* v_one_4847_; lean_object* v_a_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; 
v_abs_4846_ = lean_nat_abs(v_val_4833_);
lean_dec(v_val_4833_);
v_one_4847_ = lean_unsigned_to_nat(1u);
v_a_4848_ = lean_nat_sub(v_abs_4846_, v_one_4847_);
lean_dec(v_abs_4846_);
v___x_4849_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4850_ = lean_nat_add(v_a_4848_, v_one_4847_);
lean_dec(v_a_4848_);
v___x_4851_ = l_Nat_reprFast(v___x_4850_);
v___x_4852_ = lean_string_append(v___x_4849_, v___x_4851_);
lean_dec_ref(v___x_4851_);
v___y_4786_ = v___x_4841_;
v___y_4787_ = v___x_4852_;
goto v___jp_4785_;
}
}
}
else
{
lean_object* v___x_4864_; lean_object* v___y_4866_; lean_object* v_intZero_4871_; uint8_t v_isNeg_4872_; 
lean_dec(v_val_4833_);
v___x_4864_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_4871_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4872_ = lean_int_dec_lt(v_val_4832_, v_intZero_4871_);
if (v_isNeg_4872_ == 0)
{
lean_object* v_a_4873_; lean_object* v___x_4874_; 
v_a_4873_ = lean_nat_abs(v_val_4832_);
lean_dec(v_val_4832_);
v___x_4874_ = l_Nat_reprFast(v_a_4873_);
v___y_4866_ = v___x_4874_;
goto v___jp_4865_;
}
else
{
lean_object* v_abs_4875_; lean_object* v_one_4876_; lean_object* v_a_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
v_abs_4875_ = lean_nat_abs(v_val_4832_);
lean_dec(v_val_4832_);
v_one_4876_ = lean_unsigned_to_nat(1u);
v_a_4877_ = lean_nat_sub(v_abs_4875_, v_one_4876_);
lean_dec(v_abs_4875_);
v___x_4878_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4879_ = lean_nat_add(v_a_4877_, v_one_4876_);
lean_dec(v_a_4877_);
v___x_4880_ = l_Nat_reprFast(v___x_4879_);
v___x_4881_ = lean_string_append(v___x_4878_, v___x_4880_);
lean_dec_ref(v___x_4880_);
v___y_4866_ = v___x_4881_;
goto v___jp_4865_;
}
v___jp_4865_:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4867_ = lean_string_append(v___x_4864_, v___y_4866_);
lean_dec_ref(v___y_4866_);
v___x_4868_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_4869_ = lean_string_append(v___x_4867_, v___x_4868_);
v___x_4870_ = lean_string_append(v___x_4784_, v___x_4869_);
lean_dec_ref(v___x_4869_);
v___y_4772_ = v___x_4870_;
goto v___jp_4771_;
}
}
}
else
{
lean_object* v___x_4882_; lean_object* v___x_4883_; 
lean_dec(v_val_4833_);
lean_dec(v_val_4832_);
v___x_4882_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_4883_ = lean_string_append(v___x_4784_, v___x_4882_);
v___y_4772_ = v___x_4883_;
goto v___jp_4771_;
}
}
}
v___jp_4771_:
{
lean_object* v___x_4774_; 
if (v_isShared_4770_ == 0)
{
lean_ctor_set(v___x_4769_, 1, v_a_4764_);
lean_ctor_set(v___x_4769_, 0, v___y_4772_);
v___x_4774_ = v___x_4769_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v___y_4772_);
lean_ctor_set(v_reuseFailAlloc_4776_, 1, v_a_4764_);
v___x_4774_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
v_a_4763_ = v_tail_4767_;
v_a_4764_ = v___x_4774_;
goto _start;
}
}
v___jp_4785_:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4788_ = lean_string_append(v___y_4786_, v___y_4787_);
lean_dec_ref(v___y_4787_);
v___x_4789_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4790_ = lean_string_append(v___x_4788_, v___x_4789_);
v___x_4791_ = lean_string_append(v___x_4784_, v___x_4790_);
lean_dec_ref(v___x_4790_);
v___y_4772_ = v___x_4791_;
goto v___jp_4771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object* v_cls_4885_, lean_object* v_msg_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_){
_start:
{
lean_object* v_ref_4892_; lean_object* v___x_4893_; lean_object* v_a_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4939_; 
v_ref_4892_ = lean_ctor_get(v___y_4889_, 2);
v___x_4893_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4896_ = v___x_4893_;
v_isShared_4897_ = v_isSharedCheck_4939_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_a_4894_);
lean_dec(v___x_4893_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4939_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
lean_object* v___x_4898_; lean_object* v_traceState_4899_; lean_object* v_env_4900_; lean_object* v_nextMacroScope_4901_; lean_object* v_ngen_4902_; lean_object* v_auxDeclNGen_4903_; lean_object* v_cache_4904_; lean_object* v_recordedDeps_4905_; lean_object* v_messages_4906_; lean_object* v_infoState_4907_; lean_object* v_snapshotTasks_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4938_; 
v___x_4898_ = lean_st_ref_take(v___y_4890_);
v_traceState_4899_ = lean_ctor_get(v___x_4898_, 4);
v_env_4900_ = lean_ctor_get(v___x_4898_, 0);
v_nextMacroScope_4901_ = lean_ctor_get(v___x_4898_, 1);
v_ngen_4902_ = lean_ctor_get(v___x_4898_, 2);
v_auxDeclNGen_4903_ = lean_ctor_get(v___x_4898_, 3);
v_cache_4904_ = lean_ctor_get(v___x_4898_, 5);
v_recordedDeps_4905_ = lean_ctor_get(v___x_4898_, 6);
v_messages_4906_ = lean_ctor_get(v___x_4898_, 7);
v_infoState_4907_ = lean_ctor_get(v___x_4898_, 8);
v_snapshotTasks_4908_ = lean_ctor_get(v___x_4898_, 9);
v_isSharedCheck_4938_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4910_ = v___x_4898_;
v_isShared_4911_ = v_isSharedCheck_4938_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_snapshotTasks_4908_);
lean_inc(v_infoState_4907_);
lean_inc(v_messages_4906_);
lean_inc(v_recordedDeps_4905_);
lean_inc(v_cache_4904_);
lean_inc(v_traceState_4899_);
lean_inc(v_auxDeclNGen_4903_);
lean_inc(v_ngen_4902_);
lean_inc(v_nextMacroScope_4901_);
lean_inc(v_env_4900_);
lean_dec(v___x_4898_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4938_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
uint64_t v_tid_4912_; lean_object* v_traces_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4937_; 
v_tid_4912_ = lean_ctor_get_uint64(v_traceState_4899_, sizeof(void*)*1);
v_traces_4913_ = lean_ctor_get(v_traceState_4899_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v_traceState_4899_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4915_ = v_traceState_4899_;
v_isShared_4916_ = v_isSharedCheck_4937_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_traces_4913_);
lean_dec(v_traceState_4899_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4937_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4917_; lean_object* v___x_4918_; double v___x_4919_; uint8_t v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4928_; 
v___x_4917_ = lean_box(0);
v___x_4918_ = lean_box(0);
v___x_4919_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4920_ = 0;
v___x_4921_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4922_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4922_, 0, v_cls_4885_);
lean_ctor_set(v___x_4922_, 1, v___x_4918_);
lean_ctor_set(v___x_4922_, 2, v___x_4921_);
lean_ctor_set_float(v___x_4922_, sizeof(void*)*3, v___x_4919_);
lean_ctor_set_float(v___x_4922_, sizeof(void*)*3 + 8, v___x_4919_);
lean_ctor_set_uint8(v___x_4922_, sizeof(void*)*3 + 16, v___x_4920_);
v___x_4923_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4924_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4924_, 0, v___x_4922_);
lean_ctor_set(v___x_4924_, 1, v_a_4894_);
lean_ctor_set(v___x_4924_, 2, v___x_4923_);
lean_inc(v_ref_4892_);
v___x_4925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4925_, 0, v_ref_4892_);
lean_ctor_set(v___x_4925_, 1, v___x_4924_);
v___x_4926_ = l_Lean_PersistentArray_push___redArg(v_traces_4913_, v___x_4925_);
if (v_isShared_4916_ == 0)
{
lean_ctor_set(v___x_4915_, 0, v___x_4926_);
v___x_4928_ = v___x_4915_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4926_);
lean_ctor_set_uint64(v_reuseFailAlloc_4936_, sizeof(void*)*1, v_tid_4912_);
v___x_4928_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
lean_object* v___x_4930_; 
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 4, v___x_4928_);
v___x_4930_ = v___x_4910_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_env_4900_);
lean_ctor_set(v_reuseFailAlloc_4935_, 1, v_nextMacroScope_4901_);
lean_ctor_set(v_reuseFailAlloc_4935_, 2, v_ngen_4902_);
lean_ctor_set(v_reuseFailAlloc_4935_, 3, v_auxDeclNGen_4903_);
lean_ctor_set(v_reuseFailAlloc_4935_, 4, v___x_4928_);
lean_ctor_set(v_reuseFailAlloc_4935_, 5, v_cache_4904_);
lean_ctor_set(v_reuseFailAlloc_4935_, 6, v_recordedDeps_4905_);
lean_ctor_set(v_reuseFailAlloc_4935_, 7, v_messages_4906_);
lean_ctor_set(v_reuseFailAlloc_4935_, 8, v_infoState_4907_);
lean_ctor_set(v_reuseFailAlloc_4935_, 9, v_snapshotTasks_4908_);
v___x_4930_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
lean_object* v___x_4931_; lean_object* v___x_4933_; 
v___x_4931_ = lean_st_ref_put(v___y_4890_, v___x_4930_);
if (v_isShared_4897_ == 0)
{
lean_ctor_set(v___x_4896_, 0, v___x_4917_);
v___x_4933_ = v___x_4896_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4917_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg___boxed(lean_object* v_cls_4940_, lean_object* v_msg_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_){
_start:
{
lean_object* v_res_4947_; 
v_res_4947_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4940_, v_msg_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_);
lean_dec(v___y_4945_);
lean_dec_ref(v___y_4944_);
lean_dec(v___y_4943_);
lean_dec_ref(v___y_4942_);
return v_res_4947_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1(void){
_start:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4949_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__0));
v___x_4950_ = l_Lean_stringToMessageData(v___x_4949_);
return v___x_4950_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1(void){
_start:
{
lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4952_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__0));
v___x_4953_ = l_Lean_stringToMessageData(v___x_4952_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega(lean_object* v_p_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, uint8_t v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_){
_start:
{
lean_object* v___y_4966_; lean_object* v___y_4967_; lean_object* v___y_4968_; uint8_t v___y_4969_; lean_object* v___y_4970_; lean_object* v___y_4971_; lean_object* v___y_4972_; lean_object* v___y_4973_; lean_object* v___y_4974_; lean_object* v_toCold_4980_; lean_object* v_options_4981_; uint8_t v_hasTrace_4982_; 
v_toCold_4980_ = lean_ctor_get(v_a_4962_, 0);
v_options_4981_ = lean_ctor_get(v_toCold_4980_, 2);
v_hasTrace_4982_ = lean_ctor_get_uint8(v_options_4981_, sizeof(void*)*1);
if (v_hasTrace_4982_ == 0)
{
v___y_4966_ = v_a_4955_;
v___y_4967_ = v_a_4956_;
v___y_4968_ = v_a_4957_;
v___y_4969_ = v_a_4958_;
v___y_4970_ = v_a_4959_;
v___y_4971_ = v_a_4960_;
v___y_4972_ = v_a_4961_;
v___y_4973_ = v_a_4962_;
v___y_4974_ = v_a_4963_;
goto v___jp_4965_;
}
else
{
lean_object* v_inheritedTraceOptions_4983_; lean_object* v_cls_4984_; lean_object* v___x_4985_; uint8_t v___x_4986_; 
v_inheritedTraceOptions_4983_ = lean_ctor_get(v_toCold_4980_, 11);
v_cls_4984_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4985_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_4986_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4983_, v_options_4981_, v___x_4985_);
if (v___x_4986_ == 0)
{
v___y_4966_ = v_a_4955_;
v___y_4967_ = v_a_4956_;
v___y_4968_ = v_a_4957_;
v___y_4969_ = v_a_4958_;
v___y_4970_ = v_a_4959_;
v___y_4971_ = v_a_4960_;
v___y_4972_ = v_a_4961_;
v___y_4973_ = v_a_4962_;
v___y_4974_ = v_a_4963_;
goto v___jp_4965_;
}
else
{
lean_object* v_constraints_4987_; uint8_t v_possible_4988_; lean_object* v___x_4989_; lean_object* v___y_4991_; 
v_constraints_4987_ = lean_ctor_get(v_p_4954_, 2);
v_possible_4988_ = lean_ctor_get_uint8(v_p_4954_, sizeof(void*)*7);
v___x_4989_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_runOmega___closed__1);
if (v_possible_4988_ == 0)
{
lean_object* v___x_5004_; 
v___x_5004_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
v___y_4991_ = v___x_5004_;
goto v___jp_4990_;
}
else
{
uint8_t v___x_5005_; 
v___x_5005_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_4954_);
if (v___x_5005_ == 0)
{
lean_object* v_buckets_5006_; lean_object* v___x_5007_; lean_object* v___y_5009_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; uint8_t v___x_5016_; 
v_buckets_5006_ = lean_ctor_get(v_constraints_4987_, 1);
v___x_5007_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5013_ = lean_box(0);
v___x_5014_ = lean_array_get_size(v_buckets_5006_);
v___x_5015_ = lean_unsigned_to_nat(0u);
v___x_5016_ = lean_nat_dec_lt(v___x_5015_, v___x_5014_);
if (v___x_5016_ == 0)
{
v___y_5009_ = v___x_5013_;
goto v___jp_5008_;
}
else
{
size_t v___x_5017_; size_t v___x_5018_; lean_object* v___x_5019_; 
v___x_5017_ = lean_usize_of_nat(v___x_5014_);
v___x_5018_ = ((size_t)0ULL);
v___x_5019_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5006_, v___x_5017_, v___x_5018_, v___x_5013_);
v___y_5009_ = v___x_5019_;
goto v___jp_5008_;
}
v___jp_5008_:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5010_ = lean_box(0);
v___x_5011_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5009_, v___x_5010_);
v___x_5012_ = l_String_intercalate(v___x_5007_, v___x_5011_);
v___y_4991_ = v___x_5012_;
goto v___jp_4990_;
}
}
else
{
lean_object* v___x_5020_; 
v___x_5020_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
v___y_4991_ = v___x_5020_;
goto v___jp_4990_;
}
}
v___jp_4990_:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
v___x_4992_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4992_, 0, v___y_4991_);
v___x_4993_ = l_Lean_MessageData_ofFormat(v___x_4992_);
v___x_4994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4989_);
lean_ctor_set(v___x_4994_, 1, v___x_4993_);
v___x_4995_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_4984_, v___x_4994_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_dec_ref_known(v___x_4995_, 1);
v___y_4966_ = v_a_4955_;
v___y_4967_ = v_a_4956_;
v___y_4968_ = v_a_4957_;
v___y_4969_ = v_a_4958_;
v___y_4970_ = v_a_4959_;
v___y_4971_ = v_a_4960_;
v___y_4972_ = v_a_4961_;
v___y_4973_ = v_a_4962_;
v___y_4974_ = v_a_4963_;
goto v___jp_4965_;
}
else
{
lean_object* v_a_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5003_; 
lean_dec_ref(v_p_4954_);
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4998_ = v___x_4995_;
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_a_4996_);
lean_dec(v___x_4995_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5001_; 
if (v_isShared_4999_ == 0)
{
v___x_5001_ = v___x_4998_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_a_4996_);
v___x_5001_ = v_reuseFailAlloc_5002_;
goto v_reusejp_5000_;
}
v_reusejp_5000_:
{
return v___x_5001_;
}
}
}
}
}
}
v___jp_4965_:
{
uint8_t v_possible_4975_; 
v_possible_4975_ = lean_ctor_get_uint8(v_p_4954_, sizeof(void*)*7);
if (v_possible_4975_ == 0)
{
lean_object* v___x_4976_; 
v___x_4976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4976_, 0, v_p_4954_);
return v___x_4976_;
}
else
{
lean_object* v___x_4977_; 
v___x_4977_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_4954_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v_a_4978_; lean_object* v___x_4979_; 
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_a_4978_);
lean_dec_ref_known(v___x_4977_, 1);
v___x_4979_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_a_4978_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
return v___x_4979_;
}
else
{
return v___x_4977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination(lean_object* v_p_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, uint8_t v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_){
_start:
{
lean_object* v___y_5033_; lean_object* v___y_5034_; lean_object* v___y_5035_; uint8_t v___y_5036_; lean_object* v___y_5037_; lean_object* v___y_5038_; lean_object* v___y_5039_; lean_object* v___y_5040_; lean_object* v___y_5041_; uint8_t v_possible_5045_; 
v_possible_5045_ = lean_ctor_get_uint8(v_p_5021_, sizeof(void*)*7);
if (v_possible_5045_ == 0)
{
lean_object* v___x_5046_; 
v___x_5046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5046_, 0, v_p_5021_);
return v___x_5046_;
}
else
{
lean_object* v_constraints_5047_; uint8_t v___x_5048_; 
v_constraints_5047_ = lean_ctor_get(v_p_5021_, 2);
lean_inc_ref(v_constraints_5047_);
v___x_5048_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_5021_);
if (v___x_5048_ == 0)
{
lean_object* v_toCold_5049_; lean_object* v_options_5050_; uint8_t v_hasTrace_5051_; 
v_toCold_5049_ = lean_ctor_get(v_a_5029_, 0);
v_options_5050_ = lean_ctor_get(v_toCold_5049_, 2);
v_hasTrace_5051_ = lean_ctor_get_uint8(v_options_5050_, sizeof(void*)*1);
if (v_hasTrace_5051_ == 0)
{
lean_dec_ref(v_constraints_5047_);
v___y_5033_ = v_a_5022_;
v___y_5034_ = v_a_5023_;
v___y_5035_ = v_a_5024_;
v___y_5036_ = v_a_5025_;
v___y_5037_ = v_a_5026_;
v___y_5038_ = v_a_5027_;
v___y_5039_ = v_a_5028_;
v___y_5040_ = v_a_5029_;
v___y_5041_ = v_a_5030_;
goto v___jp_5032_;
}
else
{
lean_object* v_inheritedTraceOptions_5052_; lean_object* v_cls_5053_; lean_object* v___x_5054_; uint8_t v___x_5055_; 
v_inheritedTraceOptions_5052_ = lean_ctor_get(v_toCold_5049_, 11);
v_cls_5053_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_5054_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_5055_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5052_, v_options_5050_, v___x_5054_);
if (v___x_5055_ == 0)
{
lean_dec_ref(v_constraints_5047_);
v___y_5033_ = v_a_5022_;
v___y_5034_ = v_a_5023_;
v___y_5035_ = v_a_5024_;
v___y_5036_ = v_a_5025_;
v___y_5037_ = v_a_5026_;
v___y_5038_ = v_a_5027_;
v___y_5039_ = v_a_5028_;
v___y_5040_ = v_a_5029_;
v___y_5041_ = v_a_5030_;
goto v___jp_5032_;
}
else
{
lean_object* v_buckets_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5088_; 
v_buckets_5056_ = lean_ctor_get(v_constraints_5047_, 1);
v_isSharedCheck_5088_ = !lean_is_exclusive(v_constraints_5047_);
if (v_isSharedCheck_5088_ == 0)
{
lean_object* v_unused_5089_; 
v_unused_5089_ = lean_ctor_get(v_constraints_5047_, 0);
lean_dec(v_unused_5089_);
v___x_5058_ = v_constraints_5047_;
v_isShared_5059_ = v_isSharedCheck_5088_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_buckets_5056_);
lean_dec(v_constraints_5047_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5088_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___y_5063_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; uint8_t v___x_5084_; 
v___x_5060_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1);
v___x_5061_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5081_ = lean_box(0);
v___x_5082_ = lean_array_get_size(v_buckets_5056_);
v___x_5083_ = lean_unsigned_to_nat(0u);
v___x_5084_ = lean_nat_dec_lt(v___x_5083_, v___x_5082_);
if (v___x_5084_ == 0)
{
lean_dec_ref(v_buckets_5056_);
v___y_5063_ = v___x_5081_;
goto v___jp_5062_;
}
else
{
size_t v___x_5085_; size_t v___x_5086_; lean_object* v___x_5087_; 
v___x_5085_ = lean_usize_of_nat(v___x_5082_);
v___x_5086_ = ((size_t)0ULL);
v___x_5087_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5056_, v___x_5085_, v___x_5086_, v___x_5081_);
lean_dec_ref(v_buckets_5056_);
v___y_5063_ = v___x_5087_;
goto v___jp_5062_;
}
v___jp_5062_:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5070_; 
v___x_5064_ = lean_box(0);
v___x_5065_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5063_, v___x_5064_);
v___x_5066_ = l_String_intercalate(v___x_5061_, v___x_5065_);
v___x_5067_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5066_);
v___x_5068_ = l_Lean_MessageData_ofFormat(v___x_5067_);
if (v_isShared_5059_ == 0)
{
lean_ctor_set_tag(v___x_5058_, 7);
lean_ctor_set(v___x_5058_, 1, v___x_5068_);
lean_ctor_set(v___x_5058_, 0, v___x_5060_);
v___x_5070_ = v___x_5058_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v___x_5060_);
lean_ctor_set(v_reuseFailAlloc_5080_, 1, v___x_5068_);
v___x_5070_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
lean_object* v___x_5071_; 
v___x_5071_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5053_, v___x_5070_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_);
if (lean_obj_tag(v___x_5071_) == 0)
{
lean_dec_ref_known(v___x_5071_, 1);
v___y_5033_ = v_a_5022_;
v___y_5034_ = v_a_5023_;
v___y_5035_ = v_a_5024_;
v___y_5036_ = v_a_5025_;
v___y_5037_ = v_a_5026_;
v___y_5038_ = v_a_5027_;
v___y_5039_ = v_a_5028_;
v___y_5040_ = v_a_5029_;
v___y_5041_ = v_a_5030_;
goto v___jp_5032_;
}
else
{
lean_object* v_a_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5079_; 
lean_dec_ref(v_p_5021_);
v_a_5072_ = lean_ctor_get(v___x_5071_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5071_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5074_ = v___x_5071_;
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_a_5072_);
lean_dec(v___x_5071_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v___x_5077_; 
if (v_isShared_5075_ == 0)
{
v___x_5077_ = v___x_5074_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
v___x_5077_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
return v___x_5077_;
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
lean_object* v___x_5090_; 
lean_dec_ref(v_constraints_5047_);
v___x_5090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5090_, 0, v_p_5021_);
return v___x_5090_;
}
}
v___jp_5032_:
{
lean_object* v___x_5042_; 
v___x_5042_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_5021_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
if (lean_obj_tag(v___x_5042_) == 0)
{
lean_object* v_a_5043_; lean_object* v___x_5044_; 
v_a_5043_ = lean_ctor_get(v___x_5042_, 0);
lean_inc(v_a_5043_);
lean_dec_ref_known(v___x_5042_, 1);
v___x_5044_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_a_5043_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
return v___x_5044_;
}
else
{
return v___x_5042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___boxed(lean_object* v_p_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_){
_start:
{
uint8_t v_a_boxed_5102_; lean_object* v_res_5103_; 
v_a_boxed_5102_ = lean_unbox(v_a_5095_);
v_res_5103_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_p_5091_, v_a_5092_, v_a_5093_, v_a_5094_, v_a_boxed_5102_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_);
lean_dec(v_a_5100_);
lean_dec_ref(v_a_5099_);
lean_dec(v_a_5098_);
lean_dec_ref(v_a_5097_);
lean_dec(v_a_5096_);
lean_dec_ref(v_a_5094_);
lean_dec(v_a_5093_);
lean_dec(v_a_5092_);
return v_res_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___boxed(lean_object* v_p_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_){
_start:
{
uint8_t v_a_boxed_5115_; lean_object* v_res_5116_; 
v_a_boxed_5115_ = lean_unbox(v_a_5108_);
v_res_5116_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_p_5104_, v_a_5105_, v_a_5106_, v_a_5107_, v_a_boxed_5115_, v_a_5109_, v_a_5110_, v_a_5111_, v_a_5112_, v_a_5113_);
lean_dec(v_a_5113_);
lean_dec_ref(v_a_5112_);
lean_dec(v_a_5111_);
lean_dec_ref(v_a_5110_);
lean_dec(v_a_5109_);
lean_dec_ref(v_a_5107_);
lean_dec(v_a_5106_);
lean_dec(v_a_5105_);
return v_res_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(lean_object* v_cls_5117_, lean_object* v_msg_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, uint8_t v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_){
_start:
{
lean_object* v___x_5129_; 
v___x_5129_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5117_, v_msg_5118_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_);
return v___x_5129_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___boxed(lean_object* v_cls_5130_, lean_object* v_msg_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_){
_start:
{
uint8_t v___y_16416__boxed_5142_; lean_object* v_res_5143_; 
v___y_16416__boxed_5142_ = lean_unbox(v___y_5135_);
v_res_5143_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(v_cls_5130_, v_msg_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_16416__boxed_5142_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
lean_dec(v___y_5140_);
lean_dec_ref(v___y_5139_);
lean_dec(v___y_5138_);
lean_dec_ref(v___y_5137_);
lean_dec(v___y_5136_);
lean_dec_ref(v___y_5134_);
lean_dec(v___y_5133_);
lean_dec(v___y_5132_);
return v_res_5143_;
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
