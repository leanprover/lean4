// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.Core
// Imports: public import Lean.Elab.Tactic.Omega.OmegaM public import Lean.Elab.Tactic.Omega.MinNatAbs import Lean.CoreM
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
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
lean_inc_ref(v___y_821_);
v___x_825_ = lean_string_append(v___y_821_, v___y_824_);
lean_dec_ref(v___y_824_);
v___x_826_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_827_ = lean_string_append(v___x_825_, v___x_826_);
v_intZero_828_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_829_ = lean_int_dec_lt(v___y_823_, v_intZero_828_);
if (v_isNeg_829_ == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; 
v_a_830_ = lean_nat_abs(v___y_823_);
lean_dec(v___y_823_);
v___x_831_ = l_Nat_reprFast(v_a_830_);
v___y_814_ = v___y_822_;
v___y_815_ = v___x_827_;
v___y_816_ = v___x_831_;
goto v___jp_813_;
}
else
{
lean_object* v_abs_832_; lean_object* v_one_833_; lean_object* v_a_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_abs_832_ = lean_nat_abs(v___y_823_);
lean_dec(v___y_823_);
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
v___y_821_ = v___x_883_;
v___y_822_ = v___x_851_;
v___y_823_ = v_val_880_;
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
v___y_821_ = v___x_883_;
v___y_822_ = v___x_851_;
v___y_823_ = v_val_880_;
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
v___y_840_ = v___x_895_;
v___y_841_ = v___x_851_;
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
v___y_840_ = v___x_895_;
v___y_841_ = v___x_851_;
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
lean_inc_ref(v___y_1325_);
v___x_1327_ = l_Lean_mkAppB(v___y_1325_, v_type_1322_, v___y_1326_);
v___x_1328_ = l_Lean_Expr_app___override(v___y_1324_, v___x_1327_);
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
v___y_1324_ = v___x_1331_;
v___y_1325_ = v___x_1335_;
v___y_1326_ = v___x_1343_;
goto v___jp_1323_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = l_Int_toNat(v_val_1334_);
v___x_1345_ = l_Lean_instToExprInt_mkNat(v___x_1344_);
v___y_1324_ = v___x_1331_;
v___y_1325_ = v___x_1335_;
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
v___x_1408_ = l_Lean_Expr_app___override(v___x_1407_, v___y_1400_);
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
lean_inc_ref(v___y_1402_);
v___x_1416_ = l_Lean_Name_mkStr2(v___y_1402_, v___x_1415_);
v___x_1417_ = l_Lean_Expr_const___override(v___x_1416_, v___x_1382_);
v___x_1418_ = lean_int_neg(v_val_1410_);
v___x_1419_ = l_Int_toNat(v___x_1418_);
lean_dec(v___x_1418_);
v___x_1420_ = l_Lean_instToExprInt_mkNat(v___x_1419_);
lean_inc_ref(v___y_1400_);
v___x_1421_ = l_Lean_mkApp3(v___x_1414_, v___y_1400_, v___x_1417_, v___x_1420_);
v___y_1392_ = v___x_1406_;
v___y_1393_ = v___y_1400_;
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
v___y_1393_ = v___y_1400_;
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
lean_inc_ref(v___y_1425_);
lean_inc_ref(v___y_1429_);
v___x_1431_ = l_Lean_mkAppB(v___y_1429_, v___y_1425_, v___y_1430_);
v___y_1400_ = v___y_1425_;
v___y_1401_ = v___y_1426_;
v___y_1402_ = v___y_1427_;
v___y_1403_ = v___y_1428_;
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
v___y_1400_ = v_type_1437_;
v___y_1401_ = v___x_1435_;
v___y_1402_ = v___x_1436_;
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
v___y_1425_ = v_type_1437_;
v___y_1426_ = v___x_1435_;
v___y_1427_ = v___x_1436_;
v___y_1428_ = v___y_1433_;
v___y_1429_ = v___x_1440_;
v___y_1430_ = v___x_1448_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = l_Int_toNat(v_val_1439_);
v___x_1450_ = l_Lean_instToExprInt_mkNat(v___x_1449_);
v___y_1425_ = v_type_1437_;
v___y_1426_ = v___x_1435_;
v___y_1427_ = v___x_1436_;
v___y_1428_ = v___y_1433_;
v___y_1429_ = v___x_1440_;
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
v___x_1528_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v___y_1526_, v___y_1525_, v_y_1514_);
v___x_1529_ = l_Lean_mkApp9(v___x_1519_, v___y_1522_, v___y_1524_, v___y_1521_, v___y_1523_, v___y_1527_, v___x_1528_, v_v_1515_, v_px_1516_, v_py_1517_);
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
v___y_1521_ = v___y_1533_;
v___y_1522_ = v___y_1531_;
v___y_1523_ = v___x_1537_;
v___y_1524_ = v___y_1532_;
v___y_1525_ = v_cons_1536_;
v___y_1526_ = v_nil_1535_;
v___y_1527_ = v___x_1545_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = l_Int_toNat(v_b_1513_);
v___x_1547_ = l_Lean_instToExprInt_mkNat(v___x_1546_);
v___y_1521_ = v___y_1533_;
v___y_1522_ = v___y_1531_;
v___y_1523_ = v___x_1537_;
v___y_1524_ = v___y_1532_;
v___y_1525_ = v_cons_1536_;
v___y_1526_ = v_nil_1535_;
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
v___y_1531_ = v___y_1549_;
v___y_1532_ = v___y_1550_;
v___y_1533_ = v___x_1559_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = l_Int_toNat(v_a_1511_);
v___x_1561_ = l_Lean_instToExprInt_mkNat(v___x_1560_);
v___y_1531_ = v___y_1549_;
v___y_1532_ = v___y_1550_;
v___y_1533_ = v___x_1561_;
goto v___jp_1530_;
}
}
v___jp_1562_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_inc_ref(v___y_1564_);
v___x_1568_ = l_Lean_mkAppB(v___y_1564_, v___y_1566_, v___y_1567_);
v___x_1569_ = l_Lean_Expr_app___override(v___y_1565_, v___x_1568_);
v___y_1549_ = v___y_1563_;
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
v___x_1579_ = l_Lean_Expr_app___override(v___x_1578_, v___y_1574_);
v___x_1580_ = l_Lean_Expr_app___override(v___x_1577_, v___x_1579_);
v___y_1549_ = v___y_1571_;
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
lean_inc_ref(v___y_1574_);
v___x_1592_ = l_Lean_mkApp3(v___x_1585_, v___y_1574_, v___x_1588_, v___x_1591_);
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
lean_inc_ref(v___y_1600_);
lean_inc_ref(v___y_1596_);
v___x_1602_ = l_Lean_mkAppB(v___y_1596_, v___y_1600_, v___y_1601_);
v___y_1571_ = v___y_1597_;
v___y_1572_ = v___y_1599_;
v___y_1573_ = v___y_1598_;
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
v___y_1571_ = v___y_1604_;
v___y_1572_ = v___x_1607_;
v___y_1573_ = v___x_1606_;
v___y_1574_ = v_type_1608_;
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
v___y_1596_ = v___x_1611_;
v___y_1597_ = v___y_1604_;
v___y_1598_ = v___x_1606_;
v___y_1599_ = v___x_1607_;
v___y_1600_ = v_type_1608_;
v___y_1601_ = v___x_1619_;
goto v___jp_1595_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = l_Int_toNat(v_val_1610_);
v___x_1621_ = l_Lean_instToExprInt_mkNat(v___x_1620_);
v___y_1596_ = v___x_1611_;
v___y_1597_ = v___y_1604_;
v___y_1598_ = v___x_1606_;
v___y_1599_ = v___x_1607_;
v___y_1600_ = v_type_1608_;
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
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_unsigned_to_nat(1u);
v___x_1710_ = l_Lean_Level_ofNat(v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Justification_bmodProof(lean_object* v_m_1711_, lean_object* v_r_1712_, lean_object* v_i_1713_, lean_object* v_x_1714_, lean_object* v_v_1715_, lean_object* v_w_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_m_1722_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v_____do__lift_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1765_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_m_1722_ = l_Lean_mkNatLit(v_m_1711_);
v___x_1784_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_1785_ = lean_int_dec_le(v___x_1784_, v_r_1712_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1786_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_1787_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_1788_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_1789_ = lean_int_neg(v_r_1712_);
v___x_1790_ = l_Int_toNat(v___x_1789_);
lean_dec(v___x_1789_);
v___x_1791_ = l_Lean_instToExprInt_mkNat(v___x_1790_);
v___x_1792_ = l_Lean_mkApp3(v___x_1786_, v___x_1787_, v___x_1788_, v___x_1791_);
v___y_1765_ = v___x_1792_;
goto v___jp_1764_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = l_Int_toNat(v_r_1712_);
v___x_1794_ = l_Lean_instToExprInt_mkNat(v___x_1793_);
v___y_1765_ = v___x_1794_;
goto v___jp_1764_;
}
v___jp_1723_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1733_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__2));
lean_inc_n(v___y_1725_, 4);
lean_inc(v_____do__lift_1728_);
v___x_1734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1734_, 0, v_____do__lift_1728_);
lean_ctor_set(v___x_1734_, 1, v___y_1725_);
v___x_1735_ = l_Lean_Expr_const___override(v___x_1733_, v___x_1734_);
v___x_1736_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__4));
v___x_1737_ = l_Lean_Expr_const___override(v___x_1736_, v___y_1725_);
v___x_1738_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__6));
v___x_1739_ = l_Lean_Expr_const___override(v___x_1738_, v___y_1725_);
v___x_1740_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__9));
v___x_1741_ = l_Lean_Expr_const___override(v___x_1740_, v___y_1725_);
lean_inc_ref(v___y_1727_);
v___x_1742_ = l_Lean_Expr_app___override(v___x_1741_, v___y_1727_);
lean_inc_ref(v___y_1726_);
v___x_1743_ = l_Lean_mkApp4(v___x_1735_, v___x_1737_, v___x_1739_, v___x_1742_, v___y_1726_);
v___x_1744_ = l_Lean_Meta_mkDecideProof(v___x_1743_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref_known(v___x_1744_, 1);
v___x_1746_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__11));
lean_inc_n(v___y_1725_, 2);
v___x_1747_ = l_Lean_Expr_const___override(v___x_1746_, v___y_1725_);
lean_inc_ref(v___y_1726_);
lean_inc_ref_n(v_v_1715_, 2);
v___x_1748_ = l_Lean_mkAppB(v___x_1747_, v_v_1715_, v___y_1726_);
v___x_1749_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13));
v___x_1750_ = l_Lean_Expr_const___override(v___x_1749_, v___y_1725_);
lean_inc_ref(v___y_1727_);
lean_inc_ref(v_m_1722_);
v___x_1751_ = l_Lean_mkApp3(v___x_1750_, v_m_1722_, v___y_1727_, v_v_1715_);
v___x_1752_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(v___x_1748_, v___x_1751_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1763_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1763_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1763_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1757_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__15));
lean_inc(v___y_1725_);
v___x_1758_ = l_Lean_Expr_const___override(v___x_1757_, v___y_1725_);
v___x_1759_ = l_Lean_mkApp8(v___x_1758_, v_m_1722_, v___y_1724_, v___y_1726_, v___y_1727_, v_v_1715_, v_a_1745_, v_a_1753_, v_w_1716_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1759_);
v___x_1761_ = v___x_1755_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
else
{
lean_dec(v_a_1745_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v_m_1722_);
lean_dec_ref(v_w_1716_);
lean_dec_ref(v_v_1715_);
return v___x_1752_;
}
}
else
{
lean_dec_ref(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v_m_1722_);
lean_dec_ref(v_w_1716_);
lean_dec_ref(v_v_1715_);
return v___x_1744_;
}
}
v___jp_1764_:
{
lean_object* v_i_1766_; lean_object* v___x_1767_; lean_object* v_nil_1768_; lean_object* v_cons_1769_; lean_object* v_x_1770_; lean_object* v___x_1771_; 
v_i_1766_ = l_Lean_mkNatLit(v_i_1713_);
v___x_1767_ = lean_box(0);
v_nil_1768_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_1769_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v_x_1770_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_1768_, v_cons_1769_, v_x_1714_);
v___x_1771_ = l_Lean_leCarrierIsSort(v_a_1719_, v_a_1720_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; uint8_t v___x_1773_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v___x_1773_ = lean_unbox(v_a_1772_);
lean_dec(v_a_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__21);
v___y_1724_ = v___y_1765_;
v___y_1725_ = v___x_1767_;
v___y_1726_ = v_i_1766_;
v___y_1727_ = v_x_1770_;
v_____do__lift_1728_ = v___x_1774_;
v___y_1729_ = v_a_1717_;
v___y_1730_ = v_a_1718_;
v___y_1731_ = v_a_1719_;
v___y_1732_ = v_a_1720_;
goto v___jp_1723_;
}
else
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16, &l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__16);
v___y_1724_ = v___y_1765_;
v___y_1725_ = v___x_1767_;
v___y_1726_ = v_i_1766_;
v___y_1727_ = v_x_1770_;
v_____do__lift_1728_ = v___x_1775_;
v___y_1729_ = v_a_1717_;
v___y_1730_ = v_a_1718_;
v___y_1731_ = v_a_1719_;
v___y_1732_ = v_a_1720_;
goto v___jp_1723_;
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec_ref(v_x_1770_);
lean_dec_ref(v_i_1766_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v_m_1722_);
lean_dec_ref(v_w_1716_);
lean_dec_ref(v_v_1715_);
v_a_1776_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1771_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1771_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
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
v___x_1807_ = l_instMonadEIO___redArg();
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
lean_object* v_i_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_3464__overap_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec_ref(v_v_1815_);
v_i_1873_ = lean_ctor_get(v_x_1817_, 2);
lean_inc(v_i_1873_);
lean_dec_ref_known(v_x_1817_, 3);
v___x_1874_ = l_Lean_instInhabitedExpr;
v___x_1875_ = l_instInhabitedOfMonad___redArg(v___x_1872_, v___x_1874_);
v___x_3464__overap_1876_ = lean_array_get(v___x_1875_, v_assumptions_1816_, v_i_1873_);
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
v___x_1878_ = lean_apply_10(v___x_3464__overap_1876_, v_a_1818_, v_a_1819_, v_a_1820_, v___x_1877_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, lean_box(0));
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
lean_dec_ref_known(v_x_1817_, 3);
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
lean_dec_ref_known(v_x_1817_, 5);
lean_inc_ref(v_v_1815_);
v___x_1896_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_c_1814_, v_v_1815_, v_assumptions_1816_, v_j_1894_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1898_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
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
lean_dec_ref_known(v_x_1817_, 8);
lean_inc_ref(v_v_1815_);
v___x_1916_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1910_, v_v_1815_, v_assumptions_1816_, v_j_1913_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
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
lean_dec_ref_known(v_x_1817_, 5);
lean_inc_ref(v_v_1815_);
v___x_1933_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_1931_, v_v_1815_, v_assumptions_1816_, v_j_1932_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1935_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
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
lean_dec_ref_known(v___x_2002_, 1);
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
lean_inc(v_coeffs_2022_);
v___x_2031_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_2018_, v_b_2020_, v_coeffs_2022_, v_coeffs_2025_);
lean_inc_ref(v_constraint_2026_);
lean_inc(v_b_2020_);
lean_inc_ref(v_constraint_2023_);
lean_inc(v_a_2018_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__0(lean_object* v_a_2102_, lean_object* v_b_2103_, lean_object* v_d_2104_){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v_a_2102_);
lean_ctor_set(v___x_2105_, 1, v_b_2103_);
v___x_2106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v_d_2104_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__1(lean_object* v___x_2107_, lean_object* v_x_2108_){
_start:
{
lean_object* v_snd_2109_; lean_object* v_constraint_2110_; lean_object* v_fst_2111_; lean_object* v_lowerBound_2112_; lean_object* v_upperBound_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___y_2118_; lean_object* v___y_2119_; 
v_snd_2109_ = lean_ctor_get(v_x_2108_, 1);
v_constraint_2110_ = lean_ctor_get(v_snd_2109_, 1);
lean_inc_ref(v_constraint_2110_);
v_fst_2111_ = lean_ctor_get(v_x_2108_, 0);
lean_inc(v_fst_2111_);
lean_dec_ref(v_x_2108_);
v_lowerBound_2112_ = lean_ctor_get(v_constraint_2110_, 0);
lean_inc(v_lowerBound_2112_);
v_upperBound_2113_ = lean_ctor_get(v_constraint_2110_, 1);
lean_inc(v_upperBound_2113_);
lean_dec_ref(v_constraint_2110_);
v___x_2114_ = l_List_toString___redArg(v___x_2107_, v_fst_2111_);
v___x_2115_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_2116_ = lean_string_append(v___x_2114_, v___x_2115_);
if (lean_obj_tag(v_lowerBound_2112_) == 0)
{
if (lean_obj_tag(v_upperBound_2113_) == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_2125_ = lean_string_append(v___x_2116_, v___x_2124_);
return v___x_2125_;
}
else
{
lean_object* v_val_2126_; lean_object* v___x_2127_; lean_object* v___y_2129_; lean_object* v_intZero_2134_; uint8_t v_isNeg_2135_; 
v_val_2126_ = lean_ctor_get(v_upperBound_2113_, 0);
lean_inc(v_val_2126_);
lean_dec_ref_known(v_upperBound_2113_, 1);
v___x_2127_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_2134_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2135_ = lean_int_dec_lt(v_val_2126_, v_intZero_2134_);
if (v_isNeg_2135_ == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; 
v_a_2136_ = lean_nat_abs(v_val_2126_);
lean_dec(v_val_2126_);
v___x_2137_ = l_Nat_reprFast(v_a_2136_);
v___y_2129_ = v___x_2137_;
goto v___jp_2128_;
}
else
{
lean_object* v_abs_2138_; lean_object* v_one_2139_; lean_object* v_a_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v_abs_2138_ = lean_nat_abs(v_val_2126_);
lean_dec(v_val_2126_);
v_one_2139_ = lean_unsigned_to_nat(1u);
v_a_2140_ = lean_nat_sub(v_abs_2138_, v_one_2139_);
lean_dec(v_abs_2138_);
v___x_2141_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2142_ = lean_nat_add(v_a_2140_, v_one_2139_);
lean_dec(v_a_2140_);
v___x_2143_ = l_Nat_reprFast(v___x_2142_);
v___x_2144_ = lean_string_append(v___x_2141_, v___x_2143_);
lean_dec_ref(v___x_2143_);
v___y_2129_ = v___x_2144_;
goto v___jp_2128_;
}
v___jp_2128_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2130_ = lean_string_append(v___x_2127_, v___y_2129_);
lean_dec_ref(v___y_2129_);
v___x_2131_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2132_ = lean_string_append(v___x_2130_, v___x_2131_);
v___x_2133_ = lean_string_append(v___x_2116_, v___x_2132_);
lean_dec_ref(v___x_2132_);
return v___x_2133_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_2113_) == 0)
{
lean_object* v_val_2145_; lean_object* v___x_2146_; lean_object* v___y_2148_; lean_object* v_intZero_2153_; uint8_t v_isNeg_2154_; 
v_val_2145_ = lean_ctor_get(v_lowerBound_2112_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v_lowerBound_2112_, 1);
v___x_2146_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2153_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2154_ = lean_int_dec_lt(v_val_2145_, v_intZero_2153_);
if (v_isNeg_2154_ == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2156_; 
v_a_2155_ = lean_nat_abs(v_val_2145_);
lean_dec(v_val_2145_);
v___x_2156_ = l_Nat_reprFast(v_a_2155_);
v___y_2148_ = v___x_2156_;
goto v___jp_2147_;
}
else
{
lean_object* v_abs_2157_; lean_object* v_one_2158_; lean_object* v_a_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_abs_2157_ = lean_nat_abs(v_val_2145_);
lean_dec(v_val_2145_);
v_one_2158_ = lean_unsigned_to_nat(1u);
v_a_2159_ = lean_nat_sub(v_abs_2157_, v_one_2158_);
lean_dec(v_abs_2157_);
v___x_2160_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2161_ = lean_nat_add(v_a_2159_, v_one_2158_);
lean_dec(v_a_2159_);
v___x_2162_ = l_Nat_reprFast(v___x_2161_);
v___x_2163_ = lean_string_append(v___x_2160_, v___x_2162_);
lean_dec_ref(v___x_2162_);
v___y_2148_ = v___x_2163_;
goto v___jp_2147_;
}
v___jp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2149_ = lean_string_append(v___x_2146_, v___y_2148_);
lean_dec_ref(v___y_2148_);
v___x_2150_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_2151_ = lean_string_append(v___x_2149_, v___x_2150_);
v___x_2152_ = lean_string_append(v___x_2116_, v___x_2151_);
lean_dec_ref(v___x_2151_);
return v___x_2152_;
}
}
else
{
lean_object* v_val_2164_; lean_object* v_val_2165_; uint8_t v___x_2166_; 
v_val_2164_ = lean_ctor_get(v_lowerBound_2112_, 0);
lean_inc(v_val_2164_);
lean_dec_ref_known(v_lowerBound_2112_, 1);
v_val_2165_ = lean_ctor_get(v_upperBound_2113_, 0);
lean_inc(v_val_2165_);
lean_dec_ref_known(v_upperBound_2113_, 1);
v___x_2166_ = lean_int_dec_lt(v_val_2165_, v_val_2164_);
if (v___x_2166_ == 0)
{
uint8_t v___x_2167_; 
v___x_2167_ = lean_int_dec_eq(v_val_2164_, v_val_2165_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v___y_2170_; lean_object* v_intZero_2185_; uint8_t v_isNeg_2186_; 
v___x_2168_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_2185_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2186_ = lean_int_dec_lt(v_val_2164_, v_intZero_2185_);
if (v_isNeg_2186_ == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2188_; 
v_a_2187_ = lean_nat_abs(v_val_2164_);
lean_dec(v_val_2164_);
v___x_2188_ = l_Nat_reprFast(v_a_2187_);
v___y_2170_ = v___x_2188_;
goto v___jp_2169_;
}
else
{
lean_object* v_abs_2189_; lean_object* v_one_2190_; lean_object* v_a_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_abs_2189_ = lean_nat_abs(v_val_2164_);
lean_dec(v_val_2164_);
v_one_2190_ = lean_unsigned_to_nat(1u);
v_a_2191_ = lean_nat_sub(v_abs_2189_, v_one_2190_);
lean_dec(v_abs_2189_);
v___x_2192_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2193_ = lean_nat_add(v_a_2191_, v_one_2190_);
lean_dec(v_a_2191_);
v___x_2194_ = l_Nat_reprFast(v___x_2193_);
v___x_2195_ = lean_string_append(v___x_2192_, v___x_2194_);
lean_dec_ref(v___x_2194_);
v___y_2170_ = v___x_2195_;
goto v___jp_2169_;
}
v___jp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v_intZero_2174_; uint8_t v_isNeg_2175_; 
v___x_2171_ = lean_string_append(v___x_2168_, v___y_2170_);
lean_dec_ref(v___y_2170_);
v___x_2172_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_2173_ = lean_string_append(v___x_2171_, v___x_2172_);
v_intZero_2174_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2175_ = lean_int_dec_lt(v_val_2165_, v_intZero_2174_);
if (v_isNeg_2175_ == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2177_; 
v_a_2176_ = lean_nat_abs(v_val_2165_);
lean_dec(v_val_2165_);
v___x_2177_ = l_Nat_reprFast(v_a_2176_);
v___y_2118_ = v___x_2173_;
v___y_2119_ = v___x_2177_;
goto v___jp_2117_;
}
else
{
lean_object* v_abs_2178_; lean_object* v_one_2179_; lean_object* v_a_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v_abs_2178_ = lean_nat_abs(v_val_2165_);
lean_dec(v_val_2165_);
v_one_2179_ = lean_unsigned_to_nat(1u);
v_a_2180_ = lean_nat_sub(v_abs_2178_, v_one_2179_);
lean_dec(v_abs_2178_);
v___x_2181_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2182_ = lean_nat_add(v_a_2180_, v_one_2179_);
lean_dec(v_a_2180_);
v___x_2183_ = l_Nat_reprFast(v___x_2182_);
v___x_2184_ = lean_string_append(v___x_2181_, v___x_2183_);
lean_dec_ref(v___x_2183_);
v___y_2118_ = v___x_2173_;
v___y_2119_ = v___x_2184_;
goto v___jp_2117_;
}
}
}
else
{
lean_object* v___x_2196_; lean_object* v___y_2198_; lean_object* v_intZero_2203_; uint8_t v_isNeg_2204_; 
lean_dec(v_val_2165_);
v___x_2196_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_2203_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2204_ = lean_int_dec_lt(v_val_2164_, v_intZero_2203_);
if (v_isNeg_2204_ == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2206_; 
v_a_2205_ = lean_nat_abs(v_val_2164_);
lean_dec(v_val_2164_);
v___x_2206_ = l_Nat_reprFast(v_a_2205_);
v___y_2198_ = v___x_2206_;
goto v___jp_2197_;
}
else
{
lean_object* v_abs_2207_; lean_object* v_one_2208_; lean_object* v_a_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v_abs_2207_ = lean_nat_abs(v_val_2164_);
lean_dec(v_val_2164_);
v_one_2208_ = lean_unsigned_to_nat(1u);
v_a_2209_ = lean_nat_sub(v_abs_2207_, v_one_2208_);
lean_dec(v_abs_2207_);
v___x_2210_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_2211_ = lean_nat_add(v_a_2209_, v_one_2208_);
lean_dec(v_a_2209_);
v___x_2212_ = l_Nat_reprFast(v___x_2211_);
v___x_2213_ = lean_string_append(v___x_2210_, v___x_2212_);
lean_dec_ref(v___x_2212_);
v___y_2198_ = v___x_2213_;
goto v___jp_2197_;
}
v___jp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2199_ = lean_string_append(v___x_2196_, v___y_2198_);
lean_dec_ref(v___y_2198_);
v___x_2200_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_2201_ = lean_string_append(v___x_2199_, v___x_2200_);
v___x_2202_ = lean_string_append(v___x_2116_, v___x_2201_);
lean_dec_ref(v___x_2201_);
return v___x_2202_;
}
}
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
lean_dec(v_val_2165_);
lean_dec(v_val_2164_);
v___x_2214_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_2215_ = lean_string_append(v___x_2116_, v___x_2214_);
return v___x_2215_;
}
}
}
v___jp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2120_ = lean_string_append(v___y_2118_, v___y_2119_);
lean_dec_ref(v___y_2119_);
v___x_2121_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_2122_ = lean_string_append(v___x_2120_, v___x_2121_);
v___x_2123_ = lean_string_append(v___x_2116_, v___x_2122_);
lean_dec_ref(v___x_2122_);
return v___x_2123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2(lean_object* v___x_2216_, lean_object* v___f_2217_, lean_object* v_l_2218_, lean_object* v_acc_2219_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_2216_, v___f_2217_, v_acc_2219_, v_l_2218_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3(lean_object* v___f_2242_, lean_object* v___f_2243_, lean_object* v_p_2244_){
_start:
{
uint8_t v_possible_2245_; 
v_possible_2245_ = lean_ctor_get_uint8(v_p_2244_, sizeof(void*)*7);
if (v_possible_2245_ == 0)
{
lean_object* v___x_2246_; 
lean_dec_ref(v_p_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___f_2242_);
v___x_2246_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__0));
return v___x_2246_;
}
else
{
lean_object* v_constraints_2247_; uint8_t v___x_2248_; 
v_constraints_2247_ = lean_ctor_get(v_p_2244_, 2);
lean_inc_ref(v_constraints_2247_);
v___x_2248_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_2244_);
lean_dec_ref(v_p_2244_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; lean_object* v_buckets_2250_; lean_object* v___x_2251_; lean_object* v___y_2253_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; 
v___x_2249_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__10));
v_buckets_2250_ = lean_ctor_get(v_constraints_2247_, 1);
lean_inc_ref(v_buckets_2250_);
lean_dec_ref(v_constraints_2247_);
v___x_2251_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_2257_ = lean_box(0);
v___x_2258_ = lean_array_get_size(v_buckets_2250_);
v___x_2259_ = lean_unsigned_to_nat(0u);
v___x_2260_ = lean_nat_dec_lt(v___x_2259_, v___x_2258_);
if (v___x_2260_ == 0)
{
lean_dec_ref(v_buckets_2250_);
lean_dec_ref(v___f_2243_);
v___y_2253_ = v___x_2257_;
goto v___jp_2252_;
}
else
{
lean_object* v___f_2261_; size_t v___x_2262_; size_t v___x_2263_; lean_object* v___x_2264_; 
v___f_2261_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__2), 4, 2);
lean_closure_set(v___f_2261_, 0, v___x_2249_);
lean_closure_set(v___f_2261_, 1, v___f_2243_);
v___x_2262_ = lean_usize_of_nat(v___x_2258_);
v___x_2263_ = ((size_t)0ULL);
v___x_2264_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2249_, v___f_2261_, v_buckets_2250_, v___x_2262_, v___x_2263_, v___x_2257_);
v___y_2253_ = v___x_2264_;
goto v___jp_2252_;
}
v___jp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2254_ = lean_box(0);
v___x_2255_ = l_List_mapTR_loop___redArg(v___f_2242_, v___y_2253_, v___x_2254_);
v___x_2256_ = l_String_intercalate(v___x_2251_, v___x_2255_);
return v___x_2256_;
}
}
else
{
lean_object* v___x_2265_; 
lean_dec_ref(v_constraints_2247_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___f_2242_);
v___x_2265_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToString___lam__3___closed__11));
return v___x_2265_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = lean_box(0);
v___x_2281_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__1));
v___x_2282_ = l_Lean_Expr_const___override(v___x_2281_, v___x_2280_);
return v___x_2282_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = lean_box(0);
v___x_2289_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__5));
v___x_2290_ = l_Lean_Expr_const___override(v___x_2289_, v___x_2288_);
return v___x_2290_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = lean_box(0);
v___x_2298_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__8));
v___x_2299_ = l_Lean_Expr_const___override(v___x_2298_, v___x_2297_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse(lean_object* v_s_2300_, lean_object* v_x_2301_, lean_object* v_j_2302_, lean_object* v_assumptions_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, uint8_t v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_2305_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2316_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc_n(v_a_2315_, 2);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2316_ = l_Lean_Elab_Tactic_Omega_Justification_proof___redArg(v_x_2301_, v_a_2315_, v_assumptions_2303_, v_j_2302_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; lean_object* v_lowerBound_2319_; lean_object* v_upperBound_2320_; lean_object* v_nil_2321_; lean_object* v_cons_2322_; lean_object* v___x_2323_; lean_object* v___y_2325_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___x_2348_; lean_object* v___y_2350_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v_lowerBound_2319_ = lean_ctor_get(v_s_2300_, 0);
v_upperBound_2320_ = lean_ctor_get(v_s_2300_, 1);
v_nil_2321_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_2322_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_2323_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_2321_, v_cons_2322_, v_x_2301_);
v___x_2348_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__2);
if (lean_obj_tag(v_lowerBound_2319_) == 0)
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___y_2350_ = v___x_2366_;
goto v___jp_2349_;
}
else
{
lean_object* v_val_2367_; lean_object* v___x_2368_; lean_object* v___y_2370_; lean_object* v___x_2372_; uint8_t v___x_2373_; 
v_val_2367_ = lean_ctor_get(v_lowerBound_2319_, 0);
v___x_2368_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2372_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2373_ = lean_int_dec_le(v___x_2372_, v_val_2367_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2374_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2375_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2376_ = lean_int_neg(v_val_2367_);
v___x_2377_ = l_Int_toNat(v___x_2376_);
lean_dec(v___x_2376_);
v___x_2378_ = l_Lean_instToExprInt_mkNat(v___x_2377_);
v___x_2379_ = l_Lean_mkApp3(v___x_2374_, v___x_2318_, v___x_2375_, v___x_2378_);
v___y_2370_ = v___x_2379_;
goto v___jp_2369_;
}
else
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = l_Int_toNat(v_val_2367_);
v___x_2381_ = l_Lean_instToExprInt_mkNat(v___x_2380_);
v___y_2370_ = v___x_2381_;
goto v___jp_2369_;
}
v___jp_2369_:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_mkAppB(v___x_2368_, v___x_2318_, v___y_2370_);
v___y_2350_ = v___x_2371_;
goto v___jp_2349_;
}
}
v___jp_2324_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2326_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__2);
lean_inc_ref(v___y_2325_);
v___x_2327_ = l_Lean_Expr_app___override(v___x_2326_, v___y_2325_);
v___x_2328_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__6);
v___x_2329_ = l_Lean_Meta_mkEq(v___x_2327_, v___x_2328_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2331_ = l_Lean_Meta_mkDecideProof(v_a_2330_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2341_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2334_ = v___x_2331_;
v_isShared_2335_ = v_isSharedCheck_2341_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2341_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2336_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9, &l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9_once, _init_l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__9);
v___x_2337_ = l_Lean_mkApp5(v___x_2336_, v___y_2325_, v_a_2332_, v___x_2323_, v_a_2315_, v_a_2317_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2337_);
v___x_2339_ = v___x_2334_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
else
{
lean_dec_ref(v___y_2325_);
lean_dec_ref(v___x_2323_);
lean_dec(v_a_2317_);
lean_dec(v_a_2315_);
return v___x_2331_;
}
}
else
{
lean_dec_ref(v___y_2325_);
lean_dec_ref(v___x_2323_);
lean_dec(v_a_2317_);
lean_dec(v_a_2315_);
return v___x_2329_;
}
}
v___jp_2342_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_inc_ref(v___y_2344_);
v___x_2346_ = l_Lean_mkAppB(v___y_2344_, v___x_2318_, v___y_2345_);
v___x_2347_ = l_Lean_Expr_app___override(v___y_2343_, v___x_2346_);
v___y_2325_ = v___x_2347_;
goto v___jp_2324_;
}
v___jp_2349_:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Lean_Expr_app___override(v___x_2348_, v___y_2350_);
if (lean_obj_tag(v_upperBound_2320_) == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__7);
v___x_2353_ = l_Lean_Expr_app___override(v___x_2351_, v___x_2352_);
v___y_2325_ = v___x_2353_;
goto v___jp_2324_;
}
else
{
lean_object* v_val_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v_val_2354_ = lean_ctor_get(v_upperBound_2320_, 0);
v___x_2355_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10, &l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Omega_instToExprConstraint___lam__0___closed__10);
v___x_2356_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2357_ = lean_int_dec_le(v___x_2356_, v_val_2354_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2358_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_2359_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_2360_ = lean_int_neg(v_val_2354_);
v___x_2361_ = l_Int_toNat(v___x_2360_);
lean_dec(v___x_2360_);
v___x_2362_ = l_Lean_instToExprInt_mkNat(v___x_2361_);
v___x_2363_ = l_Lean_mkApp3(v___x_2358_, v___x_2318_, v___x_2359_, v___x_2362_);
v___y_2343_ = v___x_2351_;
v___y_2344_ = v___x_2355_;
v___y_2345_ = v___x_2363_;
goto v___jp_2342_;
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = l_Int_toNat(v_val_2354_);
v___x_2365_ = l_Lean_instToExprInt_mkNat(v___x_2364_);
v___y_2343_ = v___x_2351_;
v___y_2344_ = v___x_2355_;
v___y_2345_ = v___x_2365_;
goto v___jp_2342_;
}
}
}
}
else
{
lean_dec(v_a_2315_);
return v___x_2316_;
}
}
else
{
lean_dec_ref(v_j_2302_);
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed(lean_object* v_s_2382_, lean_object* v_x_2383_, lean_object* v_j_2384_, lean_object* v_assumptions_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
uint8_t v_a_boxed_2396_; lean_object* v_res_2397_; 
v_a_boxed_2396_ = lean_unbox(v_a_2389_);
v_res_2397_ = l_Lean_Elab_Tactic_Omega_Problem_proveFalse(v_s_2382_, v_x_2383_, v_j_2384_, v_assumptions_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_boxed_2396_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_assumptions_2385_);
lean_dec(v_x_2383_);
lean_dec_ref(v_s_2382_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0(lean_object* v_constraint_2398_, lean_object* v_coeffs_2399_, lean_object* v_justification_2400_, lean_object* v_x_2401_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_Elab_Tactic_Omega_Justification_toString(v_constraint_2398_, v_coeffs_2399_, v_justification_2400_);
return v___x_2402_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(lean_object* v_a_2403_, lean_object* v_x_2404_){
_start:
{
if (lean_obj_tag(v_x_2404_) == 0)
{
uint8_t v___x_2405_; 
v___x_2405_ = 0;
return v___x_2405_;
}
else
{
lean_object* v_key_2406_; lean_object* v_tail_2407_; uint8_t v___x_2408_; 
v_key_2406_ = lean_ctor_get(v_x_2404_, 0);
v_tail_2407_ = lean_ctor_get(v_x_2404_, 2);
v___x_2408_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2406_, v_a_2403_);
if (v___x_2408_ == 0)
{
v_x_2404_ = v_tail_2407_;
goto _start;
}
else
{
return v___x_2408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg___boxed(lean_object* v_a_2410_, lean_object* v_x_2411_){
_start:
{
uint8_t v_res_2412_; lean_object* v_r_2413_; 
v_res_2412_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2410_, v_x_2411_);
lean_dec(v_x_2411_);
lean_dec(v_a_2410_);
v_r_2413_ = lean_box(v_res_2412_);
return v_r_2413_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(uint64_t v_x_2414_, lean_object* v_x_2415_){
_start:
{
if (lean_obj_tag(v_x_2415_) == 0)
{
return v_x_2414_;
}
else
{
lean_object* v_head_2416_; lean_object* v_tail_2417_; lean_object* v_intZero_2418_; uint8_t v_isNeg_2419_; 
v_head_2416_ = lean_ctor_get(v_x_2415_, 0);
v_tail_2417_ = lean_ctor_get(v_x_2415_, 1);
v_intZero_2418_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_2419_ = lean_int_dec_lt(v_head_2416_, v_intZero_2418_);
if (v_isNeg_2419_ == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; uint64_t v___x_2423_; uint64_t v___x_2424_; 
v_a_2420_ = lean_nat_abs(v_head_2416_);
v___x_2421_ = lean_unsigned_to_nat(2u);
v___x_2422_ = lean_nat_mul(v___x_2421_, v_a_2420_);
lean_dec(v_a_2420_);
v___x_2423_ = lean_uint64_of_nat(v___x_2422_);
lean_dec(v___x_2422_);
v___x_2424_ = lean_uint64_mix_hash(v_x_2414_, v___x_2423_);
v_x_2414_ = v___x_2424_;
v_x_2415_ = v_tail_2417_;
goto _start;
}
else
{
lean_object* v_abs_2426_; lean_object* v_one_2427_; lean_object* v_a_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; uint64_t v___x_2432_; uint64_t v___x_2433_; 
v_abs_2426_ = lean_nat_abs(v_head_2416_);
v_one_2427_ = lean_unsigned_to_nat(1u);
v_a_2428_ = lean_nat_sub(v_abs_2426_, v_one_2427_);
lean_dec(v_abs_2426_);
v___x_2429_ = lean_unsigned_to_nat(2u);
v___x_2430_ = lean_nat_mul(v___x_2429_, v_a_2428_);
lean_dec(v_a_2428_);
v___x_2431_ = lean_nat_add(v___x_2430_, v_one_2427_);
lean_dec(v___x_2430_);
v___x_2432_ = lean_uint64_of_nat(v___x_2431_);
lean_dec(v___x_2431_);
v___x_2433_ = lean_uint64_mix_hash(v_x_2414_, v___x_2432_);
v_x_2414_ = v___x_2433_;
v_x_2415_ = v_tail_2417_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0___boxed(lean_object* v_x_2435_, lean_object* v_x_2436_){
_start:
{
uint64_t v_x_806__boxed_2437_; uint64_t v_res_2438_; lean_object* v_r_2439_; 
v_x_806__boxed_2437_ = lean_unbox_uint64(v_x_2435_);
lean_dec_ref(v_x_2435_);
v_res_2438_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v_x_806__boxed_2437_, v_x_2436_);
lean_dec(v_x_2436_);
v_r_2439_ = lean_box_uint64(v_res_2438_);
return v_r_2439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_2440_, lean_object* v_x_2441_){
_start:
{
if (lean_obj_tag(v_x_2441_) == 0)
{
return v_x_2440_;
}
else
{
lean_object* v_key_2442_; lean_object* v_value_2443_; lean_object* v_tail_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2468_; 
v_key_2442_ = lean_ctor_get(v_x_2441_, 0);
v_value_2443_ = lean_ctor_get(v_x_2441_, 1);
v_tail_2444_ = lean_ctor_get(v_x_2441_, 2);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_x_2441_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2446_ = v_x_2441_;
v_isShared_2447_ = v_isSharedCheck_2468_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_tail_2444_);
lean_inc(v_value_2443_);
lean_inc(v_key_2442_);
lean_dec(v_x_2441_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2468_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; uint64_t v___x_2449_; uint64_t v___x_2450_; uint64_t v___x_2451_; uint64_t v___x_2452_; uint64_t v_fold_2453_; uint64_t v___x_2454_; uint64_t v___x_2455_; uint64_t v___x_2456_; size_t v___x_2457_; size_t v___x_2458_; size_t v___x_2459_; size_t v___x_2460_; size_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2448_ = lean_array_get_size(v_x_2440_);
v___x_2449_ = 7ULL;
v___x_2450_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2449_, v_key_2442_);
v___x_2451_ = 32ULL;
v___x_2452_ = lean_uint64_shift_right(v___x_2450_, v___x_2451_);
v_fold_2453_ = lean_uint64_xor(v___x_2450_, v___x_2452_);
v___x_2454_ = 16ULL;
v___x_2455_ = lean_uint64_shift_right(v_fold_2453_, v___x_2454_);
v___x_2456_ = lean_uint64_xor(v_fold_2453_, v___x_2455_);
v___x_2457_ = lean_uint64_to_usize(v___x_2456_);
v___x_2458_ = lean_usize_of_nat(v___x_2448_);
v___x_2459_ = ((size_t)1ULL);
v___x_2460_ = lean_usize_sub(v___x_2458_, v___x_2459_);
v___x_2461_ = lean_usize_land(v___x_2457_, v___x_2460_);
v___x_2462_ = lean_array_uget_borrowed(v_x_2440_, v___x_2461_);
lean_inc(v___x_2462_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 2, v___x_2462_);
v___x_2464_ = v___x_2446_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_key_2442_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_value_2443_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_array_uset(v_x_2440_, v___x_2461_, v___x_2464_);
v_x_2440_ = v___x_2465_;
v_x_2441_ = v_tail_2444_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(lean_object* v_i_2469_, lean_object* v_source_2470_, lean_object* v_target_2471_){
_start:
{
lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2472_ = lean_array_get_size(v_source_2470_);
v___x_2473_ = lean_nat_dec_lt(v_i_2469_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_dec_ref(v_source_2470_);
lean_dec(v_i_2469_);
return v_target_2471_;
}
else
{
lean_object* v_es_2474_; lean_object* v___x_2475_; lean_object* v_source_2476_; lean_object* v_target_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v_es_2474_ = lean_array_fget(v_source_2470_, v_i_2469_);
v___x_2475_ = lean_box(0);
v_source_2476_ = lean_array_fset(v_source_2470_, v_i_2469_, v___x_2475_);
v_target_2477_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_target_2471_, v_es_2474_);
v___x_2478_ = lean_unsigned_to_nat(1u);
v___x_2479_ = lean_nat_add(v_i_2469_, v___x_2478_);
lean_dec(v_i_2469_);
v_i_2469_ = v___x_2479_;
v_source_2470_ = v_source_2476_;
v_target_2471_ = v_target_2477_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(lean_object* v_data_2481_){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v_nbuckets_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2482_ = lean_array_get_size(v_data_2481_);
v___x_2483_ = lean_unsigned_to_nat(2u);
v_nbuckets_2484_ = lean_nat_mul(v___x_2482_, v___x_2483_);
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = lean_box(0);
v___x_2487_ = lean_mk_array(v_nbuckets_2484_, v___x_2486_);
v___x_2488_ = lean_array_propagate_mark(v_data_2481_, v___x_2487_);
v___x_2489_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v___x_2485_, v_data_2481_, v___x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(lean_object* v_m_2490_, lean_object* v_a_2491_, lean_object* v_b_2492_){
_start:
{
lean_object* v_size_2493_; lean_object* v_buckets_2494_; lean_object* v___x_2495_; uint64_t v___x_2496_; uint64_t v___x_2497_; uint64_t v___x_2498_; uint64_t v___x_2499_; uint64_t v_fold_2500_; uint64_t v___x_2501_; uint64_t v___x_2502_; uint64_t v___x_2503_; size_t v___x_2504_; size_t v___x_2505_; size_t v___x_2506_; size_t v___x_2507_; size_t v___x_2508_; lean_object* v_bkt_2509_; uint8_t v___x_2510_; 
v_size_2493_ = lean_ctor_get(v_m_2490_, 0);
v_buckets_2494_ = lean_ctor_get(v_m_2490_, 1);
v___x_2495_ = lean_array_get_size(v_buckets_2494_);
v___x_2496_ = 7ULL;
v___x_2497_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2496_, v_a_2491_);
v___x_2498_ = 32ULL;
v___x_2499_ = lean_uint64_shift_right(v___x_2497_, v___x_2498_);
v_fold_2500_ = lean_uint64_xor(v___x_2497_, v___x_2499_);
v___x_2501_ = 16ULL;
v___x_2502_ = lean_uint64_shift_right(v_fold_2500_, v___x_2501_);
v___x_2503_ = lean_uint64_xor(v_fold_2500_, v___x_2502_);
v___x_2504_ = lean_uint64_to_usize(v___x_2503_);
v___x_2505_ = lean_usize_of_nat(v___x_2495_);
v___x_2506_ = ((size_t)1ULL);
v___x_2507_ = lean_usize_sub(v___x_2505_, v___x_2506_);
v___x_2508_ = lean_usize_land(v___x_2504_, v___x_2507_);
v_bkt_2509_ = lean_array_uget_borrowed(v_buckets_2494_, v___x_2508_);
v___x_2510_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2491_, v_bkt_2509_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2531_; 
lean_inc_ref(v_buckets_2494_);
lean_inc(v_size_2493_);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_m_2490_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; lean_object* v_unused_2533_; 
v_unused_2532_ = lean_ctor_get(v_m_2490_, 1);
lean_dec(v_unused_2532_);
v_unused_2533_ = lean_ctor_get(v_m_2490_, 0);
lean_dec(v_unused_2533_);
v___x_2512_ = v_m_2490_;
v_isShared_2513_ = v_isSharedCheck_2531_;
goto v_resetjp_2511_;
}
else
{
lean_dec(v_m_2490_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2531_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2514_; lean_object* v_size_x27_2515_; lean_object* v___x_2516_; lean_object* v_buckets_x27_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v___x_2514_ = lean_unsigned_to_nat(1u);
v_size_x27_2515_ = lean_nat_add(v_size_2493_, v___x_2514_);
lean_dec(v_size_2493_);
lean_inc(v_bkt_2509_);
v___x_2516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2516_, 0, v_a_2491_);
lean_ctor_set(v___x_2516_, 1, v_b_2492_);
lean_ctor_set(v___x_2516_, 2, v_bkt_2509_);
v_buckets_x27_2517_ = lean_array_uset(v_buckets_2494_, v___x_2508_, v___x_2516_);
v___x_2518_ = lean_unsigned_to_nat(4u);
v___x_2519_ = lean_nat_mul(v_size_x27_2515_, v___x_2518_);
v___x_2520_ = lean_unsigned_to_nat(3u);
v___x_2521_ = lean_nat_div(v___x_2519_, v___x_2520_);
lean_dec(v___x_2519_);
v___x_2522_ = lean_array_get_size(v_buckets_x27_2517_);
v___x_2523_ = lean_nat_dec_le(v___x_2521_, v___x_2522_);
lean_dec(v___x_2521_);
if (v___x_2523_ == 0)
{
lean_object* v_val_2524_; lean_object* v___x_2526_; 
v_val_2524_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2517_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 1, v_val_2524_);
lean_ctor_set(v___x_2512_, 0, v_size_x27_2515_);
v___x_2526_ = v___x_2512_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_size_x27_2515_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v_val_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
else
{
lean_object* v___x_2529_; 
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 1, v_buckets_x27_2517_);
lean_ctor_set(v___x_2512_, 0, v_size_x27_2515_);
v___x_2529_ = v___x_2512_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_size_x27_2515_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_buckets_x27_2517_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_dec(v_b_2492_);
lean_dec(v_a_2491_);
return v_m_2490_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(lean_object* v_a_2534_, lean_object* v_b_2535_, lean_object* v_x_2536_){
_start:
{
if (lean_obj_tag(v_x_2536_) == 0)
{
lean_dec(v_b_2535_);
lean_dec(v_a_2534_);
return v_x_2536_;
}
else
{
lean_object* v_key_2537_; lean_object* v_value_2538_; lean_object* v_tail_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2551_; 
v_key_2537_ = lean_ctor_get(v_x_2536_, 0);
v_value_2538_ = lean_ctor_get(v_x_2536_, 1);
v_tail_2539_ = lean_ctor_get(v_x_2536_, 2);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_x_2536_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2541_ = v_x_2536_;
v_isShared_2542_ = v_isSharedCheck_2551_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_tail_2539_);
lean_inc(v_value_2538_);
lean_inc(v_key_2537_);
lean_dec(v_x_2536_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2551_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
uint8_t v___x_2543_; 
v___x_2543_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2537_, v_a_2534_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2544_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2534_, v_b_2535_, v_tail_2539_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 2, v___x_2544_);
v___x_2546_ = v___x_2541_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_key_2537_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_value_2538_);
lean_ctor_set(v_reuseFailAlloc_2547_, 2, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
else
{
lean_object* v___x_2549_; 
lean_dec(v_value_2538_);
lean_dec(v_key_2537_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 1, v_b_2535_);
lean_ctor_set(v___x_2541_, 0, v_a_2534_);
v___x_2549_ = v___x_2541_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2534_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_b_2535_);
lean_ctor_set(v_reuseFailAlloc_2550_, 2, v_tail_2539_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(lean_object* v_m_2552_, lean_object* v_a_2553_, lean_object* v_b_2554_){
_start:
{
lean_object* v_size_2555_; lean_object* v_buckets_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2600_; 
v_size_2555_ = lean_ctor_get(v_m_2552_, 0);
v_buckets_2556_ = lean_ctor_get(v_m_2552_, 1);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_m_2552_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2558_ = v_m_2552_;
v_isShared_2559_ = v_isSharedCheck_2600_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_buckets_2556_);
lean_inc(v_size_2555_);
lean_dec(v_m_2552_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2600_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; uint64_t v___x_2561_; uint64_t v___x_2562_; uint64_t v___x_2563_; uint64_t v___x_2564_; uint64_t v_fold_2565_; uint64_t v___x_2566_; uint64_t v___x_2567_; uint64_t v___x_2568_; size_t v___x_2569_; size_t v___x_2570_; size_t v___x_2571_; size_t v___x_2572_; size_t v___x_2573_; lean_object* v_bkt_2574_; uint8_t v___x_2575_; 
v___x_2560_ = lean_array_get_size(v_buckets_2556_);
v___x_2561_ = 7ULL;
v___x_2562_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2561_, v_a_2553_);
v___x_2563_ = 32ULL;
v___x_2564_ = lean_uint64_shift_right(v___x_2562_, v___x_2563_);
v_fold_2565_ = lean_uint64_xor(v___x_2562_, v___x_2564_);
v___x_2566_ = 16ULL;
v___x_2567_ = lean_uint64_shift_right(v_fold_2565_, v___x_2566_);
v___x_2568_ = lean_uint64_xor(v_fold_2565_, v___x_2567_);
v___x_2569_ = lean_uint64_to_usize(v___x_2568_);
v___x_2570_ = lean_usize_of_nat(v___x_2560_);
v___x_2571_ = ((size_t)1ULL);
v___x_2572_ = lean_usize_sub(v___x_2570_, v___x_2571_);
v___x_2573_ = lean_usize_land(v___x_2569_, v___x_2572_);
v_bkt_2574_ = lean_array_uget_borrowed(v_buckets_2556_, v___x_2573_);
v___x_2575_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2553_, v_bkt_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v_size_x27_2577_; lean_object* v___x_2578_; lean_object* v_buckets_x27_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2576_ = lean_unsigned_to_nat(1u);
v_size_x27_2577_ = lean_nat_add(v_size_2555_, v___x_2576_);
lean_dec(v_size_2555_);
lean_inc(v_bkt_2574_);
v___x_2578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2578_, 0, v_a_2553_);
lean_ctor_set(v___x_2578_, 1, v_b_2554_);
lean_ctor_set(v___x_2578_, 2, v_bkt_2574_);
v_buckets_x27_2579_ = lean_array_uset(v_buckets_2556_, v___x_2573_, v___x_2578_);
v___x_2580_ = lean_unsigned_to_nat(4u);
v___x_2581_ = lean_nat_mul(v_size_x27_2577_, v___x_2580_);
v___x_2582_ = lean_unsigned_to_nat(3u);
v___x_2583_ = lean_nat_div(v___x_2581_, v___x_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_array_get_size(v_buckets_x27_2579_);
v___x_2585_ = lean_nat_dec_le(v___x_2583_, v___x_2584_);
lean_dec(v___x_2583_);
if (v___x_2585_ == 0)
{
lean_object* v_val_2586_; lean_object* v___x_2588_; 
v_val_2586_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_buckets_x27_2579_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 1, v_val_2586_);
lean_ctor_set(v___x_2558_, 0, v_size_x27_2577_);
v___x_2588_ = v___x_2558_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_size_x27_2577_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_val_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
else
{
lean_object* v___x_2591_; 
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 1, v_buckets_x27_2579_);
lean_ctor_set(v___x_2558_, 0, v_size_x27_2577_);
v___x_2591_ = v___x_2558_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_size_x27_2577_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_buckets_x27_2579_);
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
lean_object* v___x_2593_; lean_object* v_buckets_x27_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
lean_inc(v_bkt_2574_);
v___x_2593_ = lean_box(0);
v_buckets_x27_2594_ = lean_array_uset(v_buckets_2556_, v___x_2573_, v___x_2593_);
v___x_2595_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2553_, v_b_2554_, v_bkt_2574_);
v___x_2596_ = lean_array_uset(v_buckets_x27_2594_, v___x_2573_, v___x_2595_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 1, v___x_2596_);
v___x_2598_ = v___x_2558_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_size_2555_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(lean_object* v_p_2601_, lean_object* v_x_2602_){
_start:
{
lean_object* v_coeffs_2603_; lean_object* v_constraint_2604_; lean_object* v_justification_2605_; uint8_t v___x_2606_; 
v_coeffs_2603_ = lean_ctor_get(v_x_2602_, 0);
lean_inc(v_coeffs_2603_);
v_constraint_2604_ = lean_ctor_get(v_x_2602_, 1);
lean_inc_ref(v_constraint_2604_);
v_justification_2605_ = lean_ctor_get(v_x_2602_, 2);
v___x_2606_ = l_Lean_Omega_Constraint_isImpossible(v_constraint_2604_);
if (v___x_2606_ == 0)
{
lean_object* v_assumptions_2607_; lean_object* v_numVars_2608_; lean_object* v_constraints_2609_; lean_object* v_equalities_2610_; lean_object* v_eliminations_2611_; uint8_t v_possible_2612_; lean_object* v_proveFalse_x3f_2613_; lean_object* v_explanation_x3f_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2632_; 
v_assumptions_2607_ = lean_ctor_get(v_p_2601_, 0);
v_numVars_2608_ = lean_ctor_get(v_p_2601_, 1);
v_constraints_2609_ = lean_ctor_get(v_p_2601_, 2);
v_equalities_2610_ = lean_ctor_get(v_p_2601_, 3);
v_eliminations_2611_ = lean_ctor_get(v_p_2601_, 4);
v_possible_2612_ = lean_ctor_get_uint8(v_p_2601_, sizeof(void*)*7);
v_proveFalse_x3f_2613_ = lean_ctor_get(v_p_2601_, 5);
v_explanation_x3f_2614_ = lean_ctor_get(v_p_2601_, 6);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_p_2601_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2616_ = v_p_2601_;
v_isShared_2617_ = v_isSharedCheck_2632_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_explanation_x3f_2614_);
lean_inc(v_proveFalse_x3f_2613_);
lean_inc(v_eliminations_2611_);
lean_inc(v_equalities_2610_);
lean_inc(v_constraints_2609_);
lean_inc(v_numVars_2608_);
lean_inc(v_assumptions_2607_);
lean_dec(v_p_2601_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2632_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___y_2619_; lean_object* v___x_2630_; uint8_t v___x_2631_; 
v___x_2630_ = l_List_lengthTR___redArg(v_coeffs_2603_);
v___x_2631_ = lean_nat_dec_le(v_numVars_2608_, v___x_2630_);
if (v___x_2631_ == 0)
{
lean_dec(v___x_2630_);
v___y_2619_ = v_numVars_2608_;
goto v___jp_2618_;
}
else
{
lean_dec(v_numVars_2608_);
v___y_2619_ = v___x_2630_;
goto v___jp_2618_;
}
v___jp_2618_:
{
lean_object* v___x_2620_; uint8_t v___x_2621_; 
lean_inc(v_coeffs_2603_);
v___x_2620_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_constraints_2609_, v_coeffs_2603_, v_x_2602_);
v___x_2621_ = l_Lean_Omega_Constraint_isExact(v_constraint_2604_);
lean_dec_ref(v_constraint_2604_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2623_; 
lean_dec(v_coeffs_2603_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 2, v___x_2620_);
lean_ctor_set(v___x_2616_, 1, v___y_2619_);
v___x_2623_ = v___x_2616_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_assumptions_2607_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v___y_2619_);
lean_ctor_set(v_reuseFailAlloc_2624_, 2, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2624_, 3, v_equalities_2610_);
lean_ctor_set(v_reuseFailAlloc_2624_, 4, v_eliminations_2611_);
lean_ctor_set(v_reuseFailAlloc_2624_, 5, v_proveFalse_x3f_2613_);
lean_ctor_set(v_reuseFailAlloc_2624_, 6, v_explanation_x3f_2614_);
lean_ctor_set_uint8(v_reuseFailAlloc_2624_, sizeof(void*)*7, v_possible_2612_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2625_ = lean_box(0);
v___x_2626_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_equalities_2610_, v_coeffs_2603_, v___x_2625_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 3, v___x_2626_);
lean_ctor_set(v___x_2616_, 2, v___x_2620_);
lean_ctor_set(v___x_2616_, 1, v___y_2619_);
v___x_2628_ = v___x_2616_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_assumptions_2607_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v___y_2619_);
lean_ctor_set(v_reuseFailAlloc_2629_, 2, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2629_, 3, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2629_, 4, v_eliminations_2611_);
lean_ctor_set(v_reuseFailAlloc_2629_, 5, v_proveFalse_x3f_2613_);
lean_ctor_set(v_reuseFailAlloc_2629_, 6, v_explanation_x3f_2614_);
lean_ctor_set_uint8(v_reuseFailAlloc_2629_, sizeof(void*)*7, v_possible_2612_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
else
{
lean_object* v_assumptions_2633_; lean_object* v_numVars_2634_; lean_object* v_constraints_2635_; lean_object* v_equalities_2636_; lean_object* v_eliminations_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2649_; 
lean_inc_ref(v_justification_2605_);
lean_dec_ref(v_x_2602_);
v_assumptions_2633_ = lean_ctor_get(v_p_2601_, 0);
v_numVars_2634_ = lean_ctor_get(v_p_2601_, 1);
v_constraints_2635_ = lean_ctor_get(v_p_2601_, 2);
v_equalities_2636_ = lean_ctor_get(v_p_2601_, 3);
v_eliminations_2637_ = lean_ctor_get(v_p_2601_, 4);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_p_2601_);
if (v_isSharedCheck_2649_ == 0)
{
lean_object* v_unused_2650_; lean_object* v_unused_2651_; 
v_unused_2650_ = lean_ctor_get(v_p_2601_, 6);
lean_dec(v_unused_2650_);
v_unused_2651_ = lean_ctor_get(v_p_2601_, 5);
lean_dec(v_unused_2651_);
v___x_2639_ = v_p_2601_;
v_isShared_2640_ = v_isSharedCheck_2649_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_eliminations_2637_);
lean_inc(v_equalities_2636_);
lean_inc(v_constraints_2635_);
lean_inc(v_numVars_2634_);
lean_inc(v_assumptions_2633_);
lean_dec(v_p_2601_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2649_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___f_2641_; uint8_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
lean_inc_ref(v_justification_2605_);
lean_inc(v_coeffs_2603_);
lean_inc_ref(v_constraint_2604_);
v___f_2641_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_insertConstraint___lam__0), 4, 3);
lean_closure_set(v___f_2641_, 0, v_constraint_2604_);
lean_closure_set(v___f_2641_, 1, v_coeffs_2603_);
lean_closure_set(v___f_2641_, 2, v_justification_2605_);
v___x_2642_ = 0;
lean_inc_ref(v_assumptions_2633_);
v___x_2643_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___boxed), 14, 4);
lean_closure_set(v___x_2643_, 0, v_constraint_2604_);
lean_closure_set(v___x_2643_, 1, v_coeffs_2603_);
lean_closure_set(v___x_2643_, 2, v_justification_2605_);
lean_closure_set(v___x_2643_, 3, v_assumptions_2633_);
v___x_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
v___x_2645_ = lean_mk_thunk(v___f_2641_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 6, v___x_2645_);
lean_ctor_set(v___x_2639_, 5, v___x_2644_);
v___x_2647_ = v___x_2639_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_assumptions_2633_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_numVars_2634_);
lean_ctor_set(v_reuseFailAlloc_2648_, 2, v_constraints_2635_);
lean_ctor_set(v_reuseFailAlloc_2648_, 3, v_equalities_2636_);
lean_ctor_set(v_reuseFailAlloc_2648_, 4, v_eliminations_2637_);
lean_ctor_set(v_reuseFailAlloc_2648_, 5, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2648_, 6, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_ctor_set_uint8(v___x_2647_, sizeof(void*)*7, v___x_2642_);
return v___x_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0(lean_object* v_00_u03b2_2652_, lean_object* v_m_2653_, lean_object* v_a_2654_, lean_object* v_b_2655_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0___redArg(v_m_2653_, v_a_2654_, v_b_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1(lean_object* v_00_u03b2_2657_, lean_object* v_m_2658_, lean_object* v_a_2659_, lean_object* v_b_2660_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__1___redArg(v_m_2658_, v_a_2659_, v_b_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(lean_object* v_00_u03b2_2662_, lean_object* v_a_2663_, lean_object* v_x_2664_){
_start:
{
uint8_t v___x_2665_; 
v___x_2665_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___redArg(v_a_2663_, v_x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2666_, lean_object* v_a_2667_, lean_object* v_x_2668_){
_start:
{
uint8_t v_res_2669_; lean_object* v_r_2670_; 
v_res_2669_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__1(v_00_u03b2_2666_, v_a_2667_, v_x_2668_);
lean_dec(v_x_2668_);
lean_dec(v_a_2667_);
v_r_2670_ = lean_box(v_res_2669_);
return v_r_2670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2(lean_object* v_00_u03b2_2671_, lean_object* v_data_2672_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2___redArg(v_data_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3(lean_object* v_00_u03b2_2674_, lean_object* v_a_2675_, lean_object* v_b_2676_, lean_object* v_x_2677_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__3___redArg(v_a_2675_, v_b_2676_, v_x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2679_, lean_object* v_i_2680_, lean_object* v_source_2681_, lean_object* v_target_2682_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3___redArg(v_i_2680_, v_source_2681_, v_target_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_2684_, lean_object* v_x_2685_, lean_object* v_x_2686_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__2_spec__3_spec__5___redArg(v_x_2685_, v_x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(lean_object* v_a_2688_, lean_object* v_x_2689_){
_start:
{
if (lean_obj_tag(v_x_2689_) == 0)
{
lean_object* v___x_2690_; 
v___x_2690_ = lean_box(0);
return v___x_2690_;
}
else
{
lean_object* v_key_2691_; lean_object* v_value_2692_; lean_object* v_tail_2693_; uint8_t v___x_2694_; 
v_key_2691_ = lean_ctor_get(v_x_2689_, 0);
v_value_2692_ = lean_ctor_get(v_x_2689_, 1);
v_tail_2693_ = lean_ctor_get(v_x_2689_, 2);
v___x_2694_ = l_List_beq___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__1(v_key_2691_, v_a_2688_);
if (v___x_2694_ == 0)
{
v_x_2689_ = v_tail_2693_;
goto _start;
}
else
{
lean_object* v___x_2696_; 
lean_inc(v_value_2692_);
v___x_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_value_2692_);
return v___x_2696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg___boxed(lean_object* v_a_2697_, lean_object* v_x_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2697_, v_x_2698_);
lean_dec(v_x_2698_);
lean_dec(v_a_2697_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(lean_object* v_m_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v_buckets_2702_; lean_object* v___x_2703_; uint64_t v___x_2704_; uint64_t v___x_2705_; uint64_t v___x_2706_; uint64_t v___x_2707_; uint64_t v_fold_2708_; uint64_t v___x_2709_; uint64_t v___x_2710_; uint64_t v___x_2711_; size_t v___x_2712_; size_t v___x_2713_; size_t v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_buckets_2702_ = lean_ctor_get(v_m_2700_, 1);
v___x_2703_ = lean_array_get_size(v_buckets_2702_);
v___x_2704_ = 7ULL;
v___x_2705_ = l_List_foldl___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_Problem_insertConstraint_spec__0_spec__0(v___x_2704_, v_a_2701_);
v___x_2706_ = 32ULL;
v___x_2707_ = lean_uint64_shift_right(v___x_2705_, v___x_2706_);
v_fold_2708_ = lean_uint64_xor(v___x_2705_, v___x_2707_);
v___x_2709_ = 16ULL;
v___x_2710_ = lean_uint64_shift_right(v_fold_2708_, v___x_2709_);
v___x_2711_ = lean_uint64_xor(v_fold_2708_, v___x_2710_);
v___x_2712_ = lean_uint64_to_usize(v___x_2711_);
v___x_2713_ = lean_usize_of_nat(v___x_2703_);
v___x_2714_ = ((size_t)1ULL);
v___x_2715_ = lean_usize_sub(v___x_2713_, v___x_2714_);
v___x_2716_ = lean_usize_land(v___x_2712_, v___x_2715_);
v___x_2717_ = lean_array_uget_borrowed(v_buckets_2702_, v___x_2716_);
v___x_2718_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2701_, v___x_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg___boxed(lean_object* v_m_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2719_, v_a_2720_);
lean_dec(v_a_2720_);
lean_dec_ref(v_m_2719_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addConstraint(lean_object* v_p_2722_, lean_object* v_x_2723_){
_start:
{
uint8_t v_possible_2724_; 
v_possible_2724_ = lean_ctor_get_uint8(v_p_2722_, sizeof(void*)*7);
if (v_possible_2724_ == 0)
{
lean_dec_ref(v_x_2723_);
return v_p_2722_;
}
else
{
lean_object* v_coeffs_2725_; lean_object* v_constraint_2726_; lean_object* v_justification_2727_; lean_object* v_constraints_2728_; lean_object* v___x_2729_; 
v_coeffs_2725_ = lean_ctor_get(v_x_2723_, 0);
v_constraint_2726_ = lean_ctor_get(v_x_2723_, 1);
v_justification_2727_ = lean_ctor_get(v_x_2723_, 2);
v_constraints_2728_ = lean_ctor_get(v_p_2722_, 2);
v___x_2729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2728_, v_coeffs_2725_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_lowerBound_2730_; 
v_lowerBound_2730_ = lean_ctor_get(v_constraint_2726_, 0);
if (lean_obj_tag(v_lowerBound_2730_) == 0)
{
lean_object* v_upperBound_2731_; 
v_upperBound_2731_ = lean_ctor_get(v_constraint_2726_, 1);
if (lean_obj_tag(v_upperBound_2731_) == 0)
{
lean_dec_ref(v_x_2723_);
return v_p_2722_;
}
else
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2722_, v_x_2723_);
return v___x_2732_;
}
}
else
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2722_, v_x_2723_);
return v___x_2733_;
}
}
else
{
lean_object* v_val_2734_; lean_object* v_coeffs_2735_; lean_object* v_constraint_2736_; lean_object* v_justification_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2752_; 
v_val_2734_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_val_2734_);
lean_dec_ref_known(v___x_2729_, 1);
v_coeffs_2735_ = lean_ctor_get(v_val_2734_, 0);
v_constraint_2736_ = lean_ctor_get(v_val_2734_, 1);
v_justification_2737_ = lean_ctor_get(v_val_2734_, 2);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_val_2734_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2739_ = v_val_2734_;
v_isShared_2740_ = v_isSharedCheck_2752_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_justification_2737_);
lean_inc(v_constraint_2736_);
lean_inc(v_coeffs_2735_);
lean_dec(v_val_2734_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2752_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; uint8_t v___x_2742_; 
v___x_2741_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc(v_coeffs_2725_);
v___x_2742_ = l_instDecidableEqList___redArg(v___x_2741_, v_coeffs_2725_, v_coeffs_2735_);
if (v___x_2742_ == 0)
{
lean_del_object(v___x_2739_);
lean_dec_ref(v_justification_2737_);
lean_dec_ref(v_constraint_2736_);
lean_dec_ref(v_x_2723_);
return v_p_2722_;
}
else
{
lean_object* v_r_2743_; uint8_t v___x_2744_; 
lean_inc_ref_n(v_constraint_2736_, 2);
lean_inc_ref(v_constraint_2726_);
v_r_2743_ = l_Lean_Omega_Constraint_combine(v_constraint_2726_, v_constraint_2736_);
lean_inc_ref(v_r_2743_);
v___x_2744_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2743_, v_constraint_2736_);
if (v___x_2744_ == 0)
{
uint8_t v___x_2745_; 
lean_inc_ref(v_constraint_2726_);
lean_inc_ref(v_r_2743_);
v___x_2745_ = l_Lean_Omega_instDecidableEqConstraint_decEq(v_r_2743_, v_constraint_2726_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; lean_object* v___x_2748_; 
lean_inc_ref(v_justification_2727_);
lean_inc_ref(v_constraint_2726_);
lean_inc_n(v_coeffs_2725_, 2);
lean_dec_ref(v_x_2723_);
v___x_2746_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_2746_, 0, v_constraint_2726_);
lean_ctor_set(v___x_2746_, 1, v_constraint_2736_);
lean_ctor_set(v___x_2746_, 2, v_coeffs_2725_);
lean_ctor_set(v___x_2746_, 3, v_justification_2727_);
lean_ctor_set(v___x_2746_, 4, v_justification_2737_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 2, v___x_2746_);
lean_ctor_set(v___x_2739_, 1, v_r_2743_);
lean_ctor_set(v___x_2739_, 0, v_coeffs_2725_);
v___x_2748_ = v___x_2739_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_coeffs_2725_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_r_2743_);
lean_ctor_set(v_reuseFailAlloc_2750_, 2, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2722_, v___x_2748_);
return v___x_2749_;
}
}
else
{
lean_object* v___x_2751_; 
lean_dec_ref(v_r_2743_);
lean_del_object(v___x_2739_);
lean_dec_ref(v_justification_2737_);
lean_dec_ref(v_constraint_2736_);
v___x_2751_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_p_2722_, v_x_2723_);
return v___x_2751_;
}
}
else
{
lean_dec_ref(v_r_2743_);
lean_del_object(v___x_2739_);
lean_dec_ref(v_justification_2737_);
lean_dec_ref(v_constraint_2736_);
lean_dec_ref(v_x_2723_);
return v_p_2722_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(lean_object* v_00_u03b2_2753_, lean_object* v_m_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_m_2754_, v_a_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___boxed(lean_object* v_00_u03b2_2757_, lean_object* v_m_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0(v_00_u03b2_2757_, v_m_2758_, v_a_2759_);
lean_dec(v_a_2759_);
lean_dec_ref(v_m_2758_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(lean_object* v_00_u03b2_2761_, lean_object* v_a_2762_, lean_object* v_x_2763_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___redArg(v_a_2762_, v_x_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2765_, lean_object* v_a_2766_, lean_object* v_x_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0_spec__0(v_00_u03b2_2765_, v_a_2766_, v_x_2767_);
lean_dec(v_x_2767_);
lean_dec(v_a_2766_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(lean_object* v_x_2769_, lean_object* v_x_2770_){
_start:
{
if (lean_obj_tag(v_x_2770_) == 0)
{
return v_x_2769_;
}
else
{
if (lean_obj_tag(v_x_2769_) == 0)
{
lean_object* v_key_2771_; lean_object* v_tail_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_key_2771_ = lean_ctor_get(v_x_2770_, 0);
lean_inc_n(v_key_2771_, 2);
v_tail_2772_ = lean_ctor_get(v_x_2770_, 2);
lean_inc(v_tail_2772_);
lean_dec_ref_known(v_x_2770_, 3);
v___x_2773_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2771_);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v_key_2771_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
v_x_2769_ = v___x_2775_;
v_x_2770_ = v_tail_2772_;
goto _start;
}
else
{
lean_object* v_val_2777_; lean_object* v_key_2778_; lean_object* v_tail_2779_; lean_object* v_fst_2780_; lean_object* v_snd_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2802_; 
v_val_2777_ = lean_ctor_get(v_x_2769_, 0);
lean_inc(v_val_2777_);
v_key_2778_ = lean_ctor_get(v_x_2770_, 0);
lean_inc(v_key_2778_);
v_tail_2779_ = lean_ctor_get(v_x_2770_, 2);
lean_inc(v_tail_2779_);
lean_dec_ref_known(v_x_2770_, 3);
v_fst_2780_ = lean_ctor_get(v_val_2777_, 0);
v_snd_2781_ = lean_ctor_get(v_val_2777_, 1);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_val_2777_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2783_ = v_val_2777_;
v_isShared_2784_ = v_isSharedCheck_2802_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_snd_2781_);
lean_inc(v_fst_2780_);
lean_dec(v_val_2777_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2802_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2785_ = lean_unsigned_to_nat(2u);
v___x_2786_ = lean_nat_dec_le(v___x_2785_, v_snd_2781_);
if (v___x_2786_ == 0)
{
lean_del_object(v___x_2783_);
lean_dec(v_snd_2781_);
lean_dec(v_fst_2780_);
lean_dec(v_key_2778_);
v_x_2770_ = v_tail_2779_;
goto _start;
}
else
{
lean_object* v_m_x27_2788_; uint8_t v___x_2795_; 
lean_inc(v_key_2778_);
v_m_x27_2788_ = l_Lean_Elab_Tactic_Omega_List_minNatAbs(v_key_2778_);
v___x_2795_ = lean_nat_dec_lt(v_m_x27_2788_, v_snd_2781_);
if (v___x_2795_ == 0)
{
uint8_t v___x_2796_; 
v___x_2796_ = lean_nat_dec_eq(v_m_x27_2788_, v_snd_2781_);
lean_dec(v_snd_2781_);
if (v___x_2796_ == 0)
{
lean_dec(v_m_x27_2788_);
lean_del_object(v___x_2783_);
lean_dec(v_fst_2780_);
lean_dec(v_key_2778_);
v_x_2770_ = v_tail_2779_;
goto _start;
}
else
{
lean_object* v___x_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
lean_inc(v_key_2778_);
v___x_2798_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_key_2778_);
v___x_2799_ = l_Lean_Elab_Tactic_Omega_List_maxNatAbs(v_fst_2780_);
v___x_2800_ = lean_nat_dec_lt(v___x_2798_, v___x_2799_);
lean_dec(v___x_2799_);
lean_dec(v___x_2798_);
if (v___x_2800_ == 0)
{
lean_dec(v_m_x27_2788_);
lean_del_object(v___x_2783_);
lean_dec(v_key_2778_);
v_x_2770_ = v_tail_2779_;
goto _start;
}
else
{
lean_dec_ref_known(v_x_2769_, 1);
goto v___jp_2789_;
}
}
}
else
{
lean_dec(v_snd_2781_);
lean_dec(v_fst_2780_);
lean_dec_ref_known(v_x_2769_, 1);
goto v___jp_2789_;
}
v___jp_2789_:
{
lean_object* v___x_2791_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 1, v_m_x27_2788_);
lean_ctor_set(v___x_2783_, 0, v_key_2778_);
v___x_2791_ = v___x_2783_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_key_2778_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_m_x27_2788_);
v___x_2791_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2792_; 
v___x_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
v_x_2769_ = v___x_2792_;
v_x_2770_ = v_tail_2779_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(lean_object* v_as_2803_, size_t v_i_2804_, size_t v_stop_2805_, lean_object* v_b_2806_){
_start:
{
uint8_t v___x_2807_; 
v___x_2807_ = lean_usize_dec_eq(v_i_2804_, v_stop_2805_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2809_; size_t v___x_2810_; size_t v___x_2811_; 
v___x_2808_ = lean_array_uget_borrowed(v_as_2803_, v_i_2804_);
lean_inc(v___x_2808_);
v___x_2809_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__0(v_b_2806_, v___x_2808_);
v___x_2810_ = ((size_t)1ULL);
v___x_2811_ = lean_usize_add(v_i_2804_, v___x_2810_);
v_i_2804_ = v___x_2811_;
v_b_2806_ = v___x_2809_;
goto _start;
}
else
{
return v_b_2806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1___boxed(lean_object* v_as_2813_, lean_object* v_i_2814_, lean_object* v_stop_2815_, lean_object* v_b_2816_){
_start:
{
size_t v_i_boxed_2817_; size_t v_stop_boxed_2818_; lean_object* v_res_2819_; 
v_i_boxed_2817_ = lean_unbox_usize(v_i_2814_);
lean_dec(v_i_2814_);
v_stop_boxed_2818_ = lean_unbox_usize(v_stop_2815_);
lean_dec(v_stop_2815_);
v_res_2819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_as_2813_, v_i_boxed_2817_, v_stop_boxed_2818_, v_b_2816_);
lean_dec_ref(v_as_2813_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality(lean_object* v_p_2820_){
_start:
{
lean_object* v_equalities_2821_; lean_object* v_buckets_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
v_equalities_2821_ = lean_ctor_get(v_p_2820_, 3);
v_buckets_2822_ = lean_ctor_get(v_equalities_2821_, 1);
v___x_2823_ = lean_box(0);
v___x_2824_ = lean_unsigned_to_nat(0u);
v___x_2825_ = lean_array_get_size(v_buckets_2822_);
v___x_2826_ = lean_nat_dec_lt(v___x_2824_, v___x_2825_);
if (v___x_2826_ == 0)
{
return v___x_2823_;
}
else
{
size_t v___x_2827_; size_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = ((size_t)0ULL);
v___x_2828_ = lean_usize_of_nat(v___x_2825_);
v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_selectEquality_spec__1(v_buckets_2822_, v___x_2827_, v___x_2828_, v___x_2823_);
return v___x_2829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_selectEquality___boxed(lean_object* v_p_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_2830_);
lean_dec_ref(v_p_2830_);
return v_res_2831_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_unsigned_to_nat(1u);
v___x_2833_ = lean_nat_to_int(v___x_2832_);
return v___x_2833_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2835_ = lean_int_neg(v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0(lean_object* v_as_2836_, size_t v_i_2837_, size_t v_stop_2838_, lean_object* v_b_2839_){
_start:
{
uint8_t v___x_2840_; 
v___x_2840_ = lean_usize_dec_eq(v_i_2837_, v_stop_2838_);
if (v___x_2840_ == 0)
{
size_t v___x_2841_; size_t v___x_2842_; lean_object* v___x_2843_; lean_object* v_snd_2844_; lean_object* v_fst_2845_; lean_object* v_fst_2846_; lean_object* v_snd_2847_; lean_object* v_coeffs_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2841_ = ((size_t)1ULL);
v___x_2842_ = lean_usize_sub(v_i_2837_, v___x_2841_);
v___x_2843_ = lean_array_uget_borrowed(v_as_2836_, v___x_2842_);
v_snd_2844_ = lean_ctor_get(v___x_2843_, 1);
v_fst_2845_ = lean_ctor_get(v___x_2843_, 0);
v_fst_2846_ = lean_ctor_get(v_snd_2844_, 0);
v_snd_2847_ = lean_ctor_get(v_snd_2844_, 1);
v_coeffs_2848_ = lean_ctor_get(v_b_2839_, 0);
lean_inc(v_fst_2846_);
v___x_2849_ = l_Lean_Omega_IntList_get(v_coeffs_2848_, v_fst_2846_);
v___x_2850_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_2851_ = lean_int_dec_eq(v___x_2849_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2852_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__0);
v___x_2853_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Elab_Tactic_Omega_Problem_replayEliminations_spec__0_spec__0___closed__1);
v___x_2854_ = lean_int_mul(v___x_2853_, v_snd_2847_);
v___x_2855_ = lean_int_mul(v___x_2854_, v___x_2849_);
lean_dec(v___x_2849_);
lean_dec(v___x_2854_);
lean_inc(v_fst_2845_);
v___x_2856_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v___x_2855_, v_fst_2845_, v___x_2852_, v_b_2839_);
v_i_2837_ = v___x_2842_;
v_b_2839_ = v___x_2856_;
goto _start;
}
else
{
lean_dec(v___x_2849_);
v_i_2837_ = v___x_2842_;
goto _start;
}
}
else
{
return v_b_2839_;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(lean_object* v___y_2908_, lean_object* v_sign_2909_, lean_object* v_val_2910_, lean_object* v_as_2911_, size_t v_i_2912_, size_t v_stop_2913_, lean_object* v_b_2914_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1___boxed(lean_object* v___y_2921_, lean_object* v_sign_2922_, lean_object* v_val_2923_, lean_object* v_as_2924_, lean_object* v_i_2925_, lean_object* v_stop_2926_, lean_object* v_b_2927_){
_start:
{
size_t v_i_boxed_2928_; size_t v_stop_boxed_2929_; lean_object* v_res_2930_; 
v_i_boxed_2928_ = lean_unbox_usize(v_i_2925_);
lean_dec(v_i_2925_);
v_stop_boxed_2929_ = lean_unbox_usize(v_stop_2926_);
lean_dec(v_stop_2926_);
v_res_2930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2921_, v_sign_2922_, v_val_2923_, v_as_2924_, v_i_boxed_2928_, v_stop_boxed_2929_, v_b_2927_);
lean_dec_ref(v_as_2924_);
lean_dec(v_sign_2922_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
if (lean_obj_tag(v_a_2931_) == 0)
{
lean_object* v___x_2933_; 
lean_dec(v_a_2932_);
v___x_2933_ = lean_box(0);
return v___x_2933_;
}
else
{
lean_object* v_head_2934_; lean_object* v_tail_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v_head_2934_ = lean_ctor_get(v_a_2931_, 0);
v_tail_2935_ = lean_ctor_get(v_a_2931_, 1);
v___x_2936_ = lean_nat_abs(v_head_2934_);
v___x_2937_ = lean_unsigned_to_nat(1u);
v___x_2938_ = lean_nat_dec_eq(v___x_2936_, v___x_2937_);
lean_dec(v___x_2936_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_nat_add(v_a_2932_, v___x_2937_);
lean_dec(v_a_2932_);
v_a_2931_ = v_tail_2935_;
v_a_2932_ = v___x_2939_;
goto _start;
}
else
{
lean_object* v___x_2941_; 
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v_a_2932_);
return v___x_2941_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2___boxed(lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(v_a_2942_, v_a_2943_);
lean_dec(v_a_2942_);
return v_res_2944_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = lean_box(0);
v___x_2947_ = lean_unsigned_to_nat(16u);
v___x_2948_ = lean_mk_array(v___x_2947_, v___x_2946_);
return v___x_2948_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__1);
v___x_2950_ = lean_unsigned_to_nat(0u);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___x_2949_);
return v___x_2951_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3(void){
_start:
{
lean_object* v___f_2952_; lean_object* v___x_2953_; 
v___f_2952_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__0));
v___x_2953_ = lean_mk_thunk(v___f_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(lean_object* v_p_2954_, lean_object* v_c_2955_){
_start:
{
lean_object* v___y_2957_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_unsigned_to_nat(0u);
v___x_3001_ = l_List_findIdx_x3f_go___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__2(v_c_2955_, v___x_3000_);
if (lean_obj_tag(v___x_3001_) == 0)
{
v___y_2957_ = v___x_3000_;
goto v___jp_2956_;
}
else
{
lean_object* v_val_3002_; 
v_val_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_val_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___y_2957_ = v_val_3002_;
goto v___jp_2956_;
}
v___jp_2956_:
{
lean_object* v_assumptions_2958_; lean_object* v_constraints_2959_; lean_object* v_eliminations_2960_; lean_object* v___x_2961_; 
v_assumptions_2958_ = lean_ctor_get(v_p_2954_, 0);
v_constraints_2959_ = lean_ctor_get(v_p_2954_, 2);
lean_inc_ref(v_constraints_2959_);
v_eliminations_2960_ = lean_ctor_get(v_p_2954_, 4);
v___x_2961_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_Problem_addConstraint_spec__0___redArg(v_constraints_2959_, v_c_2955_);
if (lean_obj_tag(v___x_2961_) == 1)
{
lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2992_; 
lean_inc(v_eliminations_2960_);
lean_inc_ref(v_assumptions_2958_);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_p_2954_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; lean_object* v_unused_2994_; lean_object* v_unused_2995_; lean_object* v_unused_2996_; lean_object* v_unused_2997_; lean_object* v_unused_2998_; lean_object* v_unused_2999_; 
v_unused_2993_ = lean_ctor_get(v_p_2954_, 6);
lean_dec(v_unused_2993_);
v_unused_2994_ = lean_ctor_get(v_p_2954_, 5);
lean_dec(v_unused_2994_);
v_unused_2995_ = lean_ctor_get(v_p_2954_, 4);
lean_dec(v_unused_2995_);
v_unused_2996_ = lean_ctor_get(v_p_2954_, 3);
lean_dec(v_unused_2996_);
v_unused_2997_ = lean_ctor_get(v_p_2954_, 2);
lean_dec(v_unused_2997_);
v_unused_2998_ = lean_ctor_get(v_p_2954_, 1);
lean_dec(v_unused_2998_);
v_unused_2999_ = lean_ctor_get(v_p_2954_, 0);
lean_dec(v_unused_2999_);
v___x_2963_ = v_p_2954_;
v_isShared_2964_ = v_isSharedCheck_2992_;
goto v_resetjp_2962_;
}
else
{
lean_dec(v_p_2954_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2992_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v_val_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v_buckets_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2990_; 
v_val_2965_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_val_2965_);
lean_dec_ref_known(v___x_2961_, 1);
v___x_2966_ = lean_unsigned_to_nat(0u);
v___x_2967_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v_buckets_2968_ = lean_ctor_get(v_constraints_2959_, 1);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_constraints_2959_);
if (v_isSharedCheck_2990_ == 0)
{
lean_object* v_unused_2991_; 
v_unused_2991_ = lean_ctor_get(v_constraints_2959_, 0);
lean_dec(v_unused_2991_);
v___x_2970_ = v_constraints_2959_;
v_isShared_2971_ = v_isSharedCheck_2990_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_buckets_2968_);
lean_dec(v_constraints_2959_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2990_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; lean_object* v_sign_2973_; lean_object* v___x_2975_; 
lean_inc_n(v___y_2957_, 2);
v___x_2972_ = l_Lean_Omega_IntList_get(v_c_2955_, v___y_2957_);
v_sign_2973_ = l_Int_sign(v___x_2972_);
lean_dec(v___x_2972_);
lean_inc(v_sign_2973_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 1, v_sign_2973_);
lean_ctor_set(v___x_2970_, 0, v___y_2957_);
v___x_2975_ = v___x_2970_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___y_2957_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_sign_2973_);
v___x_2975_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v_init_2982_; 
lean_inc(v_val_2965_);
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v_val_2965_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
lean_ctor_set(v___x_2977_, 1, v_eliminations_2960_);
v___x_2978_ = 1;
v___x_2979_ = lean_box(0);
v___x_2980_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 6, v___x_2980_);
lean_ctor_set(v___x_2963_, 5, v___x_2979_);
lean_ctor_set(v___x_2963_, 4, v___x_2977_);
lean_ctor_set(v___x_2963_, 3, v___x_2967_);
lean_ctor_set(v___x_2963_, 2, v___x_2967_);
lean_ctor_set(v___x_2963_, 1, v___x_2966_);
v_init_2982_ = v___x_2963_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_assumptions_2958_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2988_, 2, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_2988_, 3, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_2988_, 4, v___x_2977_);
lean_ctor_set(v_reuseFailAlloc_2988_, 5, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2988_, 6, v___x_2980_);
v_init_2982_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2983_; uint8_t v___x_2984_; 
lean_ctor_set_uint8(v_init_2982_, sizeof(void*)*7, v___x_2978_);
v___x_2983_ = lean_array_get_size(v_buckets_2968_);
v___x_2984_ = lean_nat_dec_lt(v___x_2966_, v___x_2983_);
if (v___x_2984_ == 0)
{
lean_dec(v_sign_2973_);
lean_dec_ref(v_buckets_2968_);
lean_dec(v_val_2965_);
lean_dec(v___y_2957_);
return v_init_2982_;
}
else
{
size_t v___x_2985_; size_t v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = ((size_t)0ULL);
v___x_2986_ = lean_usize_of_nat(v___x_2983_);
v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_solveEasyEquality_spec__1(v___y_2957_, v_sign_2973_, v_val_2965_, v_buckets_2968_, v___x_2985_, v___x_2986_, v_init_2982_);
lean_dec_ref(v_buckets_2968_);
lean_dec(v_sign_2973_);
return v___x_2987_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2961_);
lean_dec_ref(v_constraints_2959_);
lean_dec(v___y_2957_);
return v_p_2954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___boxed(lean_object* v_p_3003_, lean_object* v_c_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_3003_, v_c_3004_);
lean_dec(v_c_3004_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(lean_object* v_msgData_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v___x_3012_; lean_object* v_env_3013_; uint8_t v___x_3014_; lean_object* v_env_3015_; lean_object* v___x_3016_; lean_object* v_toCold_3017_; lean_object* v_mctx_3018_; lean_object* v_lctx_3019_; lean_object* v_options_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3012_ = lean_st_ref_get(v___y_3010_);
v_env_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc_ref(v_env_3013_);
lean_dec(v___x_3012_);
v___x_3014_ = 0;
v_env_3015_ = l_Lean_Environment_setRecordingDeps(v_env_3013_, v___x_3014_);
v___x_3016_ = lean_st_ref_get(v___y_3008_);
v_toCold_3017_ = lean_ctor_get(v___y_3009_, 0);
v_mctx_3018_ = lean_ctor_get(v___x_3016_, 0);
lean_inc_ref(v_mctx_3018_);
lean_dec(v___x_3016_);
v_lctx_3019_ = lean_ctor_get(v___y_3007_, 2);
v_options_3020_ = lean_ctor_get(v_toCold_3017_, 2);
lean_inc_ref(v_options_3020_);
lean_inc_ref(v_lctx_3019_);
v___x_3021_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3021_, 0, v_env_3015_);
lean_ctor_set(v___x_3021_, 1, v_mctx_3018_);
lean_ctor_set(v___x_3021_, 2, v_lctx_3019_);
lean_ctor_set(v___x_3021_, 3, v_options_3020_);
v___x_3022_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
lean_ctor_set(v___x_3022_, 1, v_msgData_3006_);
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0___boxed(lean_object* v_msgData_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msgData_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(lean_object* v_msg_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v_ref_3037_; lean_object* v___x_3038_; lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3047_; 
v_ref_3037_ = lean_ctor_get(v___y_3034_, 2);
v___x_3038_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3047_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3047_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3045_; 
lean_inc(v_ref_3037_);
v___x_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3043_, 0, v_ref_3037_);
lean_ctor_set(v___x_3043_, 1, v_a_3039_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set_tag(v___x_3041_, 1);
lean_ctor_set(v___x_3041_, 0, v___x_3043_);
v___x_3045_ = v___x_3041_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg___boxed(lean_object* v_msg_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
return v_res_3054_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3055_ = lean_box(0);
v___x_3056_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_bmodProof___closed__13));
v___x_3057_ = l_Lean_Expr_const___override(v___x_3056_, v___x_3055_);
return v___x_3057_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__1));
v___x_3060_ = l_Lean_stringToMessageData(v___x_3059_);
return v___x_3060_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__3));
v___x_3063_ = l_Lean_stringToMessageData(v___x_3062_);
return v___x_3063_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__6(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__5));
v___x_3066_ = l_Lean_stringToMessageData(v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(lean_object* v_p_3067_, lean_object* v_c_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, uint8_t v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
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
v___x_3100_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__0);
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
v___x_3126_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__2);
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
v___x_3128_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__4);
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
v___x_3140_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__6, &l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___closed__6);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality___boxed(lean_object* v_p_3182_, lean_object* v_c_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
uint8_t v_a_boxed_3194_; lean_object* v_res_3195_; 
v_a_boxed_3194_ = lean_unbox(v_a_3187_);
v_res_3195_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3182_, v_c_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_boxed_3194_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3186_);
lean_dec(v_a_3185_);
lean_dec(v_a_3184_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(lean_object* v_00_u03b1_3196_, lean_object* v_msg_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, uint8_t v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___redArg(v_msg_3197_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0___boxed(lean_object* v_00_u03b1_3209_, lean_object* v_msg_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
uint8_t v___y_9011__boxed_3221_; lean_object* v_res_3222_; 
v___y_9011__boxed_3221_ = lean_unbox(v___y_3214_);
v_res_3222_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0(v_00_u03b1_3209_, v_msg_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_9011__boxed_3221_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec(v___y_3211_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality(lean_object* v_p_3223_, lean_object* v_c_3224_, lean_object* v_m_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, uint8_t v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v___x_3236_; uint8_t v___x_3237_; 
v___x_3236_ = lean_unsigned_to_nat(1u);
v___x_3237_ = lean_nat_dec_eq(v_m_3225_, v___x_3236_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality(v_p_3223_, v_c_3224_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_);
return v___x_3238_;
}
else
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality(v_p_3223_, v_c_3224_);
lean_dec(v_c_3224_);
v___x_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
return v___x_3240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEquality___boxed(lean_object* v_p_3241_, lean_object* v_c_3242_, lean_object* v_m_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
uint8_t v_a_boxed_3254_; lean_object* v_res_3255_; 
v_a_boxed_3254_ = lean_unbox(v_a_3247_);
v_res_3255_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3241_, v_c_3242_, v_m_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_boxed_3254_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
lean_dec(v_a_3252_);
lean_dec_ref(v_a_3251_);
lean_dec(v_a_3250_);
lean_dec_ref(v_a_3249_);
lean_dec(v_a_3248_);
lean_dec_ref(v_a_3246_);
lean_dec(v_a_3245_);
lean_dec(v_a_3244_);
lean_dec(v_m_3243_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(lean_object* v_p_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, uint8_t v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
uint8_t v_possible_3267_; 
v_possible_3267_ = lean_ctor_get_uint8(v_p_3256_, sizeof(void*)*7);
if (v_possible_3267_ == 0)
{
lean_object* v___x_3268_; 
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v_p_3256_);
return v___x_3268_;
}
else
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Lean_Elab_Tactic_Omega_Problem_selectEquality(v_p_3256_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v___x_3270_; 
v___x_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3270_, 0, v_p_3256_);
return v___x_3270_;
}
else
{
lean_object* v_val_3271_; lean_object* v_fst_3272_; lean_object* v_snd_3273_; lean_object* v___x_3274_; 
v_val_3271_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_val_3271_);
lean_dec_ref_known(v___x_3269_, 1);
v_fst_3272_ = lean_ctor_get(v_val_3271_, 0);
lean_inc(v_fst_3272_);
v_snd_3273_ = lean_ctor_get(v_val_3271_, 1);
lean_inc(v_snd_3273_);
lean_dec(v_val_3271_);
v___x_3274_ = l_Lean_Elab_Tactic_Omega_Problem_solveEquality(v_p_3256_, v_fst_3272_, v_snd_3273_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
lean_dec(v_snd_3273_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v_p_3256_ = v_a_3275_;
goto _start;
}
else
{
return v___x_3274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_solveEqualities___boxed(lean_object* v_p_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
uint8_t v_a_boxed_3288_; lean_object* v_res_3289_; 
v_a_boxed_3288_ = lean_unbox(v_a_3281_);
v_res_3289_ = l_Lean_Elab_Tactic_Omega_Problem_solveEqualities(v_p_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_boxed_3288_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3280_);
lean_dec(v_a_3279_);
lean_dec(v_a_3278_);
return v_res_3289_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = lean_box(0);
v___x_3297_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__1));
v___x_3298_ = l_Lean_Expr_const___override(v___x_3297_, v___x_3296_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(lean_object* v_c_3299_, lean_object* v_x_3300_, lean_object* v_p_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, uint8_t v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3303_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_a_3313_);
lean_dec_ref_known(v___x_3312_, 1);
v___x_3314_ = lean_box(v_a_3305_);
lean_inc(v_a_3310_);
lean_inc_ref(v_a_3309_);
lean_inc(v_a_3308_);
lean_inc_ref(v_a_3307_);
lean_inc(v_a_3306_);
lean_inc_ref(v_a_3304_);
lean_inc(v_a_3303_);
lean_inc(v_a_3302_);
v___x_3315_ = lean_apply_10(v_p_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v___x_3314_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, lean_box(0));
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3341_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3318_ = v___x_3315_;
v_isShared_3319_ = v_isSharedCheck_3341_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3315_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3341_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3320_; lean_object* v___y_3322_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3320_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___closed__2);
v___x_3330_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3331_ = lean_int_dec_le(v___x_3330_, v_c_3299_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3332_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3333_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3334_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3335_ = lean_int_neg(v_c_3299_);
v___x_3336_ = l_Int_toNat(v___x_3335_);
lean_dec(v___x_3335_);
v___x_3337_ = l_Lean_instToExprInt_mkNat(v___x_3336_);
v___x_3338_ = l_Lean_mkApp3(v___x_3332_, v___x_3333_, v___x_3334_, v___x_3337_);
v___y_3322_ = v___x_3338_;
goto v___jp_3321_;
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = l_Int_toNat(v_c_3299_);
v___x_3340_ = l_Lean_instToExprInt_mkNat(v___x_3339_);
v___y_3322_ = v___x_3340_;
goto v___jp_3321_;
}
v___jp_3321_:
{
lean_object* v_nil_3323_; lean_object* v_cons_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3328_; 
v_nil_3323_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3324_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3325_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3323_, v_cons_3324_, v_x_3300_);
v___x_3326_ = l_Lean_mkApp4(v___x_3320_, v___y_3322_, v___x_3325_, v_a_3313_, v_a_3316_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3326_);
v___x_3328_ = v___x_3318_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
else
{
lean_dec(v_a_3313_);
return v___x_3315_;
}
}
else
{
lean_dec_ref(v_p_3301_);
return v___x_3312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed(lean_object* v_c_3342_, lean_object* v_x_3343_, lean_object* v_p_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
uint8_t v_a_boxed_3355_; lean_object* v_res_3356_; 
v_a_boxed_3355_ = lean_unbox(v_a_3348_);
v_res_3356_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof(v_c_3342_, v_x_3343_, v_p_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_boxed_3355_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_);
lean_dec(v_a_3353_);
lean_dec_ref(v_a_3352_);
lean_dec(v_a_3351_);
lean_dec_ref(v_a_3350_);
lean_dec(v_a_3349_);
lean_dec_ref(v_a_3347_);
lean_dec(v_a_3346_);
lean_dec(v_a_3345_);
lean_dec(v_x_3343_);
lean_dec(v_c_3342_);
return v_res_3356_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = lean_box(0);
v___x_3364_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__1));
v___x_3365_ = l_Lean_Expr_const___override(v___x_3364_, v___x_3363_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(lean_object* v_c_3366_, lean_object* v_x_3367_, lean_object* v_p_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, uint8_t v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(v_a_3370_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3380_);
lean_dec_ref_known(v___x_3379_, 1);
v___x_3381_ = lean_box(v_a_3372_);
lean_inc(v_a_3377_);
lean_inc_ref(v_a_3376_);
lean_inc(v_a_3375_);
lean_inc_ref(v_a_3374_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3371_);
lean_inc(v_a_3370_);
lean_inc(v_a_3369_);
v___x_3382_ = lean_apply_10(v_p_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v___x_3381_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, lean_box(0));
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3408_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3385_ = v___x_3382_;
v_isShared_3386_ = v_isSharedCheck_3408_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3382_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3408_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; lean_object* v___y_3389_; lean_object* v___x_3397_; uint8_t v___x_3398_; 
v___x_3387_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___closed__2);
v___x_3397_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3398_ = lean_int_dec_le(v___x_3397_, v_c_3366_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3399_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__23);
v___x_3400_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__6);
v___x_3401_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__26);
v___x_3402_ = lean_int_neg(v_c_3366_);
v___x_3403_ = l_Int_toNat(v___x_3402_);
lean_dec(v___x_3402_);
v___x_3404_ = l_Lean_instToExprInt_mkNat(v___x_3403_);
v___x_3405_ = l_Lean_mkApp3(v___x_3399_, v___x_3400_, v___x_3401_, v___x_3404_);
v___y_3389_ = v___x_3405_;
goto v___jp_3388_;
}
else
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = l_Int_toNat(v_c_3366_);
v___x_3407_ = l_Lean_instToExprInt_mkNat(v___x_3406_);
v___y_3389_ = v___x_3407_;
goto v___jp_3388_;
}
v___jp_3388_:
{
lean_object* v_nil_3390_; lean_object* v_cons_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3395_; 
v_nil_3390_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__12);
v_cons_3391_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__16);
v___x_3392_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Tactic_Omega_Justification_tidyProof_spec__0(v_nil_3390_, v_cons_3391_, v_x_3367_);
v___x_3393_ = l_Lean_mkApp4(v___x_3387_, v___y_3389_, v___x_3392_, v_a_3380_, v_a_3383_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v___x_3393_);
v___x_3395_ = v___x_3385_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3393_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
lean_dec(v_a_3380_);
return v___x_3382_;
}
}
else
{
lean_dec_ref(v_p_3368_);
return v___x_3379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed(lean_object* v_c_3409_, lean_object* v_x_3410_, lean_object* v_p_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_){
_start:
{
uint8_t v_a_boxed_3422_; lean_object* v_res_3423_; 
v_a_boxed_3422_ = lean_unbox(v_a_3415_);
v_res_3423_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof(v_c_3409_, v_x_3410_, v_p_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_boxed_3422_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
lean_dec(v_a_3416_);
lean_dec_ref(v_a_3414_);
lean_dec(v_a_3413_);
lean_dec(v_a_3412_);
lean_dec(v_x_3410_);
lean_dec(v_c_3409_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(lean_object* v_prf_x3f_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, uint8_t v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
if (lean_obj_tag(v_prf_x3f_3424_) == 0)
{
lean_object* v___x_3435_; uint8_t v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3435_ = lean_box(0);
v___x_3436_ = 0;
v___x_3437_ = lean_box(0);
v___x_3438_ = l_Lean_Meta_mkFreshExprMVar(v___x_3435_, v___x_3436_, v___x_3437_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; uint8_t v___x_3440_; lean_object* v___x_3441_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3438_, 1);
v___x_3440_ = 0;
v___x_3441_ = l_Lean_Meta_mkSorry(v_a_3439_, v___x_3440_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
return v___x_3441_;
}
else
{
return v___x_3438_;
}
}
else
{
lean_object* v_val_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v_val_3442_ = lean_ctor_get(v_prf_x3f_3424_, 0);
lean_inc(v_val_3442_);
lean_dec_ref_known(v_prf_x3f_3424_, 1);
v___x_3443_ = lean_box(v___y_3428_);
lean_inc(v___y_3433_);
lean_inc_ref(v___y_3432_);
lean_inc(v___y_3431_);
lean_inc_ref(v___y_3430_);
lean_inc(v___y_3429_);
lean_inc_ref(v___y_3427_);
lean_inc(v___y_3426_);
lean_inc(v___y_3425_);
v___x_3444_ = lean_apply_10(v_val_3442_, v___y_3425_, v___y_3426_, v___y_3427_, v___x_3443_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, lean_box(0));
return v___x_3444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed(lean_object* v_prf_x3f_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
uint8_t v___y_833__boxed_3456_; lean_object* v_res_3457_; 
v___y_833__boxed_3456_ = lean_unbox(v___y_3449_);
v_res_3457_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0(v_prf_x3f_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_833__boxed_3456_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec(v___y_3446_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequality(lean_object* v_p_3458_, lean_object* v_const_3459_, lean_object* v_coeffs_3460_, lean_object* v_prf_x3f_3461_){
_start:
{
lean_object* v_assumptions_3462_; lean_object* v_numVars_3463_; lean_object* v_constraints_3464_; lean_object* v_equalities_3465_; lean_object* v_eliminations_3466_; uint8_t v_possible_3467_; lean_object* v_proveFalse_x3f_3468_; lean_object* v_explanation_x3f_3469_; lean_object* v_prf_3470_; lean_object* v_i_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v_p_x27_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v_f_3480_; lean_object* v_f_3481_; lean_object* v_f_3482_; lean_object* v___x_3483_; 
v_assumptions_3462_ = lean_ctor_get(v_p_3458_, 0);
v_numVars_3463_ = lean_ctor_get(v_p_3458_, 1);
v_constraints_3464_ = lean_ctor_get(v_p_3458_, 2);
v_equalities_3465_ = lean_ctor_get(v_p_3458_, 3);
v_eliminations_3466_ = lean_ctor_get(v_p_3458_, 4);
v_possible_3467_ = lean_ctor_get_uint8(v_p_3458_, sizeof(void*)*7);
v_proveFalse_x3f_3468_ = lean_ctor_get(v_p_3458_, 5);
v_explanation_x3f_3469_ = lean_ctor_get(v_p_3458_, 6);
v_prf_3470_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3470_, 0, v_prf_x3f_3461_);
v_i_3471_ = lean_array_get_size(v_assumptions_3462_);
lean_inc_n(v_coeffs_3460_, 2);
lean_inc(v_const_3459_);
v___x_3472_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality__proof___boxed), 13, 3);
lean_closure_set(v___x_3472_, 0, v_const_3459_);
lean_closure_set(v___x_3472_, 1, v_coeffs_3460_);
lean_closure_set(v___x_3472_, 2, v_prf_3470_);
lean_inc_ref(v_assumptions_3462_);
v___x_3473_ = lean_array_push(v_assumptions_3462_, v___x_3472_);
lean_inc_ref(v_explanation_x3f_3469_);
lean_inc(v_proveFalse_x3f_3468_);
lean_inc(v_eliminations_3466_);
lean_inc_ref(v_equalities_3465_);
lean_inc_ref(v_constraints_3464_);
lean_inc(v_numVars_3463_);
v_p_x27_3474_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3474_, 0, v___x_3473_);
lean_ctor_set(v_p_x27_3474_, 1, v_numVars_3463_);
lean_ctor_set(v_p_x27_3474_, 2, v_constraints_3464_);
lean_ctor_set(v_p_x27_3474_, 3, v_equalities_3465_);
lean_ctor_set(v_p_x27_3474_, 4, v_eliminations_3466_);
lean_ctor_set(v_p_x27_3474_, 5, v_proveFalse_x3f_3468_);
lean_ctor_set(v_p_x27_3474_, 6, v_explanation_x3f_3469_);
lean_ctor_set_uint8(v_p_x27_3474_, sizeof(void*)*7, v_possible_3467_);
v___x_3475_ = lean_int_neg(v_const_3459_);
lean_dec(v_const_3459_);
v___x_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
v___x_3477_ = lean_box(0);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3476_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
lean_inc_ref(v___x_3478_);
v___x_3479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
lean_ctor_set(v___x_3479_, 1, v_coeffs_3460_);
lean_ctor_set(v___x_3479_, 2, v_i_3471_);
v_f_3480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3480_, 0, v_coeffs_3460_);
lean_ctor_set(v_f_3480_, 1, v___x_3478_);
lean_ctor_set(v_f_3480_, 2, v___x_3479_);
v_f_3481_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3458_, v_f_3480_);
v_f_3482_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3481_);
v___x_3483_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3474_, v_f_3482_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEquality(lean_object* v_p_3484_, lean_object* v_const_3485_, lean_object* v_coeffs_3486_, lean_object* v_prf_x3f_3487_){
_start:
{
lean_object* v_assumptions_3488_; lean_object* v_numVars_3489_; lean_object* v_constraints_3490_; lean_object* v_equalities_3491_; lean_object* v_eliminations_3492_; uint8_t v_possible_3493_; lean_object* v_proveFalse_x3f_3494_; lean_object* v_explanation_x3f_3495_; lean_object* v_prf_3496_; lean_object* v_i_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v_p_x27_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v_f_3505_; lean_object* v_f_3506_; lean_object* v_f_3507_; lean_object* v___x_3508_; 
v_assumptions_3488_ = lean_ctor_get(v_p_3484_, 0);
v_numVars_3489_ = lean_ctor_get(v_p_3484_, 1);
v_constraints_3490_ = lean_ctor_get(v_p_3484_, 2);
v_equalities_3491_ = lean_ctor_get(v_p_3484_, 3);
v_eliminations_3492_ = lean_ctor_get(v_p_3484_, 4);
v_possible_3493_ = lean_ctor_get_uint8(v_p_3484_, sizeof(void*)*7);
v_proveFalse_x3f_3494_ = lean_ctor_get(v_p_3484_, 5);
v_explanation_x3f_3495_ = lean_ctor_get(v_p_3484_, 6);
v_prf_3496_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addInequality___lam__0___boxed), 11, 1);
lean_closure_set(v_prf_3496_, 0, v_prf_x3f_3487_);
v_i_3497_ = lean_array_get_size(v_assumptions_3488_);
lean_inc_n(v_coeffs_3486_, 2);
lean_inc(v_const_3485_);
v___x_3498_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_Problem_addEquality__proof___boxed), 13, 3);
lean_closure_set(v___x_3498_, 0, v_const_3485_);
lean_closure_set(v___x_3498_, 1, v_coeffs_3486_);
lean_closure_set(v___x_3498_, 2, v_prf_3496_);
lean_inc_ref(v_assumptions_3488_);
v___x_3499_ = lean_array_push(v_assumptions_3488_, v___x_3498_);
lean_inc_ref(v_explanation_x3f_3495_);
lean_inc(v_proveFalse_x3f_3494_);
lean_inc(v_eliminations_3492_);
lean_inc_ref(v_equalities_3491_);
lean_inc_ref(v_constraints_3490_);
lean_inc(v_numVars_3489_);
v_p_x27_3500_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_p_x27_3500_, 0, v___x_3499_);
lean_ctor_set(v_p_x27_3500_, 1, v_numVars_3489_);
lean_ctor_set(v_p_x27_3500_, 2, v_constraints_3490_);
lean_ctor_set(v_p_x27_3500_, 3, v_equalities_3491_);
lean_ctor_set(v_p_x27_3500_, 4, v_eliminations_3492_);
lean_ctor_set(v_p_x27_3500_, 5, v_proveFalse_x3f_3494_);
lean_ctor_set(v_p_x27_3500_, 6, v_explanation_x3f_3495_);
lean_ctor_set_uint8(v_p_x27_3500_, sizeof(void*)*7, v_possible_3493_);
v___x_3501_ = lean_int_neg(v_const_3485_);
lean_dec(v_const_3485_);
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_inc_ref(v___x_3502_);
v___x_3503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
lean_inc_ref(v___x_3503_);
v___x_3504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set(v___x_3504_, 1, v_coeffs_3486_);
lean_ctor_set(v___x_3504_, 2, v_i_3497_);
v_f_3505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_f_3505_, 0, v_coeffs_3486_);
lean_ctor_set(v_f_3505_, 1, v___x_3503_);
lean_ctor_set(v_f_3505_, 2, v___x_3504_);
v_f_3506_ = l_Lean_Elab_Tactic_Omega_Problem_replayEliminations(v_p_3484_, v_f_3505_);
v_f_3507_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v_f_3506_);
v___x_3508_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_p_x27_3500_, v_f_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(lean_object* v_x_3509_, lean_object* v_x_3510_){
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
v___x_3517_ = l_Lean_Elab_Tactic_Omega_Problem_addInequality(v_x_3509_, v_fst_3514_, v_fst_3515_, v_snd_3516_);
v_x_3509_ = v___x_3517_;
v_x_3510_ = v_tail_3513_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addInequalities(lean_object* v_p_3519_, lean_object* v_ineqs_3520_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addInequalities_spec__0(v_p_3519_, v_ineqs_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(lean_object* v_x_3522_, lean_object* v_x_3523_){
_start:
{
if (lean_obj_tag(v_x_3523_) == 0)
{
return v_x_3522_;
}
else
{
lean_object* v_head_3524_; lean_object* v_snd_3525_; lean_object* v_tail_3526_; lean_object* v_fst_3527_; lean_object* v_fst_3528_; lean_object* v_snd_3529_; lean_object* v___x_3530_; 
v_head_3524_ = lean_ctor_get(v_x_3523_, 0);
lean_inc(v_head_3524_);
v_snd_3525_ = lean_ctor_get(v_head_3524_, 1);
lean_inc(v_snd_3525_);
v_tail_3526_ = lean_ctor_get(v_x_3523_, 1);
lean_inc(v_tail_3526_);
lean_dec_ref_known(v_x_3523_, 2);
v_fst_3527_ = lean_ctor_get(v_head_3524_, 0);
lean_inc(v_fst_3527_);
lean_dec(v_head_3524_);
v_fst_3528_ = lean_ctor_get(v_snd_3525_, 0);
lean_inc(v_fst_3528_);
v_snd_3529_ = lean_ctor_get(v_snd_3525_, 1);
lean_inc(v_snd_3529_);
lean_dec(v_snd_3525_);
v___x_3530_ = l_Lean_Elab_Tactic_Omega_Problem_addEquality(v_x_3522_, v_fst_3527_, v_fst_3528_, v_snd_3529_);
v_x_3522_ = v___x_3530_;
v_x_3523_ = v_tail_3526_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_addEqualities(lean_object* v_p_3532_, lean_object* v_eqs_3533_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_addEqualities_spec__0(v_p_3532_, v_eqs_3533_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__0(lean_object* v___x_3541_, lean_object* v_x_3542_){
_start:
{
lean_object* v_constraint_3543_; lean_object* v_coeffs_3544_; lean_object* v_lowerBound_3545_; lean_object* v_upperBound_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___y_3551_; lean_object* v___y_3552_; 
v_constraint_3543_ = lean_ctor_get(v_x_3542_, 1);
lean_inc_ref(v_constraint_3543_);
v_coeffs_3544_ = lean_ctor_get(v_x_3542_, 0);
lean_inc(v_coeffs_3544_);
lean_dec_ref(v_x_3542_);
v_lowerBound_3545_ = lean_ctor_get(v_constraint_3543_, 0);
lean_inc(v_lowerBound_3545_);
v_upperBound_3546_ = lean_ctor_get(v_constraint_3543_, 1);
lean_inc(v_upperBound_3546_);
lean_dec_ref(v_constraint_3543_);
v___x_3547_ = l_List_toString___redArg(v___x_3541_, v_coeffs_3544_);
v___x_3548_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3549_ = lean_string_append(v___x_3547_, v___x_3548_);
if (lean_obj_tag(v_lowerBound_3545_) == 0)
{
if (lean_obj_tag(v_upperBound_3546_) == 0)
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3558_ = lean_string_append(v___x_3549_, v___x_3557_);
return v___x_3558_;
}
else
{
lean_object* v_val_3559_; lean_object* v___x_3560_; lean_object* v___y_3562_; lean_object* v_intZero_3567_; uint8_t v_isNeg_3568_; 
v_val_3559_ = lean_ctor_get(v_upperBound_3546_, 0);
lean_inc(v_val_3559_);
lean_dec_ref_known(v_upperBound_3546_, 1);
v___x_3560_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3567_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3568_ = lean_int_dec_lt(v_val_3559_, v_intZero_3567_);
if (v_isNeg_3568_ == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3570_; 
v_a_3569_ = lean_nat_abs(v_val_3559_);
lean_dec(v_val_3559_);
v___x_3570_ = l_Nat_reprFast(v_a_3569_);
v___y_3562_ = v___x_3570_;
goto v___jp_3561_;
}
else
{
lean_object* v_abs_3571_; lean_object* v_one_3572_; lean_object* v_a_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v_abs_3571_ = lean_nat_abs(v_val_3559_);
lean_dec(v_val_3559_);
v_one_3572_ = lean_unsigned_to_nat(1u);
v_a_3573_ = lean_nat_sub(v_abs_3571_, v_one_3572_);
lean_dec(v_abs_3571_);
v___x_3574_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3575_ = lean_nat_add(v_a_3573_, v_one_3572_);
lean_dec(v_a_3573_);
v___x_3576_ = l_Nat_reprFast(v___x_3575_);
v___x_3577_ = lean_string_append(v___x_3574_, v___x_3576_);
lean_dec_ref(v___x_3576_);
v___y_3562_ = v___x_3577_;
goto v___jp_3561_;
}
v___jp_3561_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3563_ = lean_string_append(v___x_3560_, v___y_3562_);
lean_dec_ref(v___y_3562_);
v___x_3564_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3565_ = lean_string_append(v___x_3563_, v___x_3564_);
v___x_3566_ = lean_string_append(v___x_3549_, v___x_3565_);
lean_dec_ref(v___x_3565_);
return v___x_3566_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3546_) == 0)
{
lean_object* v_val_3578_; lean_object* v___x_3579_; lean_object* v___y_3581_; lean_object* v_intZero_3586_; uint8_t v_isNeg_3587_; 
v_val_3578_ = lean_ctor_get(v_lowerBound_3545_, 0);
lean_inc(v_val_3578_);
lean_dec_ref_known(v_lowerBound_3545_, 1);
v___x_3579_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3586_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3587_ = lean_int_dec_lt(v_val_3578_, v_intZero_3586_);
if (v_isNeg_3587_ == 0)
{
lean_object* v_a_3588_; lean_object* v___x_3589_; 
v_a_3588_ = lean_nat_abs(v_val_3578_);
lean_dec(v_val_3578_);
v___x_3589_ = l_Nat_reprFast(v_a_3588_);
v___y_3581_ = v___x_3589_;
goto v___jp_3580_;
}
else
{
lean_object* v_abs_3590_; lean_object* v_one_3591_; lean_object* v_a_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v_abs_3590_ = lean_nat_abs(v_val_3578_);
lean_dec(v_val_3578_);
v_one_3591_ = lean_unsigned_to_nat(1u);
v_a_3592_ = lean_nat_sub(v_abs_3590_, v_one_3591_);
lean_dec(v_abs_3590_);
v___x_3593_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3594_ = lean_nat_add(v_a_3592_, v_one_3591_);
lean_dec(v_a_3592_);
v___x_3595_ = l_Nat_reprFast(v___x_3594_);
v___x_3596_ = lean_string_append(v___x_3593_, v___x_3595_);
lean_dec_ref(v___x_3595_);
v___y_3581_ = v___x_3596_;
goto v___jp_3580_;
}
v___jp_3580_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3582_ = lean_string_append(v___x_3579_, v___y_3581_);
lean_dec_ref(v___y_3581_);
v___x_3583_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3584_ = lean_string_append(v___x_3582_, v___x_3583_);
v___x_3585_ = lean_string_append(v___x_3549_, v___x_3584_);
lean_dec_ref(v___x_3584_);
return v___x_3585_;
}
}
else
{
lean_object* v_val_3597_; lean_object* v_val_3598_; uint8_t v___x_3599_; 
v_val_3597_ = lean_ctor_get(v_lowerBound_3545_, 0);
lean_inc(v_val_3597_);
lean_dec_ref_known(v_lowerBound_3545_, 1);
v_val_3598_ = lean_ctor_get(v_upperBound_3546_, 0);
lean_inc(v_val_3598_);
lean_dec_ref_known(v_upperBound_3546_, 1);
v___x_3599_ = lean_int_dec_lt(v_val_3598_, v_val_3597_);
if (v___x_3599_ == 0)
{
uint8_t v___x_3600_; 
v___x_3600_ = lean_int_dec_eq(v_val_3597_, v_val_3598_);
if (v___x_3600_ == 0)
{
lean_object* v___x_3601_; lean_object* v___y_3603_; lean_object* v_intZero_3618_; uint8_t v_isNeg_3619_; 
v___x_3601_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3618_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3619_ = lean_int_dec_lt(v_val_3597_, v_intZero_3618_);
if (v_isNeg_3619_ == 0)
{
lean_object* v_a_3620_; lean_object* v___x_3621_; 
v_a_3620_ = lean_nat_abs(v_val_3597_);
lean_dec(v_val_3597_);
v___x_3621_ = l_Nat_reprFast(v_a_3620_);
v___y_3603_ = v___x_3621_;
goto v___jp_3602_;
}
else
{
lean_object* v_abs_3622_; lean_object* v_one_3623_; lean_object* v_a_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v_abs_3622_ = lean_nat_abs(v_val_3597_);
lean_dec(v_val_3597_);
v_one_3623_ = lean_unsigned_to_nat(1u);
v_a_3624_ = lean_nat_sub(v_abs_3622_, v_one_3623_);
lean_dec(v_abs_3622_);
v___x_3625_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3626_ = lean_nat_add(v_a_3624_, v_one_3623_);
lean_dec(v_a_3624_);
v___x_3627_ = l_Nat_reprFast(v___x_3626_);
v___x_3628_ = lean_string_append(v___x_3625_, v___x_3627_);
lean_dec_ref(v___x_3627_);
v___y_3603_ = v___x_3628_;
goto v___jp_3602_;
}
v___jp_3602_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v_intZero_3607_; uint8_t v_isNeg_3608_; 
v___x_3604_ = lean_string_append(v___x_3601_, v___y_3603_);
lean_dec_ref(v___y_3603_);
v___x_3605_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3606_ = lean_string_append(v___x_3604_, v___x_3605_);
v_intZero_3607_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3608_ = lean_int_dec_lt(v_val_3598_, v_intZero_3607_);
if (v_isNeg_3608_ == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; 
v_a_3609_ = lean_nat_abs(v_val_3598_);
lean_dec(v_val_3598_);
v___x_3610_ = l_Nat_reprFast(v_a_3609_);
v___y_3551_ = v___x_3606_;
v___y_3552_ = v___x_3610_;
goto v___jp_3550_;
}
else
{
lean_object* v_abs_3611_; lean_object* v_one_3612_; lean_object* v_a_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v_abs_3611_ = lean_nat_abs(v_val_3598_);
lean_dec(v_val_3598_);
v_one_3612_ = lean_unsigned_to_nat(1u);
v_a_3613_ = lean_nat_sub(v_abs_3611_, v_one_3612_);
lean_dec(v_abs_3611_);
v___x_3614_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3615_ = lean_nat_add(v_a_3613_, v_one_3612_);
lean_dec(v_a_3613_);
v___x_3616_ = l_Nat_reprFast(v___x_3615_);
v___x_3617_ = lean_string_append(v___x_3614_, v___x_3616_);
lean_dec_ref(v___x_3616_);
v___y_3551_ = v___x_3606_;
v___y_3552_ = v___x_3617_;
goto v___jp_3550_;
}
}
}
else
{
lean_object* v___x_3629_; lean_object* v___y_3631_; lean_object* v_intZero_3636_; uint8_t v_isNeg_3637_; 
lean_dec(v_val_3598_);
v___x_3629_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3636_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3637_ = lean_int_dec_lt(v_val_3597_, v_intZero_3636_);
if (v_isNeg_3637_ == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3639_; 
v_a_3638_ = lean_nat_abs(v_val_3597_);
lean_dec(v_val_3597_);
v___x_3639_ = l_Nat_reprFast(v_a_3638_);
v___y_3631_ = v___x_3639_;
goto v___jp_3630_;
}
else
{
lean_object* v_abs_3640_; lean_object* v_one_3641_; lean_object* v_a_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v_abs_3640_ = lean_nat_abs(v_val_3597_);
lean_dec(v_val_3597_);
v_one_3641_ = lean_unsigned_to_nat(1u);
v_a_3642_ = lean_nat_sub(v_abs_3640_, v_one_3641_);
lean_dec(v_abs_3640_);
v___x_3643_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3644_ = lean_nat_add(v_a_3642_, v_one_3641_);
lean_dec(v_a_3642_);
v___x_3645_ = l_Nat_reprFast(v___x_3644_);
v___x_3646_ = lean_string_append(v___x_3643_, v___x_3645_);
lean_dec_ref(v___x_3645_);
v___y_3631_ = v___x_3646_;
goto v___jp_3630_;
}
v___jp_3630_:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3632_ = lean_string_append(v___x_3629_, v___y_3631_);
lean_dec_ref(v___y_3631_);
v___x_3633_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3634_ = lean_string_append(v___x_3632_, v___x_3633_);
v___x_3635_ = lean_string_append(v___x_3549_, v___x_3634_);
lean_dec_ref(v___x_3634_);
return v___x_3635_;
}
}
}
else
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
lean_dec(v_val_3598_);
lean_dec(v_val_3597_);
v___x_3647_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3648_ = lean_string_append(v___x_3549_, v___x_3647_);
return v___x_3648_;
}
}
}
v___jp_3550_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3553_ = lean_string_append(v___y_3551_, v___y_3552_);
lean_dec_ref(v___y_3552_);
v___x_3554_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3555_ = lean_string_append(v___x_3553_, v___x_3554_);
v___x_3556_ = lean_string_append(v___x_3549_, v___x_3555_);
lean_dec_ref(v___x_3555_);
return v___x_3556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__1(lean_object* v___x_3649_, lean_object* v_x_3650_){
_start:
{
lean_object* v_fst_3651_; lean_object* v_constraint_3652_; lean_object* v_coeffs_3653_; lean_object* v_lowerBound_3654_; lean_object* v_upperBound_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___y_3660_; lean_object* v___y_3661_; 
v_fst_3651_ = lean_ctor_get(v_x_3650_, 0);
lean_inc(v_fst_3651_);
lean_dec_ref(v_x_3650_);
v_constraint_3652_ = lean_ctor_get(v_fst_3651_, 1);
lean_inc_ref(v_constraint_3652_);
v_coeffs_3653_ = lean_ctor_get(v_fst_3651_, 0);
lean_inc(v_coeffs_3653_);
lean_dec(v_fst_3651_);
v_lowerBound_3654_ = lean_ctor_get(v_constraint_3652_, 0);
lean_inc(v_lowerBound_3654_);
v_upperBound_3655_ = lean_ctor_get(v_constraint_3652_, 1);
lean_inc(v_upperBound_3655_);
lean_dec_ref(v_constraint_3652_);
v___x_3656_ = l_List_toString___redArg(v___x_3649_, v_coeffs_3653_);
v___x_3657_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_3658_ = lean_string_append(v___x_3656_, v___x_3657_);
if (lean_obj_tag(v_lowerBound_3654_) == 0)
{
if (lean_obj_tag(v_upperBound_3655_) == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_3667_ = lean_string_append(v___x_3658_, v___x_3666_);
return v___x_3667_;
}
else
{
lean_object* v_val_3668_; lean_object* v___x_3669_; lean_object* v___y_3671_; lean_object* v_intZero_3676_; uint8_t v_isNeg_3677_; 
v_val_3668_ = lean_ctor_get(v_upperBound_3655_, 0);
lean_inc(v_val_3668_);
lean_dec_ref_known(v_upperBound_3655_, 1);
v___x_3669_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_3676_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3677_ = lean_int_dec_lt(v_val_3668_, v_intZero_3676_);
if (v_isNeg_3677_ == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3679_; 
v_a_3678_ = lean_nat_abs(v_val_3668_);
lean_dec(v_val_3668_);
v___x_3679_ = l_Nat_reprFast(v_a_3678_);
v___y_3671_ = v___x_3679_;
goto v___jp_3670_;
}
else
{
lean_object* v_abs_3680_; lean_object* v_one_3681_; lean_object* v_a_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v_abs_3680_ = lean_nat_abs(v_val_3668_);
lean_dec(v_val_3668_);
v_one_3681_ = lean_unsigned_to_nat(1u);
v_a_3682_ = lean_nat_sub(v_abs_3680_, v_one_3681_);
lean_dec(v_abs_3680_);
v___x_3683_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3684_ = lean_nat_add(v_a_3682_, v_one_3681_);
lean_dec(v_a_3682_);
v___x_3685_ = l_Nat_reprFast(v___x_3684_);
v___x_3686_ = lean_string_append(v___x_3683_, v___x_3685_);
lean_dec_ref(v___x_3685_);
v___y_3671_ = v___x_3686_;
goto v___jp_3670_;
}
v___jp_3670_:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3672_ = lean_string_append(v___x_3669_, v___y_3671_);
lean_dec_ref(v___y_3671_);
v___x_3673_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3674_ = lean_string_append(v___x_3672_, v___x_3673_);
v___x_3675_ = lean_string_append(v___x_3658_, v___x_3674_);
lean_dec_ref(v___x_3674_);
return v___x_3675_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_3655_) == 0)
{
lean_object* v_val_3687_; lean_object* v___x_3688_; lean_object* v___y_3690_; lean_object* v_intZero_3695_; uint8_t v_isNeg_3696_; 
v_val_3687_ = lean_ctor_get(v_lowerBound_3654_, 0);
lean_inc(v_val_3687_);
lean_dec_ref_known(v_lowerBound_3654_, 1);
v___x_3688_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3695_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3696_ = lean_int_dec_lt(v_val_3687_, v_intZero_3695_);
if (v_isNeg_3696_ == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3698_; 
v_a_3697_ = lean_nat_abs(v_val_3687_);
lean_dec(v_val_3687_);
v___x_3698_ = l_Nat_reprFast(v_a_3697_);
v___y_3690_ = v___x_3698_;
goto v___jp_3689_;
}
else
{
lean_object* v_abs_3699_; lean_object* v_one_3700_; lean_object* v_a_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v_abs_3699_ = lean_nat_abs(v_val_3687_);
lean_dec(v_val_3687_);
v_one_3700_ = lean_unsigned_to_nat(1u);
v_a_3701_ = lean_nat_sub(v_abs_3699_, v_one_3700_);
lean_dec(v_abs_3699_);
v___x_3702_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3703_ = lean_nat_add(v_a_3701_, v_one_3700_);
lean_dec(v_a_3701_);
v___x_3704_ = l_Nat_reprFast(v___x_3703_);
v___x_3705_ = lean_string_append(v___x_3702_, v___x_3704_);
lean_dec_ref(v___x_3704_);
v___y_3690_ = v___x_3705_;
goto v___jp_3689_;
}
v___jp_3689_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3691_ = lean_string_append(v___x_3688_, v___y_3690_);
lean_dec_ref(v___y_3690_);
v___x_3692_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_3693_ = lean_string_append(v___x_3691_, v___x_3692_);
v___x_3694_ = lean_string_append(v___x_3658_, v___x_3693_);
lean_dec_ref(v___x_3693_);
return v___x_3694_;
}
}
else
{
lean_object* v_val_3706_; lean_object* v_val_3707_; uint8_t v___x_3708_; 
v_val_3706_ = lean_ctor_get(v_lowerBound_3654_, 0);
lean_inc(v_val_3706_);
lean_dec_ref_known(v_lowerBound_3654_, 1);
v_val_3707_ = lean_ctor_get(v_upperBound_3655_, 0);
lean_inc(v_val_3707_);
lean_dec_ref_known(v_upperBound_3655_, 1);
v___x_3708_ = lean_int_dec_lt(v_val_3707_, v_val_3706_);
if (v___x_3708_ == 0)
{
uint8_t v___x_3709_; 
v___x_3709_ = lean_int_dec_eq(v_val_3706_, v_val_3707_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; lean_object* v___y_3712_; lean_object* v_intZero_3727_; uint8_t v_isNeg_3728_; 
v___x_3710_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_3727_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3728_ = lean_int_dec_lt(v_val_3706_, v_intZero_3727_);
if (v_isNeg_3728_ == 0)
{
lean_object* v_a_3729_; lean_object* v___x_3730_; 
v_a_3729_ = lean_nat_abs(v_val_3706_);
lean_dec(v_val_3706_);
v___x_3730_ = l_Nat_reprFast(v_a_3729_);
v___y_3712_ = v___x_3730_;
goto v___jp_3711_;
}
else
{
lean_object* v_abs_3731_; lean_object* v_one_3732_; lean_object* v_a_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_abs_3731_ = lean_nat_abs(v_val_3706_);
lean_dec(v_val_3706_);
v_one_3732_ = lean_unsigned_to_nat(1u);
v_a_3733_ = lean_nat_sub(v_abs_3731_, v_one_3732_);
lean_dec(v_abs_3731_);
v___x_3734_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3735_ = lean_nat_add(v_a_3733_, v_one_3732_);
lean_dec(v_a_3733_);
v___x_3736_ = l_Nat_reprFast(v___x_3735_);
v___x_3737_ = lean_string_append(v___x_3734_, v___x_3736_);
lean_dec_ref(v___x_3736_);
v___y_3712_ = v___x_3737_;
goto v___jp_3711_;
}
v___jp_3711_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v_intZero_3716_; uint8_t v_isNeg_3717_; 
v___x_3713_ = lean_string_append(v___x_3710_, v___y_3712_);
lean_dec_ref(v___y_3712_);
v___x_3714_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_3715_ = lean_string_append(v___x_3713_, v___x_3714_);
v_intZero_3716_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3717_ = lean_int_dec_lt(v_val_3707_, v_intZero_3716_);
if (v_isNeg_3717_ == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; 
v_a_3718_ = lean_nat_abs(v_val_3707_);
lean_dec(v_val_3707_);
v___x_3719_ = l_Nat_reprFast(v_a_3718_);
v___y_3660_ = v___x_3715_;
v___y_3661_ = v___x_3719_;
goto v___jp_3659_;
}
else
{
lean_object* v_abs_3720_; lean_object* v_one_3721_; lean_object* v_a_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v_abs_3720_ = lean_nat_abs(v_val_3707_);
lean_dec(v_val_3707_);
v_one_3721_ = lean_unsigned_to_nat(1u);
v_a_3722_ = lean_nat_sub(v_abs_3720_, v_one_3721_);
lean_dec(v_abs_3720_);
v___x_3723_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3724_ = lean_nat_add(v_a_3722_, v_one_3721_);
lean_dec(v_a_3722_);
v___x_3725_ = l_Nat_reprFast(v___x_3724_);
v___x_3726_ = lean_string_append(v___x_3723_, v___x_3725_);
lean_dec_ref(v___x_3725_);
v___y_3660_ = v___x_3715_;
v___y_3661_ = v___x_3726_;
goto v___jp_3659_;
}
}
}
else
{
lean_object* v___x_3738_; lean_object* v___y_3740_; lean_object* v_intZero_3745_; uint8_t v_isNeg_3746_; 
lean_dec(v_val_3707_);
v___x_3738_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_3745_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_3746_ = lean_int_dec_lt(v_val_3706_, v_intZero_3745_);
if (v_isNeg_3746_ == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3748_; 
v_a_3747_ = lean_nat_abs(v_val_3706_);
lean_dec(v_val_3706_);
v___x_3748_ = l_Nat_reprFast(v_a_3747_);
v___y_3740_ = v___x_3748_;
goto v___jp_3739_;
}
else
{
lean_object* v_abs_3749_; lean_object* v_one_3750_; lean_object* v_a_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v_abs_3749_ = lean_nat_abs(v_val_3706_);
lean_dec(v_val_3706_);
v_one_3750_ = lean_unsigned_to_nat(1u);
v_a_3751_ = lean_nat_sub(v_abs_3749_, v_one_3750_);
lean_dec(v_abs_3749_);
v___x_3752_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_3753_ = lean_nat_add(v_a_3751_, v_one_3750_);
lean_dec(v_a_3751_);
v___x_3754_ = l_Nat_reprFast(v___x_3753_);
v___x_3755_ = lean_string_append(v___x_3752_, v___x_3754_);
lean_dec_ref(v___x_3754_);
v___y_3740_ = v___x_3755_;
goto v___jp_3739_;
}
v___jp_3739_:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3741_ = lean_string_append(v___x_3738_, v___y_3740_);
lean_dec_ref(v___y_3740_);
v___x_3742_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_3743_ = lean_string_append(v___x_3741_, v___x_3742_);
v___x_3744_ = lean_string_append(v___x_3658_, v___x_3743_);
lean_dec_ref(v___x_3743_);
return v___x_3744_;
}
}
}
else
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
lean_dec(v_val_3707_);
lean_dec(v_val_3706_);
v___x_3756_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_3757_ = lean_string_append(v___x_3658_, v___x_3756_);
return v___x_3757_;
}
}
}
v___jp_3659_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3662_ = lean_string_append(v___y_3660_, v___y_3661_);
lean_dec_ref(v___y_3661_);
v___x_3663_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_3664_ = lean_string_append(v___x_3662_, v___x_3663_);
v___x_3665_ = lean_string_append(v___x_3658_, v___x_3664_);
lean_dec_ref(v___x_3664_);
return v___x_3665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2(lean_object* v___f_3762_, lean_object* v___f_3763_, lean_object* v___f_3764_, lean_object* v_d_3765_){
_start:
{
lean_object* v_var_3766_; lean_object* v_irrelevant_3767_; lean_object* v_lowerBounds_3768_; lean_object* v_upperBounds_3769_; lean_object* v___x_3770_; lean_object* v_irrelevant_3771_; lean_object* v_lowerBounds_3772_; lean_object* v_upperBounds_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v_var_3766_ = lean_ctor_get(v_d_3765_, 0);
lean_inc(v_var_3766_);
v_irrelevant_3767_ = lean_ctor_get(v_d_3765_, 1);
lean_inc(v_irrelevant_3767_);
v_lowerBounds_3768_ = lean_ctor_get(v_d_3765_, 2);
lean_inc(v_lowerBounds_3768_);
v_upperBounds_3769_ = lean_ctor_get(v_d_3765_, 3);
lean_inc(v_upperBounds_3769_);
lean_dec_ref(v_d_3765_);
v___x_3770_ = lean_box(0);
v_irrelevant_3771_ = l_List_mapTR_loop___redArg(v___f_3762_, v_irrelevant_3767_, v___x_3770_);
lean_inc_ref(v___f_3763_);
v_lowerBounds_3772_ = l_List_mapTR_loop___redArg(v___f_3763_, v_lowerBounds_3768_, v___x_3770_);
v_upperBounds_3773_ = l_List_mapTR_loop___redArg(v___f_3763_, v_upperBounds_3769_, v___x_3770_);
v___x_3774_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__0));
v___x_3775_ = l_Nat_reprFast(v_var_3766_);
v___x_3776_ = lean_string_append(v___x_3774_, v___x_3775_);
lean_dec_ref(v___x_3775_);
v___x_3777_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_3778_ = lean_string_append(v___x_3776_, v___x_3777_);
v___x_3779_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__1));
lean_inc_ref_n(v___f_3764_, 2);
v___x_3780_ = l_List_toString___redArg(v___f_3764_, v_irrelevant_3771_);
v___x_3781_ = lean_string_append(v___x_3779_, v___x_3780_);
lean_dec_ref(v___x_3780_);
v___x_3782_ = lean_string_append(v___x_3781_, v___x_3777_);
v___x_3783_ = lean_string_append(v___x_3778_, v___x_3782_);
lean_dec_ref(v___x_3782_);
v___x_3784_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__2));
v___x_3785_ = l_List_toString___redArg(v___f_3764_, v_lowerBounds_3772_);
v___x_3786_ = lean_string_append(v___x_3784_, v___x_3785_);
lean_dec_ref(v___x_3785_);
v___x_3787_ = lean_string_append(v___x_3786_, v___x_3777_);
v___x_3788_ = lean_string_append(v___x_3783_, v___x_3787_);
lean_dec_ref(v___x_3787_);
v___x_3789_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instToStringFourierMotzkinData___lam__2___closed__3));
v___x_3790_ = l_List_toString___redArg(v___f_3764_, v_upperBounds_3773_);
v___x_3791_ = lean_string_append(v___x_3789_, v___x_3790_);
lean_dec_ref(v___x_3790_);
v___x_3792_ = lean_string_append(v___x_3788_, v___x_3791_);
lean_dec_ref(v___x_3791_);
return v___x_3792_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(lean_object* v_d_3803_){
_start:
{
lean_object* v_lowerBounds_3804_; lean_object* v_upperBounds_3805_; uint8_t v___x_3806_; 
v_lowerBounds_3804_ = lean_ctor_get(v_d_3803_, 2);
v_upperBounds_3805_ = lean_ctor_get(v_d_3803_, 3);
v___x_3806_ = l_List_isEmpty___redArg(v_lowerBounds_3804_);
if (v___x_3806_ == 0)
{
return v___x_3806_;
}
else
{
uint8_t v___x_3807_; 
v___x_3807_ = l_List_isEmpty___redArg(v_upperBounds_3805_);
return v___x_3807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty___boxed(lean_object* v_d_3808_){
_start:
{
uint8_t v_res_3809_; lean_object* v_r_3810_; 
v_res_3809_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v_d_3808_);
lean_dec_ref(v_d_3808_);
v_r_3810_ = lean_box(v_res_3809_);
return v_r_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(lean_object* v_d_3811_){
_start:
{
lean_object* v_lowerBounds_3812_; lean_object* v_upperBounds_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_lowerBounds_3812_ = lean_ctor_get(v_d_3811_, 2);
v_upperBounds_3813_ = lean_ctor_get(v_d_3811_, 3);
v___x_3814_ = l_List_lengthTR___redArg(v_lowerBounds_3812_);
v___x_3815_ = l_List_lengthTR___redArg(v_upperBounds_3813_);
v___x_3816_ = lean_nat_mul(v___x_3814_, v___x_3815_);
lean_dec(v___x_3815_);
lean_dec(v___x_3814_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size___boxed(lean_object* v_d_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_d_3817_);
lean_dec_ref(v_d_3817_);
return v_res_3818_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(lean_object* v_d_3819_){
_start:
{
uint8_t v_lowerExact_3820_; 
v_lowerExact_3820_ = lean_ctor_get_uint8(v_d_3819_, sizeof(void*)*4);
if (v_lowerExact_3820_ == 0)
{
uint8_t v_upperExact_3821_; 
v_upperExact_3821_ = lean_ctor_get_uint8(v_d_3819_, sizeof(void*)*4 + 1);
return v_upperExact_3821_;
}
else
{
return v_lowerExact_3820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact___boxed(lean_object* v_d_3822_){
_start:
{
uint8_t v_res_3823_; lean_object* v_r_3824_; 
v_res_3823_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_d_3822_);
lean_dec_ref(v_d_3822_);
v_r_3824_ = lean_box(v_res_3823_);
return v_r_3824_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(lean_object* v_x_3825_, lean_object* v_x_3826_){
_start:
{
if (lean_obj_tag(v_x_3826_) == 0)
{
return v_x_3825_;
}
else
{
lean_object* v_head_3827_; lean_object* v_tail_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v_head_3827_ = lean_ctor_get(v_x_3826_, 0);
v_tail_3828_ = lean_ctor_get(v_x_3826_, 1);
v___x_3829_ = lean_box(0);
v___x_3830_ = 1;
lean_inc(v_head_3827_);
v___x_3831_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3831_, 0, v_head_3827_);
lean_ctor_set(v___x_3831_, 1, v___x_3829_);
lean_ctor_set(v___x_3831_, 2, v___x_3829_);
lean_ctor_set(v___x_3831_, 3, v___x_3829_);
lean_ctor_set_uint8(v___x_3831_, sizeof(void*)*4, v___x_3830_);
lean_ctor_set_uint8(v___x_3831_, sizeof(void*)*4 + 1, v___x_3830_);
v___x_3832_ = lean_array_push(v_x_3825_, v___x_3831_);
v_x_3825_ = v___x_3832_;
v_x_3826_ = v_tail_3828_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2___boxed(lean_object* v_x_3834_, lean_object* v_x_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v_x_3834_, v_x_3835_);
lean_dec(v_x_3835_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(lean_object* v_upperBound_3837_, lean_object* v_b_3838_, lean_object* v___x_3839_, uint8_t v___x_3840_, lean_object* v_____r_3841_, lean_object* v_d_x27_3842_){
_start:
{
if (lean_obj_tag(v_upperBound_3837_) == 0)
{
lean_dec(v___x_3839_);
lean_dec_ref(v_b_3838_);
return v_d_x27_3842_;
}
else
{
lean_object* v_var_3843_; lean_object* v_irrelevant_3844_; lean_object* v_lowerBounds_3845_; lean_object* v_upperBounds_3846_; uint8_t v_lowerExact_3847_; uint8_t v_upperExact_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3863_; 
v_var_3843_ = lean_ctor_get(v_d_x27_3842_, 0);
v_irrelevant_3844_ = lean_ctor_get(v_d_x27_3842_, 1);
v_lowerBounds_3845_ = lean_ctor_get(v_d_x27_3842_, 2);
v_upperBounds_3846_ = lean_ctor_get(v_d_x27_3842_, 3);
v_lowerExact_3847_ = lean_ctor_get_uint8(v_d_x27_3842_, sizeof(void*)*4);
v_upperExact_3848_ = lean_ctor_get_uint8(v_d_x27_3842_, sizeof(void*)*4 + 1);
v_isSharedCheck_3863_ = !lean_is_exclusive(v_d_x27_3842_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3850_ = v_d_x27_3842_;
v_isShared_3851_ = v_isSharedCheck_3863_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_upperBounds_3846_);
lean_inc(v_lowerBounds_3845_);
lean_inc(v_irrelevant_3844_);
lean_inc(v_var_3843_);
lean_dec(v_d_x27_3842_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3863_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
lean_inc(v___x_3839_);
v___x_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3852_, 0, v_b_3838_);
lean_ctor_set(v___x_3852_, 1, v___x_3839_);
v___x_3853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
lean_ctor_set(v___x_3853_, 1, v_upperBounds_3846_);
if (v_upperExact_3848_ == 0)
{
lean_object* v___x_3855_; 
lean_dec(v___x_3839_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 3, v___x_3853_);
v___x_3855_ = v___x_3850_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_var_3843_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_irrelevant_3844_);
lean_ctor_set(v_reuseFailAlloc_3856_, 2, v_lowerBounds_3845_);
lean_ctor_set(v_reuseFailAlloc_3856_, 3, v___x_3853_);
lean_ctor_set_uint8(v_reuseFailAlloc_3856_, sizeof(void*)*4, v_lowerExact_3847_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*4 + 1, v___x_3840_);
return v___x_3855_;
}
}
else
{
lean_object* v___x_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; lean_object* v___x_3861_; 
v___x_3857_ = lean_nat_abs(v___x_3839_);
lean_dec(v___x_3839_);
v___x_3858_ = lean_unsigned_to_nat(1u);
v___x_3859_ = lean_nat_dec_eq(v___x_3857_, v___x_3858_);
lean_dec(v___x_3857_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 3, v___x_3853_);
v___x_3861_ = v___x_3850_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_var_3843_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_irrelevant_3844_);
lean_ctor_set(v_reuseFailAlloc_3862_, 2, v_lowerBounds_3845_);
lean_ctor_set(v_reuseFailAlloc_3862_, 3, v___x_3853_);
lean_ctor_set_uint8(v_reuseFailAlloc_3862_, sizeof(void*)*4, v_lowerExact_3847_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_ctor_set_uint8(v___x_3861_, sizeof(void*)*4 + 1, v___x_3859_);
return v___x_3861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0___boxed(lean_object* v_upperBound_3864_, lean_object* v_b_3865_, lean_object* v___x_3866_, lean_object* v___x_3867_, lean_object* v_____r_3868_, lean_object* v_d_x27_3869_){
_start:
{
uint8_t v___x_1956__boxed_3870_; lean_object* v_res_3871_; 
v___x_1956__boxed_3870_ = lean_unbox(v___x_3867_);
v_res_3871_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v_upperBound_3864_, v_b_3865_, v___x_3866_, v___x_1956__boxed_3870_, v_____r_3868_, v_d_x27_3869_);
lean_dec(v_upperBound_3864_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(lean_object* v_upperBound_3872_, lean_object* v_coeffs_3873_, lean_object* v_constraint_3874_, lean_object* v_b_3875_, lean_object* v_a_3876_, lean_object* v_b_3877_){
_start:
{
lean_object* v_a_3879_; uint8_t v___x_3883_; 
v___x_3883_ = lean_nat_dec_lt(v_a_3876_, v_upperBound_3872_);
if (v___x_3883_ == 0)
{
lean_dec(v_a_3876_);
lean_dec_ref(v_b_3875_);
lean_dec_ref(v_constraint_3874_);
return v_b_3877_;
}
else
{
lean_object* v___x_3884_; uint8_t v___x_3885_; 
v___x_3884_ = lean_array_get_size(v_b_3877_);
v___x_3885_ = lean_nat_dec_lt(v_a_3876_, v___x_3884_);
if (v___x_3885_ == 0)
{
v_a_3879_ = v_b_3877_;
goto v___jp_3878_;
}
else
{
lean_object* v___x_3886_; lean_object* v_v_3887_; lean_object* v___x_3888_; lean_object* v_xs_x27_3889_; lean_object* v___y_3891_; lean_object* v___x_3893_; uint8_t v___x_3894_; 
lean_inc(v_a_3876_);
v___x_3886_ = l_Lean_Omega_IntList_get(v_coeffs_3873_, v_a_3876_);
v_v_3887_ = lean_array_fget(v_b_3877_, v_a_3876_);
v___x_3888_ = lean_box(0);
v_xs_x27_3889_ = lean_array_fset(v_b_3877_, v_a_3876_, v___x_3888_);
v___x_3893_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v___x_3894_ = lean_int_dec_eq(v___x_3886_, v___x_3893_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; lean_object* v_lowerBound_3896_; 
lean_inc_ref(v_constraint_3874_);
lean_inc(v___x_3886_);
v___x_3895_ = l_Lean_Omega_Constraint_scale(v___x_3886_, v_constraint_3874_);
v_lowerBound_3896_ = lean_ctor_get(v___x_3895_, 0);
if (lean_obj_tag(v_lowerBound_3896_) == 0)
{
lean_object* v_upperBound_3897_; lean_object* v___x_3898_; 
v_upperBound_3897_ = lean_ctor_get(v___x_3895_, 1);
lean_inc(v_upperBound_3897_);
lean_dec_ref(v___x_3895_);
lean_inc_ref(v_b_3875_);
v___x_3898_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v_upperBound_3897_, v_b_3875_, v___x_3886_, v___x_3894_, v___x_3888_, v_v_3887_);
lean_dec(v_upperBound_3897_);
v___y_3891_ = v___x_3898_;
goto v___jp_3890_;
}
else
{
lean_object* v_upperBound_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3926_; 
v_upperBound_3899_ = lean_ctor_get(v___x_3895_, 1);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3926_ == 0)
{
lean_object* v_unused_3927_; 
v_unused_3927_ = lean_ctor_get(v___x_3895_, 0);
lean_dec(v_unused_3927_);
v___x_3901_ = v___x_3895_;
v_isShared_3902_ = v_isSharedCheck_3926_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_upperBound_3899_);
lean_dec(v___x_3895_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3926_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v_var_3903_; lean_object* v_irrelevant_3904_; lean_object* v_lowerBounds_3905_; lean_object* v_upperBounds_3906_; uint8_t v_lowerExact_3907_; uint8_t v_upperExact_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3925_; 
v_var_3903_ = lean_ctor_get(v_v_3887_, 0);
v_irrelevant_3904_ = lean_ctor_get(v_v_3887_, 1);
v_lowerBounds_3905_ = lean_ctor_get(v_v_3887_, 2);
v_upperBounds_3906_ = lean_ctor_get(v_v_3887_, 3);
v_lowerExact_3907_ = lean_ctor_get_uint8(v_v_3887_, sizeof(void*)*4);
v_upperExact_3908_ = lean_ctor_get_uint8(v_v_3887_, sizeof(void*)*4 + 1);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_v_3887_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3910_ = v_v_3887_;
v_isShared_3911_ = v_isSharedCheck_3925_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_upperBounds_3906_);
lean_inc(v_lowerBounds_3905_);
lean_inc(v_irrelevant_3904_);
lean_inc(v_var_3903_);
lean_dec(v_v_3887_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3925_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
lean_inc(v___x_3886_);
lean_inc_ref(v_b_3875_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 1, v___x_3886_);
lean_ctor_set(v___x_3901_, 0, v_b_3875_);
v___x_3913_ = v___x_3901_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_b_3875_);
lean_ctor_set(v_reuseFailAlloc_3924_, 1, v___x_3886_);
v___x_3913_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3914_; uint8_t v___y_3916_; 
v___x_3914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
lean_ctor_set(v___x_3914_, 1, v_lowerBounds_3905_);
if (v_lowerExact_3907_ == 0)
{
v___y_3916_ = v___x_3894_;
goto v___jp_3915_;
}
else
{
lean_object* v___x_3921_; lean_object* v___x_3922_; uint8_t v___x_3923_; 
v___x_3921_ = lean_nat_abs(v___x_3886_);
v___x_3922_ = lean_unsigned_to_nat(1u);
v___x_3923_ = lean_nat_dec_eq(v___x_3921_, v___x_3922_);
lean_dec(v___x_3921_);
v___y_3916_ = v___x_3923_;
goto v___jp_3915_;
}
v___jp_3915_:
{
lean_object* v___x_3918_; 
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 2, v___x_3914_);
v___x_3918_ = v___x_3910_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_var_3903_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v_irrelevant_3904_);
lean_ctor_set(v_reuseFailAlloc_3920_, 2, v___x_3914_);
lean_ctor_set(v_reuseFailAlloc_3920_, 3, v_upperBounds_3906_);
lean_ctor_set_uint8(v_reuseFailAlloc_3920_, sizeof(void*)*4 + 1, v_upperExact_3908_);
v___x_3918_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
lean_object* v___x_3919_; 
lean_ctor_set_uint8(v___x_3918_, sizeof(void*)*4, v___y_3916_);
lean_inc_ref(v_b_3875_);
v___x_3919_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___lam__0(v_upperBound_3899_, v_b_3875_, v___x_3886_, v___x_3894_, v___x_3888_, v___x_3918_);
lean_dec(v_upperBound_3899_);
v___y_3891_ = v___x_3919_;
goto v___jp_3890_;
}
}
}
}
}
}
}
else
{
lean_object* v_var_3928_; lean_object* v_irrelevant_3929_; lean_object* v_lowerBounds_3930_; lean_object* v_upperBounds_3931_; uint8_t v_lowerExact_3932_; uint8_t v_upperExact_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3941_; 
lean_dec(v___x_3886_);
v_var_3928_ = lean_ctor_get(v_v_3887_, 0);
v_irrelevant_3929_ = lean_ctor_get(v_v_3887_, 1);
v_lowerBounds_3930_ = lean_ctor_get(v_v_3887_, 2);
v_upperBounds_3931_ = lean_ctor_get(v_v_3887_, 3);
v_lowerExact_3932_ = lean_ctor_get_uint8(v_v_3887_, sizeof(void*)*4);
v_upperExact_3933_ = lean_ctor_get_uint8(v_v_3887_, sizeof(void*)*4 + 1);
v_isSharedCheck_3941_ = !lean_is_exclusive(v_v_3887_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3935_ = v_v_3887_;
v_isShared_3936_ = v_isSharedCheck_3941_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_upperBounds_3931_);
lean_inc(v_lowerBounds_3930_);
lean_inc(v_irrelevant_3929_);
lean_inc(v_var_3928_);
lean_dec(v_v_3887_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3941_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3937_; lean_object* v___x_3939_; 
lean_inc_ref(v_b_3875_);
v___x_3937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3937_, 0, v_b_3875_);
lean_ctor_set(v___x_3937_, 1, v_irrelevant_3929_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 1, v___x_3937_);
v___x_3939_ = v___x_3935_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_var_3928_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3940_, 2, v_lowerBounds_3930_);
lean_ctor_set(v_reuseFailAlloc_3940_, 3, v_upperBounds_3931_);
lean_ctor_set_uint8(v_reuseFailAlloc_3940_, sizeof(void*)*4, v_lowerExact_3932_);
lean_ctor_set_uint8(v_reuseFailAlloc_3940_, sizeof(void*)*4 + 1, v_upperExact_3933_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
v___y_3891_ = v___x_3939_;
goto v___jp_3890_;
}
}
}
v___jp_3890_:
{
lean_object* v___x_3892_; 
v___x_3892_ = lean_array_fset(v_xs_x27_3889_, v_a_3876_, v___y_3891_);
v_a_3879_ = v___x_3892_;
goto v___jp_3878_;
}
}
}
v___jp_3878_:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = lean_unsigned_to_nat(1u);
v___x_3881_ = lean_nat_add(v_a_3876_, v___x_3880_);
lean_dec(v_a_3876_);
v_a_3876_ = v___x_3881_;
v_b_3877_ = v_a_3879_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg___boxed(lean_object* v_upperBound_3942_, lean_object* v_coeffs_3943_, lean_object* v_constraint_3944_, lean_object* v_b_3945_, lean_object* v_a_3946_, lean_object* v_b_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3942_, v_coeffs_3943_, v_constraint_3944_, v_b_3945_, v_a_3946_, v_b_3947_);
lean_dec(v_coeffs_3943_);
lean_dec(v_upperBound_3942_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(lean_object* v_n_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
if (lean_obj_tag(v_a_3950_) == 0)
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3952_, 0, v_a_3951_);
return v___x_3952_;
}
else
{
lean_object* v_value_3953_; lean_object* v_tail_3954_; lean_object* v_coeffs_3955_; lean_object* v_constraint_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v_value_3953_ = lean_ctor_get(v_a_3950_, 1);
lean_inc(v_value_3953_);
v_tail_3954_ = lean_ctor_get(v_a_3950_, 2);
lean_inc(v_tail_3954_);
lean_dec_ref_known(v_a_3950_, 3);
v_coeffs_3955_ = lean_ctor_get(v_value_3953_, 0);
lean_inc(v_coeffs_3955_);
v_constraint_3956_ = lean_ctor_get(v_value_3953_, 1);
lean_inc_ref(v_constraint_3956_);
v___x_3957_ = lean_unsigned_to_nat(0u);
v___x_3958_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_n_3949_, v_coeffs_3955_, v_constraint_3956_, v_value_3953_, v___x_3957_, v_a_3951_);
lean_dec(v_coeffs_3955_);
v_a_3950_ = v_tail_3954_;
v_a_3951_ = v___x_3958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1___boxed(lean_object* v_n_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3960_, v_a_3961_, v_a_3962_);
lean_dec(v_n_3960_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(lean_object* v_n_3964_, lean_object* v_as_3965_, size_t v_sz_3966_, size_t v_i_3967_, lean_object* v_b_3968_){
_start:
{
uint8_t v___x_3969_; 
v___x_3969_ = lean_usize_dec_lt(v_i_3967_, v_sz_3966_);
if (v___x_3969_ == 0)
{
return v_b_3968_;
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3971_; 
v_a_3970_ = lean_array_uget_borrowed(v_as_3965_, v_i_3967_);
lean_inc(v_a_3970_);
v___x_3971_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__1(v_n_3964_, v_a_3970_, v_b_3968_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_a_3972_);
lean_dec_ref_known(v___x_3971_, 1);
return v_a_3972_;
}
else
{
lean_object* v_a_3973_; size_t v___x_3974_; size_t v___x_3975_; 
v_a_3973_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_a_3973_);
lean_dec_ref_known(v___x_3971_, 1);
v___x_3974_ = ((size_t)1ULL);
v___x_3975_ = lean_usize_add(v_i_3967_, v___x_3974_);
v_i_3967_ = v___x_3975_;
v_b_3968_ = v_a_3973_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3___boxed(lean_object* v_n_3977_, lean_object* v_as_3978_, lean_object* v_sz_3979_, lean_object* v_i_3980_, lean_object* v_b_3981_){
_start:
{
size_t v_sz_boxed_3982_; size_t v_i_boxed_3983_; lean_object* v_res_3984_; 
v_sz_boxed_3982_ = lean_unbox_usize(v_sz_3979_);
lean_dec(v_sz_3979_);
v_i_boxed_3983_ = lean_unbox_usize(v_i_3980_);
lean_dec(v_i_3980_);
v_res_3984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_n_3977_, v_as_3978_, v_sz_boxed_3982_, v_i_boxed_3983_, v_b_3981_);
lean_dec_ref(v_as_3978_);
lean_dec(v_n_3977_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(lean_object* v_p_3987_){
_start:
{
lean_object* v_constraints_3988_; lean_object* v_numVars_3989_; lean_object* v_buckets_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v_data_3993_; size_t v_sz_3994_; size_t v___x_3995_; lean_object* v___x_3996_; 
v_constraints_3988_ = lean_ctor_get(v_p_3987_, 2);
lean_inc_ref(v_constraints_3988_);
v_numVars_3989_ = lean_ctor_get(v_p_3987_, 1);
lean_inc_n(v_numVars_3989_, 2);
lean_dec_ref(v_p_3987_);
v_buckets_3990_ = lean_ctor_get(v_constraints_3988_, 1);
lean_inc_ref(v_buckets_3990_);
lean_dec_ref(v_constraints_3988_);
v___x_3991_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_3992_ = l_List_range(v_numVars_3989_);
v_data_3993_ = l_List_foldl___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__2(v___x_3991_, v___x_3992_);
lean_dec(v___x_3992_);
v_sz_3994_ = lean_array_size(v_buckets_3990_);
v___x_3995_ = ((size_t)0ULL);
v___x_3996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__3(v_numVars_3989_, v_buckets_3990_, v_sz_3994_, v___x_3995_, v_data_3993_);
lean_dec_ref(v_buckets_3990_);
lean_dec(v_numVars_3989_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(lean_object* v_upperBound_3997_, lean_object* v_coeffs_3998_, lean_object* v_constraint_3999_, lean_object* v_b_4000_, lean_object* v_inst_4001_, lean_object* v_R_4002_, lean_object* v_a_4003_, lean_object* v_b_4004_, lean_object* v_c_4005_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___redArg(v_upperBound_3997_, v_coeffs_3998_, v_constraint_3999_, v_b_4000_, v_a_4003_, v_b_4004_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0___boxed(lean_object* v_upperBound_4007_, lean_object* v_coeffs_4008_, lean_object* v_constraint_4009_, lean_object* v_b_4010_, lean_object* v_inst_4011_, lean_object* v_R_4012_, lean_object* v_a_4013_, lean_object* v_b_4014_, lean_object* v_c_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData_spec__0(v_upperBound_4007_, v_coeffs_4008_, v_constraint_4009_, v_b_4010_, v_inst_4011_, v_R_4012_, v_a_4013_, v_b_4014_, v_c_4015_);
lean_dec(v_coeffs_4008_);
lean_dec(v_upperBound_4007_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(lean_object* v_cls_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v_toCold_4026_; lean_object* v_options_4027_; uint8_t v_hasTrace_4028_; 
v_toCold_4026_ = lean_ctor_get(v___y_4023_, 0);
v_options_4027_ = lean_ctor_get(v_toCold_4026_, 2);
v_hasTrace_4028_ = lean_ctor_get_uint8(v_options_4027_, sizeof(void*)*1);
if (v_hasTrace_4028_ == 0)
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
lean_dec(v_cls_4020_);
v___x_4029_ = lean_box(v_hasTrace_4028_);
v___x_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
return v___x_4030_;
}
else
{
lean_object* v_inheritedTraceOptions_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; uint8_t v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v_inheritedTraceOptions_4031_ = lean_ctor_get(v_toCold_4026_, 11);
v___x_4032_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4033_ = l_Lean_Name_append(v___x_4032_, v_cls_4020_);
v___x_4034_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4031_, v_options_4027_, v___x_4033_);
lean_dec(v___x_4033_);
v___x_4035_ = lean_box(v___x_4034_);
v___x_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
return v___x_4036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___boxed(lean_object* v_cls_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(lean_object* v___x_4044_, lean_object* v_fst_4045_, lean_object* v_snd_4046_, lean_object* v_fst_4047_, lean_object* v_____r_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4044_);
v___x_4055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4055_, 0, v_fst_4045_);
lean_ctor_set(v___x_4055_, 1, v_snd_4046_);
v___x_4056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4056_, 0, v_fst_4047_);
lean_ctor_set(v___x_4056_, 1, v___x_4055_);
v___x_4057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4054_);
lean_ctor_set(v___x_4057_, 1, v___x_4056_);
v___x_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
v___x_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0___boxed(lean_object* v___x_4060_, lean_object* v_fst_4061_, lean_object* v_snd_4062_, lean_object* v_fst_4063_, lean_object* v_____r_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4060_, v_fst_4061_, v_snd_4062_, v_fst_4063_, v_____r_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
return v_res_4070_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4071_; double v___x_4072_; 
v___x_4071_ = lean_unsigned_to_nat(0u);
v___x_4072_ = lean_float_of_nat(v___x_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(lean_object* v_cls_4075_, lean_object* v_msg_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_ref_4082_; lean_object* v___x_4083_; lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4129_; 
v_ref_4082_ = lean_ctor_get(v___y_4079_, 2);
v___x_4083_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4086_ = v___x_4083_;
v_isShared_4087_ = v_isSharedCheck_4129_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4083_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4129_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4088_; lean_object* v_traceState_4089_; lean_object* v_env_4090_; lean_object* v_nextMacroScope_4091_; lean_object* v_ngen_4092_; lean_object* v_auxDeclNGen_4093_; lean_object* v_cache_4094_; lean_object* v_recordedDeps_4095_; lean_object* v_messages_4096_; lean_object* v_infoState_4097_; lean_object* v_snapshotTasks_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4128_; 
v___x_4088_ = lean_st_ref_take(v___y_4080_);
v_traceState_4089_ = lean_ctor_get(v___x_4088_, 4);
v_env_4090_ = lean_ctor_get(v___x_4088_, 0);
v_nextMacroScope_4091_ = lean_ctor_get(v___x_4088_, 1);
v_ngen_4092_ = lean_ctor_get(v___x_4088_, 2);
v_auxDeclNGen_4093_ = lean_ctor_get(v___x_4088_, 3);
v_cache_4094_ = lean_ctor_get(v___x_4088_, 5);
v_recordedDeps_4095_ = lean_ctor_get(v___x_4088_, 6);
v_messages_4096_ = lean_ctor_get(v___x_4088_, 7);
v_infoState_4097_ = lean_ctor_get(v___x_4088_, 8);
v_snapshotTasks_4098_ = lean_ctor_get(v___x_4088_, 9);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4100_ = v___x_4088_;
v_isShared_4101_ = v_isSharedCheck_4128_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_snapshotTasks_4098_);
lean_inc(v_infoState_4097_);
lean_inc(v_messages_4096_);
lean_inc(v_recordedDeps_4095_);
lean_inc(v_cache_4094_);
lean_inc(v_traceState_4089_);
lean_inc(v_auxDeclNGen_4093_);
lean_inc(v_ngen_4092_);
lean_inc(v_nextMacroScope_4091_);
lean_inc(v_env_4090_);
lean_dec(v___x_4088_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4128_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
uint64_t v_tid_4102_; lean_object* v_traces_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4127_; 
v_tid_4102_ = lean_ctor_get_uint64(v_traceState_4089_, sizeof(void*)*1);
v_traces_4103_ = lean_ctor_get(v_traceState_4089_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_traceState_4089_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4105_ = v_traceState_4089_;
v_isShared_4106_ = v_isSharedCheck_4127_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_traces_4103_);
lean_dec(v_traceState_4089_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4127_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; double v___x_4109_; uint8_t v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4118_; 
v___x_4107_ = lean_box(0);
v___x_4108_ = lean_box(0);
v___x_4109_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4110_ = 0;
v___x_4111_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4112_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4112_, 0, v_cls_4075_);
lean_ctor_set(v___x_4112_, 1, v___x_4108_);
lean_ctor_set(v___x_4112_, 2, v___x_4111_);
lean_ctor_set_float(v___x_4112_, sizeof(void*)*3, v___x_4109_);
lean_ctor_set_float(v___x_4112_, sizeof(void*)*3 + 8, v___x_4109_);
lean_ctor_set_uint8(v___x_4112_, sizeof(void*)*3 + 16, v___x_4110_);
v___x_4113_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4114_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4112_);
lean_ctor_set(v___x_4114_, 1, v_a_4084_);
lean_ctor_set(v___x_4114_, 2, v___x_4113_);
lean_inc(v_ref_4082_);
v___x_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4115_, 0, v_ref_4082_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
v___x_4116_ = l_Lean_PersistentArray_push___redArg(v_traces_4103_, v___x_4115_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 0, v___x_4116_);
v___x_4118_ = v___x_4105_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4116_);
lean_ctor_set_uint64(v_reuseFailAlloc_4126_, sizeof(void*)*1, v_tid_4102_);
v___x_4118_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
lean_object* v___x_4120_; 
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 4, v___x_4118_);
v___x_4120_ = v___x_4100_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_env_4090_);
lean_ctor_set(v_reuseFailAlloc_4125_, 1, v_nextMacroScope_4091_);
lean_ctor_set(v_reuseFailAlloc_4125_, 2, v_ngen_4092_);
lean_ctor_set(v_reuseFailAlloc_4125_, 3, v_auxDeclNGen_4093_);
lean_ctor_set(v_reuseFailAlloc_4125_, 4, v___x_4118_);
lean_ctor_set(v_reuseFailAlloc_4125_, 5, v_cache_4094_);
lean_ctor_set(v_reuseFailAlloc_4125_, 6, v_recordedDeps_4095_);
lean_ctor_set(v_reuseFailAlloc_4125_, 7, v_messages_4096_);
lean_ctor_set(v_reuseFailAlloc_4125_, 8, v_infoState_4097_);
lean_ctor_set(v_reuseFailAlloc_4125_, 9, v_snapshotTasks_4098_);
v___x_4120_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
lean_object* v___x_4121_; lean_object* v___x_4123_; 
v___x_4121_ = lean_st_ref_put(v___y_4080_, v___x_4120_);
if (v_isShared_4087_ == 0)
{
lean_ctor_set(v___x_4086_, 0, v___x_4107_);
v___x_4123_ = v___x_4086_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v___x_4107_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___boxed(lean_object* v_cls_4130_, lean_object* v_msg_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4130_, v_msg_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
return v_res_4137_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v_cls_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v_cls_4138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4139_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0___closed__1));
v___x_4140_ = l_Lean_Name_append(v___x_4139_, v_cls_4138_);
return v___x_4140_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4142_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__1));
v___x_4143_ = l_Lean_stringToMessageData(v___x_4142_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(lean_object* v_upperBound_4144_, lean_object* v___y_4145_, lean_object* v_a_4146_, lean_object* v_b_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_a_4154_; lean_object* v___y_4159_; uint8_t v___x_4178_; 
v___x_4178_ = lean_nat_dec_lt(v_a_4146_, v_upperBound_4144_);
if (v___x_4178_ == 0)
{
lean_object* v___x_4179_; 
lean_dec(v_a_4146_);
v___x_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4179_, 0, v_b_4147_);
return v___x_4179_;
}
else
{
lean_object* v_snd_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4250_; 
v_snd_4180_ = lean_ctor_get(v_b_4147_, 1);
v_isSharedCheck_4250_ = !lean_is_exclusive(v_b_4147_);
if (v_isSharedCheck_4250_ == 0)
{
lean_object* v_unused_4251_; 
v_unused_4251_ = lean_ctor_get(v_b_4147_, 0);
lean_dec(v_unused_4251_);
v___x_4182_ = v_b_4147_;
v_isShared_4183_ = v_isSharedCheck_4250_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_snd_4180_);
lean_dec(v_b_4147_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4250_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v_snd_4184_; lean_object* v_fst_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4249_; 
v_snd_4184_ = lean_ctor_get(v_snd_4180_, 1);
v_fst_4185_ = lean_ctor_get(v_snd_4180_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v_snd_4180_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4187_ = v_snd_4180_;
v_isShared_4188_ = v_isSharedCheck_4249_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_snd_4184_);
lean_inc(v_fst_4185_);
lean_dec(v_snd_4180_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4249_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v_fst_4189_; lean_object* v_snd_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4248_; 
v_fst_4189_ = lean_ctor_get(v_snd_4184_, 0);
v_snd_4190_ = lean_ctor_get(v_snd_4184_, 1);
v_isSharedCheck_4248_ = !lean_is_exclusive(v_snd_4184_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4192_ = v_snd_4184_;
v_isShared_4193_ = v_isSharedCheck_4248_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_snd_4190_);
lean_inc(v_fst_4189_);
lean_dec(v_snd_4184_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4248_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4194_; lean_object* v_bestIdx_4205_; lean_object* v_cls_4206_; lean_object* v___x_4207_; uint8_t v___x_4211_; lean_object* v___x_4212_; uint8_t v___x_4213_; 
v___x_4194_ = lean_box(0);
v_bestIdx_4205_ = lean_unsigned_to_nat(0u);
v_cls_4206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___x_4207_ = lean_array_fget_borrowed(v___y_4145_, v_a_4146_);
v___x_4211_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4207_);
v___x_4212_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4207_);
v___x_4213_ = lean_nat_dec_eq(v___x_4212_, v_bestIdx_4205_);
if (v___x_4213_ == 0)
{
uint8_t v___x_4247_; 
v___x_4247_ = lean_unbox(v_snd_4190_);
if (v___x_4247_ == 0)
{
if (v___x_4211_ == 0)
{
goto v___jp_4244_;
}
else
{
lean_del_object(v___x_4192_);
lean_del_object(v___x_4187_);
lean_del_object(v___x_4182_);
goto v___jp_4214_;
}
}
else
{
goto v___jp_4244_;
}
}
else
{
lean_del_object(v___x_4192_);
lean_del_object(v___x_4187_);
lean_del_object(v___x_4182_);
goto v___jp_4214_;
}
v___jp_4195_:
{
lean_object* v___x_4197_; 
if (v_isShared_4193_ == 0)
{
v___x_4197_ = v___x_4192_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_fst_4189_);
lean_ctor_set(v_reuseFailAlloc_4204_, 1, v_snd_4190_);
v___x_4197_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4199_; 
if (v_isShared_4188_ == 0)
{
lean_ctor_set(v___x_4187_, 1, v___x_4197_);
v___x_4199_ = v___x_4187_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_fst_4185_);
lean_ctor_set(v_reuseFailAlloc_4203_, 1, v___x_4197_);
v___x_4199_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
lean_object* v___x_4201_; 
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 1, v___x_4199_);
lean_ctor_set(v___x_4182_, 0, v___x_4194_);
v___x_4201_ = v___x_4182_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v___x_4194_);
lean_ctor_set(v_reuseFailAlloc_4202_, 1, v___x_4199_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
v_a_4154_ = v___x_4201_;
goto v___jp_4153_;
}
}
}
}
v___jp_4208_:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4209_ = lean_box(0);
lean_inc(v___x_4207_);
v___x_4210_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4207_, v_fst_4189_, v_snd_4190_, v_fst_4185_, v___x_4209_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
v___y_4159_ = v___x_4210_;
goto v___jp_4158_;
}
v___jp_4214_:
{
if (v___x_4213_ == 0)
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
lean_dec(v_snd_4190_);
lean_dec(v_fst_4189_);
lean_dec(v_fst_4185_);
v___x_4215_ = lean_box(v___x_4211_);
v___x_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4212_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
lean_inc(v_a_4146_);
v___x_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4217_, 0, v_a_4146_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
v___x_4218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4194_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
v_a_4154_ = v___x_4218_;
goto v___jp_4153_;
}
else
{
lean_object* v_toCold_4219_; lean_object* v_options_4220_; uint8_t v_hasTrace_4221_; 
lean_dec(v___x_4212_);
v_toCold_4219_ = lean_ctor_get(v___y_4150_, 0);
v_options_4220_ = lean_ctor_get(v_toCold_4219_, 2);
v_hasTrace_4221_ = lean_ctor_get_uint8(v_options_4220_, sizeof(void*)*1);
if (v_hasTrace_4221_ == 0)
{
goto v___jp_4208_;
}
else
{
lean_object* v_inheritedTraceOptions_4222_; lean_object* v___x_4223_; uint8_t v___x_4224_; 
v_inheritedTraceOptions_4222_ = lean_ctor_get(v_toCold_4219_, 11);
v___x_4223_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__0);
v___x_4224_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4222_, v_options_4220_, v___x_4223_);
if (v___x_4224_ == 0)
{
goto v___jp_4208_;
}
else
{
lean_object* v_var_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
v_var_4225_ = lean_ctor_get(v___x_4207_, 0);
v___x_4226_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4225_);
v___x_4227_ = l_Nat_reprFast(v_var_4225_);
v___x_4228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4227_);
v___x_4229_ = l_Lean_MessageData_ofFormat(v___x_4228_);
v___x_4230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4226_);
lean_ctor_set(v___x_4230_, 1, v___x_4229_);
v___x_4231_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4206_, v___x_4230_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4233_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4231_, 1);
lean_inc(v___x_4207_);
v___x_4233_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___lam__0(v___x_4207_, v_fst_4189_, v_snd_4190_, v_fst_4185_, v_a_4232_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
v___y_4159_ = v___x_4233_;
goto v___jp_4158_;
}
else
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
lean_dec(v_snd_4190_);
lean_dec(v_fst_4189_);
lean_dec(v_fst_4185_);
lean_dec(v_a_4146_);
v_a_4234_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4236_ = v___x_4231_;
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4231_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
}
}
}
v___jp_4242_:
{
uint8_t v___x_4243_; 
v___x_4243_ = lean_nat_dec_lt(v___x_4212_, v_fst_4189_);
if (v___x_4243_ == 0)
{
lean_dec(v___x_4212_);
goto v___jp_4195_;
}
else
{
lean_del_object(v___x_4192_);
lean_del_object(v___x_4187_);
lean_del_object(v___x_4182_);
goto v___jp_4214_;
}
}
v___jp_4244_:
{
if (v___x_4211_ == 0)
{
uint8_t v___x_4245_; 
v___x_4245_ = lean_unbox(v_snd_4190_);
if (v___x_4245_ == 0)
{
goto v___jp_4242_;
}
else
{
lean_dec(v___x_4212_);
goto v___jp_4195_;
}
}
else
{
uint8_t v___x_4246_; 
v___x_4246_ = lean_unbox(v_snd_4190_);
if (v___x_4246_ == 0)
{
lean_dec(v___x_4212_);
goto v___jp_4195_;
}
else
{
goto v___jp_4242_;
}
}
}
}
}
}
}
v___jp_4153_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4155_ = lean_unsigned_to_nat(1u);
v___x_4156_ = lean_nat_add(v_a_4146_, v___x_4155_);
lean_dec(v_a_4146_);
v_a_4146_ = v___x_4156_;
v_b_4147_ = v_a_4154_;
goto _start;
}
v___jp_4158_:
{
if (lean_obj_tag(v___y_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4169_; 
v_a_4160_ = lean_ctor_get(v___y_4159_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___y_4159_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4162_ = v___y_4159_;
v_isShared_4163_ = v_isSharedCheck_4169_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___y_4159_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4169_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
if (lean_obj_tag(v_a_4160_) == 0)
{
lean_object* v_a_4164_; lean_object* v___x_4166_; 
lean_dec(v_a_4146_);
v_a_4164_ = lean_ctor_get(v_a_4160_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v_a_4160_, 1);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 0, v_a_4164_);
v___x_4166_ = v___x_4162_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4164_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
else
{
lean_object* v_a_4168_; 
lean_del_object(v___x_4162_);
v_a_4168_ = lean_ctor_get(v_a_4160_, 0);
lean_inc(v_a_4168_);
lean_dec_ref_known(v_a_4160_, 1);
v_a_4154_ = v_a_4168_;
goto v___jp_4153_;
}
}
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
lean_dec(v_a_4146_);
v_a_4170_ = lean_ctor_get(v___y_4159_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___y_4159_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___y_4159_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___y_4159_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___boxed(lean_object* v_upperBound_4252_, lean_object* v___y_4253_, lean_object* v_a_4254_, lean_object* v_b_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4252_, v___y_4253_, v_a_4254_, v_b_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec_ref(v___y_4253_);
lean_dec(v_upperBound_4252_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(lean_object* v_as_4262_, size_t v_i_4263_, size_t v_stop_4264_, lean_object* v_b_4265_){
_start:
{
lean_object* v___y_4267_; uint8_t v___x_4271_; 
v___x_4271_ = lean_usize_dec_eq(v_i_4263_, v_stop_4264_);
if (v___x_4271_ == 0)
{
lean_object* v___x_4272_; uint8_t v___x_4273_; 
v___x_4272_ = lean_array_uget_borrowed(v_as_4262_, v_i_4263_);
v___x_4273_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_isEmpty(v___x_4272_);
if (v___x_4273_ == 0)
{
lean_object* v___x_4274_; 
lean_inc(v___x_4272_);
v___x_4274_ = lean_array_push(v_b_4265_, v___x_4272_);
v___y_4267_ = v___x_4274_;
goto v___jp_4266_;
}
else
{
v___y_4267_ = v_b_4265_;
goto v___jp_4266_;
}
}
else
{
return v_b_4265_;
}
v___jp_4266_:
{
size_t v___x_4268_; size_t v___x_4269_; 
v___x_4268_ = ((size_t)1ULL);
v___x_4269_ = lean_usize_add(v_i_4263_, v___x_4268_);
v_i_4263_ = v___x_4269_;
v_b_4265_ = v___y_4267_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4___boxed(lean_object* v_as_4275_, lean_object* v_i_4276_, lean_object* v_stop_4277_, lean_object* v_b_4278_){
_start:
{
size_t v_i_boxed_4279_; size_t v_stop_boxed_4280_; lean_object* v_res_4281_; 
v_i_boxed_4279_ = lean_unbox_usize(v_i_4276_);
lean_dec(v_i_4276_);
v_stop_boxed_4280_ = lean_unbox_usize(v_stop_4277_);
lean_dec(v_stop_4277_);
v_res_4281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_as_4275_, v_i_boxed_4279_, v_stop_boxed_4280_, v_b_4278_);
lean_dec_ref(v_as_4275_);
return v_res_4281_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2(void){
_start:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4285_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__1));
v___x_4286_ = l_Lean_MessageData_ofFormat(v___x_4285_);
return v___x_4286_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4287_ = lean_box(1);
v___x_4288_ = l_Lean_MessageData_ofFormat(v___x_4287_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(lean_object* v_a_4290_, lean_object* v_a_4291_){
_start:
{
if (lean_obj_tag(v_a_4290_) == 0)
{
lean_object* v___x_4292_; 
v___x_4292_ = l_List_reverse___redArg(v_a_4291_);
return v___x_4292_;
}
else
{
lean_object* v_head_4293_; lean_object* v_snd_4294_; lean_object* v_tail_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4342_; 
v_head_4293_ = lean_ctor_get(v_a_4290_, 0);
lean_inc(v_head_4293_);
v_snd_4294_ = lean_ctor_get(v_head_4293_, 1);
lean_inc(v_snd_4294_);
v_tail_4295_ = lean_ctor_get(v_a_4290_, 1);
v_isSharedCheck_4342_ = !lean_is_exclusive(v_a_4290_);
if (v_isSharedCheck_4342_ == 0)
{
lean_object* v_unused_4343_; 
v_unused_4343_ = lean_ctor_get(v_a_4290_, 0);
lean_dec(v_unused_4343_);
v___x_4297_ = v_a_4290_;
v_isShared_4298_ = v_isSharedCheck_4342_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_tail_4295_);
lean_dec(v_a_4290_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4342_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v_fst_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4340_; 
v_fst_4299_ = lean_ctor_get(v_head_4293_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v_head_4293_);
if (v_isSharedCheck_4340_ == 0)
{
lean_object* v_unused_4341_; 
v_unused_4341_ = lean_ctor_get(v_head_4293_, 1);
lean_dec(v_unused_4341_);
v___x_4301_ = v_head_4293_;
v_isShared_4302_ = v_isSharedCheck_4340_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_fst_4299_);
lean_dec(v_head_4293_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4340_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v_fst_4303_; lean_object* v_snd_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4339_; 
v_fst_4303_ = lean_ctor_get(v_snd_4294_, 0);
v_snd_4304_ = lean_ctor_get(v_snd_4294_, 1);
v_isSharedCheck_4339_ = !lean_is_exclusive(v_snd_4294_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4306_ = v_snd_4294_;
v_isShared_4307_ = v_isSharedCheck_4339_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_snd_4304_);
lean_inc(v_fst_4303_);
lean_dec(v_snd_4294_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4339_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4313_; 
v___x_4308_ = l_Nat_reprFast(v_fst_4299_);
v___x_4309_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
v___x_4310_ = l_Lean_MessageData_ofFormat(v___x_4309_);
v___x_4311_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__2);
if (v_isShared_4307_ == 0)
{
lean_ctor_set_tag(v___x_4306_, 7);
lean_ctor_set(v___x_4306_, 1, v___x_4311_);
lean_ctor_set(v___x_4306_, 0, v___x_4310_);
v___x_4313_ = v___x_4306_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4310_);
lean_ctor_set(v_reuseFailAlloc_4338_, 1, v___x_4311_);
v___x_4313_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
lean_object* v___x_4314_; lean_object* v___x_4316_; 
v___x_4314_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__3);
if (v_isShared_4302_ == 0)
{
lean_ctor_set_tag(v___x_4301_, 7);
lean_ctor_set(v___x_4301_, 1, v___x_4314_);
lean_ctor_set(v___x_4301_, 0, v___x_4313_);
v___x_4316_ = v___x_4301_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4313_);
lean_ctor_set(v_reuseFailAlloc_4337_, 1, v___x_4314_);
v___x_4316_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___y_4323_; uint8_t v___x_4334_; 
v___x_4317_ = l_Nat_reprFast(v_fst_4303_);
v___x_4318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4317_);
v___x_4319_ = l_Lean_MessageData_ofFormat(v___x_4318_);
v___x_4320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
lean_ctor_set(v___x_4320_, 1, v___x_4311_);
v___x_4321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4320_);
lean_ctor_set(v___x_4321_, 1, v___x_4314_);
v___x_4334_ = lean_unbox(v_snd_4304_);
lean_dec(v_snd_4304_);
if (v___x_4334_ == 0)
{
lean_object* v___x_4335_; 
v___x_4335_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3___closed__4));
v___y_4323_ = v___x_4335_;
goto v___jp_4322_;
}
else
{
lean_object* v___x_4336_; 
v___x_4336_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_proveFalse___closed__4));
v___y_4323_ = v___x_4336_;
goto v___jp_4322_;
}
v___jp_4322_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4331_; 
lean_inc_ref(v___y_4323_);
v___x_4324_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4324_, 0, v___y_4323_);
v___x_4325_ = l_Lean_MessageData_ofFormat(v___x_4324_);
v___x_4326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4326_, 0, v___x_4321_);
lean_ctor_set(v___x_4326_, 1, v___x_4325_);
v___x_4327_ = l_Lean_MessageData_paren(v___x_4326_);
v___x_4328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4328_, 0, v___x_4316_);
lean_ctor_set(v___x_4328_, 1, v___x_4327_);
v___x_4329_ = l_Lean_MessageData_paren(v___x_4328_);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 1, v_a_4291_);
lean_ctor_set(v___x_4297_, 0, v___x_4329_);
v___x_4331_ = v___x_4297_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4329_);
lean_ctor_set(v_reuseFailAlloc_4333_, 1, v_a_4291_);
v___x_4331_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
v_a_4290_ = v_tail_4295_;
v_a_4291_ = v___x_4331_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(size_t v_sz_4344_, size_t v_i_4345_, lean_object* v_bs_4346_){
_start:
{
uint8_t v___x_4347_; 
v___x_4347_ = lean_usize_dec_lt(v_i_4345_, v_sz_4344_);
if (v___x_4347_ == 0)
{
return v_bs_4346_;
}
else
{
lean_object* v_v_4348_; lean_object* v_var_4349_; lean_object* v___x_4350_; lean_object* v_bs_x27_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; size_t v___x_4357_; size_t v___x_4358_; lean_object* v___x_4359_; 
v_v_4348_ = lean_array_uget(v_bs_4346_, v_i_4345_);
v_var_4349_ = lean_ctor_get(v_v_4348_, 0);
lean_inc(v_var_4349_);
v___x_4350_ = lean_unsigned_to_nat(0u);
v_bs_x27_4351_ = lean_array_uset(v_bs_4346_, v_i_4345_, v___x_4350_);
v___x_4352_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v_v_4348_);
v___x_4353_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v_v_4348_);
lean_dec(v_v_4348_);
v___x_4354_ = lean_box(v___x_4353_);
v___x_4355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4352_);
lean_ctor_set(v___x_4355_, 1, v___x_4354_);
v___x_4356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4356_, 0, v_var_4349_);
lean_ctor_set(v___x_4356_, 1, v___x_4355_);
v___x_4357_ = ((size_t)1ULL);
v___x_4358_ = lean_usize_add(v_i_4345_, v___x_4357_);
v___x_4359_ = lean_array_uset(v_bs_x27_4351_, v_i_4345_, v___x_4356_);
v_i_4345_ = v___x_4358_;
v_bs_4346_ = v___x_4359_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2___boxed(lean_object* v_sz_4361_, lean_object* v_i_4362_, lean_object* v_bs_4363_){
_start:
{
size_t v_sz_boxed_4364_; size_t v_i_boxed_4365_; lean_object* v_res_4366_; 
v_sz_boxed_4364_ = lean_unbox_usize(v_sz_4361_);
lean_dec(v_sz_4361_);
v_i_boxed_4365_ = lean_unbox_usize(v_i_4362_);
lean_dec(v_i_4362_);
v_res_4366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_boxed_4364_, v_i_boxed_4365_, v_bs_4363_);
return v_res_4366_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1(void){
_start:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4368_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__0));
v___x_4369_ = l_Lean_stringToMessageData(v___x_4368_);
return v___x_4369_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4(void){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__3));
v___x_4374_ = l_Lean_stringToMessageData(v___x_4373_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(lean_object* v_data_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_){
_start:
{
lean_object* v___x_4381_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v_bestIdx_4387_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4515_; lean_object* v___x_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; 
v___x_4381_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_instInhabitedFourierMotzkinData_default));
v_bestIdx_4387_ = lean_unsigned_to_nat(0u);
v___x_4539_ = lean_array_get_size(v_data_4375_);
v___x_4540_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData___closed__0));
v___x_4541_ = lean_nat_dec_lt(v_bestIdx_4387_, v___x_4539_);
if (v___x_4541_ == 0)
{
v___y_4515_ = v___x_4540_;
goto v___jp_4514_;
}
else
{
size_t v___x_4542_; size_t v___x_4543_; lean_object* v___x_4544_; 
v___x_4542_ = ((size_t)0ULL);
v___x_4543_ = lean_usize_of_nat(v___x_4539_);
v___x_4544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__4(v_data_4375_, v___x_4542_, v___x_4543_, v___x_4540_);
v___y_4515_ = v___x_4544_;
goto v___jp_4514_;
}
v___jp_4382_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = lean_array_get(v___x_4381_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
v___x_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
return v___x_4386_;
}
v___jp_4388_:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; uint8_t v___x_4398_; 
v___x_4396_ = lean_array_get_borrowed(v___x_4381_, v___y_4389_, v_bestIdx_4387_);
v___x_4397_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_size(v___x_4396_);
v___x_4398_ = lean_nat_dec_eq(v___x_4397_, v_bestIdx_4387_);
if (v___x_4398_ == 0)
{
lean_object* v___x_4399_; lean_object* v___x_4400_; uint8_t v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4399_ = lean_unsigned_to_nat(1u);
v___x_4400_ = lean_array_get_size(v___y_4389_);
v___x_4401_ = l_Lean_Elab_Tactic_Omega_Problem_FourierMotzkinData_exact(v___x_4396_);
v___x_4402_ = lean_box(0);
v___x_4403_ = lean_box(v___x_4401_);
v___x_4404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4397_);
lean_ctor_set(v___x_4404_, 1, v___x_4403_);
v___x_4405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4405_, 0, v_bestIdx_4387_);
lean_ctor_set(v___x_4405_, 1, v___x_4404_);
v___x_4406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4402_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
v___x_4407_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v___x_4400_, v___y_4389_, v___x_4399_, v___x_4406_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4462_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4410_ = v___x_4407_;
v_isShared_4411_ = v_isSharedCheck_4462_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4407_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4462_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v_fst_4412_; 
v_fst_4412_ = lean_ctor_get(v_a_4408_, 0);
if (lean_obj_tag(v_fst_4412_) == 0)
{
lean_object* v_snd_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4456_; 
lean_del_object(v___x_4410_);
v_snd_4413_ = lean_ctor_get(v_a_4408_, 1);
v_isSharedCheck_4456_ = !lean_is_exclusive(v_a_4408_);
if (v_isSharedCheck_4456_ == 0)
{
lean_object* v_unused_4457_; 
v_unused_4457_ = lean_ctor_get(v_a_4408_, 0);
lean_dec(v_unused_4457_);
v___x_4415_ = v_a_4408_;
v_isShared_4416_ = v_isSharedCheck_4456_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_snd_4413_);
lean_dec(v_a_4408_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4456_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v_fst_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4454_; 
v_fst_4417_ = lean_ctor_get(v_snd_4413_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v_snd_4413_);
if (v_isSharedCheck_4454_ == 0)
{
lean_object* v_unused_4455_; 
v_unused_4455_ = lean_ctor_get(v_snd_4413_, 1);
lean_dec(v_unused_4455_);
v___x_4419_ = v_snd_4413_;
v_isShared_4420_ = v_isSharedCheck_4454_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_fst_4417_);
lean_dec(v_snd_4413_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4454_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4421_; 
lean_inc_ref(v___y_4391_);
lean_inc(v___y_4395_);
lean_inc_ref(v___y_4394_);
lean_inc(v___y_4393_);
lean_inc_ref(v___y_4392_);
v___x_4421_ = lean_apply_5(v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, lean_box(0));
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; uint8_t v___x_4423_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_a_4422_);
lean_dec_ref_known(v___x_4421_, 1);
v___x_4423_ = lean_unbox(v_a_4422_);
lean_dec(v_a_4422_);
if (v___x_4423_ == 0)
{
lean_del_object(v___x_4419_);
lean_del_object(v___x_4415_);
lean_dec(v___y_4390_);
v___y_4383_ = v___y_4389_;
v___y_4384_ = v_fst_4417_;
goto v___jp_4382_;
}
else
{
lean_object* v___x_4424_; lean_object* v_var_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4431_; 
v___x_4424_ = lean_array_get_borrowed(v___x_4381_, v___y_4389_, v_fst_4417_);
v_var_4425_ = lean_ctor_get(v___x_4424_, 0);
v___x_4426_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4425_);
v___x_4427_ = l_Nat_reprFast(v_var_4425_);
v___x_4428_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4427_);
v___x_4429_ = l_Lean_MessageData_ofFormat(v___x_4428_);
if (v_isShared_4420_ == 0)
{
lean_ctor_set_tag(v___x_4419_, 7);
lean_ctor_set(v___x_4419_, 1, v___x_4429_);
lean_ctor_set(v___x_4419_, 0, v___x_4426_);
v___x_4431_ = v___x_4419_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v___x_4426_);
lean_ctor_set(v_reuseFailAlloc_4445_, 1, v___x_4429_);
v___x_4431_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4432_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
if (v_isShared_4416_ == 0)
{
lean_ctor_set_tag(v___x_4415_, 7);
lean_ctor_set(v___x_4415_, 1, v___x_4432_);
lean_ctor_set(v___x_4415_, 0, v___x_4431_);
v___x_4434_ = v___x_4415_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4431_);
lean_ctor_set(v_reuseFailAlloc_4444_, 1, v___x_4432_);
v___x_4434_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4390_, v___x_4434_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_dec_ref_known(v___x_4435_, 1);
v___y_4383_ = v___y_4389_;
v___y_4384_ = v_fst_4417_;
goto v___jp_4382_;
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec(v_fst_4417_);
lean_dec_ref(v___y_4389_);
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4435_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4435_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_del_object(v___x_4419_);
lean_dec(v_fst_4417_);
lean_del_object(v___x_4415_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
v_a_4446_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4421_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4421_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
}
}
}
else
{
lean_object* v_val_4458_; lean_object* v___x_4460_; 
lean_inc_ref(v_fst_4412_);
lean_dec(v_a_4408_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
v_val_4458_ = lean_ctor_get(v_fst_4412_, 0);
lean_inc(v_val_4458_);
lean_dec_ref_known(v_fst_4412_, 1);
if (v_isShared_4411_ == 0)
{
lean_ctor_set(v___x_4410_, 0, v_val_4458_);
v___x_4460_ = v___x_4410_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_val_4458_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
v_a_4463_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4407_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4407_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
else
{
lean_object* v___x_4471_; 
lean_inc(v___x_4396_);
lean_dec(v___x_4397_);
lean_dec_ref(v___y_4389_);
lean_inc_ref(v___y_4391_);
lean_inc(v___y_4395_);
lean_inc_ref(v___y_4394_);
lean_inc(v___y_4393_);
lean_inc_ref(v___y_4392_);
v___x_4471_ = lean_apply_5(v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, lean_box(0));
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v_a_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4505_; 
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4474_ = v___x_4471_;
v_isShared_4475_ = v_isSharedCheck_4505_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_a_4472_);
lean_dec(v___x_4471_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4505_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
uint8_t v___x_4476_; 
v___x_4476_ = lean_unbox(v_a_4472_);
lean_dec(v_a_4472_);
if (v___x_4476_ == 0)
{
lean_object* v___x_4478_; 
lean_dec(v___y_4390_);
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 0, v___x_4396_);
v___x_4478_ = v___x_4474_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4396_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
else
{
lean_object* v_var_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
lean_del_object(v___x_4474_);
v_var_4480_ = lean_ctor_get(v___x_4396_, 0);
v___x_4481_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg___closed__2);
lean_inc(v_var_4480_);
v___x_4482_ = l_Nat_reprFast(v_var_4480_);
v___x_4483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4482_);
v___x_4484_ = l_Lean_MessageData_ofFormat(v___x_4483_);
v___x_4485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4481_);
lean_ctor_set(v___x_4485_, 1, v___x_4484_);
v___x_4486_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__1);
v___x_4487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4485_);
lean_ctor_set(v___x_4487_, 1, v___x_4486_);
v___x_4488_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v___y_4390_, v___x_4487_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4495_ == 0)
{
lean_object* v_unused_4496_; 
v_unused_4496_ = lean_ctor_get(v___x_4488_, 0);
lean_dec(v_unused_4496_);
v___x_4490_ = v___x_4488_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_dec(v___x_4488_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 0, v___x_4396_);
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4396_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
else
{
lean_object* v_a_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4504_; 
lean_dec(v___x_4396_);
v_a_4497_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4499_ = v___x_4488_;
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_a_4497_);
lean_dec(v___x_4488_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4502_; 
if (v_isShared_4500_ == 0)
{
v___x_4502_ = v___x_4499_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4497_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec(v___x_4396_);
lean_dec(v___y_4390_);
v_a_4506_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4471_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4471_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
}
v___jp_4514_:
{
lean_object* v_cls_4516_; lean_object* v___f_4517_; lean_object* v___x_4518_; lean_object* v_a_4519_; uint8_t v___x_4520_; 
v_cls_4516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_initFn___closed__1_00___x40_Lean_Elab_Tactic_Omega_Core_3193685152____hygCtx___hyg_2_));
v___f_4517_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__2));
v___x_4518_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___lam__0(v_cls_4516_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_);
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
lean_inc(v_a_4519_);
lean_dec_ref(v___x_4518_);
v___x_4520_ = lean_unbox(v_a_4519_);
lean_dec(v_a_4519_);
if (v___x_4520_ == 0)
{
v___y_4389_ = v___y_4515_;
v___y_4390_ = v_cls_4516_;
v___y_4391_ = v___f_4517_;
v___y_4392_ = v_a_4376_;
v___y_4393_ = v_a_4377_;
v___y_4394_ = v_a_4378_;
v___y_4395_ = v_a_4379_;
goto v___jp_4388_;
}
else
{
lean_object* v___x_4521_; size_t v_sz_4522_; size_t v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4521_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4, &l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4_once, _init_l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___closed__4);
v_sz_4522_ = lean_array_size(v___y_4515_);
v___x_4523_ = ((size_t)0ULL);
lean_inc_ref(v___y_4515_);
v___x_4524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__2(v_sz_4522_, v___x_4523_, v___y_4515_);
v___x_4525_ = lean_array_to_list(v___x_4524_);
v___x_4526_ = lean_box(0);
v___x_4527_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__3(v___x_4525_, v___x_4526_);
v___x_4528_ = l_Lean_MessageData_ofList(v___x_4527_);
v___x_4529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4529_, 0, v___x_4521_);
lean_ctor_set(v___x_4529_, 1, v___x_4528_);
v___x_4530_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0(v_cls_4516_, v___x_4529_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_dec_ref_known(v___x_4530_, 1);
v___y_4389_ = v___y_4515_;
v___y_4390_ = v_cls_4516_;
v___y_4391_ = v___f_4517_;
v___y_4392_ = v_a_4376_;
v___y_4393_ = v_a_4377_;
v___y_4394_ = v_a_4378_;
v___y_4395_ = v_a_4379_;
goto v___jp_4388_;
}
else
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4538_; 
lean_dec_ref(v___y_4515_);
v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4533_ = v___x_4530_;
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4530_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4536_; 
if (v_isShared_4534_ == 0)
{
v___x_4536_ = v___x_4533_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect___boxed(lean_object* v_data_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_);
lean_dec(v_a_4549_);
lean_dec_ref(v_a_4548_);
lean_dec(v_a_4547_);
lean_dec_ref(v_a_4546_);
lean_dec_ref(v_data_4545_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(lean_object* v_upperBound_4552_, lean_object* v___y_4553_, lean_object* v_inst_4554_, lean_object* v_R_4555_, lean_object* v_a_4556_, lean_object* v_b_4557_, lean_object* v_c_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___redArg(v_upperBound_4552_, v___y_4553_, v_a_4556_, v_b_4557_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1___boxed(lean_object* v_upperBound_4565_, lean_object* v___y_4566_, lean_object* v_inst_4567_, lean_object* v_R_4568_, lean_object* v_a_4569_, lean_object* v_b_4570_, lean_object* v_c_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__1(v_upperBound_4565_, v___y_4566_, v_inst_4567_, v_R_4568_, v_a_4569_, v_b_4570_, v_c_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec_ref(v___y_4566_);
lean_dec(v_upperBound_4565_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(lean_object* v_snd_4578_, lean_object* v_fst_4579_, lean_object* v_as_x27_4580_, lean_object* v_b_4581_){
_start:
{
if (lean_obj_tag(v_as_x27_4580_) == 0)
{
lean_object* v___x_4583_; 
lean_dec_ref(v_fst_4579_);
v___x_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4583_, 0, v_b_4581_);
return v___x_4583_;
}
else
{
lean_object* v_head_4584_; lean_object* v_tail_4585_; lean_object* v_fst_4586_; lean_object* v_snd_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v_head_4584_ = lean_ctor_get(v_as_x27_4580_, 0);
v_tail_4585_ = lean_ctor_get(v_as_x27_4580_, 1);
v_fst_4586_ = lean_ctor_get(v_head_4584_, 0);
v_snd_4587_ = lean_ctor_get(v_head_4584_, 1);
v___x_4588_ = lean_int_neg(v_snd_4578_);
lean_inc(v_fst_4586_);
lean_inc_ref(v_fst_4579_);
lean_inc(v_snd_4587_);
v___x_4589_ = l_Lean_Elab_Tactic_Omega_Fact_combo(v_snd_4587_, v_fst_4579_, v___x_4588_, v_fst_4586_);
v___x_4590_ = l_Lean_Elab_Tactic_Omega_Fact_tidy(v___x_4589_);
v___x_4591_ = l_Lean_Elab_Tactic_Omega_Problem_addConstraint(v_b_4581_, v___x_4590_);
v_as_x27_4580_ = v_tail_4585_;
v_b_4581_ = v___x_4591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg___boxed(lean_object* v_snd_4593_, lean_object* v_fst_4594_, lean_object* v_as_x27_4595_, lean_object* v_b_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4593_, v_fst_4594_, v_as_x27_4595_, v_b_4596_);
lean_dec(v_as_x27_4595_);
lean_dec(v_snd_4593_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(lean_object* v_upperBounds_4599_, lean_object* v_as_x27_4600_, lean_object* v_b_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_){
_start:
{
if (lean_obj_tag(v_as_x27_4600_) == 0)
{
lean_object* v___x_4607_; 
v___x_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4607_, 0, v_b_4601_);
return v___x_4607_;
}
else
{
lean_object* v_head_4608_; lean_object* v_tail_4609_; lean_object* v_fst_4610_; lean_object* v_snd_4611_; lean_object* v___x_4612_; lean_object* v_a_4613_; 
v_head_4608_ = lean_ctor_get(v_as_x27_4600_, 0);
v_tail_4609_ = lean_ctor_get(v_as_x27_4600_, 1);
v_fst_4610_ = lean_ctor_get(v_head_4608_, 0);
v_snd_4611_ = lean_ctor_get(v_head_4608_, 1);
lean_inc(v_fst_4610_);
v___x_4612_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4611_, v_fst_4610_, v_upperBounds_4599_, v_b_4601_);
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
lean_inc(v_a_4613_);
lean_dec_ref(v___x_4612_);
v_as_x27_4600_ = v_tail_4609_;
v_b_4601_ = v_a_4613_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg___boxed(lean_object* v_upperBounds_4615_, lean_object* v_as_x27_4616_, lean_object* v_b_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4615_, v_as_x27_4616_, v_b_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
lean_dec(v_as_x27_4616_);
lean_dec(v_upperBounds_4615_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(lean_object* v_as_x27_4624_, lean_object* v_b_4625_){
_start:
{
if (lean_obj_tag(v_as_x27_4624_) == 0)
{
lean_object* v___x_4627_; 
v___x_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4627_, 0, v_b_4625_);
return v___x_4627_;
}
else
{
lean_object* v_head_4628_; lean_object* v_tail_4629_; lean_object* v___x_4630_; 
v_head_4628_ = lean_ctor_get(v_as_x27_4624_, 0);
v_tail_4629_ = lean_ctor_get(v_as_x27_4624_, 1);
lean_inc(v_head_4628_);
v___x_4630_ = l_Lean_Elab_Tactic_Omega_Problem_insertConstraint(v_b_4625_, v_head_4628_);
v_as_x27_4624_ = v_tail_4629_;
v_b_4625_ = v___x_4630_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg___boxed(lean_object* v_as_x27_4632_, lean_object* v_b_4633_, lean_object* v___y_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4632_, v_b_4633_);
lean_dec(v_as_x27_4632_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(lean_object* v_p_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v_data_4642_; lean_object* v___x_4643_; 
lean_inc_ref(v_p_4636_);
v_data_4642_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinData(v_p_4636_);
v___x_4643_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect(v_data_4642_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
lean_dec_ref(v_data_4642_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_object* v_a_4644_; lean_object* v_irrelevant_4645_; lean_object* v_lowerBounds_4646_; lean_object* v_upperBounds_4647_; lean_object* v_assumptions_4648_; lean_object* v_eliminations_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4664_; 
v_a_4644_ = lean_ctor_get(v___x_4643_, 0);
lean_inc(v_a_4644_);
lean_dec_ref_known(v___x_4643_, 1);
v_irrelevant_4645_ = lean_ctor_get(v_a_4644_, 1);
lean_inc(v_irrelevant_4645_);
v_lowerBounds_4646_ = lean_ctor_get(v_a_4644_, 2);
lean_inc(v_lowerBounds_4646_);
v_upperBounds_4647_ = lean_ctor_get(v_a_4644_, 3);
lean_inc(v_upperBounds_4647_);
lean_dec(v_a_4644_);
v_assumptions_4648_ = lean_ctor_get(v_p_4636_, 0);
v_eliminations_4649_ = lean_ctor_get(v_p_4636_, 4);
v_isSharedCheck_4664_ = !lean_is_exclusive(v_p_4636_);
if (v_isSharedCheck_4664_ == 0)
{
lean_object* v_unused_4665_; lean_object* v_unused_4666_; lean_object* v_unused_4667_; lean_object* v_unused_4668_; lean_object* v_unused_4669_; 
v_unused_4665_ = lean_ctor_get(v_p_4636_, 6);
lean_dec(v_unused_4665_);
v_unused_4666_ = lean_ctor_get(v_p_4636_, 5);
lean_dec(v_unused_4666_);
v_unused_4667_ = lean_ctor_get(v_p_4636_, 3);
lean_dec(v_unused_4667_);
v_unused_4668_ = lean_ctor_get(v_p_4636_, 2);
lean_dec(v_unused_4668_);
v_unused_4669_ = lean_ctor_get(v_p_4636_, 1);
lean_dec(v_unused_4669_);
v___x_4651_ = v_p_4636_;
v_isShared_4652_ = v_isSharedCheck_4664_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_eliminations_4649_);
lean_inc(v_assumptions_4648_);
lean_dec(v_p_4636_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4664_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; uint8_t v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4659_; 
v___x_4653_ = lean_unsigned_to_nat(0u);
v___x_4654_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__2);
v___x_4655_ = 1;
v___x_4656_ = lean_box(0);
v___x_4657_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3, &l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3_once, _init_l_Lean_Elab_Tactic_Omega_Problem_solveEasyEquality___closed__3);
if (v_isShared_4652_ == 0)
{
lean_ctor_set(v___x_4651_, 6, v___x_4657_);
lean_ctor_set(v___x_4651_, 5, v___x_4656_);
lean_ctor_set(v___x_4651_, 3, v___x_4654_);
lean_ctor_set(v___x_4651_, 2, v___x_4654_);
lean_ctor_set(v___x_4651_, 1, v___x_4653_);
v___x_4659_ = v___x_4651_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_assumptions_4648_);
lean_ctor_set(v_reuseFailAlloc_4663_, 1, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4663_, 2, v___x_4654_);
lean_ctor_set(v_reuseFailAlloc_4663_, 3, v___x_4654_);
lean_ctor_set(v_reuseFailAlloc_4663_, 4, v_eliminations_4649_);
lean_ctor_set(v_reuseFailAlloc_4663_, 5, v___x_4656_);
lean_ctor_set(v_reuseFailAlloc_4663_, 6, v___x_4657_);
v___x_4659_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
lean_object* v___x_4660_; lean_object* v_a_4661_; lean_object* v___x_4662_; 
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*7, v___x_4655_);
v___x_4660_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_irrelevant_4645_, v___x_4659_);
lean_dec(v_irrelevant_4645_);
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4661_);
lean_dec_ref(v___x_4660_);
v___x_4662_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4647_, v_lowerBounds_4646_, v_a_4661_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
lean_dec(v_lowerBounds_4646_);
lean_dec(v_upperBounds_4647_);
return v___x_4662_;
}
}
}
else
{
lean_object* v_a_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4677_; 
lean_dec_ref(v_p_4636_);
v_a_4670_ = lean_ctor_get(v___x_4643_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4672_ = v___x_4643_;
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_a_4670_);
lean_dec(v___x_4643_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4675_; 
if (v_isShared_4673_ == 0)
{
v___x_4675_ = v___x_4672_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4670_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin___boxed(lean_object* v_p_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_){
_start:
{
lean_object* v_res_4684_; 
v_res_4684_ = l_Lean_Elab_Tactic_Omega_Problem_fourierMotzkin(v_p_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_);
lean_dec(v_a_4682_);
lean_dec_ref(v_a_4681_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4679_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(lean_object* v_snd_4685_, lean_object* v_fst_4686_, lean_object* v_as_4687_, lean_object* v_as_x27_4688_, lean_object* v_b_4689_, lean_object* v_a_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
lean_object* v___x_4696_; 
v___x_4696_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___redArg(v_snd_4685_, v_fst_4686_, v_as_x27_4688_, v_b_4689_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0___boxed(lean_object* v_snd_4697_, lean_object* v_fst_4698_, lean_object* v_as_4699_, lean_object* v_as_x27_4700_, lean_object* v_b_4701_, lean_object* v_a_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__0(v_snd_4697_, v_fst_4698_, v_as_4699_, v_as_x27_4700_, v_b_4701_, v_a_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
lean_dec(v___y_4706_);
lean_dec_ref(v___y_4705_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
lean_dec(v_as_x27_4700_);
lean_dec(v_as_4699_);
lean_dec(v_snd_4697_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(lean_object* v_as_4709_, lean_object* v_as_x27_4710_, lean_object* v_b_4711_, lean_object* v_a_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
lean_object* v___x_4718_; 
v___x_4718_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___redArg(v_as_x27_4710_, v_b_4711_);
return v___x_4718_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1___boxed(lean_object* v_as_4719_, lean_object* v_as_x27_4720_, lean_object* v_b_4721_, lean_object* v_a_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__1(v_as_4719_, v_as_x27_4720_, v_b_4721_, v_a_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v_as_x27_4720_);
lean_dec(v_as_4719_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(lean_object* v_upperBounds_4729_, lean_object* v_as_4730_, lean_object* v_as_x27_4731_, lean_object* v_b_4732_, lean_object* v_a_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
lean_object* v___x_4739_; 
v___x_4739_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___redArg(v_upperBounds_4729_, v_as_x27_4731_, v_b_4732_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2___boxed(lean_object* v_upperBounds_4740_, lean_object* v_as_4741_, lean_object* v_as_x27_4742_, lean_object* v_b_4743_, lean_object* v_a_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_){
_start:
{
lean_object* v_res_4750_; 
v_res_4750_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkin_spec__2(v_upperBounds_4740_, v_as_4741_, v_as_x27_4742_, v_b_4743_, v_a_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_);
lean_dec(v___y_4748_);
lean_dec_ref(v___y_4747_);
lean_dec(v___y_4746_);
lean_dec_ref(v___y_4745_);
lean_dec(v_as_x27_4742_);
lean_dec(v_as_4741_);
lean_dec(v_upperBounds_4740_);
return v_res_4750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(lean_object* v_x_4751_, lean_object* v_x_4752_){
_start:
{
if (lean_obj_tag(v_x_4752_) == 0)
{
lean_inc(v_x_4751_);
return v_x_4751_;
}
else
{
lean_object* v_key_4753_; lean_object* v_value_4754_; lean_object* v_tail_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v_key_4753_ = lean_ctor_get(v_x_4752_, 0);
v_value_4754_ = lean_ctor_get(v_x_4752_, 1);
v_tail_4755_ = lean_ctor_get(v_x_4752_, 2);
v___x_4756_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4751_, v_tail_4755_);
lean_inc(v_value_4754_);
lean_inc(v_key_4753_);
v___x_4757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4757_, 0, v_key_4753_);
lean_ctor_set(v___x_4757_, 1, v_value_4754_);
v___x_4758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4757_);
lean_ctor_set(v___x_4758_, 1, v___x_4756_);
return v___x_4758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2___boxed(lean_object* v_x_4759_, lean_object* v_x_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_x_4759_, v_x_4760_);
lean_dec(v_x_4760_);
lean_dec(v_x_4759_);
return v_res_4761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(lean_object* v_as_4762_, size_t v_i_4763_, size_t v_stop_4764_, lean_object* v_b_4765_){
_start:
{
uint8_t v___x_4766_; 
v___x_4766_ = lean_usize_dec_eq(v_i_4763_, v_stop_4764_);
if (v___x_4766_ == 0)
{
size_t v___x_4767_; size_t v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; 
v___x_4767_ = ((size_t)1ULL);
v___x_4768_ = lean_usize_sub(v_i_4763_, v___x_4767_);
v___x_4769_ = lean_array_uget_borrowed(v_as_4762_, v___x_4768_);
v___x_4770_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__2(v_b_4765_, v___x_4769_);
lean_dec(v_b_4765_);
v_i_4763_ = v___x_4768_;
v_b_4765_ = v___x_4770_;
goto _start;
}
else
{
return v_b_4765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3___boxed(lean_object* v_as_4772_, lean_object* v_i_4773_, lean_object* v_stop_4774_, lean_object* v_b_4775_){
_start:
{
size_t v_i_boxed_4776_; size_t v_stop_boxed_4777_; lean_object* v_res_4778_; 
v_i_boxed_4776_ = lean_unbox_usize(v_i_4773_);
lean_dec(v_i_4773_);
v_stop_boxed_4777_ = lean_unbox_usize(v_stop_4774_);
lean_dec(v_stop_4774_);
v_res_4778_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_as_4772_, v_i_boxed_4776_, v_stop_boxed_4777_, v_b_4775_);
lean_dec_ref(v_as_4772_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(lean_object* v_a_4779_, lean_object* v_a_4780_){
_start:
{
if (lean_obj_tag(v_a_4779_) == 0)
{
lean_object* v___x_4781_; 
v___x_4781_ = l_List_reverse___redArg(v_a_4780_);
return v___x_4781_;
}
else
{
lean_object* v_head_4782_; lean_object* v_tail_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4900_; 
v_head_4782_ = lean_ctor_get(v_a_4779_, 0);
v_tail_4783_ = lean_ctor_get(v_a_4779_, 1);
v_isSharedCheck_4900_ = !lean_is_exclusive(v_a_4779_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4785_ = v_a_4779_;
v_isShared_4786_ = v_isSharedCheck_4900_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_tail_4783_);
lean_inc(v_head_4782_);
lean_dec(v_a_4779_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4900_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___y_4788_; lean_object* v_snd_4793_; lean_object* v_constraint_4794_; lean_object* v_fst_4795_; lean_object* v_lowerBound_4796_; lean_object* v_upperBound_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___y_4802_; lean_object* v___y_4803_; 
v_snd_4793_ = lean_ctor_get(v_head_4782_, 1);
v_constraint_4794_ = lean_ctor_get(v_snd_4793_, 1);
lean_inc_ref(v_constraint_4794_);
v_fst_4795_ = lean_ctor_get(v_head_4782_, 0);
lean_inc(v_fst_4795_);
lean_dec(v_head_4782_);
v_lowerBound_4796_ = lean_ctor_get(v_constraint_4794_, 0);
lean_inc(v_lowerBound_4796_);
v_upperBound_4797_ = lean_ctor_get(v_constraint_4794_, 1);
lean_inc(v_upperBound_4797_);
lean_dec_ref(v_constraint_4794_);
v___x_4798_ = l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0(v_fst_4795_);
lean_dec(v_fst_4795_);
v___x_4799_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__0));
v___x_4800_ = lean_string_append(v___x_4798_, v___x_4799_);
if (lean_obj_tag(v_lowerBound_4796_) == 0)
{
if (lean_obj_tag(v_upperBound_4797_) == 0)
{
lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4808_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__2));
v___x_4809_ = lean_string_append(v___x_4800_, v___x_4808_);
v___y_4788_ = v___x_4809_;
goto v___jp_4787_;
}
else
{
lean_object* v_val_4810_; lean_object* v___x_4811_; lean_object* v___y_4813_; lean_object* v_intZero_4818_; uint8_t v_isNeg_4819_; 
v_val_4810_ = lean_ctor_get(v_upperBound_4797_, 0);
lean_inc(v_val_4810_);
lean_dec_ref_known(v_upperBound_4797_, 1);
v___x_4811_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__3));
v_intZero_4818_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4819_ = lean_int_dec_lt(v_val_4810_, v_intZero_4818_);
if (v_isNeg_4819_ == 0)
{
lean_object* v_a_4820_; lean_object* v___x_4821_; 
v_a_4820_ = lean_nat_abs(v_val_4810_);
lean_dec(v_val_4810_);
v___x_4821_ = l_Nat_reprFast(v_a_4820_);
v___y_4813_ = v___x_4821_;
goto v___jp_4812_;
}
else
{
lean_object* v_abs_4822_; lean_object* v_one_4823_; lean_object* v_a_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; 
v_abs_4822_ = lean_nat_abs(v_val_4810_);
lean_dec(v_val_4810_);
v_one_4823_ = lean_unsigned_to_nat(1u);
v_a_4824_ = lean_nat_sub(v_abs_4822_, v_one_4823_);
lean_dec(v_abs_4822_);
v___x_4825_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4826_ = lean_nat_add(v_a_4824_, v_one_4823_);
lean_dec(v_a_4824_);
v___x_4827_ = l_Nat_reprFast(v___x_4826_);
v___x_4828_ = lean_string_append(v___x_4825_, v___x_4827_);
lean_dec_ref(v___x_4827_);
v___y_4813_ = v___x_4828_;
goto v___jp_4812_;
}
v___jp_4812_:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4814_ = lean_string_append(v___x_4811_, v___y_4813_);
lean_dec_ref(v___y_4813_);
v___x_4815_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4816_ = lean_string_append(v___x_4814_, v___x_4815_);
v___x_4817_ = lean_string_append(v___x_4800_, v___x_4816_);
lean_dec_ref(v___x_4816_);
v___y_4788_ = v___x_4817_;
goto v___jp_4787_;
}
}
}
else
{
if (lean_obj_tag(v_upperBound_4797_) == 0)
{
lean_object* v_val_4829_; lean_object* v___x_4830_; lean_object* v___y_4832_; lean_object* v_intZero_4837_; uint8_t v_isNeg_4838_; 
v_val_4829_ = lean_ctor_get(v_lowerBound_4796_, 0);
lean_inc(v_val_4829_);
lean_dec_ref_known(v_lowerBound_4796_, 1);
v___x_4830_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4837_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4838_ = lean_int_dec_lt(v_val_4829_, v_intZero_4837_);
if (v_isNeg_4838_ == 0)
{
lean_object* v_a_4839_; lean_object* v___x_4840_; 
v_a_4839_ = lean_nat_abs(v_val_4829_);
lean_dec(v_val_4829_);
v___x_4840_ = l_Nat_reprFast(v_a_4839_);
v___y_4832_ = v___x_4840_;
goto v___jp_4831_;
}
else
{
lean_object* v_abs_4841_; lean_object* v_one_4842_; lean_object* v_a_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; 
v_abs_4841_ = lean_nat_abs(v_val_4829_);
lean_dec(v_val_4829_);
v_one_4842_ = lean_unsigned_to_nat(1u);
v_a_4843_ = lean_nat_sub(v_abs_4841_, v_one_4842_);
lean_dec(v_abs_4841_);
v___x_4844_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4845_ = lean_nat_add(v_a_4843_, v_one_4842_);
lean_dec(v_a_4843_);
v___x_4846_ = l_Nat_reprFast(v___x_4845_);
v___x_4847_ = lean_string_append(v___x_4844_, v___x_4846_);
lean_dec_ref(v___x_4846_);
v___y_4832_ = v___x_4847_;
goto v___jp_4831_;
}
v___jp_4831_:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
v___x_4833_ = lean_string_append(v___x_4830_, v___y_4832_);
lean_dec_ref(v___y_4832_);
v___x_4834_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__5));
v___x_4835_ = lean_string_append(v___x_4833_, v___x_4834_);
v___x_4836_ = lean_string_append(v___x_4800_, v___x_4835_);
lean_dec_ref(v___x_4835_);
v___y_4788_ = v___x_4836_;
goto v___jp_4787_;
}
}
else
{
lean_object* v_val_4848_; lean_object* v_val_4849_; uint8_t v___x_4850_; 
v_val_4848_ = lean_ctor_get(v_lowerBound_4796_, 0);
lean_inc(v_val_4848_);
lean_dec_ref_known(v_lowerBound_4796_, 1);
v_val_4849_ = lean_ctor_get(v_upperBound_4797_, 0);
lean_inc(v_val_4849_);
lean_dec_ref_known(v_upperBound_4797_, 1);
v___x_4850_ = lean_int_dec_lt(v_val_4849_, v_val_4848_);
if (v___x_4850_ == 0)
{
uint8_t v___x_4851_; 
v___x_4851_ = lean_int_dec_eq(v_val_4848_, v_val_4849_);
if (v___x_4851_ == 0)
{
lean_object* v___x_4852_; lean_object* v___y_4854_; lean_object* v_intZero_4869_; uint8_t v_isNeg_4870_; 
v___x_4852_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__1));
v_intZero_4869_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4870_ = lean_int_dec_lt(v_val_4848_, v_intZero_4869_);
if (v_isNeg_4870_ == 0)
{
lean_object* v_a_4871_; lean_object* v___x_4872_; 
v_a_4871_ = lean_nat_abs(v_val_4848_);
lean_dec(v_val_4848_);
v___x_4872_ = l_Nat_reprFast(v_a_4871_);
v___y_4854_ = v___x_4872_;
goto v___jp_4853_;
}
else
{
lean_object* v_abs_4873_; lean_object* v_one_4874_; lean_object* v_a_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v_abs_4873_ = lean_nat_abs(v_val_4848_);
lean_dec(v_val_4848_);
v_one_4874_ = lean_unsigned_to_nat(1u);
v_a_4875_ = lean_nat_sub(v_abs_4873_, v_one_4874_);
lean_dec(v_abs_4873_);
v___x_4876_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4877_ = lean_nat_add(v_a_4875_, v_one_4874_);
lean_dec(v_a_4875_);
v___x_4878_ = l_Nat_reprFast(v___x_4877_);
v___x_4879_ = lean_string_append(v___x_4876_, v___x_4878_);
lean_dec_ref(v___x_4878_);
v___y_4854_ = v___x_4879_;
goto v___jp_4853_;
}
v___jp_4853_:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v_intZero_4858_; uint8_t v_isNeg_4859_; 
v___x_4855_ = lean_string_append(v___x_4852_, v___y_4854_);
lean_dec_ref(v___y_4854_);
v___x_4856_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0_spec__0___closed__0));
v___x_4857_ = lean_string_append(v___x_4855_, v___x_4856_);
v_intZero_4858_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4859_ = lean_int_dec_lt(v_val_4849_, v_intZero_4858_);
if (v_isNeg_4859_ == 0)
{
lean_object* v_a_4860_; lean_object* v___x_4861_; 
v_a_4860_ = lean_nat_abs(v_val_4849_);
lean_dec(v_val_4849_);
v___x_4861_ = l_Nat_reprFast(v_a_4860_);
v___y_4802_ = v___x_4857_;
v___y_4803_ = v___x_4861_;
goto v___jp_4801_;
}
else
{
lean_object* v_abs_4862_; lean_object* v_one_4863_; lean_object* v_a_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; 
v_abs_4862_ = lean_nat_abs(v_val_4849_);
lean_dec(v_val_4849_);
v_one_4863_ = lean_unsigned_to_nat(1u);
v_a_4864_ = lean_nat_sub(v_abs_4862_, v_one_4863_);
lean_dec(v_abs_4862_);
v___x_4865_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4866_ = lean_nat_add(v_a_4864_, v_one_4863_);
lean_dec(v_a_4864_);
v___x_4867_ = l_Nat_reprFast(v___x_4866_);
v___x_4868_ = lean_string_append(v___x_4865_, v___x_4867_);
lean_dec_ref(v___x_4867_);
v___y_4802_ = v___x_4857_;
v___y_4803_ = v___x_4868_;
goto v___jp_4801_;
}
}
}
else
{
lean_object* v___x_4880_; lean_object* v___y_4882_; lean_object* v_intZero_4887_; uint8_t v_isNeg_4888_; 
lean_dec(v_val_4849_);
v___x_4880_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__6));
v_intZero_4887_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17, &l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Omega_instToExprLinearCombo___lam__0___closed__17);
v_isNeg_4888_ = lean_int_dec_lt(v_val_4848_, v_intZero_4887_);
if (v_isNeg_4888_ == 0)
{
lean_object* v_a_4889_; lean_object* v___x_4890_; 
v_a_4889_ = lean_nat_abs(v_val_4848_);
lean_dec(v_val_4848_);
v___x_4890_ = l_Nat_reprFast(v_a_4889_);
v___y_4882_ = v___x_4890_;
goto v___jp_4881_;
}
else
{
lean_object* v_abs_4891_; lean_object* v_one_4892_; lean_object* v_a_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; 
v_abs_4891_ = lean_nat_abs(v_val_4848_);
lean_dec(v_val_4848_);
v_one_4892_ = lean_unsigned_to_nat(1u);
v_a_4893_ = lean_nat_sub(v_abs_4891_, v_one_4892_);
lean_dec(v_abs_4891_);
v___x_4894_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__4));
v___x_4895_ = lean_nat_add(v_a_4893_, v_one_4892_);
lean_dec(v_a_4893_);
v___x_4896_ = l_Nat_reprFast(v___x_4895_);
v___x_4897_ = lean_string_append(v___x_4894_, v___x_4896_);
lean_dec_ref(v___x_4896_);
v___y_4882_ = v___x_4897_;
goto v___jp_4881_;
}
v___jp_4881_:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4883_ = lean_string_append(v___x_4880_, v___y_4882_);
lean_dec_ref(v___y_4882_);
v___x_4884_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__7));
v___x_4885_ = lean_string_append(v___x_4883_, v___x_4884_);
v___x_4886_ = lean_string_append(v___x_4800_, v___x_4885_);
lean_dec_ref(v___x_4885_);
v___y_4788_ = v___x_4886_;
goto v___jp_4787_;
}
}
}
else
{
lean_object* v___x_4898_; lean_object* v___x_4899_; 
lean_dec(v_val_4849_);
lean_dec(v_val_4848_);
v___x_4898_ = ((lean_object*)(l_Lean_Elab_Tactic_Omega_Justification_toString___closed__8));
v___x_4899_ = lean_string_append(v___x_4800_, v___x_4898_);
v___y_4788_ = v___x_4899_;
goto v___jp_4787_;
}
}
}
v___jp_4787_:
{
lean_object* v___x_4790_; 
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 1, v_a_4780_);
lean_ctor_set(v___x_4785_, 0, v___y_4788_);
v___x_4790_ = v___x_4785_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___y_4788_);
lean_ctor_set(v_reuseFailAlloc_4792_, 1, v_a_4780_);
v___x_4790_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
v_a_4779_ = v_tail_4783_;
v_a_4780_ = v___x_4790_;
goto _start;
}
}
v___jp_4801_:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4804_ = lean_string_append(v___y_4802_, v___y_4803_);
lean_dec_ref(v___y_4803_);
v___x_4805_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_Tactic_Omega_Justification_toString_spec__0___closed__2));
v___x_4806_ = lean_string_append(v___x_4804_, v___x_4805_);
v___x_4807_ = lean_string_append(v___x_4800_, v___x_4806_);
lean_dec_ref(v___x_4806_);
v___y_4788_ = v___x_4807_;
goto v___jp_4787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(lean_object* v_cls_4901_, lean_object* v_msg_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_){
_start:
{
lean_object* v_ref_4908_; lean_object* v___x_4909_; lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4955_; 
v_ref_4908_ = lean_ctor_get(v___y_4905_, 2);
v___x_4909_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Omega_Problem_dealWithHardEquality_spec__0_spec__0(v_msg_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_);
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4912_ = v___x_4909_;
v_isShared_4913_ = v_isSharedCheck_4955_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4909_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4955_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4914_; lean_object* v_traceState_4915_; lean_object* v_env_4916_; lean_object* v_nextMacroScope_4917_; lean_object* v_ngen_4918_; lean_object* v_auxDeclNGen_4919_; lean_object* v_cache_4920_; lean_object* v_recordedDeps_4921_; lean_object* v_messages_4922_; lean_object* v_infoState_4923_; lean_object* v_snapshotTasks_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4954_; 
v___x_4914_ = lean_st_ref_take(v___y_4906_);
v_traceState_4915_ = lean_ctor_get(v___x_4914_, 4);
v_env_4916_ = lean_ctor_get(v___x_4914_, 0);
v_nextMacroScope_4917_ = lean_ctor_get(v___x_4914_, 1);
v_ngen_4918_ = lean_ctor_get(v___x_4914_, 2);
v_auxDeclNGen_4919_ = lean_ctor_get(v___x_4914_, 3);
v_cache_4920_ = lean_ctor_get(v___x_4914_, 5);
v_recordedDeps_4921_ = lean_ctor_get(v___x_4914_, 6);
v_messages_4922_ = lean_ctor_get(v___x_4914_, 7);
v_infoState_4923_ = lean_ctor_get(v___x_4914_, 8);
v_snapshotTasks_4924_ = lean_ctor_get(v___x_4914_, 9);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4926_ = v___x_4914_;
v_isShared_4927_ = v_isSharedCheck_4954_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_snapshotTasks_4924_);
lean_inc(v_infoState_4923_);
lean_inc(v_messages_4922_);
lean_inc(v_recordedDeps_4921_);
lean_inc(v_cache_4920_);
lean_inc(v_traceState_4915_);
lean_inc(v_auxDeclNGen_4919_);
lean_inc(v_ngen_4918_);
lean_inc(v_nextMacroScope_4917_);
lean_inc(v_env_4916_);
lean_dec(v___x_4914_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4954_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
uint64_t v_tid_4928_; lean_object* v_traces_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4953_; 
v_tid_4928_ = lean_ctor_get_uint64(v_traceState_4915_, sizeof(void*)*1);
v_traces_4929_ = lean_ctor_get(v_traceState_4915_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v_traceState_4915_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4931_ = v_traceState_4915_;
v_isShared_4932_ = v_isSharedCheck_4953_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_traces_4929_);
lean_dec(v_traceState_4915_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4953_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4933_; lean_object* v___x_4934_; double v___x_4935_; uint8_t v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4944_; 
v___x_4933_ = lean_box(0);
v___x_4934_ = lean_box(0);
v___x_4935_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__0);
v___x_4936_ = 0;
v___x_4937_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__1));
v___x_4938_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4938_, 0, v_cls_4901_);
lean_ctor_set(v___x_4938_, 1, v___x_4934_);
lean_ctor_set(v___x_4938_, 2, v___x_4937_);
lean_ctor_set_float(v___x_4938_, sizeof(void*)*3, v___x_4935_);
lean_ctor_set_float(v___x_4938_, sizeof(void*)*3 + 8, v___x_4935_);
lean_ctor_set_uint8(v___x_4938_, sizeof(void*)*3 + 16, v___x_4936_);
v___x_4939_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_fourierMotzkinSelect_spec__0___closed__1));
v___x_4940_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4938_);
lean_ctor_set(v___x_4940_, 1, v_a_4910_);
lean_ctor_set(v___x_4940_, 2, v___x_4939_);
lean_inc(v_ref_4908_);
v___x_4941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4941_, 0, v_ref_4908_);
lean_ctor_set(v___x_4941_, 1, v___x_4940_);
v___x_4942_ = l_Lean_PersistentArray_push___redArg(v_traces_4929_, v___x_4941_);
if (v_isShared_4932_ == 0)
{
lean_ctor_set(v___x_4931_, 0, v___x_4942_);
v___x_4944_ = v___x_4931_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4942_);
lean_ctor_set_uint64(v_reuseFailAlloc_4952_, sizeof(void*)*1, v_tid_4928_);
v___x_4944_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
lean_object* v___x_4946_; 
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 4, v___x_4944_);
v___x_4946_ = v___x_4926_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_env_4916_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_nextMacroScope_4917_);
lean_ctor_set(v_reuseFailAlloc_4951_, 2, v_ngen_4918_);
lean_ctor_set(v_reuseFailAlloc_4951_, 3, v_auxDeclNGen_4919_);
lean_ctor_set(v_reuseFailAlloc_4951_, 4, v___x_4944_);
lean_ctor_set(v_reuseFailAlloc_4951_, 5, v_cache_4920_);
lean_ctor_set(v_reuseFailAlloc_4951_, 6, v_recordedDeps_4921_);
lean_ctor_set(v_reuseFailAlloc_4951_, 7, v_messages_4922_);
lean_ctor_set(v_reuseFailAlloc_4951_, 8, v_infoState_4923_);
lean_ctor_set(v_reuseFailAlloc_4951_, 9, v_snapshotTasks_4924_);
v___x_4946_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
lean_object* v___x_4947_; lean_object* v___x_4949_; 
v___x_4947_ = lean_st_ref_put(v___y_4906_, v___x_4946_);
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 0, v___x_4933_);
v___x_4949_ = v___x_4912_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4933_);
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
lean_inc_ref(v_constraints_5063_);
v___x_5064_ = l_Lean_Elab_Tactic_Omega_Problem_isEmpty(v_p_5037_);
if (v___x_5064_ == 0)
{
lean_object* v_toCold_5065_; lean_object* v_options_5066_; uint8_t v_hasTrace_5067_; 
v_toCold_5065_ = lean_ctor_get(v_a_5045_, 0);
v_options_5066_ = lean_ctor_get(v_toCold_5065_, 2);
v_hasTrace_5067_ = lean_ctor_get_uint8(v_options_5066_, sizeof(void*)*1);
if (v_hasTrace_5067_ == 0)
{
lean_dec_ref(v_constraints_5063_);
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
lean_dec_ref(v_constraints_5063_);
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
lean_object* v_buckets_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5104_; 
v_buckets_5072_ = lean_ctor_get(v_constraints_5063_, 1);
v_isSharedCheck_5104_ = !lean_is_exclusive(v_constraints_5063_);
if (v_isSharedCheck_5104_ == 0)
{
lean_object* v_unused_5105_; 
v_unused_5105_ = lean_ctor_get(v_constraints_5063_, 0);
lean_dec(v_unused_5105_);
v___x_5074_ = v_constraints_5063_;
v_isShared_5075_ = v_isSharedCheck_5104_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_buckets_5072_);
lean_dec(v_constraints_5063_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5104_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___y_5079_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; uint8_t v___x_5100_; 
v___x_5076_ = lean_obj_once(&l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1, &l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1_once, _init_l_Lean_Elab_Tactic_Omega_Problem_elimination___closed__1);
v___x_5077_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Elab_Tactic_Omega_Core_0__Lean_Elab_Tactic_Omega_Justification_bullet_spec__0___redArg___closed__0));
v___x_5097_ = lean_box(0);
v___x_5098_ = lean_array_get_size(v_buckets_5072_);
v___x_5099_ = lean_unsigned_to_nat(0u);
v___x_5100_ = lean_nat_dec_lt(v___x_5099_, v___x_5098_);
if (v___x_5100_ == 0)
{
lean_dec_ref(v_buckets_5072_);
v___y_5079_ = v___x_5097_;
goto v___jp_5078_;
}
else
{
size_t v___x_5101_; size_t v___x_5102_; lean_object* v___x_5103_; 
v___x_5101_ = lean_usize_of_nat(v___x_5098_);
v___x_5102_ = ((size_t)0ULL);
v___x_5103_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__3(v_buckets_5072_, v___x_5101_, v___x_5102_, v___x_5097_);
lean_dec_ref(v_buckets_5072_);
v___y_5079_ = v___x_5103_;
goto v___jp_5078_;
}
v___jp_5078_:
{
lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5086_; 
v___x_5080_ = lean_box(0);
v___x_5081_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__1(v___y_5079_, v___x_5080_);
v___x_5082_ = l_String_intercalate(v___x_5077_, v___x_5081_);
v___x_5083_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5083_, 0, v___x_5082_);
v___x_5084_ = l_Lean_MessageData_ofFormat(v___x_5083_);
if (v_isShared_5075_ == 0)
{
lean_ctor_set_tag(v___x_5074_, 7);
lean_ctor_set(v___x_5074_, 1, v___x_5084_);
lean_ctor_set(v___x_5074_, 0, v___x_5076_);
v___x_5086_ = v___x_5074_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v___x_5076_);
lean_ctor_set(v_reuseFailAlloc_5096_, 1, v___x_5084_);
v___x_5086_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
lean_object* v___x_5087_; 
v___x_5087_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5069_, v___x_5086_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_dec_ref_known(v___x_5087_, 1);
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
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5095_; 
lean_dec_ref(v_p_5037_);
v_a_5088_ = lean_ctor_get(v___x_5087_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5087_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5090_ = v___x_5087_;
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___x_5087_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5093_; 
if (v_isShared_5091_ == 0)
{
v___x_5093_ = v___x_5090_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_a_5088_);
v___x_5093_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
return v___x_5093_;
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
lean_object* v___x_5106_; 
lean_dec_ref(v_constraints_5063_);
v___x_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5106_, 0, v_p_5037_);
return v___x_5106_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_elimination___boxed(lean_object* v_p_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_){
_start:
{
uint8_t v_a_boxed_5118_; lean_object* v_res_5119_; 
v_a_boxed_5118_ = lean_unbox(v_a_5111_);
v_res_5119_ = l_Lean_Elab_Tactic_Omega_Problem_elimination(v_p_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_boxed_5118_, v_a_5112_, v_a_5113_, v_a_5114_, v_a_5115_, v_a_5116_);
lean_dec(v_a_5116_);
lean_dec_ref(v_a_5115_);
lean_dec(v_a_5114_);
lean_dec_ref(v_a_5113_);
lean_dec(v_a_5112_);
lean_dec_ref(v_a_5110_);
lean_dec(v_a_5109_);
lean_dec(v_a_5108_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_Problem_runOmega___boxed(lean_object* v_p_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_){
_start:
{
uint8_t v_a_boxed_5131_; lean_object* v_res_5132_; 
v_a_boxed_5131_ = lean_unbox(v_a_5124_);
v_res_5132_ = l_Lean_Elab_Tactic_Omega_Problem_runOmega(v_p_5120_, v_a_5121_, v_a_5122_, v_a_5123_, v_a_boxed_5131_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_);
lean_dec(v_a_5129_);
lean_dec_ref(v_a_5128_);
lean_dec(v_a_5127_);
lean_dec_ref(v_a_5126_);
lean_dec(v_a_5125_);
lean_dec_ref(v_a_5123_);
lean_dec(v_a_5122_);
lean_dec(v_a_5121_);
return v_res_5132_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(lean_object* v_cls_5133_, lean_object* v_msg_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, uint8_t v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_){
_start:
{
lean_object* v___x_5145_; 
v___x_5145_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___redArg(v_cls_5133_, v_msg_5134_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_);
return v___x_5145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0___boxed(lean_object* v_cls_5146_, lean_object* v_msg_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_){
_start:
{
uint8_t v___y_16417__boxed_5158_; lean_object* v_res_5159_; 
v___y_16417__boxed_5158_ = lean_unbox(v___y_5151_);
v_res_5159_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_Problem_runOmega_spec__0(v_cls_5146_, v_msg_5147_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_16417__boxed_5158_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_);
lean_dec(v___y_5156_);
lean_dec_ref(v___y_5155_);
lean_dec(v___y_5154_);
lean_dec_ref(v___y_5153_);
lean_dec(v___y_5152_);
lean_dec_ref(v___y_5150_);
lean_dec(v___y_5149_);
lean_dec(v___y_5148_);
return v_res_5159_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Omega_MinNatAbs(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
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
res = runtime_initialize_Lean_CoreM(builtin);
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
lean_object* initialize_Lean_CoreM(uint8_t builtin);
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
res = initialize_Lean_CoreM(builtin);
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
